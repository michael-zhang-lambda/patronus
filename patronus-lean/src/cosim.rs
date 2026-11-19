// released under BSD 3-Clause License

//! Co-simulation support: run the same initial state and input trace through the
//! patronus [`Interpreter`] and through the generated Lean model (`TransSys.simulate`),
//! producing comparable canonical text lines.
//!
//! Canonical line format (one per step `k`, for states `s_0 .. s_n`):
//! `name=<decimal> ...` for every state, sorted by name, followed by ` bad=<0|1>` for
//! steps `0 .. n-1` (where `bad s_k i_k` is defined). The final state line has no `bad`.

use crate::utils::{escape_name, no_next_state_set};
use crate::{signal_names, translate_to_str};
use baa::{ArrayOps, ArrayValue, BitVecOps, BitVecValue, Value};
use patronus::expr::{Context, Type, TypeCheck};
use patronus::sim::{InitKind, Interpreter, Simulator};
use patronus::system::TransitionSystem;
use rand::SeedableRng;
use rand::rngs::SmallRng;
use std::fmt::Write;

/// Marker printed by the Lean harness before the trace, so compiler messages
/// (e.g. `declaration uses 'sorry'`) can be separated from the simulation output.
pub const LEAN_TRACE_MARKER: &str = "--- cosim trace ---";

/// An initial-state oracle plus a sequence of input assignments.
#[derive(Debug, Clone)]
pub struct Trace {
    /// Seed passed to `InitKind::Random` for the interpreter's initialization.
    pub seed: u64,
    /// Value of every state (by Lean field name) right after `init`, used as the Lean oracle `o`.
    pub oracle: Vec<(String, Value)>,
    /// Input values (by Lean field name) for each step.
    pub inputs: Vec<Vec<(String, Value)>>,
}

fn array_elems(a: &ArrayValue) -> impl Iterator<Item = BitVecValue> + '_ {
    (0..a.num_elements() as u64).map(|i| a.select(&BitVecValue::from_u64(i, a.index_width())))
}

pub fn val_to_string(v: &Value) -> String {
    match v {
        Value::BitVec(bv) => bv.to_dec_str(),
        Value::Array(av) => format!(
            "[{}]",
            array_elems(av)
                .map(|v| v.to_dec_str())
                .collect::<Vec<_>>()
                .join("; ")
        ),
    }
}

fn val_to_lean(v: &Value) -> String {
    match v {
        Value::BitVec(bv) => format!("{}#{}", bv.to_dec_str(), bv.width()),
        Value::Array(av) => {
            let xs = array_elems(av)
                .map(|v| format!("{}#{}", v.to_dec_str(), v.width()))
                .collect::<Vec<_>>()
                .join(", ");
            format!("(BVArray.ofList [{xs}])")
        }
    }
}

/// Create a random trace: initialize with `InitKind::Random(seed)`, read the oracle from the
/// resulting state values, and draw `steps` random input assignments.
pub fn random_trace(ctx: &Context, sys: &TransitionSystem, steps: usize, seed: u64) -> Trace {
    let (states, inputs) = signal_names(ctx, sys);
    let mut sim = Interpreter::new(ctx, sys);
    sim.init(InitKind::Random(seed));
    let oracle = states
        .iter()
        .map(|(state, name)| (name.clone(), sim.get(state.symbol)))
        .collect();

    // use a different stream than the one the interpreter used for initialization
    let mut rng = SmallRng::seed_from_u64(seed ^ 0x9e37_79b9_7f4a_7c15);
    let inputs = (0..=steps)
        .map(|_| {
            inputs
                .iter()
                .map(|(expr, name)| {
                    (
                        name.clone(),
                        match expr.get_type(ctx) {
                            Type::BV(w) => Value::BitVec(BitVecValue::random(&mut rng, w)),
                            Type::Array(t) => Value::Array(ArrayValue::random(
                                &mut rng,
                                t.index_width,
                                t.data_width,
                            )),
                        },
                    )
                })
                .collect()
        })
        .collect();
    Trace {
        seed,
        oracle,
        inputs,
    }
}

/// Run `trace` through the patronus interpreter and return the canonical lines.
pub fn rust_states(ctx: &Context, sys: &TransitionSystem, trace: &Trace) -> Vec<String> {
    let (states, inputs) = signal_names(ctx, sys);
    let mut sorted_states: Vec<_> = states.iter().collect();
    sorted_states.sort_by(|a, b| a.1.cmp(&b.1));

    let state_line = |sim: &Interpreter| -> String {
        sorted_states
            .iter()
            .map(|(state, name)| format!("{name}={}", val_to_string(&sim.get(state.symbol))))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let trace_line = |cycle: u64, sys: &TransitionSystem, sim: &Interpreter| -> String {
        let bad = sys.bad_states.iter().any(|&b| match sim.get(b) {
            Value::BitVec(bv) => bv.is_true(),
            Value::Array(_) => unreachable!(),
        });
        let cons = sys.constraints.iter().all(|&c| match sim.get(c) {
            Value::BitVec(bv) => bv.is_true(),
            Value::Array(_) => unreachable!(),
        });
        format!(
            "{}, {}, bad={}, constraint={}",
            cycle,
            state_line(sim),
            bad as u8,
            cons as u8
        )
    };

    // Same initialization the oracle was derived from: Lean's `init o` must reproduce this
    // state (uninitialized states read `o.name`, initialized ones re-evaluate their init expr).
    let mut sim = Interpreter::new(ctx, sys);
    sim.init(InitKind::Random(trace.seed));
    for ((state, name), (oname, value)) in states.iter().zip(trace.oracle.iter()) {
        assert_eq!(name, oname, "oracle does not match system states");
        debug_assert_eq!(val_to_string(&sim.get(state.symbol)), val_to_string(value));
    }

    // A state without `next` is keyed by its own symbol in `inputs` (its `$next` input). The
    // interpreter holds such a state's value across `step`, so its `$next` value from cycle k is
    // written into the state *after* stepping, matching Lean's `next := i.«x$next»`.
    let next_less = no_next_state_set(sys);
    let set = |sim: &mut Interpreter, expr, value: &Value| match value {
        Value::BitVec(bv) => sim.set(expr, bv),
        Value::Array(av) => sim.set_array(expr, av.clone()),
    };

    let mut lines = Vec::with_capacity(trace.inputs.len() + 1);
    for (cycle, step_inputs) in trace.inputs.iter().enumerate() {
        assert_eq!(inputs.len(), step_inputs.len(), "trace inputs do not match system inputs");
        for ((expr, name), (iname, value)) in inputs.iter().zip(step_inputs.iter()) {
            assert_eq!(name, iname, "trace inputs do not match system inputs");
            if !next_less.contains(expr) {
                set(&mut sim, *expr, value);
            }
        }
        lines.push(trace_line(cycle as u64, sys, &sim));
        sim.step();
        for ((expr, _), (_, value)) in inputs.iter().zip(step_inputs.iter()) {
            if next_less.contains(expr) {
                set(&mut sim, *expr, value);
            }
        }
    }
    lines
}

fn lean_struct(fields: &[(String, Value)]) -> String {
    if fields.is_empty() {
        return "{}".to_string();
    }
    let body = fields
        .iter()
        .map(|(name, v)| format!("{} := {}", escape_name(name.clone()), val_to_lean(v)))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{{ {body} }}")
}

/// Generate a self-contained Lean file: the translated system plus a `main` that prints
/// the canonical lines of `TransSys.simulate` on `trace` (after [`LEAN_TRACE_MARKER`]).
pub fn lean_harness(ctx: &Context, sys: &TransitionSystem, trace: &Trace) -> String {
    let sys_name = if sys.name.is_empty() {
        "System"
    } else {
        sys.name.as_str()
    };
    let (states, _) = signal_names(ctx, sys);
    let mut sorted_states: Vec<_> = states.iter().collect();
    sorted_states.sort_by(|a, b| a.1.cmp(&b.1));

    let mut out = translate_to_str(ctx, sys);
    let w = &mut out;
    writeln!(w).unwrap();
    writeln!(w, "namespace {sys_name}").unwrap();
    writeln!(w).unwrap();
    writeln!(
        w,
        "def cosimOracle : State := {}",
        lean_struct(&trace.oracle)
    )
    .unwrap();
    writeln!(w).unwrap();
    writeln!(w, "def cosimInputs : List Input := [").unwrap();
    for (k, step) in trace.inputs.iter().enumerate() {
        let sep = if k + 1 == trace.inputs.len() { "" } else { "," };
        writeln!(w, "  {}{sep}", lean_struct(step)).unwrap();
    }
    writeln!(w, "]").unwrap();
    writeln!(w).unwrap();
    let line = sorted_states
        .iter()
        .map(|(state, n)| {
            let esc = escape_name(n.clone());
            match state.symbol.get_type(ctx) {
                Type::BV(_) => format!("{n}={{s.{esc}.toNat}}"),
                Type::Array(_) => format!("{n}={{BVArray.toString s.{esc}}}"),
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    writeln!(w, "instance : ToString State where").unwrap();
    writeln!(w, "  toString (s : State) : String := s!\"{line}\"").unwrap();
    writeln!(w).unwrap();
    writeln!(w, "end {sys_name}").unwrap();
    writeln!(w).unwrap();
    writeln!(w, "def main : IO Unit := do").unwrap();
    writeln!(w, "  IO.println \"{LEAN_TRACE_MARKER}\"").unwrap();
    writeln!(w, "  IO.println ({sys_name}.{sys_name}_sys.formatTrace {sys_name}.cosimOracle {sys_name}.cosimInputs)").unwrap();
    out
}

/// Extract the canonical lines from the stdout of the Lean harness.
pub fn parse_lean_output(stdout: &str) -> Option<Vec<String>> {
    let mut lines = stdout.lines();
    lines.find(|l| l.trim() == LEAN_TRACE_MARKER)?;
    Some(lines.map(|l| l.trim_end().to_string()).collect())
}
