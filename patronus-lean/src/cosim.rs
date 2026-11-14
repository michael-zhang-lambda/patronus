// released under BSD 3-Clause License

//! Co-simulation support: run the same initial state and input trace through the
//! patronus [`Interpreter`] and through the generated Lean model (`TransSys.simulate`),
//! producing comparable canonical text lines.
//!
//! Canonical line format (one per step `k`, for states `s_0 .. s_n`):
//! `name=<decimal> ...` for every state, sorted by name, followed by ` bad=<0|1>` for
//! steps `0 .. n-1` (where `bad s_k i_k` is defined). The final state line has no `bad`.

use crate::{signal_names, translate_to_str};
use baa::{BitVecOps, BitVecValue};
use patronus::expr::{Context, ExprRef, TypeCheck};
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
    pub oracle: Vec<(String, BitVecValue)>,
    /// Input values (by Lean field name) for each step.
    pub inputs: Vec<Vec<(String, BitVecValue)>>,
}

fn bv_value(sim: &Interpreter, expr: ExprRef) -> BitVecValue {
    match sim.get(expr) {
        baa::Value::BitVec(v) => v,
        baa::Value::Array(_) => unimplemented!("arrays are not supported"),
    }
}

fn bv_width(ctx: &Context, expr: ExprRef) -> baa::WidthInt {
    expr.get_bv_type(ctx)
        .expect("only bit-vector signals are supported")
}

/// Create a random trace: initialize with `InitKind::Random(seed)`, read the oracle from the
/// resulting state values, and draw `steps` random input assignments.
pub fn random_trace(ctx: &Context, sys: &TransitionSystem, steps: usize, seed: u64) -> Trace {
    let (states, inputs) = signal_names(ctx, sys);
    let mut sim = Interpreter::new(ctx, sys);
    sim.init(InitKind::Random(seed));
    let oracle = states
        .iter()
        .map(|(state, name)| (name.clone(), bv_value(&sim, state.symbol)))
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
                        BitVecValue::random(&mut rng, bv_width(ctx, *expr)),
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
            .map(|(state, name)| format!("{name}={}", bv_value(sim, state.symbol).to_dec_str()))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let trace_line = |cycle: u64, sys: &TransitionSystem, sim: &Interpreter| -> String {
        let bad = sys.bad_states.iter().any(|&b| bv_value(sim, b).is_true());
        let cons = sys.constraints.iter().all(|&c| bv_value(sim, c).is_true());
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
        debug_assert_eq!(&bv_value(&sim, state.symbol), value);
    }

    let mut lines = Vec::with_capacity(trace.inputs.len() + 1);
    for (cycle, step_inputs) in trace.inputs.iter().enumerate() {
        for ((expr, name), (iname, value)) in inputs.iter().zip(step_inputs.iter()) {
            assert_eq!(name, iname, "trace inputs do not match system inputs");
            sim.set(*expr, value);
        }
        lines.push(trace_line(cycle as u64, sys, &sim));
        sim.step();
    }
    lines
}

fn lean_struct(fields: &[(String, BitVecValue)]) -> String {
    if fields.is_empty() {
        return "{}".to_string();
    }
    let body = fields
        .iter()
        .map(|(name, v)| format!("{name} := {}#{}", v.to_dec_str(), v.width()))
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
    let mut sorted_names: Vec<&str> = states.iter().map(|(_, n)| n.as_str()).collect();
    sorted_names.sort();

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
    let line = sorted_names
        .iter()
        .map(|n| format!("{n}={{s.{n}.toNat}}"))
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
