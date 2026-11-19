// released under BSD 3-Clause License

//! Co-simulates the generated Lean model (`TransSys.simulate`) against the patronus interpreter.
//!
//! Requires `lake` and the hw-formal Lean project (`$HW_FORMAL_DIR`, default
//! `patronus-lean/hw-formal`). If either is missing the tests print a skip message
//! and pass.

use baa::Value;
use patronus::btor2;
use patronus::expr::Context;
use patronus::system::TransitionSystem;
use patronus_lean::cosim::{
    Trace, lean_harness, parse_lean_output, random_trace, rust_states, val_to_string,
};
use std::path::PathBuf;
use std::process::Command;
use std::sync::OnceLock;

const STEPS: usize = 80;
const SEEDS: [u64; 3] = [0, 1, 0xdead_beef];

fn hw_formal_dir() -> Option<PathBuf> {
    let dir = match std::env::var_os("HW_FORMAL_DIR") {
        Some(d) => PathBuf::from(d),
        None => PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("hw-formal"),
    };
    let is_lake_project = dir.join("lakefile.toml").exists() || dir.join("lakefile.lean").exists();
    is_lake_project.then_some(dir)
}

/// Print a skip message, or panic if `PATRONUS_REQUIRE_LEAN` is set (used in CI so that a
/// missing Lean toolchain fails the build instead of silently skipping the co-simulation).
fn skip(msg: &str) -> Option<PathBuf> {
    if std::env::var_os("PATRONUS_REQUIRE_LEAN").is_some() {
        panic!("{msg} (PATRONUS_REQUIRE_LEAN is set)");
    }
    eprintln!("SKIP: {msg}");
    None
}

/// Locate the Lean project and build `HwFormal` once. Returns `None` (skip) if unavailable.
fn lean_env() -> Option<&'static PathBuf> {
    static ENV: OnceLock<Option<PathBuf>> = OnceLock::new();
    ENV.get_or_init(|| {
        let Some(dir) = hw_formal_dir() else {
            return skip("hw-formal Lean project not found (set HW_FORMAL_DIR)");
        };
        match Command::new("lake")
            .args(["build", "HwFormal"])
            .current_dir(&dir)
            .output()
        {
            Err(e) => skip(&format!("could not run `lake`: {e}")),
            Ok(out) if !out.status.success() => panic!(
                "`lake build HwFormal` failed in {}:\n{}{}",
                dir.display(),
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ),
            Ok(_) => Some(dir),
        }
    })
    .as_ref()
}

fn run_lean(dir: &PathBuf, file: &PathBuf) -> Vec<String> {
    let out = Command::new("lake")
        .args(["env", "lean", "--run"])
        .arg(file)
        .current_dir(dir)
        .output()
        .expect("failed to run `lake env lean --run`");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "Lean harness failed (kept at {}):\n{stdout}{stderr}",
        file.display()
    );
    parse_lean_output(&stdout).unwrap_or_else(|| {
        panic!(
            "no trace marker in Lean output (harness kept at {}):\n{stdout}{stderr}",
            file.display()
        )
    })
}

fn fmt_values(values: &[(String, Value)]) -> String {
    values
        .iter()
        .map(|(n, v)| format!("{n}={}", val_to_string(v)))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Set `COSIM_KEEP=1` to keep the generated harness files even when the traces match.
fn cosim(test_name: &str, ctx: &Context, sys: &TransitionSystem) {
    let Some(dir) = lean_env() else {
        eprintln!("SKIP {test_name}: Lean environment unavailable");
        return;
    };
    for seed in SEEDS {
        let trace: Trace = random_trace(ctx, sys, STEPS, seed);
        let expected = rust_states(ctx, sys, &trace);
        let harness = lean_harness(ctx, sys, &trace);
        let file = std::env::temp_dir().join(format!(
            "patronus_cosim_{test_name}_{seed}_{}.lean",
            std::process::id()
        ));
        std::fs::write(&file, &harness).unwrap();
        let actual = run_lean(dir, &file);

        if let Some(k) =
            (0..expected.len().max(actual.len())).find(|&k| expected.get(k) != actual.get(k))
        {
            let inputs = trace
                .inputs
                .get(k)
                .map(|i| fmt_values(i))
                .unwrap_or_else(|| "<none: final state>".to_string());
            let prev_inputs = k
                .checked_sub(1)
                .and_then(|p| trace.inputs.get(p))
                .map(|i| fmt_values(i))
                .unwrap_or_else(|| "<none: initial state>".to_string());
            panic!(
                "{test_name} seed={seed}: first mismatch at step {k}\n  rust: {:?}\n  lean: {:?}\n  \
                 inputs at step {k}: {inputs}\n  inputs at step {}: {prev_inputs}\n  \
                 oracle: {}\n  harness kept at {}",
                expected.get(k),
                actual.get(k),
                k.saturating_sub(1),
                fmt_values(&trace.oracle),
                file.display()
            );
        }
        println!("{test_name} seed={seed}: {} lines match", expected.len());
        if std::env::var_os("COSIM_KEEP").is_none() {
            let _ = std::fs::remove_file(&file);
        }
    }
}

fn cosim_file(test_name: &str, path: &str) {
    let (ctx, sys) = btor2::parse_file(path).unwrap();
    cosim(test_name, &ctx, &sys);
}

#[test]
fn cosim_aman_goel_4bit() {
    cosim_file("aman_goel_4bit", "../inputs/unittest/aman_goel_4bit.btor");
}

#[test]
fn cosim_aman_goel_16bit() {
    cosim_file("aman_goel_16bit", "../inputs/unittest/aman_goel_16bit.btor");
}

#[test]
fn cosim_swap() {
    cosim_file("swap", "../inputs/verilog_tests/Swap.btor");
}

#[test]
fn cosim_delay() {
    cosim_file("delay", "../inputs/verilog_tests/Delay.btor");
}

#[test]
fn cosim_overflow() {
    cosim_file("overflow", "../inputs/verilog_tests/Overflow.btor");
}

#[test]
fn cosim_accumulate() {
    cosim_file("accumulate", "../inputs/verilog_tests/Accumulate.btor");
}

#[test]
fn cosim_array_equal() {
    cosim_file("array_equal", "../inputs/verilog_tests/ArrayEqual.btor");
}

#[test]
fn cosim_memory() {
    cosim_file("memory", "../inputs/verilog_tests/Memory.btor");
}

#[test]
fn cosim_memory_init() {
    cosim_file("memory_init", "../inputs/verilog_tests/MemoryInit.btor");
}

#[test]
fn cosim_memory_pair() {
    cosim_file("memory_pair", "../inputs/verilog_tests/MemoryPair.btor");
}

#[test]
fn cosim_memory_unsafe() {
    cosim_file("memory_unsafe", "../inputs/verilog_tests/MemoryUnsafe.btor");
}

/// Exercises the oracle path (a state without `init`) and an `init` expression that
/// references another state (translated with the `o.` prefix).
#[test]
fn cosim_uninit_state() {
    let src = "\
1 sort bitvec 4
2 sort bitvec 1
3 input 1 d
4 input 2 en
5 state 1 x
6 state 1 y
7 init 1 6 5
8 add 1 5 3
9 ite 1 4 8 5
10 next 1 5 9
11 next 1 6 5
12 ugt 2 5 6
13 bad 12
";
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, src, Some("Uninit")).unwrap();
    cosim("uninit_state", &ctx, &sys);
}

#[test]
fn cosim_arith() {
    cosim_file("arith", "../inputs/verilog_tests/Arith.btor");
}

#[test]
fn cosim_bitwise() {
    cosim_file("bitwise", "../inputs/verilog_tests/Bitwise.btor");
}

#[test]
fn cosim_compare() {
    cosim_file("compare", "../inputs/verilog_tests/Compare.btor");
}

#[test]
fn cosim_shift() {
    cosim_file("shift", "../inputs/verilog_tests/Shift.btor");
}

#[test]
fn cosim_extend() {
    cosim_file("extend", "../inputs/verilog_tests/Extend.btor");
}

/// The patronus interpreter does not implement `udiv`/`urem`/`sdiv`/`srem`/`smod` yet
/// (`eval.rs` hits a `todo!`), so this co-simulation cannot run until it does.
#[test]
#[ignore = "patronus interpreter lacks div/rem support"]
fn cosim_divide() {
    cosim_file("divide", "../inputs/verilog_tests/Divide.btor");
}

/// `implies` is never emitted by yosys, so it is tested with inline BTOR.
#[test]
fn cosim_implies() {
    let src = "\
1 sort bitvec 4
2 sort bitvec 1
3 input 1 a
4 input 1 b
5 state 2 r
6 ugt 2 3 4
7 ult 2 3 4
8 implies 2 6 7
9 next 2 5 8
10 bad 5
";
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, src, Some("Implies")).unwrap();
    cosim("implies", &ctx, &sys);
}

/// yosys never emits whole-array `eq`, so array equality is tested with inline BTOR:
/// two zero-initialized memories receive identical writes; bad if they differ.
#[test]
fn cosim_array_equal_inline() {
    let src = "\
1 sort bitvec 2
2 sort bitvec 4
3 sort array 1 2
4 sort bitvec 1
5 input 1 a
6 input 2 d
7 const 2 0000
8 state 3 m1
9 state 3 m2
10 init 3 8 7
11 init 3 9 7
12 write 3 8 5 6
13 write 3 9 5 6
14 next 3 8 12
15 next 3 9 13
16 eq 4 8 9
17 not 4 16
18 bad 17
";
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, src, Some("ArrayEqualInline")).unwrap();
    cosim("array_equal_inline", &ctx, &sys);
}

/// Constraints over an input and over state+input (from `assume`); the `constraint=` column of
/// the trace must agree between the interpreter and Lean.
#[test]
fn cosim_constraint() {
    cosim_file("constraint", "../inputs/verilog_tests/Constraint.btor");
}

/// States with `init` but without `next` (named and unnamed): their `init` holds in cycle 0,
/// afterwards their value comes from the previous cycle's `$next` input. One of them is used
/// in a constraint.
///
/// Inline BTOR because yosys never emits a state with `init` but no `next` (see the comment on
/// `NO_NEXT_SRC` in `translate_tests.rs`).
#[test]
fn cosim_no_next_state() {
    let src = "\
1 sort bitvec 4
2 sort bitvec 1
3 input 1 a
4 state 1 x
5 state 1 free
6 state 2
7 add 1 4 3
8 next 1 4 7
9 add 1 4 5
10 ugt 2 9 4
11 and 2 10 6
12 bad 11
13 ugt 2 5 3
14 constraint 13
15 const 1 0101
16 init 1 5 15
17 const 2 1
18 init 2 6 17
";
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, src, Some("NoNext")).unwrap();
    cosim("no_next_state", &ctx, &sys);
}
