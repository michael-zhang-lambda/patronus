// released under BSD 3-Clause License

//! Co-simulates the generated Lean model (`TransSys.simulate`) against the patronus interpreter.
//!
//! Requires `lake` and the hw-formal Lean project (`$HW_FORMAL_DIR`, default
//! `~/cornell/research/lean/hw-formal`). If either is missing the tests print a skip message
//! and pass.

use baa::{BitVecOps, BitVecValue};
use patronus::btor2;
use patronus::expr::Context;
use patronus::system::TransitionSystem;
use patronus_lean::cosim::{Trace, lean_harness, parse_lean_output, random_trace, rust_states};
use std::path::PathBuf;
use std::process::Command;
use std::sync::OnceLock;

const STEPS: usize = 80;
const SEEDS: [u64; 3] = [0, 1, 0xdead_beef];

fn hw_formal_dir() -> Option<PathBuf> {
    let dir = match std::env::var_os("HW_FORMAL_DIR") {
        Some(d) => PathBuf::from(d),
        None => PathBuf::from(std::env::var_os("HOME")?).join("cornell/research/lean/hw-formal"),
    };
    let is_lake_project = dir.join("lakefile.toml").exists() || dir.join("lakefile.lean").exists();
    is_lake_project.then_some(dir)
}

/// Locate the Lean project and build `HwFormal` once. Returns `None` (skip) if unavailable.
fn lean_env() -> Option<&'static PathBuf> {
    static ENV: OnceLock<Option<PathBuf>> = OnceLock::new();
    ENV.get_or_init(|| {
        let Some(dir) = hw_formal_dir() else {
            eprintln!("SKIP: hw-formal Lean project not found (set HW_FORMAL_DIR)");
            return None;
        };
        match Command::new("lake")
            .args(["build", "HwFormal"])
            .current_dir(&dir)
            .output()
        {
            Err(e) => {
                eprintln!("SKIP: could not run `lake`: {e}");
                None
            }
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

fn fmt_values(values: &[(String, BitVecValue)]) -> String {
    values
        .iter()
        .map(|(n, v)| format!("{n}={}", v.to_dec_str()))
        .collect::<Vec<_>>()
        .join(" ")
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
