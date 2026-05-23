// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::btor2;
use patronus::expr::Context;
use patronus::mc::{ModelCheckResult, bmc, pdr};
use patronus::smt::{BITWUZLA, Solver};

/// A 3-bit counter (no inputs) that starts at 0, increments by 1 each cycle,
/// and asserts bad when counter == 7 (0b111). CEX trace length = 7 steps.
const COUNT_2: &str = r#"
1 sort bitvec 3
2 zero 1
3 state 1
4 init 1 3 2
5 one 1
6 add 1 3 5
7 next 1 3 6
8 ones 1
9 sort bitvec 1
10 eq 9 3 8
11 bad 10
"#;

fn bitwuzla_available() -> bool {
    std::process::Command::new("bitwuzla")
        .arg("--version")
        .output()
        .is_ok()
}

fn run_pdr_file(path: &str) -> ModelCheckResult {
    let (mut ctx, sys) = btor2::parse_file(path).expect("parse failed");
    let mut smt_ctx = BITWUZLA.start(None).expect("solver start failed");
    pdr(&mut ctx, &mut smt_ctx, &sys).expect("PDR error")
}

fn run_bmc_file(path: &str) -> ModelCheckResult {
    let (mut ctx, sys) = btor2::parse_file(path).expect("parse failed");
    let mut smt_ctx = BITWUZLA.start(None).expect("solver start failed");
    bmc(&mut ctx, &mut smt_ctx, &sys, false, false, 50).expect("BMC error")
}

fn run_pdr_str(src: &str) -> ModelCheckResult {
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, src, Some("test")).expect("parse failed");
    let mut smt_ctx = BITWUZLA.start(None).expect("solver start failed");
    pdr(&mut ctx, &mut smt_ctx, &sys).expect("PDR error")
}

fn run_bmc_str(src: &str) -> ModelCheckResult {
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, src, Some("test")).expect("parse failed");
    let mut smt_ctx = BITWUZLA.start(None).expect("solver start failed");
    bmc(&mut ctx, &mut smt_ctx, &sys, false, false, 50).expect("BMC error")
}

// ─────────────────────────────────────────────────────────────────────────────
// Safe systems
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn delay_btor_pdr_success() {
    if !bitwuzla_available() {
        return;
    }
    // delay.btor has no bad states → instant Success.
    let res = run_pdr_file("../inputs/unittest/delay.btor");
    assert!(matches!(res, ModelCheckResult::Success));
}

#[test]
fn swap_btor_pdr_success() {
    if !bitwuzla_available() {
        return;
    }
    // swap.btor has no bad states → instant Success.
    let res = run_pdr_file("../inputs/unittest/swap.btor");
    assert!(matches!(res, ModelCheckResult::Success));
}

#[test]
fn quiz1_unsat_pdr_success() {
    if !bitwuzla_available() {
        return;
    }
    let res = run_pdr_file("../inputs/chiseltest/Quiz1.unsat.btor");
    assert!(
        matches!(res, ModelCheckResult::Success),
        "Expected Success (or Unknown) for Quiz1.unsat, got {:?}",
        res
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Unsafe systems: CEX detection
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn count2_pdr_fail() {
    if !bitwuzla_available() {
        return;
    }
    let res = run_pdr_str(COUNT_2);
    assert!(
        matches!(res, ModelCheckResult::Fail(_)),
        "Expected Fail for COUNT_2 (counter reaches 7)"
    );
}

#[test]
fn count2_pdr_witness_nonempty() {
    if !bitwuzla_available() {
        return;
    }
    if let ModelCheckResult::Fail(wit) = run_pdr_str(COUNT_2) {
        assert!(!wit.failed_safety.is_empty(), "Must name at least one failed property");
        // CEX must have at least 8 steps (states 0..7).
        assert!(wit.inputs.len() >= 7, "Witness too short: {} steps", wit.inputs.len());
    } else {
        panic!("Expected Fail");
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Agreement with BMC
// ─────────────────────────────────────────────────────────────────────────────

fn check_pdr_bmc_agree(pdr_res: ModelCheckResult, bmc_res: ModelCheckResult, label: &str) {
    match (pdr_res, bmc_res) {
        (ModelCheckResult::Fail(pw), ModelCheckResult::Fail(bw)) => {
            assert_eq!(
                pw.failed_safety, bw.failed_safety,
                "{label}: PDR and BMC disagree on which properties failed"
            );
        }
        (ModelCheckResult::Success, ModelCheckResult::Success) => {}
        (ModelCheckResult::Success, ModelCheckResult::Fail(_)) => {
            panic!("{label}: PDR says safe but BMC found a counterexample");
        }
        (ModelCheckResult::Fail(_), ModelCheckResult::Success) => {
            panic!("{label}: PDR found a counterexample but BMC says safe");
        }
        (ModelCheckResult::Unknown, ModelCheckResult::Unknown) => {
            ()
        }
        // Unknown from BMC XOR PDR is unacceptable.
        _ => panic!("Unknown result")
    }
}

#[test]
fn pdr_bmc_agree_count2() {
    if !bitwuzla_available() {
        return;
    }
    check_pdr_bmc_agree(run_pdr_str(COUNT_2), run_bmc_str(COUNT_2), "COUNT_2");
}

#[test]
fn pdr_bmc_agree_delay() {
    if !bitwuzla_available() {
        return;
    }
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/unittest/delay.btor"),
        run_bmc_file("../inputs/unittest/delay.btor"),
        "delay.btor",
    );
}

#[test]
fn pdr_bmc_agree_swap() {
    if !bitwuzla_available() {
        return;
    }
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/unittest/swap.btor"),
        run_bmc_file("../inputs/unittest/swap.btor"),
        "swap.btor",
    );
}

#[test]
fn pdr_bmc_agree_quiz1_pass() {
    if !bitwuzla_available() {
        return;
    }
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/chiseltest/Quiz1_should_pass_with_assumption_Quiz1.btor"),
        run_bmc_file("../inputs/chiseltest/Quiz1_should_pass_with_assumption_Quiz1.btor"),
        "Quiz1_should_pass",
    );
}
