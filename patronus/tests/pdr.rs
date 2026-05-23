// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::{BitVecOps, Value};
use patronus::btor2;
use patronus::expr::Context;
use patronus::mc::{InitValue, ModelCheckResult, Witness, bmc, pdr};
use patronus::sim::{InitKind, Interpreter, Simulator};
use patronus::smt::{BITWUZLA, Solver};
use patronus::system::TransitionSystem;

/// 1-bit state initialised to 1, held at 1 forever — bad state fires immediately (0-step CEX).
const STARTS_BAD: &str = r#"
1 sort bitvec 1
2 ones 1
3 state 1
4 init 1 3 2
5 next 1 3 2
6 bad 3
"#;

/// 1-bit state (init 0) that copies a `trigger` input each cycle.
/// Bad when state = 1. Minimal CEX: trigger=1 at step 0 → bad at step 1.
const TRIGGER_BAD: &str = r#"
1 sort bitvec 1
2 input 1 trigger
3 zero 1
4 state 1 st
5 init 1 4 3
6 next 1 4 2
7 bad 4
"#;

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

/// Like run_pdr_str but also returns the context and system needed for witness replay.
fn run_pdr_str_full(src: &str) -> (Context, TransitionSystem, ModelCheckResult) {
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, src, Some("test")).expect("parse failed");
    let mut smt_ctx = BITWUZLA.start(None).expect("solver start failed");
    let result = pdr(&mut ctx, &mut smt_ctx, &sys).expect("PDR error");
    (ctx, sys, result)
}

/// Replays a PDR counterexample witness through the interpreter and asserts
/// that every property in `wit.failed_safety` fires at the final step.
///
/// The witness encodes a chain of `N` states: `wit.inputs[i]` are the inputs
/// at step `i`, and the bad state fires when the simulator reaches step `N-1`
/// with those inputs applied.  For a 0-step CEX `N == 1` and no `step()` call
/// is made.
fn validate_witness(ctx: &Context, sys: &TransitionSystem, wit: &Witness) {
    assert!(
        !wit.failed_safety.is_empty(),
        "witness must name at least one failed safety property"
    );
    assert!(!wit.inputs.is_empty(), "witness must have at least one step entry");

    let mut sim = Interpreter::new(ctx, sys);
    sim.init(InitKind::Zero);

    // Override initial state values with those captured by the solver.
    for (state, init_val) in sys.states.iter().zip(wit.init.iter()) {
        if let InitValue::BitVec(bv) = init_val {
            sim.set(state.symbol, bv);
        }
        // Array states: sim.init already applied the init expression; skip.
    }

    let last_step = wit.inputs.len() - 1;
    for (step, step_inputs) in wit.inputs.iter().enumerate() {
        // Apply inputs for this step.
        for (inp_sym, inp_val) in sys.inputs.iter().zip(step_inputs.iter()) {
            if let Some(Value::BitVec(bv)) = inp_val {
                sim.set(*inp_sym, bv);
            }
        }

        if step == last_step {
            // At the final step, every listed bad state must be non-zero.
            for &bad_idx in &wit.failed_safety {
                let bad_expr = sys.bad_states[bad_idx as usize];
                if let Value::BitVec(bv) = sim.get(bad_expr) {
                    assert!(
                        !bv.is_zero(),
                        "bad state {bad_idx} should fire at step {step} but evaluates to 0"
                    );
                } else {
                    panic!("bad state {bad_idx} is not a bit-vector expression");
                }
            }
        } else {
            sim.step();
        }
    }
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
        (ModelCheckResult::Unknown, _) => panic!("Unknown result from PDR"),
        _ => panic!("Unknown result from BMC"),
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

#[test]
fn pdr_bmc_agree_quiz2_pass() {
    if !bitwuzla_available() {
        return;
    }
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/chiseltest/Quiz2.unsat.btor"),
        run_bmc_file("../inputs/chiseltest/Quiz2.unsat.btor"),
        "Quiz2_should_pass",
    );
}

#[test]
fn pdr_bmc_agree_quiz2_fail() {
    if !bitwuzla_available() {
        return;
    }
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/chiseltest/Quiz2.sat.btor"),
        run_bmc_file("../inputs/chiseltest/Quiz2.sat.btor"),
        "Quiz2_should_fail",
    );
}

#[test]
fn pdr_bmc_agree_quiz4_pass() {
    if !bitwuzla_available() {
        return;
    }
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/chiseltest/Quiz4.unsat.btor"),
        run_bmc_file("../inputs/chiseltest/Quiz4.unsat.btor"),
        "Quiz4_should_pass",
    );
}

#[test]
fn pdr_bmc_agree_quiz4_fail() {
    if !bitwuzla_available() {
        return;
    }
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/chiseltest/Quiz4.sat.btor"),
        run_bmc_file("../inputs/chiseltest/Quiz4.sat.btor"),
        "Quiz4_should_fail",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Witness validation: replay PDR counterexamples through the simulator
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn starts_bad_pdr_witness_valid() {
    if !bitwuzla_available() {
        return;
    }
    // STARTS_BAD fires at step 0 — the witness chain has exactly one entry.
    let (ctx, sys, result) = run_pdr_str_full(STARTS_BAD);
    if let ModelCheckResult::Fail(wit) = result {
        assert_eq!(wit.inputs.len(), 1, "expected a 0-step witness, got {} steps", wit.inputs.len());
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("Expected Fail for STARTS_BAD, got {:?}", result);
    }
}

#[test]
fn count2_pdr_witness_valid() {
    if !bitwuzla_available() {
        return;
    }
    let (ctx, sys, result) = run_pdr_str_full(COUNT_2);
    if let ModelCheckResult::Fail(wit) = result {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("Expected Fail for COUNT_2, got {:?}", result);
    }
}

#[test]
fn trigger_bad_pdr_witness_valid() {
    if !bitwuzla_available() {
        return;
    }
    // TRIGGER_BAD needs exactly one transition (trigger=1 at step 0 → bad at step 1).
    let (ctx, sys, result) = run_pdr_str_full(TRIGGER_BAD);
    if let ModelCheckResult::Fail(wit) = result {
        assert_eq!(wit.inputs.len(), 2, "expected a 2-step witness, got {} steps", wit.inputs.len());
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("Expected Fail for TRIGGER_BAD, got {:?}", result);
    }
}
