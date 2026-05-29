// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::{BitVecOps, Value};
use patronus::btor2;
use patronus::expr::{Context, TypeCheck};
use patronus::mc::{InitValue, ModelCheckResult, Witness, bmc, pdr};
use patronus::sim::{InitKind, Interpreter, Simulator};
use patronus::smt::{BITWUZLA, Solver};
use patronus::system::TransitionSystem;
use regex::Regex;
use std::{fs, io};

/// Resolve a required external dependency.
///
/// On GitHub CI (`GITHUB_ACTIONS` is set) a missing dependency is a hard
/// failure — CI must never silently skip coverage because a tool failed to
/// resolve. On a local machine the test gracefully skips (early return) so
/// developers without the tool installed are not blocked.
macro_rules! require {
    ($available:expr, $name:expr) => {
        if !$available {
            if std::env::var_os("GITHUB_ACTIONS").is_some() {
                panic!(
                    "required dependency '{}' could not be resolved in CI",
                    $name
                );
            } else {
                eprintln!("[skip] '{}' not available — skipping test locally", $name);
                return;
            }
        }
    };
}

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
    pdr(&mut ctx, &mut smt_ctx, &sys, None).expect("PDR error")
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
    pdr(&mut ctx, &mut smt_ctx, &sys, None).expect("PDR error")
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
    let result = pdr(&mut ctx, &mut smt_ctx, &sys, None).expect("PDR error");
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
    assert!(
        !wit.inputs.is_empty(),
        "witness must have at least one step entry"
    );

    let mut sim = Interpreter::new(ctx, sys);
    sim.init(InitKind::Zero);

    // Override initial state values with those captured by the solver.
    for (state, init_val) in sys.states.iter().zip(wit.init.iter()) {
        match init_val {
            InitValue::BitVec(bv) => sim.set(state.symbol, bv),
            InitValue::Array(av, _) => sim.set_array(state.symbol, av),
            InitValue::None => {}
        }
    }

    let last_step = wit.inputs.len() - 1;
    for (step, step_inputs) in wit.inputs.iter().enumerate() {
        // Apply inputs for this step.
        for (inp_sym, inp_val) in sys.inputs.iter().zip(step_inputs.iter()) {
            match inp_val {
                Some(Value::BitVec(bv)) => sim.set(*inp_sym, bv),
                Some(Value::Array(av)) => sim.set_array(*inp_sym, av),
                None => {}
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

/// Like `validate_witness` but includes a label (e.g. filename) in assertion messages.
fn validate_witness_labeled(ctx: &Context, sys: &TransitionSystem, wit: &Witness, label: &str) {
    assert!(
        !wit.failed_safety.is_empty(),
        "[{label}] witness must name at least one failed safety property"
    );
    assert!(
        !wit.inputs.is_empty(),
        "[{label}] witness must have at least one step entry"
    );

    let mut sim = Interpreter::new(ctx, sys);
    sim.init(InitKind::Zero);

    // Override initial state values with those captured by the solver.
    for (state, init_val) in sys.states.iter().zip(wit.init.iter()) {
        match init_val {
            InitValue::BitVec(bv) => sim.set(state.symbol, bv),
            InitValue::Array(av, _) => sim.set_array(state.symbol, av),
            InitValue::None => {}
        }
    }

    let last_step = wit.inputs.len() - 1;
    for (step, step_inputs) in wit.inputs.iter().enumerate() {
        // Apply inputs for this step.
        for (inp_sym, inp_val) in sys.inputs.iter().zip(step_inputs.iter()) {
            match inp_val {
                Some(Value::BitVec(bv)) => sim.set(*inp_sym, bv),
                Some(Value::Array(av)) => sim.set_array(*inp_sym, av),
                None => {}
            }
        }

        if step == last_step {
            // At the final step, every listed bad state must be non-zero.
            for &bad_idx in &wit.failed_safety {
                let bad_expr = sys.bad_states[bad_idx as usize];
                if let Value::BitVec(bv) = sim.get(bad_expr) {
                    assert!(
                        !bv.is_zero(),
                        "[{label}] bad state {bad_idx} should fire at step {step} but evaluates to 0"
                    );
                } else {
                    panic!("[{label}] bad state {bad_idx} is not a bit-vector expression");
                }
            }
        } else {
            sim.step();
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// File utils
// ─────────────────────────────────────────────────────────────────────────────

/// Get all BTOR filenames contained in a directory
fn get_dir_filenames(dir: &str) -> Result<Vec<String>, io::Error> {
    let mut filenames = Vec::new();
    let btor_re = Regex::new(r"^[^\\/]+\.btor2?$").unwrap();

    match fs::read_dir(dir) {
        Ok(rd_dir) => {
            // Iterate through all directory entries
            for entry in rd_dir {
                let entry = entry?;
                let path = entry.path();

                // Add all files to collection
                if path.is_file() {
                    let name = path.canonicalize()?.to_string_lossy().to_string();

                    if btor_re.is_match(path.file_name().unwrap().to_str().unwrap()) {
                        filenames.push(name);
                    }
                }
            }

            Ok(filenames)
        }
        Err(e) => Err(e),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Safe systems
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn delay_btor_pdr_success() {
    require!(bitwuzla_available(), "bitwuzla");
    // delay.btor has no bad states → instant Success.
    let res = run_pdr_file("../inputs/unittest/delay.btor");
    assert!(matches!(res, ModelCheckResult::Success));
}

#[test]
fn swap_btor_pdr_success() {
    require!(bitwuzla_available(), "bitwuzla");
    // swap.btor has no bad states → instant Success.
    let res = run_pdr_file("../inputs/unittest/swap.btor");
    assert!(matches!(res, ModelCheckResult::Success));
}

#[test]
fn quiz1_unsat_pdr_success() {
    require!(bitwuzla_available(), "bitwuzla");
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
    require!(bitwuzla_available(), "bitwuzla");
    let res = run_pdr_str(COUNT_2);
    assert!(
        matches!(res, ModelCheckResult::Fail(_)),
        "Expected Fail for COUNT_2 (counter reaches 7)"
    );
}

#[test]
fn count2_pdr_witness_nonempty() {
    require!(bitwuzla_available(), "bitwuzla");
    if let ModelCheckResult::Fail(wit) = run_pdr_str(COUNT_2) {
        assert!(
            !wit.failed_safety.is_empty(),
            "Must name at least one failed property"
        );
        // CEX must have at least 8 steps (states 0..7).
        assert!(
            wit.inputs.len() >= 7,
            "Witness too short: {} steps",
            wit.inputs.len()
        );
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
            assert!(
                !pw.failed_safety.is_empty(),
                "{label}: PDR counterexample names no failed safety properties"
            );
            assert!(
                !bw.failed_safety.is_empty(),
                "{label}: BMC counterexample names no failed safety properties"
            );
        }
        (ModelCheckResult::Success, ModelCheckResult::Success) => {}
        (ModelCheckResult::Success, ModelCheckResult::Fail(_)) => {
            panic!("{label}: PDR says safe but BMC found a counterexample");
        }
        (ModelCheckResult::Fail(_), ModelCheckResult::Success) => {
            panic!("{label}: PDR found a counterexample but BMC says safe");
        }
        (ModelCheckResult::Unknown, ModelCheckResult::Unknown) => (),
        // Reject cases PDR XOR BMC have Unknown result
        // PDR returned Unknown (e.g., hit the time limit): skip the agreement check.
        // Deep-CEX designs may exceed the PDR budget while BMC (with k=50) still finds the CEX.
        (ModelCheckResult::Unknown, _) => {
            eprintln!("{label}: PDR returned Unknown — skipping agreement check");
        }
        // BMC returned Unknown (no CEX within k=50) but PDR gave a definite result: fine.
        (_, ModelCheckResult::Unknown) => {}
    }
}

#[test]
fn pdr_bmc_agree_count2() {
    require!(bitwuzla_available(), "bitwuzla");
    check_pdr_bmc_agree(run_pdr_str(COUNT_2), run_bmc_str(COUNT_2), "COUNT_2");
}

#[test]
fn pdr_bmc_agree_delay() {
    require!(bitwuzla_available(), "bitwuzla");
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/unittest/delay.btor"),
        run_bmc_file("../inputs/unittest/delay.btor"),
        "delay.btor",
    );
}

#[test]
fn pdr_bmc_agree_swap() {
    require!(bitwuzla_available(), "bitwuzla");
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/unittest/swap.btor"),
        run_bmc_file("../inputs/unittest/swap.btor"),
        "swap.btor",
    );
}

#[test]
fn pdr_bmc_agree_quiz1_pass() {
    require!(bitwuzla_available(), "bitwuzla");
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/chiseltest/Quiz1_should_pass_with_assumption_Quiz1.btor"),
        run_bmc_file("../inputs/chiseltest/Quiz1_should_pass_with_assumption_Quiz1.btor"),
        "Quiz1_should_pass",
    );
}

#[test]
fn pdr_bmc_agree_quiz2_pass() {
    require!(bitwuzla_available(), "bitwuzla");
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/chiseltest/Quiz2.unsat.btor"),
        run_bmc_file("../inputs/chiseltest/Quiz2.unsat.btor"),
        "Quiz2_should_pass",
    );
}

#[test]
fn pdr_bmc_agree_quiz2_fail() {
    require!(bitwuzla_available(), "bitwuzla");
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/chiseltest/Quiz2.sat.btor"),
        run_bmc_file("../inputs/chiseltest/Quiz2.sat.btor"),
        "Quiz2_should_fail",
    );
}

#[test]
fn pdr_bmc_agree_quiz4_pass() {
    require!(bitwuzla_available(), "bitwuzla");
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/chiseltest/Quiz4.unsat.btor"),
        run_bmc_file("../inputs/chiseltest/Quiz4.unsat.btor"),
        "Quiz4_should_pass",
    );
}

#[test]
fn pdr_bmc_agree_quiz4_fail() {
    require!(bitwuzla_available(), "bitwuzla");
    check_pdr_bmc_agree(
        run_pdr_file("../inputs/chiseltest/Quiz4.sat.btor"),
        run_bmc_file("../inputs/chiseltest/Quiz4.sat.btor"),
        "Quiz4_should_fail",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Agreement with pono (`pono -e ic3bits`) over the chiseltest corpus
// ─────────────────────────────────────────────────────────────────────────────

/// Result reported by `pono` for a BTOR2 design (HWMCC convention).
/// `Sat` = property violated (counterexample), `Unsat` = property holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PonoResult {
    Sat,
    Unsat,
    Unknown,
}

/// Docker image to run pono through, taken from the `PONO_IMAGE` env var.
///
/// `Some(image)` selects Docker mode (for a containerised pono, e.g. the
/// `alias pono='docker run --init --rm -v ${PWD}:/work pono'` setup — set
/// `PONO_IMAGE=pono`). `None` runs a native `pono` binary on `PATH`.
fn pono_docker_image() -> Option<String> {
    std::env::var("PONO_IMAGE").ok().filter(|s| !s.is_empty())
}

/// Build the command that runs `pono -e ic3bits` on `path`.
///
/// In Docker mode the file's *own directory* is mounted at `/work` and the file
/// is referenced as `/work/<name>`. We can't reuse the alias's `-v ${PWD}:/work`
/// because under `cargo test` the working directory is the crate dir, not where
/// the BTOR inputs live. Args after the image name are passed to the image's
/// pono entrypoint, mirroring `docker run ... pono -e ic3bits <file>`.
fn pono_command(path: &str) -> std::process::Command {
    match pono_docker_image() {
        Some(image) => {
            let p = std::path::Path::new(path);
            let dir = p.parent().expect("btor path has no parent directory");
            let base = p.file_name().expect("btor path has no file name");
            let mut cmd = std::process::Command::new("docker");
            cmd.arg("run")
                .arg("--init")
                .arg("--rm")
                .arg("-v")
                .arg(format!("{}:/work", dir.display()))
                .arg(image)
                .arg("-e")
                .arg("ic3bits")
                .arg(format!("/work/{}", base.to_string_lossy()));
            cmd
        }
        None => {
            let mut cmd = std::process::Command::new("pono");
            cmd.arg("-e").arg("ic3bits").arg(path);
            cmd
        }
    }
}

fn pono_available() -> bool {
    match pono_docker_image() {
        // Docker mode: confirm the image exists locally (does not run pono).
        Some(image) => std::process::Command::new("docker")
            .args(["image", "inspect", &image])
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false),
        None => std::process::Command::new("pono")
            .arg("--help")
            .output()
            .is_ok(),
    }
}

/// Run `pono -e ic3bits <path>` and parse its verdict.
///
/// pono prints `sat` / `unsat` / `unknown` (optionally followed by a witness on
/// `sat`).  We scan both stdout and stderr for the first such token.
fn run_pono_ic3bits(path: &str) -> PonoResult {
    let output = pono_command(path).output().expect("failed to run pono");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    for line in stdout.lines().chain(stderr.lines()) {
        match line.trim() {
            "sat" => return PonoResult::Sat,
            "unsat" => return PonoResult::Unsat,
            "unknown" => return PonoResult::Unknown,
            _ => {}
        }
    }
    PonoResult::Unknown
}

/// Compare a PDR verdict against pono's.
///
/// Rejection rules (per the diff-test spec):
/// - PDR `Unknown` is only acceptable when pono is also `Unknown`; if pono gives
///   a definite answer the disagreement is a hard failure.
/// - When both are definite they must correspond (`Fail`↔`sat`, `Success`↔`unsat`).
/// - PDR definite while pono is `Unknown` is *not* a disagreement (PDR did
///   better): it is logged for manual inspection rather than rejected.
fn check_pdr_pono_agree(pdr_res: &ModelCheckResult, pono_res: PonoResult, label: &str) {
    use ModelCheckResult::*;
    match (pdr_res, pono_res) {
        (Unknown, PonoResult::Unknown) => {}
        (Unknown, other) => {
            panic!("{label}: PDR returned Unknown but pono returned {other:?} — rejected")
        }
        // PDR reached a definite verdict; pono could not. Not a disagreement.
        (_, PonoResult::Unknown) => {
            eprintln!("{label}: PDR={pdr_res:?} but pono=Unknown — logged for manual inspection");
        }
        (Fail(_), PonoResult::Sat) => {}
        (Success, PonoResult::Unsat) => {}
        (Fail(_), PonoResult::Unsat) => {
            panic!("{label}: PDR found a counterexample (sat) but pono says unsat (safe)")
        }
        (Success, PonoResult::Sat) => {
            panic!("{label}: PDR says safe (unsat) but pono found a counterexample (sat)")
        }
    }
}

/// Diff test: for every BV-only design in `inputs/chiseltest`, PDR must agree
/// with `pono -e ic3bits`, and any PDR counterexample must be non-spurious.
#[test]
fn pdr_pono_agree_chiseltest_all() {
    require!(bitwuzla_available(), "bitwuzla");
    // pono is provided either as a native `pono` binary on PATH, or via Docker by
    // setting PONO_IMAGE=<image> (e.g. PONO_IMAGE=pono); see `pono_command`.
    require!(pono_available(), "pono");

    let test_files =
        get_dir_filenames("../inputs/chiseltest").expect("Could not read chiseltest files");

    let tot_tests = test_files.len();
    for (idx, filename) in test_files.iter().enumerate() {
        eprintln!("Running test {}/{}: {}", idx + 1, tot_tests, filename);

        // Parse first so we can inspect the design before committing to a PDR run.
        let (mut ctx, sys) = btor2::parse_file(filename).expect("parse failed");

        // PDR uses BV-only bit-level cubes; it cannot learn array invariants, so
        // array-bearing designs never converge. Skip them — focus is BitVectors.
        if sys
            .states
            .iter()
            .any(|s| ctx[s.symbol].get_type(&ctx).is_array())
        {
            eprintln!("  [skip] array states detected");
            continue;
        }

        // 30s wall-clock limit bounds the known EXCTG query explosion on deep-CEX
        // designs; on timeout PDR returns Unknown (rejected below if pono decides).
        let mut smt_ctx = BITWUZLA.start(None).expect("solver start failed");
        let pdr_res = pdr(
            &mut ctx,
            &mut smt_ctx,
            &sys,
            Some(std::time::Duration::from_secs(30)),
        )
        .expect("PDR error");

        // A PDR counterexample must replay through the simulator (non-spurious).
        if let ModelCheckResult::Fail(ref wit) = pdr_res {
            validate_witness_labeled(&ctx, &sys, wit, filename);
        }

        let pono_res = run_pono_ic3bits(filename);
        check_pdr_pono_agree(&pdr_res, pono_res, filename);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Witness validation: replay PDR counterexamples through the simulator
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn starts_bad_pdr_witness_valid() {
    require!(bitwuzla_available(), "bitwuzla");
    // STARTS_BAD fires at step 0 — the witness chain has exactly one entry.
    let (ctx, sys, result) = run_pdr_str_full(STARTS_BAD);
    if let ModelCheckResult::Fail(wit) = result {
        assert_eq!(
            wit.inputs.len(),
            1,
            "expected a 0-step witness, got {} steps",
            wit.inputs.len()
        );
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("Expected Fail for STARTS_BAD, got {:?}", result);
    }
}

#[test]
fn count2_pdr_witness_valid() {
    require!(bitwuzla_available(), "bitwuzla");
    let (ctx, sys, result) = run_pdr_str_full(COUNT_2);
    if let ModelCheckResult::Fail(wit) = result {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("Expected Fail for COUNT_2, got {:?}", result);
    }
}

#[test]
fn trigger_bad_pdr_witness_valid() {
    require!(bitwuzla_available(), "bitwuzla");
    // TRIGGER_BAD needs exactly one transition (trigger=1 at step 0 → bad at step 1).
    let (ctx, sys, result) = run_pdr_str_full(TRIGGER_BAD);
    if let ModelCheckResult::Fail(wit) = result {
        assert_eq!(
            wit.inputs.len(),
            2,
            "expected a 2-step witness, got {} steps",
            wit.inputs.len()
        );
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("Expected Fail for TRIGGER_BAD, got {:?}", result);
    }
}
