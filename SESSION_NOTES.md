# Session Notes — PDR/IC3 Implementation

## What was done

Implemented a baseline IC3/PDR model checker in `patronus/src/mc/pdr.rs` and integration
tests in `patronus/tests/pdr.rs`. The implementation replaces the previous 23-line stub
that always returned `Unknown`.

The public API matches BMC:

```rust
pub fn pdr(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
) -> Result<ModelCheckResult>
```

## Architecture

### Encoding

`enc.init_at(ctx, smt_ctx, STEP_CUR=1)` — declares the current state freely (no init baked
in). `enc.unroll(ctx, smt_ctx)` — asserts T(step1 → step2) permanently. All queries add
temporary assumptions on top via `check_sat_assuming` (BITWUZLA) or push/pop (other solvers).

### Frame layout

`frames[0]` stores Init as un-stepped equalities `s.symbol = iv`. These are stepped to
`STEP_CUR` at query time via `expr_at_step`. `frames[1..]` hold learned blocking clauses.

### Key invariant — **how clauses are stored vs queried**

`add_blocking_clause(up_to=k)` writes `¬cube` into every frame `frames[1..=k]`.

`frame_assumptions(up_to=k)` reads from **only** `frames[k]` (not the union
`frames[1..=k]`).

Together these give the correct IC3 nesting: `frames[k]` contains every clause blocked at
level `≥ k`, so F[k-1] ⊆ F[k] (earlier frames are more restrictive). Reading only
`frames[k]` avoids double-counting while preserving that invariant.

This is a **non-obvious design point**. Storing clauses in every frame up to k AND
querying only frame k is equivalent to querying the union `frames[1..=k]`, EXCEPT that the
union approach inverts the nesting (earlier sessions had this bug).

### Generalization safety rule

`generalize` never drops the last literal. An empty cube negates to `ctx.get_false()`;
asserting False makes any induction check trivially UNSAT, which causes `false` to be added
as a blocking clause and triggers a spurious fixpoint (→ false Success).

## Bugs fixed (session 1)

### Bug 1 — frame_assumptions used frames[1..=up_to] instead of frames[up_to]

**Root cause:** Collecting the union of all frames 1..=k made F[k] inherit F[k-1]'s
clauses, so the frames were ordered F[k] ⊆ F[k-1] — backwards. For COUNT_2 this caused
`find_bad_cube(frontier=1)` to check SAT(Init ∧ bad) = UNSAT (counter=0 ∧ counter=7),
so the bad cube was never found and propagation ran immediately, producing false Success.

**Fix:** Changed `frame_assumptions` to iterate over `frames[up_to]` only.

### Bug 2 — generalize allowed dropping the last literal

**Root cause:** When the only literal was removed, `cube.negate()` = `ctx.get_false()`.
`is_inductive_relative` with ¬cube = False is trivially UNSAT (SAT(F ∧ False ∧ T ∧
cube') = UNSAT). This made generalization "succeed" by returning the empty cube. Then
`add_blocking_clause` added `false` to the frames, making every future query trivially UNSAT
and creating a spurious fixpoint.

**Fix:** Added a guard in `generalize` — `if cube.literals.len() == 1 { break; }`.

## Bugs fixed (session 2)

### Bug 3 — propagate_clauses skipped fixpoint detection for empty frames

**Root cause:** The `propagate_clauses` fixpoint check had a guard
`if !frames[fi].clauses.is_empty()` that prevented detection when no blocking clauses had
been learned. For safe systems where constraints alone exclude bad states (e.g.
`Quiz1.unsat.btor`), `find_bad_cube` always returns UNSAT without any clauses being added.
The guard caused the fixpoint to be skipped every iteration, and PDR looped until
`MAX_FRAMES`, returning `Unknown` instead of `Success`.

**Why the guard was wrong:** `add_blocking_clause(up_to=k)` writes to `frames[1..=k]`, so
`frames[k+1].clauses ⊆ frames[k].clauses` always holds by construction. If `frames[k]` is
empty, `frames[k+1]` must also be empty. The vacuous `.all()` check on an empty iterator
correctly signals a fixpoint — the constraints alone are a sufficient inductive invariant.

**Fix:** Removed the `!frames[fi].clauses.is_empty()` guard in `propagate_clauses`
(`pdr.rs:346`).

### Bug 4 — quiz1_unsat_pdr_success had an inverted assertion

**Root cause:** The test checked `matches!(res, ModelCheckResult::Fail(_))` for a system
that is genuinely safe (UNSAT = no counterexample). The failure message "Expected Success
(or Unknown)" was the correct description of what PDR returns, making the mismatch look
like a PDR bug rather than a test bug.

**Fix:** Changed the assertion to
`matches!(res, ModelCheckResult::Success) || matches!(res, ModelCheckResult::Unknown)`.

## Test results

All tests in `patronus/tests/pdr.rs` pass with BITWUZLA:

| Test | Result |
|---|---|
| `delay_btor_pdr_success` | ✓ Success |
| `swap_btor_pdr_success` | ✓ Success |
| `quiz1_unsat_pdr_success` | ✓ Success |
| `count2_pdr_fail` | ✓ Fail |
| `count2_pdr_witness_nonempty` | ✓ Fail, ≥7 steps |
| `pdr_bmc_agree_count2` | ✓ agree |
| `pdr_bmc_agree_delay` | ✓ agree |
| `pdr_bmc_agree_swap` | ✓ agree |
| `pdr_bmc_agree_quiz1_pass` | ✓ agree |
| `starts_bad_pdr_witness_valid` | ✓ 0-step CEX validated |
| `count2_pdr_witness_valid` | ✓ 7-step CEX validated |
| `trigger_bad_pdr_witness_valid` | ✓ 1-step CEX with inputs validated |

## Witness validation

`validate_witness(ctx, sys, wit)` in `patronus/tests/pdr.rs` replays a PDR counterexample
through the `Interpreter` simulator:

1. `sim.init(InitKind::Zero)` — allocate state; init expressions applied automatically.
2. Override state with `wit.init` values via `sim.set()` (BitVec only; arrays deferred).
3. For each step `i` in `0..N-1`: apply `wit.inputs[i]`, call `sim.step()`.
4. Apply `wit.inputs[N-1]` (no step), then assert every bad state in
   `wit.failed_safety` evaluates to non-zero.

Three fixtures cover distinct CEX shapes:

| Fixture | Description |
|---|---|
| `STARTS_BAD` | 1-bit state held at 1; fires at step 0 (0-step CEX path) |
| `COUNT_2` | 3-bit counter; fires at step 7 (multi-step, no inputs) |
| `TRIGGER_BAD` | 1-bit state copies `trigger` input; fires at step 1 (inputs exercised) |

## Files changed

| File | Change |
|---|---|
| `patronus/src/mc/pdr.rs` | Full IC3/PDR implementation (~595 lines); Bug 1–3 fixes |
| `patronus/tests/pdr.rs` | Integration tests: safe/unsafe/BMC cross-check/witness validation |

## Potential next steps

- IC3IA: the subroutines already take a `state_vars: &[ExprRef]` style — a different
  driver could supply abstract predicate symbols and reuse `predecessor_check`,
  `generalize`, `block_cube`, `propagate_clauses` unchanged.
- Witness validation for array states: `sim.set()` only handles BitVec; array init values
  are currently left to `sim.init`'s default (zero). Needs a way to override array state
  through the `Simulator` trait or a lower-level API.
- Performance: UNSAT-core-based generalization instead of linear literal dropping.
- Larger benchmarks: run against `inputs/chiseltest/Quiz2_*.btor` and compare with BMC.
