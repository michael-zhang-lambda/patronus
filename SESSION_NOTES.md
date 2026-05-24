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
  `exctg_generalize`, `block_cube`, `propagate_clauses` unchanged.
- Witness validation for array states: `sim.set()` only handles BitVec; array init values
  are currently left to `sim.init`'s default (zero). Needs a way to override array state
  through the `Simulator` trait or a lower-level API.
- DynAMic (Algorithm 5, arXiv:2501.02480v1): dynamically select Standard/CTG/EXCTG per
  bad-state difficulty using an activity counter; thresholds CTG_TH=10, EXCTG_TH=40.
- UNSAT-core-based generalization to replace the greedy linear literal-dropping loop.

---

## Session 3 — EXCTG generalization + bit-level cubes

### Root cause diagnosis

`pdr()` was returning `Unknown` on Quiz2/Quiz4 BMC-comparison tests via **MAX_FRAMES
exhaustion** (pdr.rs loop at the time, now preserved), not a solver issue. BITWUZLA has no
timeout configured; the solver is complete on these small `QF_BV` formulas. Confirmed
empirically: `pdr_bmc_agree_quiz2_pass` churned ~8s of SAT queries before hitting the limit.

**Mechanism:** all four designs (Quiz2.{sat,unsat}, Quiz4.{sat,unsat}) carry a 16-bit
`counter` state. The old `cube_from_state_values` encoded each state as one whole-word
equality literal (`counter = 0x0005`). The old `generalize` could only drop that literal
atomically — dropping the sole constraint on a 16-bit register is never relatively
inductive. PDR blocked concrete counter values one-at-a-time, needing up to ~2¹⁷ lemmas
while `MAX_FRAMES = 1000`. Whole-word cubes cannot represent the range invariants
(e.g., `counter < 4`) needed to converge.

### Changes

**1. Bit-level cube representation** (`cube_from_state_values`, pdr.rs:170)

Each BitVec state now contributes one literal **per bit**: `slice(sym, j, j) = bit_j`
(using `baa::BitVecOps::is_bit_set` for LSB-0 bit access and `ctx.slice`/`ctx.bit_vec_val`
for the SMT expression). Array states are skipped. This is the foundational change — without
it, EXCTG would not converge on wide-counter designs.

**2. EXCTG generalization** (`exctg_generalize` / `exctg_down` / `exctg_block`, pdr.rs:~330)

Replaced the old greedy literal-dropping `generalize` with the three-function EXCTG
algorithm from Su et al., arXiv:2501.02480v1, Algorithm 4. Parameters:
`CTG_MAX=3`, `CTG_LV=1`, `EXCTG_LIMIT=5`.

Key functions:
- `relind_check` — like old `is_inductive_relative` but returns the predecessor cube
  (bit-level, from the SAT model) on failure, needed by the down/CTG/EXCTG loop.
- `cube_intersect(a, b)` — set intersection of ExprRefs (works because interned literals
  are unique per value); implements the `c := c ∩ p` fallback in `exctg_down`.
- `init_intersects` — checks `SAT(Init ∧ cube)`, guarding against blocking initial states.
  An empty cube (`to_expr()` = True) returns true here, preventing empty-cube blocking.
- `exctg_block(c, i, limit&, cl)` — the "extended" part: recursively blocks the
  predecessor chain of c, sharing a budget `limit` (decremented by ref). Returns false
  when `limit` is exhausted or a predecessor hits Init.
- `exctg_down(c, i, cl)` — the core loop: checks relind, tries CTG-blocking (up to
  CTG_MAX attempts), falls back to `c := c ∩ p` when the CTG budget is exhausted.
- `exctg_generalize(c, i, cl)` — iterates over literals, attempting to drop each via
  `exctg_down`. Uses the returned (possibly further minimized) cube.

Two transcription quirks resolved vs. the PDF: (a) `exctg_block`'s success branch
generalizes `c` (not `p` as printed — typo in the paper); (b) `limit` is decremented
shared across the recursion subtree (consistent with Algorithm 4's intent).

### Test results (all 16 pass)

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
| `pdr_bmc_agree_quiz2_pass` | ✓ agree (was: Unknown) |
| `pdr_bmc_agree_quiz2_fail` | ✓ agree (was: Unknown) |
| `pdr_bmc_agree_quiz4_pass` | ✓ agree (was: Unknown) |
| `pdr_bmc_agree_quiz4_fail` | ✓ agree (was: Unknown) |
| `starts_bad_pdr_witness_valid` | ✓ 0-step CEX validated |
| `count2_pdr_witness_valid` | ✓ 7-step CEX validated |
| `trigger_bad_pdr_witness_valid` | ✓ 1-step CEX with inputs validated |

Total runtime: 0.83s (vs ~8s per failing test before).

### Files changed

| File | Change |
|---|---|
| `patronus/src/mc/pdr.rs` | Bit-level cubes; `cube_intersect`, `init_intersects`, `relind_check`; EXCTG: `exctg_generalize`/`exctg_down`/`exctg_block`; `CTG_MAX`/`CTG_LV`/`EXCTG_LIMIT` consts; updated `block_cube` call sites |
