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

## Bugs fixed in this session

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

## Test results

All 9 tests in `patronus/tests/pdr.rs` pass in ~1.8 s with BITWUZLA:

| Test | Result |
|---|---|
| `delay_btor_pdr_success` | ✓ Success |
| `swap_btor_pdr_success` | ✓ Success |
| `quiz1_unsat_pdr_success` | ✓ Success/Unknown |
| `count2_pdr_fail` | ✓ Fail |
| `count2_pdr_witness_nonempty` | ✓ Fail, ≥7 steps |
| `pdr_bmc_agree_count2` | ✓ agree |
| `pdr_bmc_agree_delay` | ✓ agree |
| `pdr_bmc_agree_swap` | ✓ agree |
| `pdr_bmc_agree_quiz1_pass` | ✓ agree |

## Files changed

| File | Change |
|---|---|
| `patronus/src/mc/pdr.rs` | Full IC3/PDR implementation (~590 lines) |
| `patronus/tests/pdr.rs` | Integration tests (safe/unsafe/BMC cross-check) |

## Potential next steps

- IC3IA: the subroutines already take a `state_vars: &[ExprRef]` style — a different
  driver could supply abstract predicate symbols and reuse `predecessor_check`,
  `generalize`, `block_cube`, `propagate_clauses` unchanged.
- Witness validation: replay the CEX through the simulator and assert bad states fire.
- Performance: UNSAT-core-based generalization instead of linear literal dropping.
- Larger benchmarks: run against `inputs/chiseltest/Quiz2_*.btor` and compare with BMC.
