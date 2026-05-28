// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::*;
use crate::mc::ModelCheckResult;
use crate::mc::bmc::{
    TransitionSystemEncoding, check_assuming, check_assuming_end, get_smt_value, start_bmc_or_pdr,
};
use crate::mc::types::{InitValue, Witness};
use crate::smt::*;
use crate::system::TransitionSystem;
use baa::*;

type Result<T> = crate::smt::Result<T>;

// STEP_CUR = 1: "current" state, declared freely (no init baked in).
// STEP_NXT = 2: "next" state, defined by T(step1 → step2) permanently in the solver.
const STEP_CUR: u64 = 1;
const STEP_NXT: u64 = 2;

const MAX_FRAMES: usize = 1000;

// EXCTG parameters (Su et al., arXiv:2501.02480v1, §V-A defaults).
// EXCTG subsumes Standard (CTG_LV=0) and CTG (EXCTG_LIMIT=1) as special cases.
const CTG_MAX: usize = 3; // max CTG-blocking attempts per exctg_down loop
const CTG_LV: usize = 1; // max generalization recursion depth
const EXCTG_LIMIT: usize = 5; // predecessor-chain budget per exctg_block subtree

// ─────────────────────────────────────────────────────────────────────────────
// Core data structures
// ─────────────────────────────────────────────────────────────────────────────

/// A conjunction of literals over the original (un-stepped) state symbols.
///
/// Literals are single-bit equalities: `slice(sym, j, j) = bit`, one per state bit.
/// Interning guarantees that two structurally equal literals share the same ExprRef,
/// so set operations (intersection, membership) work directly on ExprRef values.
#[derive(Clone, Debug, Default)]
struct Cube {
    literals: Vec<ExprRef>,
}

impl Cube {
    /// Conjunction of all literals; `true` if the cube is empty.
    fn to_expr(&self, ctx: &mut Context) -> ExprRef {
        let mut result = ctx.get_true();
        for &lit in &self.literals {
            result = ctx.and(result, lit);
        }
        result
    }

    /// Negation of the cube as a disjunction of negated literals; `false` if empty.
    fn negate(&self, ctx: &mut Context) -> ExprRef {
        let mut result = ctx.get_false();
        for &lit in &self.literals {
            let neg = ctx.not(lit);
            result = ctx.or(result, neg);
        }
        result
    }
}

/// One PDR frame: a set of blocking clauses stored over original (un-stepped) symbols.
/// frames[0] is special: it holds the Init constraints (sym = init_val equalities).
#[derive(Clone, Debug, Default)]
struct Frame {
    clauses: Vec<ExprRef>,
}

/// One step in the CEX chain, captured when the corresponding SAT query succeeded.
struct CexEntry {
    /// Concrete values for every state variable (same order as sys.states).
    state_values: Vec<Value>,
    /// Concrete values for every input (same order as sys.inputs).
    inputs: Vec<Option<Value>>,
}

/// Tri-state outcome of a single SAT query.
enum QueryResult<T> {
    Sat(T),
    Unsat,
    Unknown,
}

// ─────────────────────────────────────────────────────────────────────────────
// Low-level helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Maps every symbol in `expr` (over original symbols) to its stepped counterpart.
fn expr_at_step(
    ctx: &mut Context,
    enc: &impl TransitionSystemEncoding,
    expr: ExprRef,
    step: u64,
) -> ExprRef {
    simple_transform_expr(ctx, expr, |ctx, e, _| {
        if ctx[e].is_symbol() {
            Some(enc.get_at(ctx, e, step))
        } else {
            None
        }
    })
}

/// Collect frame clauses stepped to `step` as a flat Vec of assumptions.
///
/// frames[0] holds Init constraints and is only included when up_to == 0.
/// For frames 1..=k, only the blocking clauses learned at those levels are included.
fn frame_assumptions(
    ctx: &mut Context,
    enc: &impl TransitionSystemEncoding,
    frames: &[Frame],
    up_to: usize,
    step: u64,
) -> Vec<ExprRef> {
    // Use ONLY frames[up_to] (not the union of frames[1..=up_to]).
    //
    // add_blocking_clause(up_to=k) writes a clause into every frame 1..=k, so
    // frames[k] already contains exactly the clauses valid at depth k.
    // Unioning frames[1..=k] would double-count and invert the F[k-1] ⊆ F[k] nesting.
    let frame = &frames[up_to];
    frame
        .clauses
        .iter()
        .map(|&cl| expr_at_step(ctx, enc, cl, step))
        .collect()
}

/// Extract concrete values for all state symbols at `step` from the current SAT model.
fn extract_state_values(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    sys: &TransitionSystem,
    step: u64,
) -> Result<Vec<Value>> {
    let mut out = Vec::with_capacity(sys.states.len());
    for s in &sys.states {
        let sym = enc.get_at(ctx, s.symbol, step);
        out.push(get_smt_value(ctx, smt_ctx, sym)?);
    }
    Ok(out)
}

/// Extract concrete values for all inputs at `step` from the current SAT model.
fn extract_input_values(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    sys: &TransitionSystem,
    step: u64,
) -> Result<Vec<Option<Value>>> {
    let mut out = Vec::with_capacity(sys.inputs.len());
    for &inp in &sys.inputs {
        let sym = enc.get_at(ctx, inp, step);
        out.push(Some(get_smt_value(ctx, smt_ctx, sym)?));
    }
    Ok(out)
}

/// Build a bit-level cube from concrete state values.
///
/// Each BitVec state contributes one literal per bit: `slice(sym, j, j) = bit_j`.
/// Array states are skipped (no natural bit-level encoding).
/// Using one literal per bit (rather than one whole-word equality) is essential for
/// generalization: dropping a bit literal turns that bit into a "don't care", allowing
/// IC3 to learn range-style invariants like `counter < 4`.
fn cube_from_state_values(
    ctx: &mut Context,
    sys: &TransitionSystem,
    state_values: &[Value],
) -> Cube {
    debug_assert_eq!(sys.states.len(), state_values.len());
    let mut literals = Vec::new();
    for (s, val) in sys.states.iter().zip(state_values.iter()) {
        if let Value::BitVec(bv) = val {
            let width = bv.width();
            for j in 0..width {
                let bit_val: u64 = if bv.is_bit_set(j) { 1 } else { 0 };
                let slice_expr = ctx.slice(s.symbol, j, j);
                let bit_expr = ctx.bit_vec_val(bit_val, 1u32);
                literals.push(ctx.equal(slice_expr, bit_expr));
            }
        }
        // Array states: skip; cube blocks only bitvec state bits.
    }
    Cube { literals }
}

/// Compute the intersection of two cubes: literals present in both.
///
/// Correct because identical bit-literals are interned to the same ExprRef.
fn cube_intersect(a: &Cube, b: &Cube) -> Cube {
    let b_set: std::collections::HashSet<ExprRef> = b.literals.iter().copied().collect();
    let literals = a
        .literals
        .iter()
        .copied()
        .filter(|l| b_set.contains(l))
        .collect();
    Cube { literals }
}

/// Issue a `check_sat_assuming` (or push/assert/check_sat) and clean up.
fn query(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    assumptions: Vec<ExprRef>,
) -> Result<CheckSatResponse> {
    let res = check_assuming(ctx, smt_ctx, assumptions)?;
    check_assuming_end(smt_ctx)?;
    Ok(res)
}

// ─────────────────────────────────────────────────────────────────────────────
// PDR subroutines
// ─────────────────────────────────────────────────────────────────────────────

/// Check whether SMT expression holds and return `SAT` counterexample, `UNSAT`, or `UNKNOWN`
#[inline]
fn query_and_result(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    sys: &TransitionSystem,
    assumptions: Vec<ExprRef>,
) -> Result<QueryResult<(Cube, CexEntry)>> {
    match query(ctx, smt_ctx, assumptions)? {
        CheckSatResponse::Sat => {
            let state_values = extract_state_values(ctx, smt_ctx, enc, sys, STEP_CUR)?;
            let inputs = extract_input_values(ctx, smt_ctx, enc, sys, STEP_CUR)?;
            let cube = cube_from_state_values(ctx, sys, &state_values);
            Ok(QueryResult::Sat((
                cube,
                CexEntry {
                    state_values,
                    inputs,
                },
            )))
        }
        CheckSatResponse::Unsat => Ok(QueryResult::Unsat),
        CheckSatResponse::Unknown => Ok(QueryResult::Unknown),
    }
}

/// Check SAT(F[frame_idx]@CUR ∧ Bad@CUR). On SAT, extract a bad predecessor cube.
fn find_bad_cube(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    sys: &TransitionSystem,
    frames: &[Frame],
    frame_idx: usize,
) -> Result<QueryResult<(Cube, CexEntry)>> {
    let mut assumptions = frame_assumptions(ctx, enc, frames, frame_idx, STEP_CUR);
    let mut bad_cur = ctx.get_false();
    for &b in &sys.bad_states {
        let b_cur = expr_at_step(ctx, enc, b, STEP_CUR);
        bad_cur = ctx.or(bad_cur, b_cur);
    }
    assumptions.push(bad_cur);
    query_and_result(ctx, smt_ctx, enc, sys, assumptions)
}

/// Check SAT(F[frame_idx]@CUR ∧ ¬cube@CUR ∧ cube@NXT).
/// T(CUR→NXT) is already permanently in the solver.
fn predecessor_check(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    sys: &TransitionSystem,
    frames: &[Frame],
    frame_idx: usize,
    cube: &Cube,
) -> Result<QueryResult<(Cube, CexEntry)>> {
    let mut assumptions = frame_assumptions(ctx, enc, frames, frame_idx, STEP_CUR);
    let neg_cube = cube.negate(ctx);
    assumptions.push(expr_at_step(ctx, enc, neg_cube, STEP_CUR));
    let cube_expr = cube.to_expr(ctx);
    assumptions.push(expr_at_step(ctx, enc, cube_expr, STEP_NXT));
    query_and_result(ctx, smt_ctx, enc, sys, assumptions)
}

/// Check SAT(F[frame_idx]@CUR ∧ ¬cube@CUR ∧ cube@NXT).
///
/// Returns Unsat when ¬cube is inductive relative to F[frame_idx] (cube is blockable).
/// Returns Sat(predecessor_cube) with the predecessor's bit-level cube extracted from the model.
fn relind_check(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    sys: &TransitionSystem,
    frames: &[Frame],
    frame_idx: usize,
    cube: &Cube,
) -> Result<QueryResult<Cube>> {
    let mut assumptions = frame_assumptions(ctx, enc, frames, frame_idx, STEP_CUR);
    let neg_cube = cube.negate(ctx);
    assumptions.push(expr_at_step(ctx, enc, neg_cube, STEP_CUR));
    let cube_expr = cube.to_expr(ctx);
    assumptions.push(expr_at_step(ctx, enc, cube_expr, STEP_NXT));

    match query(ctx, smt_ctx, assumptions)? {
        CheckSatResponse::Sat => {
            let state_values = extract_state_values(ctx, smt_ctx, enc, sys, STEP_CUR)?;
            let pred_cube = cube_from_state_values(ctx, sys, &state_values);
            Ok(QueryResult::Sat(pred_cube))
        }
        CheckSatResponse::Unsat => Ok(QueryResult::Unsat),
        CheckSatResponse::Unknown => Ok(QueryResult::Unknown),
    }
}

/// Check whether Init ∧ cube is satisfiable (cube intersects the initial states).
///
/// An empty cube's to_expr() = True, so init_intersects(empty) = SAT(Init) = true,
/// which prevents the generalization functions from producing empty cubes.
fn init_intersects(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    frames: &[Frame],
    cube: &Cube,
) -> Result<bool> {
    let mut assumptions = frame_assumptions(ctx, enc, frames, 0, STEP_CUR);
    let cube_expr = cube.to_expr(ctx);
    assumptions.push(expr_at_step(ctx, enc, cube_expr, STEP_CUR));
    match query(ctx, smt_ctx, assumptions)? {
        CheckSatResponse::Sat => Ok(true),
        CheckSatResponse::Unsat => Ok(false),
        // Conservative: treat Unknown as "intersects Init" to avoid blocking initial states.
        CheckSatResponse::Unknown => Ok(true),
    }
}

/// Add the negation of `cube` as a blocking clause to frames 1..=up_to.
fn add_blocking_clause(ctx: &mut Context, frames: &mut [Frame], cube: &Cube, up_to: usize) {
    let clause = cube.negate(ctx);
    for f in frames[1..=up_to].iter_mut() {
        f.clauses.push(clause);
    }
}

/// Recursively block cube `c` at frame `frame_idx`, chasing predecessor chains up to `limit`.
///
/// The "extended" part of EXCTG: unlike CTG (which only tries to block the direct CTG),
/// this function recursively tries to block each predecessor in the chain until either all
/// predecessors are blocked (success) or the budget `limit` is exhausted (failure).
///
/// Algorithm 4, exctg_block (Su et al., arXiv:2501.02480v1).
fn exctg_block(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    sys: &TransitionSystem,
    frames: &mut Vec<Frame>,
    cube: Cube,
    frame_idx: usize,
    limit: &mut usize,
    cl: usize,
) -> Result<bool> {
    if init_intersects(ctx, smt_ctx, enc, frames, &cube)? {
        return Ok(false);
    }
    // frame_idx == 0 means we would need relind(c, -1) — undefined; can't go deeper.
    if frame_idx == 0 {
        return Ok(false);
    }
    if *limit == 0 {
        return Ok(false);
    }
    *limit -= 1;

    let c = cube;
    loop {
        match relind_check(ctx, smt_ctx, enc, sys, frames, frame_idx - 1, &c)? {
            QueryResult::Sat(pred) => {
                // c is not yet blockable; recurse to block its predecessor.
                if !exctg_block(
                    ctx,
                    smt_ctx,
                    enc,
                    sys,
                    frames,
                    pred,
                    frame_idx - 1,
                    limit,
                    cl,
                )? {
                    return Ok(false);
                }
                // Predecessor blocked — loop to re-check relind(c, frame_idx-1).
            }
            QueryResult::Unsat => {
                // c is inductive relative to F[frame_idx-1]; generalize and add clause.
                let generalized =
                    exctg_generalize(ctx, smt_ctx, enc, sys, frames, frame_idx - 1, c, cl)?;
                add_blocking_clause(ctx, frames, &generalized, frame_idx);
                return Ok(true);
            }
            QueryResult::Unknown => return Ok(false),
        }
    }
}

/// Try to show that literal-dropped cube `c` is inductively blockable at `frame_idx`.
///
/// Attempts CTG/EXCTG blocking (up to CTG_MAX CTGs) to strengthen F[frame_idx] so
/// that the relind check succeeds.  Falls back to intersecting c with the predecessor
/// (the "down" strategy) when the CTG budget is exhausted.
///
/// Returns Some(minimized_cube) on success, None on failure.
///
/// Algorithm 4, exctg_down (Su et al., arXiv:2501.02480v1).
fn exctg_down(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    sys: &TransitionSystem,
    frames: &mut Vec<Frame>,
    mut cube: Cube,
    frame_idx: usize,
    cl: usize,
) -> Result<Option<Cube>> {
    let mut num_ctg = 0usize;
    loop {
        if init_intersects(ctx, smt_ctx, enc, frames, &cube)? {
            return Ok(None);
        }
        match relind_check(ctx, smt_ctx, enc, sys, frames, frame_idx, &cube)? {
            QueryResult::Unsat => return Ok(Some(cube)),
            QueryResult::Sat(pred) => {
                if cl > 0 && num_ctg < CTG_MAX && frame_idx > 0 {
                    let mut fresh_limit = EXCTG_LIMIT;
                    if exctg_block(
                        ctx,
                        smt_ctx,
                        enc,
                        sys,
                        frames,
                        pred.clone(),
                        frame_idx,
                        &mut fresh_limit,
                        cl - 1,
                    )? {
                        num_ctg += 1;
                        continue;
                    }
                }
                // CTG budget exhausted or blocking failed: intersect with predecessor (down).
                num_ctg = 0;
                cube = cube_intersect(&cube, &pred);
            }
            QueryResult::Unknown => return Ok(None),
        }
    }
}

/// Greedily drop literals from `cube` while preserving relative inductiveness.
///
/// For each literal, attempts to drop it via exctg_down (which in turn may block
/// CTG predecessors to enable the drop).  Returns the minimized cube.
///
/// Algorithm 4, exctg_generalize (Su et al., arXiv:2501.02480v1).
fn exctg_generalize(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    sys: &TransitionSystem,
    frames: &mut Vec<Frame>,
    frame_idx: usize,
    mut cube: Cube,
    cl: usize,
) -> Result<Cube> {
    let mut i = 0;
    while i < cube.literals.len() {
        let mut cand_lits = cube.literals.clone();
        cand_lits.remove(i);
        let cand = Cube {
            literals: cand_lits,
        };

        match exctg_down(ctx, smt_ctx, enc, sys, frames, cand, frame_idx, cl)? {
            Some(reduced) => {
                // Drop succeeded (possibly further minimized by down's intersection).
                cube = reduced;
                // i stays: the element at position i is now the next literal.
            }
            None => {
                i += 1;
            }
        }
    }
    Ok(cube)
}

/// Propagate clauses from frame fi into fi+1 if they're preserved by T.
/// Pushes a new empty frontier frame. Returns `Sat(i)` on fixpoint.
fn propagate_clauses(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    frames: &mut Vec<Frame>,
) -> Result<QueryResult<usize>> {
    frames.push(Frame::default());
    let last = frames.len() - 1;

    for fi in 1..last {
        let clauses_snapshot: Vec<ExprRef> = frames[fi].clauses.clone();
        for cl in clauses_snapshot {
            // UNSAT(F[fi]@CUR ∧ ¬cl@NXT) → cl preserved by T → copy to F[fi+1].
            let mut assumptions = frame_assumptions(ctx, enc, frames, fi, STEP_CUR);
            let cl_nxt = expr_at_step(ctx, enc, cl, STEP_NXT);
            assumptions.push(ctx.not(cl_nxt));

            match query(ctx, smt_ctx, assumptions)? {
                CheckSatResponse::Unsat => frames[fi + 1].clauses.push(cl),
                CheckSatResponse::Sat => {}
                CheckSatResponse::Unknown => return Ok(QueryResult::Unknown),
            }
        }

        // Fixpoint: every clause of F[fi] is also in F[fi+1].
        // Works correctly for empty frames too: add_blocking_clause(up_to=k) writes to
        // frames[1..=k], so frames[k+1].clauses ⊆ frames[k].clauses always holds. If
        // frames[k] is empty then frames[k+1] is also empty, and the vacuous .all()
        // correctly detects the fixpoint (constraints alone exclude all bad states).
        let fi1_set: std::collections::HashSet<ExprRef> =
            frames[fi + 1].clauses.iter().copied().collect();
        if frames[fi].clauses.iter().all(|cl| fi1_set.contains(cl)) {
            return Ok(QueryResult::Sat(fi));
        }
    }
    Ok(QueryResult::Unsat)
}

/// Iterative proof-obligation loop.
///
/// `frames[0]` encodes Init (already populated before calling this).
/// Returns `Sat(chain)` on a real CEX (chain[0]=init state, chain[last]=bad state),
/// `Unsat` when all obligations are blocked, or `Unknown`.
fn block_cube(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    sys: &TransitionSystem,
    frames: &mut Vec<Frame>,
    bad_cube: Cube,
    bad_entry: CexEntry,
    frame_idx: usize,
) -> Result<QueryResult<Vec<CexEntry>>> {
    let mut stack: Vec<(usize, Cube, CexEntry)> = vec![(frame_idx, bad_cube, bad_entry)];

    loop {
        let (fi, cube) = match stack.last() {
            Some((fi, c, _)) => (*fi, c.clone()),
            None => return Ok(QueryResult::Unsat),
        };

        if fi == 0 {
            // Check if cube ∩ Init ≠ ∅ (F[0] = Init via frames[0].clauses).
            let mut assumptions = frame_assumptions(ctx, enc, frames, 0, STEP_CUR);
            let cube_expr = cube.to_expr(ctx);
            assumptions.push(expr_at_step(ctx, enc, cube_expr, STEP_CUR));

            match query(ctx, smt_ctx, assumptions)? {
                CheckSatResponse::Sat => {
                    // Real CEX: drain the stack from top (init-side) to bottom (bad-side).
                    let mut chain: Vec<CexEntry> = Vec::with_capacity(stack.len());
                    while let Some((_, _, e)) = stack.pop() {
                        chain.push(e);
                    }
                    return Ok(QueryResult::Sat(chain));
                }
                CheckSatResponse::Unsat => {
                    // Defensive: shouldn't happen normally. Block and continue.
                    let gen_cube_lbl =
                        exctg_generalize(ctx, smt_ctx, enc, sys, frames, 0, cube.clone(), CTG_LV)?;
                    add_blocking_clause(ctx, frames, &gen_cube_lbl, 1);
                    stack.pop();
                }
                CheckSatResponse::Unknown => return Ok(QueryResult::Unknown),
            }
        } else {
            match predecessor_check(ctx, smt_ctx, enc, sys, frames, fi - 1, &cube)? {
                QueryResult::Sat((pred_cube, pred_entry)) => {
                    stack.push((fi - 1, pred_cube, pred_entry));
                }
                QueryResult::Unsat => {
                    let gen_cube_lbl = exctg_generalize(
                        ctx,
                        smt_ctx,
                        enc,
                        sys,
                        frames,
                        fi - 1,
                        cube.clone(),
                        CTG_LV,
                    )?;
                    add_blocking_clause(ctx, frames, &gen_cube_lbl, fi);
                    stack.pop();
                }
                QueryResult::Unknown => return Ok(QueryResult::Unknown),
            }
        }
    }
}

/// Reconstruct a `Witness` from the CEX chain.
/// chain[0] = initial state entry, chain[last] = bad state entry.
fn make_witness(ctx: &mut Context, sys: &TransitionSystem, chain: Vec<CexEntry>) -> Witness {
    let mut wit = Witness::default();

    for s in &sys.states {
        wit.init_names
            .push(Some(ctx.get_symbol_name(s.symbol).unwrap().to_string()));
    }
    for &inp in &sys.inputs {
        wit.input_names
            .push(Some(ctx.get_symbol_name(inp).unwrap().to_string()));
    }

    let init_entry = &chain[0];
    for val in &init_entry.state_values {
        let wit_value = match val {
            Value::BitVec(v) => InitValue::BitVec(v.clone()),
            Value::Array(v) => {
                let indices = (0..v.num_elements())
                    .map(|ii| BitVecValue::from_u64(ii as u64, v.index_width()))
                    .collect();
                InitValue::Array(v.clone(), indices)
            }
        };
        wit.init.push(wit_value);
    }

    for entry in &chain {
        wit.inputs.push(entry.inputs.clone());
    }

    // Evaluate bad states against the final step's concrete state values.
    let last_entry = chain.last().unwrap();
    let mut store = SymbolValueStore::default();
    for (s, val) in sys.states.iter().zip(last_entry.state_values.iter()) {
        match val {
            Value::BitVec(bv) => store.define_bv(s.symbol, bv),
            Value::Array(av) => store.define_array(s.symbol, av.clone()),
        }
    }
    for (inp, val) in sys.inputs.iter().zip(last_entry.inputs.iter()) {
        if let Some(v) = val {
            match v {
                Value::BitVec(bv) => store.define_bv(*inp, bv),
                Value::Array(av) => store.define_array(*inp, av.clone()),
            }
        }
    }
    for (bad_idx, &bad_expr) in sys.bad_states.iter().enumerate() {
        if let Value::BitVec(bv) = eval_expr(ctx, &store, bad_expr) {
            if !bv.is_zero() {
                wit.failed_safety.push(bad_idx as u32);
            }
        }
    }

    wit
}

// ─────────────────────────────────────────────────────────────────────────────
// Public entry point
// ─────────────────────────────────────────────────────────────────────────────

/// Runs PDR/IC3 with EXCTG generalization for a maximum of `MAX_FRAMES` frames.
///
/// EXCTG (Su et al., arXiv:2501.02480v1) subsumes CTG and Standard generalization
/// as parameter special cases (CTG_LV=0 → Standard; EXCTG_LIMIT=1 → CTG).
/// Cubes use bit-level literals (one per state bit) rather than whole-word equalities,
/// which is required for generalization to learn range-style inductive invariants.
///
/// `time_limit` caps wall-clock execution; returns `Unknown` if the deadline is exceeded.
pub fn pdr(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    time_limit: Option<std::time::Duration>,
) -> Result<ModelCheckResult> {
    let deadline = time_limit.map(|d| std::time::Instant::now() + d);
    let mut enc = match start_bmc_or_pdr(ctx, smt_ctx, sys)? {
        (r, None) => return Ok(r),
        (_, Some(enc)) => enc,
    };

    // Declare the current state freely (no init baked in).
    enc.init_at(ctx, smt_ctx, STEP_CUR)?;
    // Assert T(STEP_CUR → STEP_NXT) permanently.
    enc.unroll(ctx, smt_ctx)?;

    // Assert constraints at both steps permanently.
    let constraints: Vec<ExprRef> = sys.constraints.clone();
    for c in &constraints {
        let c_cur = expr_at_step(ctx, &enc, *c, STEP_CUR);
        smt_ctx.assert(ctx, c_cur)?;
        let c_nxt = expr_at_step(ctx, &enc, *c, STEP_NXT);
        smt_ctx.assert(ctx, c_nxt)?;
    }

    // frames[0] holds Init constraints as un-stepped equalities (sym = init_val).
    // These are automatically stepped when used in frame_assumptions.
    let mut frames: Vec<Frame> = vec![Frame::default(), Frame::default()];
    for s in &sys.states {
        if let Some(iv) = s.init {
            let eq = ctx.equal(s.symbol, iv);
            frames[0].clauses.push(eq);
        }
    }

    // Early check: SAT(Init ∧ Bad) → 0-step CEX.
    {
        let mut assumptions = frame_assumptions(ctx, &enc, &frames, 0, STEP_CUR);
        let mut bad_cur = ctx.get_false();
        for &b in &sys.bad_states {
            let b_cur = expr_at_step(ctx, &enc, b, STEP_CUR);
            bad_cur = ctx.or(bad_cur, b_cur);
        }
        assumptions.push(bad_cur);

        match query(ctx, smt_ctx, assumptions)? {
            CheckSatResponse::Sat => {
                let state_values = extract_state_values(ctx, smt_ctx, &enc, sys, STEP_CUR)?;
                let inputs = extract_input_values(ctx, smt_ctx, &enc, sys, STEP_CUR)?;
                let wit = make_witness(
                    ctx,
                    sys,
                    vec![CexEntry {
                        state_values,
                        inputs,
                    }],
                );
                return Ok(ModelCheckResult::Fail(wit));
            }
            CheckSatResponse::Unknown => return Ok(ModelCheckResult::Unknown),
            CheckSatResponse::Unsat => {}
        }
    }

    let mut frontier = 1usize;

    for _ in 0..MAX_FRAMES {
        if let Some(dl) = deadline {
            if std::time::Instant::now() >= dl {
                return Ok(ModelCheckResult::Unknown);
            }
        }
        match find_bad_cube(ctx, smt_ctx, &enc, sys, &frames, frontier)? {
            QueryResult::Unsat => match propagate_clauses(ctx, smt_ctx, &enc, &mut frames)? {
                QueryResult::Sat(_) => return Ok(ModelCheckResult::Success),
                QueryResult::Unsat => {
                    frontier += 1;
                }
                QueryResult::Unknown => return Ok(ModelCheckResult::Unknown),
            },
            QueryResult::Sat((bad_cube, bad_entry)) => {
                match block_cube(
                    ctx,
                    smt_ctx,
                    &enc,
                    sys,
                    &mut frames,
                    bad_cube,
                    bad_entry,
                    frontier,
                )? {
                    QueryResult::Unsat => {
                        // Blocked — loop back to find_bad_cube at the same frontier.
                    }
                    QueryResult::Sat(chain) => {
                        return Ok(ModelCheckResult::Fail(make_witness(ctx, sys, chain)));
                    }
                    QueryResult::Unknown => return Ok(ModelCheckResult::Unknown),
                }
            }
            QueryResult::Unknown => return Ok(ModelCheckResult::Unknown),
        }
    }

    Ok(ModelCheckResult::Unknown)
}
