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

// ─────────────────────────────────────────────────────────────────────────────
// Core data structures
// ─────────────────────────────────────────────────────────────────────────────

/// A conjunction of literals over the original (un-stepped) state symbols.
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
/// Literals and other non-symbol sub-expressions are left unchanged.
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
/// frames[0] holds Init constraints and is only included when up_to == 0
/// (for Init-level queries such as the 0-step CEX check and predecessor checks
/// against Init). For frames 1..=k, only the blocking clauses learned at those
/// levels are included — NOT Init — because each F_k over-approximates k-step
/// reachable states independently of the initial state set.
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
    // frames[k] already contains exactly the clauses that are valid at depth k.
    // Unioning frames[1..=k] would double-count and, worse, would make F[k] a
    // subset of F[k-1] — inverting the required nesting F[k-1] ⊆ F[k].
    //
    // The Init frame (frames[0]) is a special case: it is only included when
    // up_to == 0, i.e. for queries that must be anchored to the initial states.
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

/// Build a cube as `sym = val` literals for all states, stored over original symbols.
fn cube_from_state_values(
    ctx: &mut Context,
    sys: &TransitionSystem,
    state_values: &[Value],
) -> Cube {
    let mut literals = Vec::with_capacity(sys.states.len());
    for (s, val) in sys.states.iter().zip(state_values.iter()) {
        let val_expr = ctx.lit(val);
        literals.push(ctx.equal(s.symbol, val_expr));
    }
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

    match query(ctx, smt_ctx, assumptions)? {
        CheckSatResponse::Sat => {
            let state_values = extract_state_values(ctx, smt_ctx, enc, sys, STEP_CUR)?;
            let inputs = extract_input_values(ctx, smt_ctx, enc, sys, STEP_CUR)?;
            let cube = cube_from_state_values(ctx, sys, &state_values);
            Ok(QueryResult::Sat((cube, CexEntry { state_values, inputs })))
        }
        CheckSatResponse::Unsat => Ok(QueryResult::Unsat),
        CheckSatResponse::Unknown => Ok(QueryResult::Unknown),
    }
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

    match query(ctx, smt_ctx, assumptions)? {
        CheckSatResponse::Sat => {
            let state_values = extract_state_values(ctx, smt_ctx, enc, sys, STEP_CUR)?;
            let inputs = extract_input_values(ctx, smt_ctx, enc, sys, STEP_CUR)?;
            let pred_cube = cube_from_state_values(ctx, sys, &state_values);
            Ok(QueryResult::Sat((pred_cube, CexEntry { state_values, inputs })))
        }
        CheckSatResponse::Unsat => Ok(QueryResult::Unsat),
        CheckSatResponse::Unknown => Ok(QueryResult::Unknown),
    }
}

/// Check SAT(F[frame_idx]@CUR ∧ ¬cube@CUR ∧ cube@NXT) without model extraction.
fn is_inductive_relative(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    frames: &[Frame],
    frame_idx: usize,
    cube: &Cube,
) -> Result<QueryResult<()>> {
    let mut assumptions = frame_assumptions(ctx, enc, frames, frame_idx, STEP_CUR);
    let neg_cube = cube.negate(ctx);
    assumptions.push(expr_at_step(ctx, enc, neg_cube, STEP_CUR));
    let cube_expr = cube.to_expr(ctx);
    assumptions.push(expr_at_step(ctx, enc, cube_expr, STEP_NXT));

    match query(ctx, smt_ctx, assumptions)? {
        CheckSatResponse::Sat => Ok(QueryResult::Sat(())),
        CheckSatResponse::Unsat => Ok(QueryResult::Unsat),
        CheckSatResponse::Unknown => Ok(QueryResult::Unknown),
    }
}

/// Greedily drop literals while preserving relative inductiveness w.r.t. `frame_idx`.
fn generalize(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    frames: &[Frame],
    frame_idx: usize,
    mut cube: Cube,
) -> Result<QueryResult<Cube>> {
    let mut i = 0;
    while i < cube.literals.len() {
        // Never drop the last literal: an empty cube negates to `false`, which
        // would be trivially UNSAT in any induction check and cause `false` to
        // be added as a blocking clause — corrupting all future queries.
        if cube.literals.len() == 1 {
            break;
        }

        let mut candidate_lits = cube.literals.clone();
        candidate_lits.remove(i);
        let candidate = Cube { literals: candidate_lits };

        match is_inductive_relative(ctx, smt_ctx, enc, frames, frame_idx, &candidate)? {
            QueryResult::Unsat => {
                cube = candidate; // drop is safe
            }
            QueryResult::Sat(_) => {
                i += 1;
            }
            QueryResult::Unknown => return Ok(QueryResult::Unknown),
        }
    }
    Ok(QueryResult::Sat(cube))
}

/// Add the negation of `cube` as a blocking clause to frames 1..=up_to.
fn add_blocking_clause(ctx: &mut Context, frames: &mut [Frame], cube: &Cube, up_to: usize) {
    let clause = cube.negate(ctx);
    for f in frames[1..=up_to].iter_mut() {
        f.clauses.push(clause);
    }
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
        if !frames[fi].clauses.is_empty() {
            let fi1_set: std::collections::HashSet<ExprRef> =
                frames[fi + 1].clauses.iter().copied().collect();
            if frames[fi].clauses.iter().all(|cl| fi1_set.contains(cl)) {
                return Ok(QueryResult::Sat(fi));
            }
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
            // If SAT: a real initial state reaches the bad state — CEX found.
            // If UNSAT: cube is blocked from Init. This path should not occur in a
            // correct run (predecessors found in Init are always in Init by construction),
            // but we handle it defensively.
            let mut assumptions = frame_assumptions(ctx, enc, frames, 0, STEP_CUR);
            let cube_expr = cube.to_expr(ctx);
            assumptions.push(expr_at_step(ctx, enc, cube_expr, STEP_CUR));

            match query(ctx, smt_ctx, assumptions)? {
                CheckSatResponse::Sat => {
                    // Real CEX: drain the stack from top (init-side) to bottom (bad-side).
                    // Stack = [(bad, ...), ..., (fi=1, ...), (fi=0, e0)].
                    // pop() gives fi=0 first, then fi=1, ..., then bad_entry.
                    let mut chain: Vec<CexEntry> = Vec::with_capacity(stack.len());
                    while let Some((_, _, e)) = stack.pop() {
                        chain.push(e);
                    }
                    // chain = [e0 (init state), e1, ..., e_{k-1}, bad_entry]
                    return Ok(QueryResult::Sat(chain));
                }
                CheckSatResponse::Unsat => {
                    // Defensive: shouldn't happen normally. Block and continue.
                    let gen_cube =
                        match generalize(ctx, smt_ctx, enc, frames, 0, cube.clone())? {
                            QueryResult::Sat(g) => g,
                            _ => cube.clone(),
                        };
                    add_blocking_clause(ctx, frames, &gen_cube, 1);
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
                    let gen_cube =
                        match generalize(ctx, smt_ctx, enc, frames, fi - 1, cube.clone())? {
                            QueryResult::Sat(g) => g,
                            _ => cube.clone(),
                        };
                    add_blocking_clause(ctx, frames, &gen_cube, fi);
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

/// Runs PDR/IC3.
pub fn pdr(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
) -> Result<ModelCheckResult> {
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
            // iv may be a literal or an init-signal expression; store un-stepped.
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
                let wit = make_witness(ctx, sys, vec![CexEntry { state_values, inputs }]);
                return Ok(ModelCheckResult::Fail(wit));
            }
            CheckSatResponse::Unknown => return Ok(ModelCheckResult::Unknown),
            CheckSatResponse::Unsat => {}
        }
    }

    let mut frontier = 1usize;

    for _ in 0..MAX_FRAMES {
        match find_bad_cube(ctx, smt_ctx, &enc, sys, &frames, frontier)? {
            QueryResult::Unsat => {
                match propagate_clauses(ctx, smt_ctx, &enc, &mut frames)? {
                    QueryResult::Sat(_) => return Ok(ModelCheckResult::Success),
                    QueryResult::Unsat => {
                        frontier += 1;
                    }
                    QueryResult::Unknown => return Ok(ModelCheckResult::Unknown),
                }
            }
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
