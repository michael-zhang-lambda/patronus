// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::*;
use crate::mc::ModelCheckResult;
use crate::mc::bmc::{
    TransitionSystemEncoding, UnrollSmtEncoding, check_assuming, check_assuming_end,
    get_smt_value, start_bmc_or_pdr,
};
use crate::mc::types::{InitValue, Witness};
use crate::smt::*;
use crate::system::TransitionSystem;
use baa::{BitVecOps, BitVecValue, Value};
use std::collections::BinaryHeap;

type Result<T> = crate::smt::Result<T>;

// ---------------------------------------------------------------------------
// Public data types
// ---------------------------------------------------------------------------

/// A literal: a state symbol bound to a concrete bit-vector value.
#[derive(Debug, Clone)]
pub struct Literal {
    pub var: ExprRef,
    pub value: BitVecValue,
}

/// A conjunction of literals representing a state.
#[derive(Debug, Clone)]
pub struct Cube {
    pub lits: Vec<Literal>,
}

/// A clause: disjunction of negated literals (i.e. `!cube`).
/// Frames store sets of clauses; F_i over-approximates states reachable in ≤i steps.
#[derive(Debug, Clone)]
pub struct Clause {
    pub lits: Vec<Literal>,
}

// ---------------------------------------------------------------------------
// PdrEncoding trait — the IC3IA seam
// ---------------------------------------------------------------------------

#[derive(Copy, Clone)]
pub enum StateCopy {
    Current,
    Primed,
}

pub trait PdrEncoding {
    fn state_vars(&self) -> &[ExprRef];
    fn current_state(&self, ctx: &Context, var: ExprRef) -> ExprRef;
    fn primed_state(&self, ctx: &Context, var: ExprRef) -> ExprRef;
    fn lit_expr(&self, ctx: &mut Context, lit: &Literal, copy: StateCopy) -> ExprRef;
}

// ---------------------------------------------------------------------------
// Concrete bit-vector encoding
// ---------------------------------------------------------------------------

pub struct ConcreteBvEncoding {
    inner: UnrollSmtEncoding,
    state_vars: Vec<ExprRef>,
}

impl ConcreteBvEncoding {
    pub fn new(
        ctx: &mut Context,
        smt: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: UnrollSmtEncoding,
    ) -> Result<Self> {
        let mut enc = enc;
        enc.init_at(ctx, smt, 0)?;
        for &c in sys.constraints.iter() {
            let c0 = enc.get_at(ctx, c, 0);
            smt.assert(ctx, c0)?;
        }
        enc.unroll(ctx, smt)?;
        for &c in sys.constraints.iter() {
            let c1 = enc.get_at(ctx, c, 1);
            smt.assert(ctx, c1)?;
        }
        let state_vars = sys.states.iter().map(|s| s.symbol).collect();
        Ok(Self { inner: enc, state_vars })
    }
}

impl PdrEncoding for ConcreteBvEncoding {
    fn state_vars(&self) -> &[ExprRef] {
        &self.state_vars
    }

    fn current_state(&self, ctx: &Context, var: ExprRef) -> ExprRef {
        self.inner.get_at(ctx, var, 0)
    }

    fn primed_state(&self, ctx: &Context, var: ExprRef) -> ExprRef {
        self.inner.get_at(ctx, var, 1)
    }

    fn lit_expr(&self, ctx: &mut Context, lit: &Literal, copy: StateCopy) -> ExprRef {
        let sym = match copy {
            StateCopy::Current => self.inner.get_at(ctx, lit.var, 0),
            StateCopy::Primed => self.inner.get_at(ctx, lit.var, 1),
        };
        let val = ctx.bv_lit(&lit.value);
        ctx.equal(sym, val)
    }
}

// ---------------------------------------------------------------------------
// Internal PDR state
// ---------------------------------------------------------------------------

struct PdrState<E: PdrEncoding> {
    enc: E,
    /// frames[i] holds the clauses learned at level i. frames[0] is always empty
    /// (Init is handled by the solver's permanent state).
    frames: Vec<Vec<Clause>>,
    /// Backward trace for CEX reconstruction: cubes[0] is an Init-intersecting
    /// state, cubes[k] is the bad state.
    cex_cubes: Option<Vec<Cube>>,
    /// Per-step input values matching cex_cubes (cex_inputs[i] = inputs driving
    /// the transition from cex_cubes[i] to cex_cubes[i+1]).
    cex_inputs: Option<Vec<Vec<Option<Value>>>>,
    /// Which bad-state index was violated (set by find_bad_cube).
    failed_safety: Vec<u32>,
}

impl<E: PdrEncoding> PdrState<E> {
    fn new(enc: E) -> Self {
        Self {
            enc,
            frames: vec![vec![]],
            cex_cubes: None,
            cex_inputs: None,
            failed_safety: vec![],
        }
    }
}

// ---------------------------------------------------------------------------
// Proof obligation
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct ProofObligation {
    cube: Cube,
    frame: usize,
    depth: usize,
}

impl PartialEq for ProofObligation {
    fn eq(&self, other: &Self) -> bool {
        self.frame == other.frame && self.depth == other.depth
    }
}
impl Eq for ProofObligation {}
impl PartialOrd for ProofObligation {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
// min-heap by frame (process obligations closest to Init first)
impl Ord for ProofObligation {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.frame.cmp(&self.frame).then(other.depth.cmp(&self.depth))
    }
}

// ---------------------------------------------------------------------------
// Result enums for each subroutine
// ---------------------------------------------------------------------------

enum FindBadResult {
    NoBad,
    Bad(Cube),
    Unknown,
}

enum RelIndResult {
    Inductive,
    Predecessor(Cube, Vec<Option<Value>>),
    Unknown,
}

enum InitIntersectResult {
    Disjoint,
    Intersects,
    Unknown,
}

enum BlockResult {
    Blocked,
    RealCex,
    Unknown,
}

enum PropagateResult {
    Fixpoint,
    Continue,
}

// ---------------------------------------------------------------------------
// Top-level pdr()
// ---------------------------------------------------------------------------

/// Runs PDR (IC3) on the given transition system.
pub fn pdr(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
) -> Result<ModelCheckResult> {
    let raw_enc = match start_bmc_or_pdr(ctx, smt_ctx, sys)? {
        (r, None) => return Ok(r),
        (_, Some(enc)) => enc,
    };
    let enc = ConcreteBvEncoding::new(ctx, smt_ctx, sys, raw_enc)?;
    let mut st = PdrState::new(enc);

    loop {
        let n = st.frames.len() - 1;
        match find_bad_cube(ctx, smt_ctx, &mut st, sys)? {
            FindBadResult::NoBad => {
                st.frames.push(vec![]);
                match propagate_clauses(ctx, smt_ctx, &mut st)? {
                    PropagateResult::Fixpoint => return Ok(ModelCheckResult::Success),
                    PropagateResult::Continue => {}
                }
            }
            FindBadResult::Bad(bad) => {
                match block_cube(ctx, smt_ctx, &mut st, bad, n, sys)? {
                    BlockResult::Blocked => {}
                    BlockResult::RealCex => {
                        let wit = build_witness(ctx, &st, sys);
                        return Ok(ModelCheckResult::Fail(wit));
                    }
                    BlockResult::Unknown => return Ok(ModelCheckResult::Unknown),
                }
            }
            FindBadResult::Unknown => return Ok(ModelCheckResult::Unknown),
        }
    }
}

// ---------------------------------------------------------------------------
// find_bad_cube — F_N(s@0) ∧ bad(s@0)
// ---------------------------------------------------------------------------

fn find_bad_cube<E: PdrEncoding>(
    ctx: &mut Context,
    smt: &mut impl SolverContext,
    st: &mut PdrState<E>,
    sys: &TransitionSystem,
) -> Result<FindBadResult> {
    let n = st.frames.len() - 1;

    smt.push()?;
    assert_frame_clauses(ctx, smt, &st.enc, &st.frames, n, StateCopy::Current)?;

    // any bad state at step 0
    let bad_lits: Vec<ExprRef> = sys
        .bad_states
        .iter()
        .map(|&b| st.enc.current_state(ctx, b))
        .collect();
    let any_bad = bad_lits.iter().copied().reduce(|a, b| ctx.or(a, b)).unwrap();

    let res = check_assuming(ctx, smt, [any_bad])?;
    let result = match res {
        CheckSatResponse::Sat => {
            let cube = extract_cube(ctx, smt, &st.enc, StateCopy::Current)?;
            // record which bad states are violated
            st.failed_safety.clear();
            for (i, &b) in sys.bad_states.iter().enumerate() {
                let bval = get_smt_value(ctx, smt, st.enc.current_state(ctx, b))?;
                if let Value::BitVec(v) = bval {
                    if !v.is_zero() {
                        st.failed_safety.push(i as u32);
                    }
                }
            }
            FindBadResult::Bad(cube)
        }
        CheckSatResponse::Unsat => FindBadResult::NoBad,
        CheckSatResponse::Unknown => FindBadResult::Unknown,
    };
    check_assuming_end(smt)?;
    smt.pop()?;
    Ok(result)
}

// ---------------------------------------------------------------------------
// solve_relative — F_{i-1}(s@0) ∧ ¬cube(s@0) ∧ T ∧ cube(s@1)
// ---------------------------------------------------------------------------

fn solve_relative<E: PdrEncoding>(
    ctx: &mut Context,
    smt: &mut impl SolverContext,
    st: &PdrState<E>,
    cube: &Cube,
    frame: usize,
    sys: &TransitionSystem,
) -> Result<RelIndResult> {
    smt.push()?;
    // assert F_{i-1} at step 0 (frames[1..frame] are the non-Init clauses)
    assert_frame_clauses(ctx, smt, &st.enc, &st.frames, frame - 1, StateCopy::Current)?;
    // assert ¬cube at step 0
    let not_cube = negate_cube(ctx, &st.enc, cube, StateCopy::Current);
    smt.assert(ctx, not_cube)?;

    // check assuming cube at step 1
    let primed_lits: Vec<ExprRef> = cube
        .lits
        .iter()
        .map(|lit| st.enc.lit_expr(ctx, lit, StateCopy::Primed))
        .collect();
    let res = check_assuming(ctx, smt, primed_lits)?;

    let result = match res {
        CheckSatResponse::Unsat => RelIndResult::Inductive,
        CheckSatResponse::Sat => {
            let pred = extract_cube(ctx, smt, &st.enc, StateCopy::Current)?;
            let inputs = extract_inputs(ctx, smt, &st.enc, sys)?;
            RelIndResult::Predecessor(pred, inputs)
        }
        CheckSatResponse::Unknown => RelIndResult::Unknown,
    };
    check_assuming_end(smt)?;
    smt.pop()?;
    Ok(result)
}

// ---------------------------------------------------------------------------
// intersects_init — Init ∧ cube(s@0)
// ---------------------------------------------------------------------------

fn intersects_init<E: PdrEncoding>(
    ctx: &mut Context,
    smt: &mut impl SolverContext,
    enc: &E,
    cube: &Cube,
) -> Result<InitIntersectResult> {
    smt.push()?;
    // Init is permanently asserted via init_at(0); just add cube literals
    let cube_lits: Vec<ExprRef> = cube
        .lits
        .iter()
        .map(|lit| enc.lit_expr(ctx, lit, StateCopy::Current))
        .collect();
    let res = check_assuming(ctx, smt, cube_lits)?;
    let result = match res {
        CheckSatResponse::Unsat => InitIntersectResult::Disjoint,
        CheckSatResponse::Sat => InitIntersectResult::Intersects,
        CheckSatResponse::Unknown => InitIntersectResult::Unknown,
    };
    check_assuming_end(smt)?;
    smt.pop()?;
    Ok(result)
}

// ---------------------------------------------------------------------------
// generalize — deletion-based cube minimization
// ---------------------------------------------------------------------------

fn generalize<E: PdrEncoding>(
    ctx: &mut Context,
    smt: &mut impl SolverContext,
    st: &PdrState<E>,
    cube: Cube,
    frame: usize,
    sys: &TransitionSystem,
) -> Result<Cube> {
    let mut cur = cube;
    let mut idx = 0;
    while idx < cur.lits.len() {
        let mut trial = cur.clone();
        trial.lits.remove(idx);
        if trial.lits.is_empty() {
            idx += 1;
            continue;
        }
        let init_ok = matches!(
            intersects_init(ctx, smt, &st.enc, &trial)?,
            InitIntersectResult::Disjoint
        );
        let ind_ok = init_ok
            && matches!(
                solve_relative(ctx, smt, st, &trial, frame, sys)?,
                RelIndResult::Inductive
            );
        if ind_ok {
            cur = trial;
            // do not advance idx — try to drop the new literal at this position
        } else {
            idx += 1;
        }
    }
    Ok(cur)
}

// ---------------------------------------------------------------------------
// block_cube — recursive blocking via priority queue
// ---------------------------------------------------------------------------

fn block_cube<E: PdrEncoding>(
    ctx: &mut Context,
    smt: &mut impl SolverContext,
    st: &mut PdrState<E>,
    bad: Cube,
    n: usize,
    sys: &TransitionSystem,
) -> Result<BlockResult> {
    let mut queue: BinaryHeap<ProofObligation> = BinaryHeap::new();
    queue.push(ProofObligation { cube: bad, frame: n, depth: 0 });

    // parallel backward trace storage (built bottom-up, reversed at the end)
    let mut trace_cubes: Vec<(usize, Cube)> = vec![];
    let mut trace_inputs: Vec<Vec<Option<Value>>> = vec![];

    while let Some(obl) = queue.pop() {
        let ProofObligation { cube, frame, depth } = obl;

        if frame == 0 {
            match intersects_init(ctx, smt, &st.enc, &cube)? {
                InitIntersectResult::Intersects => {
                    // real CEX: build backward trace
                    trace_cubes.push((0, cube));
                    trace_cubes.sort_by_key(|(d, _)| *d);
                    let cex: Vec<Cube> = trace_cubes.into_iter().map(|(_, c)| c).collect();
                    st.cex_cubes = Some(cex);
                    trace_inputs.reverse();
                    st.cex_inputs = Some(trace_inputs);
                    return Ok(BlockResult::RealCex);
                }
                InitIntersectResult::Disjoint => {
                    // push obligation up — block it at frame 1
                    queue.push(ProofObligation { cube, frame: 1, depth });
                }
                InitIntersectResult::Unknown => return Ok(BlockResult::Unknown),
            }
        } else {
            match solve_relative(ctx, smt, st, &cube, frame, sys)? {
                RelIndResult::Inductive => {
                    let gen_cube = generalize(ctx, smt, st, cube, frame, sys)?;
                    let clause = cube_to_clause(&gen_cube);
                    // add clause to all frames up to and including `frame`
                    for f in 1..=frame {
                        st.frames[f].push(clause.clone());
                    }
                    // push obligation to next frame to strengthen invariant
                    if frame < st.frames.len() - 1 {
                        queue.push(ProofObligation {
                            cube: gen_cube.clone(),
                            frame: frame + 1,
                            depth,
                        });
                    }
                    // record this cube in the trace at this depth
                    trace_cubes.push((depth, gen_cube));
                }
                RelIndResult::Predecessor(pred, inputs) => {
                    trace_cubes.push((depth, cube.clone()));
                    trace_inputs.push(inputs);
                    queue.push(ProofObligation { cube: pred, frame: frame - 1, depth: depth + 1 });
                    queue.push(ProofObligation { cube, frame, depth });
                }
                RelIndResult::Unknown => return Ok(BlockResult::Unknown),
            }
        }
    }
    Ok(BlockResult::Blocked)
}

// ---------------------------------------------------------------------------
// propagate_clauses — push clauses to the next frame where possible
// ---------------------------------------------------------------------------

fn propagate_clauses<E: PdrEncoding>(
    ctx: &mut Context,
    smt: &mut impl SolverContext,
    st: &mut PdrState<E>,
) -> Result<PropagateResult> {
    let depth = st.frames.len() - 1;
    for i in 1..depth {
        let clauses = st.frames[i].clone();
        for clause in clauses.iter() {
            // check: F_i(s@0) ∧ T ∧ ¬clause(s@1)
            // i.e. check_assuming(not_clause_primed); if UNSAT → clause is inductive
            smt.push()?;
            assert_frame_clauses(ctx, smt, &st.enc, &st.frames, i, StateCopy::Current)?;
            // build ¬clause at step 1: AND of (lit_expr for each lit in clause) primed
            // clause is OR(var != val), so ¬clause is AND(var == val) — i.e., the cube
            let neg_clause_primed: Vec<ExprRef> = clause
                .lits
                .iter()
                .map(|lit| st.enc.lit_expr(ctx, lit, StateCopy::Primed))
                .collect();
            let res = check_assuming(ctx, smt, neg_clause_primed)?;
            check_assuming_end(smt)?;
            smt.pop()?;

            if res == CheckSatResponse::Unsat {
                st.frames[i + 1].push(clause.clone());
            }
            // Sat or Unknown → leave clause in place
        }

        // fixpoint check: every clause in frames[i] is also in frames[i+1]
        if clauses
            .iter()
            .all(|c| clause_in_frame(c, &st.frames[i + 1]))
        {
            return Ok(PropagateResult::Fixpoint);
        }
    }
    Ok(PropagateResult::Continue)
}

// ---------------------------------------------------------------------------
// Witness construction
// ---------------------------------------------------------------------------

fn build_witness<E: PdrEncoding>(
    ctx: &Context,
    st: &PdrState<E>,
    sys: &TransitionSystem,
) -> Witness {
    let mut wit = Witness::default();
    wit.failed_safety = st.failed_safety.clone();

    let cubes = st.cex_cubes.as_ref().expect("cex_cubes must be set");
    let inputs = st.cex_inputs.as_ref().expect("cex_inputs must be set");

    // initial state from cubes[0]
    let init_cube = &cubes[0];
    for state in sys.states.iter() {
        let sym = state.symbol;
        let val = init_cube
            .lits
            .iter()
            .find(|l| l.var == sym)
            .map(|l| InitValue::BitVec(l.value.clone()))
            .unwrap_or(InitValue::None);
        wit.init.push(val);
        wit.init_names
            .push(ctx.get_symbol_name(sym).map(|s| s.to_string()));
    }

    // input names
    for &inp in sys.inputs.iter() {
        wit.input_names
            .push(ctx.get_symbol_name(inp).map(|s| s.to_string()));
    }

    // input values per step
    wit.inputs = inputs.clone();

    wit
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Assert all clauses from frames[1..=level] at the given state copy.
fn assert_frame_clauses<E: PdrEncoding>(
    ctx: &mut Context,
    smt: &mut impl SolverContext,
    enc: &E,
    frames: &[Vec<Clause>],
    level: usize,
    copy: StateCopy,
) -> Result<()> {
    for fi in 1..=level {
        if fi >= frames.len() {
            break;
        }
        for clause in frames[fi].iter() {
            let expr = clause_expr(ctx, enc, clause, copy);
            smt.assert(ctx, expr)?;
        }
    }
    Ok(())
}

/// Build the SMT expression for a clause: OR of (var != value) for each literal.
fn clause_expr<E: PdrEncoding>(
    ctx: &mut Context,
    enc: &E,
    clause: &Clause,
    copy: StateCopy,
) -> ExprRef {
    let negs: Vec<ExprRef> = clause
        .lits
        .iter()
        .map(|lit| {
            let eq = enc.lit_expr(ctx, lit, copy);
            ctx.not(eq)
        })
        .collect();
    negs.into_iter()
        .reduce(|a, b| ctx.or(a, b))
        .expect("clause must have at least one literal")
}

/// Build NOT(cube) at the given state copy: OR of (var != value).
fn negate_cube<E: PdrEncoding>(
    ctx: &mut Context,
    enc: &E,
    cube: &Cube,
    copy: StateCopy,
) -> ExprRef {
    let negs: Vec<ExprRef> = cube
        .lits
        .iter()
        .map(|lit| {
            let eq = enc.lit_expr(ctx, lit, copy);
            ctx.not(eq)
        })
        .collect();
    negs.into_iter()
        .reduce(|a, b| ctx.or(a, b))
        .expect("cube must have at least one literal")
}

/// Convert a cube into its blocking clause (negation).
fn cube_to_clause(cube: &Cube) -> Clause {
    Clause { lits: cube.lits.clone() }
}

/// Extract a cube from the current SAT model over state vars.
fn extract_cube<E: PdrEncoding>(
    ctx: &mut Context,
    smt: &mut impl SolverContext,
    enc: &E,
    copy: StateCopy,
) -> Result<Cube> {
    let mut lits = Vec::new();
    for &var in enc.state_vars() {
        let sym = match copy {
            StateCopy::Current => enc.current_state(ctx, var),
            StateCopy::Primed => enc.primed_state(ctx, var),
        };
        let val = get_smt_value(ctx, smt, sym)?;
        if let Value::BitVec(bv) = val {
            lits.push(Literal { var, value: bv });
        }
    }
    Ok(Cube { lits })
}

/// Extract input values at step 0 from the current SAT model.
fn extract_inputs<E: PdrEncoding>(
    ctx: &mut Context,
    smt: &mut impl SolverContext,
    enc: &E,
    sys: &TransitionSystem,
) -> Result<Vec<Option<Value>>> {
    let mut vals = Vec::new();
    for &inp in sys.inputs.iter() {
        let sym = enc.current_state(ctx, inp);
        let val = get_smt_value(ctx, smt, sym).ok();
        vals.push(val);
    }
    Ok(vals)
}

/// Check whether a clause is syntactically present in a frame.
fn clause_in_frame(clause: &Clause, frame: &[Clause]) -> bool {
    frame.iter().any(|c| clauses_equal(c, clause))
}

fn clauses_equal(a: &Clause, b: &Clause) -> bool {
    if a.lits.len() != b.lits.len() {
        return false;
    }
    a.lits.iter().zip(b.lits.iter()).all(|(la, lb)| {
        la.var == lb.var && la.value == lb.value
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mc::{ModelCheckResult, bmc};
    use crate::smt::BITWUZLA;
    use crate::system::State;

    fn make_one_bit_safe() -> (Context, TransitionSystem) {
        let mut ctx = Context::default();
        let mut sys = TransitionSystem::new("safe".to_string());
        // state s : bv<1>, init = 0, next = 0
        let s = ctx.bv_symbol("s", 1);
        let zero = ctx.bit_vec_val(0u32, 1);
        sys.add_state(&ctx, State { symbol: s, init: Some(zero), next: Some(zero) });
        // bad = (s = 1) — unreachable
        let one = ctx.bit_vec_val(1u32, 1);
        let bad = ctx.equal(s, one);
        sys.bad_states.push(bad);
        (ctx, sys)
    }

    fn make_one_bit_unsafe() -> (Context, TransitionSystem) {
        let mut ctx = Context::default();
        let mut sys = TransitionSystem::new("unsafe".to_string());
        // state s : bv<1>, init = 0, next = !s
        let s = ctx.bv_symbol("s", 1);
        let zero = ctx.bit_vec_val(0u32, 1);
        let not_s = ctx.not(s);
        sys.add_state(&ctx, State { symbol: s, init: Some(zero), next: Some(not_s) });
        // bad = (s = 1)
        let one = ctx.bit_vec_val(1u32, 1);
        let bad = ctx.equal(s, one);
        sys.bad_states.push(bad);
        (ctx, sys)
    }

    fn make_two_bit_counter_unsafe() -> (Context, TransitionSystem) {
        let mut ctx = Context::default();
        let mut sys = TransitionSystem::new("counter".to_string());
        // 2-bit counter: init = 0, next = s + 1
        let s = ctx.bv_symbol("s", 2);
        let zero = ctx.bit_vec_val(0u32, 2);
        let one = ctx.bit_vec_val(1u32, 2);
        let next_s = ctx.add(s, one);
        sys.add_state(&ctx, State { symbol: s, init: Some(zero), next: Some(next_s) });
        // bad = (s = 3)
        let three = ctx.bit_vec_val(3u32, 2);
        let bad = ctx.equal(s, three);
        sys.bad_states.push(bad);
        (ctx, sys)
    }

    #[test]
    fn test_pdr_trivial_safe() {
        let (mut ctx, sys) = make_one_bit_safe();
        let mut smt = BITWUZLA.start(None).unwrap();
        let res = pdr(&mut ctx, &mut smt, &sys).unwrap();
        assert!(
            matches!(res, ModelCheckResult::Success),
            "expected Success for trivially safe system"
        );
    }

    #[test]
    fn test_pdr_trivial_unsafe() {
        let (mut ctx, sys) = make_one_bit_unsafe();
        let mut smt = BITWUZLA.start(None).unwrap();
        let res = pdr(&mut ctx, &mut smt, &sys).unwrap();
        assert!(
            matches!(res, ModelCheckResult::Fail(_)),
            "expected Fail for trivially unsafe system"
        );
        if let ModelCheckResult::Fail(wit) = res {
            assert_eq!(wit.failed_safety, vec![0u32]);
        }
    }

    #[test]
    fn test_pdr_two_bit_counter_unsafe() {
        let (mut ctx, sys) = make_two_bit_counter_unsafe();
        let mut smt = BITWUZLA.start(None).unwrap();
        let res = pdr(&mut ctx, &mut smt, &sys).unwrap();
        assert!(
            matches!(res, ModelCheckResult::Fail(_)),
            "expected Fail for 2-bit counter reaching 3"
        );
    }

    #[test]
    fn test_pdr_agrees_with_bmc_safe() {
        let (mut ctx, sys) = make_one_bit_safe();
        let mut smt_pdr = BITWUZLA.start(None).unwrap();
        let pdr_res = pdr(&mut ctx, &mut smt_pdr, &sys).unwrap();

        let (mut ctx2, sys2) = make_one_bit_safe();
        let mut smt_bmc = BITWUZLA.start(None).unwrap();
        let bmc_res = bmc(&mut ctx2, &mut smt_bmc, &sys2, false, false, 20).unwrap();

        let pdr_safe = matches!(pdr_res, ModelCheckResult::Success);
        let bmc_safe = matches!(bmc_res, ModelCheckResult::Success);
        assert_eq!(pdr_safe, bmc_safe, "PDR and BMC disagree on safe system");
    }

    #[test]
    fn test_pdr_agrees_with_bmc_unsafe() {
        let (mut ctx, sys) = make_one_bit_unsafe();
        let mut smt_pdr = BITWUZLA.start(None).unwrap();
        let pdr_res = pdr(&mut ctx, &mut smt_pdr, &sys).unwrap();

        let (mut ctx2, sys2) = make_one_bit_unsafe();
        let mut smt_bmc = BITWUZLA.start(None).unwrap();
        let bmc_res = bmc(&mut ctx2, &mut smt_bmc, &sys2, false, false, 20).unwrap();

        let pdr_fail = matches!(pdr_res, ModelCheckResult::Fail(_));
        let bmc_fail = matches!(bmc_res, ModelCheckResult::Fail(_));
        assert_eq!(pdr_fail, bmc_fail, "PDR and BMC disagree on unsafe system");
    }

    #[test]
    fn test_pdr_delay_btor() {
        let (mut ctx, mut sys) =
            crate::btor2::parse_file("../inputs/unittest/delay.btor").unwrap();
        crate::system::transform::simplify_expressions(&mut ctx, &mut sys);
        let mut smt = BITWUZLA.start(None).unwrap();
        // delay.btor has no bad states, so PDR should return Success immediately
        let res = pdr(&mut ctx, &mut smt, &sys).unwrap();
        assert!(
            matches!(res, ModelCheckResult::Success),
            "expected Success for delay.btor (no bad states)"
        );
    }
}
