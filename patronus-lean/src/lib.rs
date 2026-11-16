// released under BSD 3-Clause License

//! Translates a patronus [`TransitionSystem`] into Lean source code.

use baa::BitVecOps;
use patronus::expr::{Context, Expr, ExprRef, Type, TypeCheck};
use patronus::system::{State, TransitionSystem};
use rustc_hash::FxHashSet;

pub mod cosim;
use std::io::Write;

const ESCAPE_L: &str = "«";
const ESCAPE_R: &str = "»";

/// Escape BTOR name `name` to Lean name
#[inline]
fn escape_name(name: String) -> String {
    format!("{ESCAPE_L}{name}{ESCAPE_R}")
}

/// Translate BTOR expression into Lean expression string
fn translate_expr(
    ctx: &Context,
    expr: ExprRef,
    state_names: &(&str, &FxHashSet<String>),
    input_names: &(&str, &FxHashSet<String>),
) -> String {
    match &ctx[expr] {
        Expr::BVLiteral(lit) => {
            let width = lit.width();
            let value = lit.get(ctx);
            let dec = value.to_dec_str();
            format!("{dec}#{width}")
        }
        Expr::ArrayConstant { e, index_width, .. } => {
            let e_str = translate_expr(ctx, *e, state_names, input_names);
            format!("(BVArray.const (iw := {index_width}) {e_str})")
        }
        Expr::BVSymbol { name, .. } | Expr::ArraySymbol { name, .. } => {
            let name = ctx[name.to_owned()].clone();
            let prefix = if state_names.1.contains(&name) {
                state_names.0
            } else if input_names.1.contains(&name) {
                input_names.0
            } else {
                panic!("symbol must be state or input")
            };
            let esc_name = escape_name(name);
            format!("{prefix}.{esc_name}")
        }
        Expr::BVZeroExt { e, by: _, width } => {
            let e_str = translate_expr(ctx, *e, state_names, input_names);
            format!("(BitVec.zeroExtend {width} {e_str})")
        }
        Expr::BVSignExt { e, by: _, width } => {
            let e_str = translate_expr(ctx, *e, state_names, input_names);
            format!("(BitVec.signExtend {width} {e_str})")
        }
        Expr::BVSlice { e, hi, lo } => {
            let e_str = translate_expr(ctx, *e, state_names, input_names);
            format!("(BitVec.extractLsb {hi} {lo} {e_str})")
        }
        Expr::BVConcat(a, b, _) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("(BitVec.append {a_str} {b_str})")
        }
        Expr::BVAdd(a, b, _) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("({a_str} + {b_str})")
        }
        Expr::BVSub(a, b, _) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("({a_str} - {b_str})")
        }
        Expr::BVMul(a, b, _) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("({a_str} * {b_str})")
        }
        Expr::BVUnsignedDiv(a, b, _) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("({a_str} / {b_str})")
        }
        Expr::BVSignedDiv(a, b, _) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("(BitVec.sdiv {a_str} {b_str})")
        }
        Expr::BVSignedMod(a, b, _) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("(BitVec.smod {a_str} {b_str})")
        }
        Expr::BVUnsignedRem(a, b, _) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("(BitVec.smod {a_str} {b_str})")
        }
        Expr::BVSignedRem(a, b, _) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("({a_str} % {b_str})")
        }
        Expr::BVEqual(a, b) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("(BitVec.ofBool ({a_str} == {b_str}))")
        }
        Expr::BVAnd(a, b, _width) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("({a_str} &&& {b_str})")
        }
        Expr::BVOr(a, b, _width) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("({a_str} ||| {b_str})")
        }
        Expr::BVXor(a, b, _) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("({a_str} ^^^ {b_str})")
        }
        Expr::BVShiftLeft(e, shamt, _) => {
            let (e_str, shamt_str) = (
                translate_expr(ctx, *e, state_names, input_names),
                translate_expr(ctx, *shamt, state_names, input_names),
            );
            format!("({e_str} <<< ({shamt_str}).toNat)")
        }
        Expr::BVShiftRight(e, shamt, _) => {
            let (e_str, shamt_str) = (
                translate_expr(ctx, *e, state_names, input_names),
                translate_expr(ctx, *shamt, state_names, input_names),
            );
            format!("(BitVec.ushiftRight {e_str} ({shamt_str}).toNat)")
        }
        Expr::BVArithmeticShiftRight(e, shamt, _) => {
            let (e_str, shamt_str) = (
                translate_expr(ctx, *e, state_names, input_names),
                translate_expr(ctx, *shamt, state_names, input_names),
            );
            format!("({e_str} >>> ({shamt_str}).toNat)")
        }
        Expr::BVGreater(a, b) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("(BitVec.ofBool (BitVec.ult {b_str} {a_str}))")
        }
        Expr::BVGreaterSigned(a, b, _) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("(BitVec.ofBool (BitVec.slt {b_str} {a_str}))")
        }
        Expr::BVGreaterEqual(a, b) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("(BitVec.ofBool (BitVec.ule {b_str} {a_str}))")
        }
        Expr::BVGreaterEqualSigned(a, b, _) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("(BitVec.ofBool (BitVec.sle {b_str} {a_str}))")
        }
        Expr::BVIte { cond, tru, fals } | Expr::ArrayIte { cond, tru, fals } => {
            let cond_str = {
                let cond_str = translate_expr(ctx, *cond, state_names, input_names);
                format!("({cond_str} == 1#1)")
            };
            let (tru_str, fals_str) = (
                translate_expr(ctx, *tru, state_names, input_names),
                translate_expr(ctx, *fals, state_names, input_names),
            );

            format!("(if {cond_str} then {tru_str} else {fals_str})")
        }
        Expr::BVImplies(a, b) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("(~~~({a_str}) ||| {b_str})")
        }
        Expr::BVNot(e, _) => {
            let e_str = translate_expr(ctx, *e, state_names, input_names);
            format!("~~~({e_str})")
        }
        Expr::BVNegate(e, _) => {
            let e_str = translate_expr(ctx, *e, state_names, input_names);
            format!("-({e_str})")
        }
        Expr::BVArrayRead { array, index, .. } => {
            let (a_str, i_str) = (
                translate_expr(ctx, *array, state_names, input_names),
                translate_expr(ctx, *index, state_names, input_names),
            );
            format!("(BVArray.read {a_str} {i_str})")
        }
        Expr::ArrayStore { array, index, data } => {
            let (a_str, i_str, d_str) = (
                translate_expr(ctx, *array, state_names, input_names),
                translate_expr(ctx, *index, state_names, input_names),
                translate_expr(ctx, *data, state_names, input_names),
            );
            format!("(BVArray.write {a_str} {i_str} {d_str})")
        }
        Expr::ArrayEqual(a, b) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, state_names, input_names),
                translate_expr(ctx, *b, state_names, input_names),
            );
            format!("(BitVec.ofBool (BVArray.equals {a_str} {b_str}))")
        }
    }
}

/// Lean field names of the states, in declaration order
pub type StateNames = Vec<(State, String)>;
/// Lean field names of the inputs, in declaration order
pub type InputNames = Vec<(ExprRef, String)>;

/// Assign a Lean field name to every state and input of `sys`, in declaration order
///
/// Signals with a symbol name keep it; unnamed ones get `state{n}` / `input{n}`
pub fn signal_names(ctx: &Context, sys: &TransitionSystem) -> (StateNames, InputNames) {
    let mut state_ct = 0u64;
    let states = sys
        .states
        .iter()
        .map(|state| {
            let name = if let Some(name) = ctx.get_symbol_name(state.symbol) {
                name.to_string()
            } else {
                let name = format!("state{state_ct}");
                state_ct += 1;
                name
            };
            (*state, name)
        })
        .collect();

    let mut input_ct = 0u64;
    let inputs = sys
        .inputs
        .iter()
        .map(|&input| {
            let name = if let Some(name) = ctx.get_symbol_name(input) {
                name.to_string()
            } else {
                let name = format!("input{input_ct}");
                input_ct += 1;
                name
            };
            (input, name)
        })
        .collect();

    (states, inputs)
}

/// Translate stateful elements into Lean `structure` text
fn translate_system(
    ctx: &Context,
    sys: &TransitionSystem,
    sys_name: &str,
    out: &mut impl Write,
) -> std::io::Result<()> {
    let (state_names, input_list) = signal_names(ctx, sys);

    writeln!(out, "structure State where")?;
    writeln!(out, "  mk ::")?;
    for (state, name) in state_names.iter() {
        let esc_name = escape_name(name.clone());
        match state.symbol.get_type(ctx) {
            Type::BV(width) => writeln!(out, "  {esc_name} : BitVec {width}")?,
            Type::Array(av) => {
                let (iw, dw) = (av.index_width, av.data_width);
                writeln!(out, "  {esc_name} : BVArray {iw} {dw}")?
            }
        };
    }
    writeln!(out)?;

    writeln!(out, "structure Input where")?;
    writeln!(out, "  mk ::")?;
    for (input, name) in input_list.iter() {
        // NOTE: arrays are ignored for now
        let esc_name = escape_name(name.clone());
        match input.get_type(ctx) {
            Type::BV(width) => writeln!(out, "  {esc_name} : BitVec {width}")?,
            Type::Array(av) => {
                let (iw, dw) = (av.index_width, av.data_width);
                writeln!(out, "  {esc_name} : BVArray {iw} {dw}")?
            }
        };
    }
    writeln!(out)?;

    let input_names: FxHashSet<String> = input_list.iter().map(|(_, n)| n.clone()).collect();
    let state_set: FxHashSet<String> = state_names.iter().map(|(_, n)| n.clone()).collect();

    writeln!(out, "def {sys_name}_sys : TransSys State Input State := {{")?;
    writeln!(out, "  init := fun (o : State) (i : Input) => {{")?;
    for (state, name) in state_names.iter() {
        let esc_name = escape_name(name.clone());
        if let Some(init) = state.init {
            // State has explicit initial expression
            let init_str = translate_expr(ctx, init, &("o", &state_set), &("i", &input_names));
            writeln!(out, "    {esc_name} := {init_str}")?;
        } else {
            // State has no explicit initial expression: let oracle decide
            writeln!(out, "    {esc_name} := o.{esc_name}")?;
        }
    }
    writeln!(out, "  }},")?;

    writeln!(out, "  next := fun (s : State) (i : Input) => {{")?;
    for (state, name) in state_names.iter() {
        let esc_name = escape_name(name.clone());
        if let Some(next) = state.next {
            // State has explicit transition
            let next_str = translate_expr(ctx, next, &("s", &state_set), &("i", &input_names));
            writeln!(out, "    {esc_name} := {next_str}")?;
        } else {
            // State does not transition: preserve old state
            writeln!(out, "    {esc_name} := s.{esc_name}")?;
        }
    }
    writeln!(out, "  }},")?;

    // NOTE: constraints are ignored for now
    writeln!(out, "  constraint := fun _ _ => true,")?;

    writeln!(out, "  bad := fun (s : State) (i : Input) => (")?;
    write!(out, "    false")?;
    for &bad in sys.bad_states.iter() {
        let bad_str = translate_expr(ctx, bad, &("s", &state_set), &("i", &input_names));
        write!(out, " || ({bad_str} == 1#1)")?;
    }
    writeln!(out)?;
    writeln!(out, "  ),")?;
    writeln!(out, "}}")?;

    // Write top-level safety theorem
    writeln!(out)?;
    writeln!(
        out,
        "theorem {sys_name}_safe : {sys_name}_sys.safe := by sorry"
    )
}

/// Translate `sys` into Lean and returns the source as a string
pub fn translate_to_str(ctx: &Context, sys: &TransitionSystem) -> String {
    let mut buf = Vec::new();
    translate(ctx, sys, &mut buf).expect("writing to an in-memory buffer cannot fail");
    String::from_utf8(buf).expect("generated Lean is valid UTF-8")
}

/// Translate `sys` into Lean and writes the source to `out`
pub fn translate(
    ctx: &Context,
    sys: &TransitionSystem,
    out: &mut impl Write,
) -> std::io::Result<()> {
    let sys_name = if sys.name.is_empty() {
        "System"
    } else {
        sys.name.as_str()
    };
    writeln!(out, "-- generated by patronus-lean")?;
    writeln!(out)?;
    writeln!(out, "import HwFormal.TransSys")?;
    writeln!(out, "import HwFormal.BVArray")?;
    writeln!(out)?;
    writeln!(out, "namespace {sys_name}")?;
    writeln!(out)?;
    translate_system(ctx, sys, sys_name, out)?;
    writeln!(out)?;
    writeln!(out, "end {sys_name}")?;
    Ok(())
}
