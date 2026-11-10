// released under BSD 3-Clause License

//! Translates a patronus [`TransitionSystem`] into Lean source code.

use baa::BitVecOps;
use patronus::expr::{Context, Expr, ExprRef, Type, TypeCheck};
use patronus::system::{State, TransitionSystem};
use rustc_hash::FxHashMap;
use std::io::Write;

/// Translate BTOR expression into Lean expression
fn translate_expr(ctx: &Context, expr: ExprRef, prefix: &str) -> String {
    match &ctx[expr] {
        Expr::BVLiteral(lit) => {
            let width = lit.width();
            let value = lit.get(ctx);
            let dec = value.to_dec_str();
            format!("{dec}#{width}")
        }
        Expr::BVSymbol { name, width: _ } => {
            let name = ctx[name.to_owned()].clone();
            format!("{prefix}.{name}")
        }
        Expr::BVAdd(a, b, _width) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, prefix),
                translate_expr(ctx, *b, prefix),
            );
            format!("({a_str} + {b_str})")
        }
        Expr::BVEqual(a, b) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, prefix),
                translate_expr(ctx, *b, prefix),
            );
            format!("({a_str} == {b_str})")
        }
        Expr::BVAnd(a, b, _width) => {
            let (a_str, b_str) = (
                {
                    let str = translate_expr(ctx, *a, prefix);
                    if str == "1#1" {
                        String::from("true")
                    } else if str == "0#1" {
                        String::from("false")
                    } else {
                        str
                    }
                },
                {
                    let str = translate_expr(ctx, *b, prefix);
                    if str == "1#1" {
                        String::from("true")
                    } else if str == "0#1" {
                        String::from("false")
                    } else {
                        str
                    }
                },
            );
            format!("({a_str} && {b_str})")
        }
        Expr::BVGreater(a, b) => {
            let (a_str, b_str) = (
                translate_expr(ctx, *a, prefix),
                translate_expr(ctx, *b, prefix),
            );
            format!("({a_str} > {b_str})")
        }
        Expr::BVIte { cond, tru, fals } => {
            let (cond_str, tru_str, fals_str) = (
                translate_expr(ctx, *cond, prefix),
                translate_expr(ctx, *tru, prefix),
                translate_expr(ctx, *fals, prefix),
            );
            format!("(if {cond_str} then {tru_str} else {fals_str})")
        }
        Expr::BVNot(e, _width) => {
            let e_str = translate_expr(ctx, *e, prefix);
            format!("¬({e_str})")
        }
        _ => unimplemented!(),
    }
}

/// Translate stateful elements into Lean `structure` text
fn translate_system(
    ctx: &Context,
    sys: &TransitionSystem,
    sys_name: &str,
    out: &mut impl Write,
) -> std::io::Result<()> {
    let (mut state_ct, mut input_ct) = (0u64, 0u64);
    let mut state_names: FxHashMap<State, String> = FxHashMap::default();

    writeln!(out, "structure State where")?;
    writeln!(out, "  mk ::")?;
    for state in sys.states.iter() {
        // Get human-readable name of state, or assign default name
        let name = if let Some(name) = ctx.get_symbol_name(state.symbol) {
            name.to_string()
        } else {
            let name = format!("state{state_ct}");
            state_ct += 1;
            name
        };

        // Add name entry to map
        state_names.insert(*state, name.clone());

        // Write appropriate field definition
        // NOTE: arrays are ignored for now
        match state.symbol.get_type(ctx) {
            Type::BV(width) => writeln!(out, "  {name} : BitVec {width}")?,
            Type::Array(_) => unimplemented!(),
        };
    }
    writeln!(out)?;
    writeln!(out)?;

    writeln!(out, "structure Input where")?;
    writeln!(out, "  mk ::")?;
    for input in sys.inputs.iter() {
        // Get human-readable name of input, or assign default name
        let name = if let Some(name) = ctx.get_symbol_name(*input) {
            name.to_string()
        } else {
            let name = format!("input{input_ct}");
            input_ct += 1;
            name
        };

        // Write appropriate field definition
        // NOTE: arrays are ignored for now
        match input.get_type(ctx) {
            Type::BV(width) => writeln!(out, "  {name} : BitVec {width}")?,
            Type::Array(_) => unimplemented!(),
        };
    }
    writeln!(out)?;
    writeln!(out)?;

    writeln!(out, "def {sys_name}_sys : TransSys State Input State := {{")?;
    writeln!(out, "  init := fun (o : State) => {{")?;
    for (state, name) in state_names.iter() {
        if let Some(init) = state.init {
            // State has explicit initial expression
            let init_str = translate_expr(ctx, init, "");
            writeln!(out, "    {name} := {init_str}")?;
        } else {
            // State has no explicit initial expression: let oracle decide
            writeln!(out, "    {name} := o.{name}")?;
        }
    }
    writeln!(out, "  }},")?;

    writeln!(out, "next := fun (s : State) (i : Input) => {{")?;
    for (state, name) in state_names.iter() {
        if let Some(next) = state.next {
            // State has explicit transition
            let next_str = translate_expr(ctx, next, "s");
            writeln!(out, "    {name} := {next_str}")?;
        } else {
            // State does not transition: preserve old state
            writeln!(out, "    {name} := s.{name}")?;
        }
    }
    writeln!(out, "  }},")?;

    // NOTE: constraints are ignored for now
    writeln!(out, "constraint := fun _ _ => true,")?;

    writeln!(out, "bad := fun (s : State) (i : Input) => {{")?;
    write!(out, "false")?;
    for &bad in sys.bad_states.iter() {
        // TODO: investigate whethe inputs can be in bad state formula
        let bad_str = translate_expr(ctx, bad, "s");
        write!(out, " || {bad_str}")?;
    }
    writeln!(out)?;
    writeln!(out, "  }},")?;
    writeln!(out, "}}")?;

    // Write top-level safety theorem
    writeln!(out)?;
    writeln!(
        out,
        "theorem {sys_name}_safe : {sys_name}_sys.safe := by sorry"
    )
}

/// Translate `sys` into Lean and returns the source as a string.
pub fn translate_to_str(ctx: &Context, sys: &TransitionSystem) -> String {
    let mut buf = Vec::new();
    translate(ctx, sys, &mut buf).expect("writing to an in-memory buffer cannot fail");
    String::from_utf8(buf).expect("generated Lean is valid UTF-8")
}

/// Translate `sys` into Lean and writes the source to `out`.
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
    writeln!(out)?;
    writeln!(out, "namespace {sys_name}")?;
    writeln!(out)?;
    translate_system(ctx, sys, sys_name, out)?;
    writeln!(out)?;
    writeln!(out, "end {sys_name}")?;
    Ok(())
}
