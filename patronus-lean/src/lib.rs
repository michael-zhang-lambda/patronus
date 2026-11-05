// released under BSD 3-Clause License

//! Translates a patronus [`TransitionSystem`] into Lean source code.

use baa::BitVecOps;
use patronus::expr::{Context, Expr, ExprRef, Type, TypeCheck};
use patronus::system::{State, TransitionSystem};
use rustc_hash::FxHashMap;
use std::io::Write;

/// Translate BTOR expression into Lean expression
fn translate_expr(ctx: &Context, expr: ExprRef, prefix: &str) -> String {
    let prefix_str = prefix.to_string();
    match &ctx[expr] {
        Expr::BVLiteral(lit) => {
            let width = lit.width();
            let value = lit.get(ctx);
            let dec = value.to_dec_str();
            format!("{dec}#{width}")
        }
        Expr::BVSymbol { name, width: _ } => {
            let name = ctx[name.to_owned()].clone();
            format!("{prefix_str}.{name}")
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
            format!("({a_str} = {b_str})")
        }
        Expr::BVAnd(a, b, _width) => {
            let (a_str, b_str) = (
                {
                    let str = translate_expr(ctx, *a, prefix);
                    if str == "1#1" {
                        String::from("True")
                    } else if str == "0#1" {
                        String::from("False")
                    } else {
                        str
                    }
                },
                {
                    let str = translate_expr(ctx, *b, prefix);
                    if str == "1#1" {
                        String::from("True")
                    } else if str == "0#1" {
                        String::from("False")
                    } else {
                        str
                    }
                },
            );
            format!("({a_str} ∧ {b_str})")
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
    out: &mut impl Write,
) -> std::io::Result<()> {
    let mut state_ct = 0u64;
    let mut name_map: FxHashMap<State, String> = FxHashMap::default();

    let name = if sys.name.is_empty() {
        "System"
    } else {
        sys.name.as_str()
    };

    writeln!(out, "structure {name} where\n\tmk ::")?;
    for state in sys.states.iter() {
        // Get name of state variable
        let state_name = if let Some(name) = ctx.get_symbol_name(state.symbol) {
            name.to_string()
        } else {
            let name = format!("state{state_ct}");
            state_ct += 1;
            name
        };

        name_map.insert(*state, state_name.clone());

        // Get width of bitvector (ignore arrays for now)
        let width = match state.symbol.get_type(ctx) {
            Type::BV(width) => width,
            Type::Array(_at) => unimplemented!(),
        };

        // Add state definition
        writeln!(out, "\t{state_name} : BitVec {width}")?;
    }
    writeln!(out)?;

    writeln!(out, "instance : Circuit {name} where")?;

    write!(out, "\tInit c := True")?;
    for state in sys.states.iter() {
        let state_name = name_map[state].clone();
        if let Some(init) = state.init {
            // If there is an initial value for some state
            // conjunct the assignment to the `Init` formula
            let init_str = translate_expr(ctx, init, "c");
            write!(out, " ∧ c.{state_name} = {init_str}")?;
        }
    }
    writeln!(out)?;

    write!(out, "\tTrans cb ca := True")?;
    for state in sys.states.iter() {
        let state_name = name_map[state].clone();
        if let Some(next) = state.next {
            // If there is a next state, construct formula
            let next_str = translate_expr(ctx, next, "cb");
            write!(out, " ∧ ca.{state_name} = {next_str}")?;
        }
    }
    writeln!(out)?;

    // NOTE: constraints are not supported yet
    writeln!(out, "\tAssump _ := True\n")?;

    write!(out, "def bad (c : {name}) : Prop := False")?;
    for &bad in sys.bad_states.iter() {
        let bad_str = translate_expr(ctx, bad, "c");
        write!(out, " ∨ {bad_str}")?;
    }
    writeln!(out)?;
    writeln!(out)?;

    // Create final safety theorem
    writeln!(
        out,
        "theorem {name}_safe (n : Nat) (hb : 0 < n) : ∀(t : List ({name})), (∀c ∈ t, Circuit.Assump c) -> Trace t -> (∀c ∈ t, ¬(bad c)) := by sorry"
    )
}

/// Translates `sys` into Lean and returns the source as a string.
pub fn translate_to_str(ctx: &Context, sys: &TransitionSystem) -> String {
    let mut buf = Vec::new();
    translate(ctx, sys, &mut buf).expect("writing to an in-memory buffer cannot fail");
    String::from_utf8(buf).expect("generated Lean is valid UTF-8")
}

/// Translates `sys` into Lean and writes the source to `out`.
pub fn translate(
    ctx: &Context,
    sys: &TransitionSystem,
    out: &mut impl Write,
) -> std::io::Result<()> {
    let namespace = if sys.name.is_empty() {
        "System"
    } else {
        sys.name.as_str()
    };
    writeln!(out, "-- generated by patronus-lean")?;
    writeln!(out, "namespace {namespace}")?;
    writeln!(out)?;
    translate_system(ctx, sys, out)?;
    writeln!(out)?;
    writeln!(out, "end {namespace}")?;
    Ok(())
}
