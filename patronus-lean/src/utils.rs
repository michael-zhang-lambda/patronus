// released under BSD 3-Clause License

//! Naming helpers shared by the translator and the co-simulation harness.

use patronus::expr::{Context, ExprRef};
use patronus::system::{State, TransitionSystem};
use rustc_hash::FxHashSet;

const ESCAPE_L: &str = "«";
const ESCAPE_R: &str = "»";

/// Suffix of the input that supplies the next value of a state without a `next` expression
const NEXT_SUFFIX: &str = "$next";

/// Escape BTOR name `name` to Lean name
#[inline]
pub(crate) fn escape_name(name: String) -> String {
    format!("{ESCAPE_L}{name}{ESCAPE_R}")
}

/// Lean field names of the states, in declaration order
pub type StateNames = Vec<(State, String)>;
/// Lean field names of the inputs, in declaration order
pub type InputNames = Vec<(ExprRef, String)>;

/// Symbols of the states of `sys` that have no `next` expression, in declaration order
pub(crate) fn no_next_states(sys: &TransitionSystem) -> Vec<ExprRef> {
    sys.states
        .iter()
        .filter(|state| state.next.is_none())
        .map(|state| state.symbol)
        .collect()
}

/// Assign a Lean field name to every state and input of `sys`, in declaration order
///
/// Signals with a symbol name keep it; unnamed ones get `state{n}` / `input{n}`.
///
/// A state without a `next` expression stays a state (so its `init` is honored), and
/// additionally gets an input named `{state name}$next` which supplies its value in the next
/// cycle. These inputs come after the regular inputs, in state declaration order, and are
/// keyed by the state's symbol.
pub fn signal_names(ctx: &Context, sys: &TransitionSystem) -> (StateNames, InputNames) {
    let mut state_ct = 0u64;
    let states: StateNames = sys
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
    let regular_inputs = sys.inputs.iter().map(|&input| {
        let name = if let Some(name) = ctx.get_symbol_name(input) {
            name.to_string()
        } else {
            let name = format!("input{input_ct}");
            input_ct += 1;
            name
        };
        (input, name)
    });
    // derive the `$next` name from the state's (possibly generated) name so that both agree
    let next_inputs = states
        .iter()
        .filter(|(state, _)| state.next.is_none())
        .map(|(state, name)| (state.symbol, format!("{name}{NEXT_SUFFIX}")));
    let inputs = regular_inputs.chain(next_inputs).collect();

    (states, inputs)
}

/// Symbols of the states without `next`, as a set (see [`no_next_states`])
pub(crate) fn no_next_state_set(sys: &TransitionSystem) -> FxHashSet<ExprRef> {
    no_next_states(sys).into_iter().collect()
}
