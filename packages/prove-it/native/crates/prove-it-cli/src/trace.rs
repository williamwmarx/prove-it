//! TLC's states as it prints them in a violation: `TLCState.toString`, as `formatState` in
//! `values.ts` writes it, a line per variable in TLC's order, as a conjunction when there are
//! several.

use tla_ir::Ir;
use tla_values::print::{is_printable, write_value};
use tla_values::{Id, Store};

use crate::pretty::pretty_print;

/// The state whose variables, in the engine's order, have these values, or nothing when the
/// store has forgotten how TLC built one of them.
pub fn format_state(ir: &Ir, store: &Store, state: &[Id]) -> Option<String> {
    let is_conjunction = ir.tlc_order.len() > 1;
    let mut text = String::new();
    for &position in &ir.tlc_order {
        let id = state[position as usize];
        if !is_printable(store, id) {
            return None;
        }
        let mut value = Vec::new();
        write_value(store, id, &mut value);
        let name = &ir.texts[ir.variables[position as usize] as usize];
        let conjunct = if is_conjunction { "/\\ " } else { "" };
        text.push_str(&format!("{conjunct}{name} = {}\n", pretty_print(&value)));
    }
    Some(text)
}
