//! Ported from Isabelle2025's Pure/Isar/object_logic.ML, atomize_prems_tac, and the CONVERSION of
//! Pure/tactic.ML. Copyright (c) 1986-2025 University of Cambridge, Technische Universitaet
//! Muenchen, and contributors, see LICENSE.

use std::rc::Rc;

use crate::error::{Exception, Res};

use super::conv::{Conversion, gconv_rule, params_conv, prems_conv};
use super::logic::has_meta_prems;
use super::raw_simplifier::{SimpContext, add_simps, empty_simpset};
use super::rewriter::{RewriteMode, rewrite_conv, simple_prover};
use super::seq::{empty_seq, single_seq};
use super::tactical::GoalTactic;
use super::thm::{Thm, reflexive};

/// Object_Logic.atomize_prems_tac: rewrites the premises of a goal with the atomize rules, newest
/// first as Object_Logic keeps them, which turns meta-level premises into object-level formulas.
/// Raises where add_simps does, when the tactic is built (never with meta-equalities as rules).
pub fn atomize_prems_tac(rules: &[Thm]) -> Res<GoalTactic> {
    let empty = SimpContext {
        simpset: empty_simpset(),
        bounds: 0,
    };
    let context = SimpContext {
        simpset: add_simps(&empty, rules)?,
        ..empty
    };
    // Raw_Simplifier.rewrite ctxt true: full rewriting, with a prover that proves no premises.
    let atomize = params_conv(prems_conv(rewrite_conv(
        RewriteMode {
            simprem: true,
            useprem: false,
            mutsimp: false,
        },
        Rc::new(simple_prover),
        context,
    )));
    let convert: Conversion = Rc::new(move |term| {
        if has_meta_prems(term) {
            atomize(term)
        } else {
            reflexive(term)
        }
    });
    Ok(Rc::new(move |index| {
        let convert = convert.clone();
        Rc::new(
            move |state: Thm| match gconv_rule(&convert, index, &state) {
                Ok(thm) => Ok(single_seq(thm)),
                // CONVERSION fails on THM, CTERM, TERM and TYPE.
                Err(error)
                    if error.is(Exception::Thm)
                        || error.is(Exception::Term)
                        || error.is(Exception::Type) =>
                {
                    Ok(empty_seq())
                }
                Err(error) => Err(error),
            },
        )
    }))
}
