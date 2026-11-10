//! Ported from Isabelle2025's Pure/variable.ML, the import and export of schematic variables.
//! Copyright (c) 1986-2025 University of Cambridge, Technische Universitaet Muenchen, and
//! contributors, see LICENSE.

use crate::error::Res;

use super::name::variant_list;
use super::term::{Name, add_free_names, add_vars, mk_free};
use super::thm::{Instantiation, Thm, generalize, instantiate};

/// Variable.trade with import true: fixes the schematic variables of a theorem as fresh free ones,
/// derives theorems from it, and makes those variables schematic again.
pub fn trade(derive: impl FnOnce(Thm) -> Res<Vec<Thm>>, thm: &Thm) -> Res<Vec<Thm>> {
    let vars = add_vars(&thm.prop, Vec::new());
    let names = variant_list(
        &thm.hyps
            .iter()
            .fold(add_free_names(&thm.prop, Vec::new()), |used, hyp| {
                add_free_names(hyp, used)
            }),
        &vars
            .iter()
            .map(|variable| variable.name().expect("a Var").clone())
            .collect::<Vec<Name>>(),
    );
    let derived = derive(instantiate(
        &vars
            .iter()
            .zip(&names)
            .map(|(variable, name)| Instantiation {
                variable: variable.clone(),
                term: mk_free(name.clone(), variable.ty().expect("a Var").clone()),
            })
            .collect::<Vec<_>>(),
        thm,
    )?)?;
    let index = derived
        .iter()
        .fold(thm.maxidx, |maxidx, result| maxidx.max(result.maxidx))
        + 1;
    derived
        .iter()
        .map(|result| generalize(&names, index, result))
        .collect()
}
