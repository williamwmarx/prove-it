//! Ported from Isabelle2025's Pure/conv.ML, conversions: functions from a term to a theorem that
//! it equals another. Copyright (c) 1986-2025 University of Cambridge, Technische Universitaet
//! Muenchen, and contributors, see LICENSE.

use std::rc::Rc;

use crate::error::{Res, thm_exn};

use super::logic::{dest_equals, dest_implies, implies, is_implies};
use super::name::{NameContext, declare_name, make_name_context, variant_name};
use super::term::{Term, TermNode, aconv, add_free_names, mk_free, subst_bound};
use super::thm::{
    Thm, abstract_rule, combination, equal_elim, nprems, permute_prems, prem_of, reflexive,
};

pub type Conversion = Rc<dyn Fn(&Term) -> Res<Thm>>;

fn is_reflexive(eq: &Thm) -> Res<bool> {
    let (lhs, rhs) = dest_equals(&eq.prop)?;
    Ok(aconv(&lhs, &rhs))
}

/// Drule.imp_cong_rule
pub fn imp_cong_rule(first: &Thm, second: &Thm) -> Res<Thm> {
    combination(&combination(&reflexive(&implies())?, first)?, second)
}

/// Conv.prems_conv ~1: converts every premise.
pub fn prems_conv(convert: Conversion) -> Conversion {
    Rc::new(move |term| {
        if is_implies(term) {
            imp_cong_rule(
                &convert(&dest_implies(term)?.0)?,
                &prems_conv(convert.clone())(&dest_implies(term)?.1)?,
            )
        } else {
            reflexive(term)
        }
    })
}

/// Conv.params_conv ~1: converts the body under every outer parameter, fixed as a fresh free
/// variable.
pub fn params_conv(convert: Conversion) -> Conversion {
    fn under(convert: &Conversion, names: NameContext, term: &Term) -> Res<Thm> {
        let Some((fun, arg)) = term.dest_app() else {
            return convert(term);
        };
        let TermNode::Abs { name, ty, body, .. } = &**arg else {
            return convert(term);
        };
        if !fun.is_const_named("Pure.all") {
            return convert(term);
        }
        let (fresh, next_names) = variant_name(name, &names);
        let free = mk_free(fresh.clone(), ty.clone());
        let eq = under(
            convert,
            declare_name(&fresh, &next_names),
            &subst_bound(&free, body),
        )?;
        if is_reflexive(&eq)? {
            reflexive(term)
        } else {
            combination(&reflexive(fun)?, &abstract_rule(name, &free, &eq)?)
        }
    }
    Rc::new(move |term| {
        under(
            &convert,
            make_name_context(&add_free_names(term, Vec::new())),
            term,
        )
    })
}

/// Conv.gconv_rule: converts goal index of a state.
pub fn gconv_rule(convert: &Conversion, index: i32, state: &Thm) -> Res<Thm> {
    if index < 1 || index > nprems(state) as i32 {
        return Err(thm_exn(format!("gconv_rule {index}")));
    }
    let eq = convert(&prem_of(state, index)?)?;
    if is_reflexive(&eq)? {
        return Ok(state.clone());
    }
    let rotated = permute_prems(0, index - 1, state)?;
    let rest = &rotated.prop;
    if !is_implies(rest) {
        return Err(thm_exn("gconv_rule"));
    }
    let converted = equal_elim(
        &imp_cong_rule(&eq, &reflexive(&dest_implies(rest)?.1)?)?,
        &rotated,
    )?;
    permute_prems(0, 1 - index, &converted)
}

/// Conv.fconv_rule: converts a theorem's proposition.
pub fn fconv_rule(convert: &Conversion, thm: &Thm) -> Res<Thm> {
    let eq = convert(&thm.prop)?;
    if is_reflexive(&eq)? {
        Ok(thm.clone())
    } else {
        equal_elim(&eq, thm)
    }
}
