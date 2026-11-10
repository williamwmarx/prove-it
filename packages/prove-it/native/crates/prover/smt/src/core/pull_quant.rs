//! Ported from Z3 (src/ast/normal_forms/pull_quant.cpp), MIT license, through `pull-quant.ts`.
//! Pulls the universal quantifiers nested in a formula in Skolem normal form to the top, so the
//! model finder sees one flat quantifier.

use crate::core::ast::{
    AstManager, Decl, Expr, KIND_QUANTIFIER, OP_AND, OP_NOT, OP_OR, QuantifierData, SmtSymbol, Sort,
};
use crate::core::ast_util::mk_not;
use crate::core::rewriter_tpl::{
    LastResult, Reduced, Rewrite, RewriterConfig, RewriterTpl, VarShifter,
};
use crate::util::error::SmtError;

/// pull_quant's rw_cfg.
#[derive(Clone, Debug)]
pub struct PullQuantConfig {
    // rw_cfg::m_shift.
    var_shifter: VarShifter,
}

/// rewriter_tpl with pull_quant's rw_cfg.
pub type PullQuant = RewriterTpl<PullQuantConfig>;

impl PullQuantConfig {
    pub fn new(m: &AstManager) -> PullQuantConfig {
        PullQuantConfig {
            var_shifter: VarShifter::new(m),
        }
    }

    /// pull_quant1_core for an application of not, and or or. The result comes with a reference,
    /// and is -1 when nothing is pulled.
    fn pull_from_app(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Expr, SmtError> {
        if m.func_decls[decl as usize].op == OP_NOT {
            let child = args[0];
            if m.kinds[child as usize] != KIND_QUANTIFIER {
                return Ok(-1);
            }
            let data = m.get_quantifier(child)?.clone();
            let body = mk_not(m, data.body)?;
            let result = m.mk_quantifier(QuantifierData {
                is_forall: !data.is_forall,
                body,
                ..data
            })?;
            m.inc_ref(result);
            return Ok(result);
        }
        let mut is_forall: Option<bool> = None;
        // The variables in reverse, the last variable of the first quantifier first. A name that
        // repeats becomes a fresh one.
        let mut sorts: Vec<Sort> = Vec::new();
        let mut names: Vec<SmtSymbol> = Vec::new();
        let mut weight = i32::MAX;
        let mut qid = String::new();
        for child in args {
            if m.kinds[*child as usize] != KIND_QUANTIFIER {
                continue;
            }
            let data = m.get_quantifier(*child)?.clone();
            match is_forall {
                None => is_forall = Some(data.is_forall),
                Some(is_forall) if is_forall != data.is_forall => return Ok(-1),
                Some(_) => {}
            }
            if sorts.is_empty() {
                qid = data.qid.clone();
            }
            weight = weight.min(data.weight);
            for index in (0..data.sorts.len()).rev() {
                let name = &data.names[index];
                sorts.push(data.sorts[index]);
                let name = if names.contains(name) {
                    SmtSymbol::Name(m.mk_fresh_var_name(match name {
                        SmtSymbol::Number(_) => None,
                        SmtSymbol::Name(name) => Some(name),
                    }))
                } else {
                    name.clone()
                };
                names.push(name);
            }
        }
        let Some(is_forall) = is_forall else {
            return Ok(-1);
        };
        let num_decls = sorts.len() as i32;
        let mut shift_amount = 0;
        // new_adjusted_children, which holds each shifted child.
        let mut adjusted = Vec::with_capacity(args.len());
        for child in args {
            if m.kinds[*child as usize] != KIND_QUANTIFIER {
                adjusted.push(self.var_shifter.shift(m, *child, 0, num_decls, 0)?);
                continue;
            }
            let data = m.get_quantifier(*child)?;
            let body = data.body;
            let count = data.sorts.len() as i32;
            let shifted =
                self.var_shifter
                    .shift(m, body, count, num_decls - count, shift_amount)?;
            shift_amount += count;
            adjusted.push(shifted);
        }
        sorts.reverse();
        names.reverse();
        let body = m.mk_app(decl, &adjusted, sort)?;
        let result = m.mk_quantifier(QuantifierData {
            is_forall,
            sorts,
            names,
            body,
            patterns: Vec::new(),
            weight,
            qid,
        })?;
        m.inc_ref(result);
        for child in adjusted {
            m.dec_ref(child)?;
        }
        Ok(result)
    }
}

impl RewriterConfig for PullQuantConfig {
    fn reduce_app(
        &mut self,
        m: &mut AstManager,
        _last_result: &mut LastResult,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Reduced, SmtError> {
        let op = m.func_decls[decl as usize].op;
        if op == OP_NOT && m.is_not(args[0]) {
            let expr = m.get_arg(args[0], 0);
            m.inc_ref(expr);
            return Ok(Reduced::Rewrite(Rewrite { expr, depth: 1 }));
        }
        if op != OP_OR && op != OP_AND && op != OP_NOT {
            return Ok(Reduced::Failed);
        }
        let result = self.pull_from_app(m, decl, args, sort)?;
        Ok(if result == -1 {
            Reduced::Failed
        } else {
            Reduced::Done(result)
        })
    }

    fn reduce_quantifier(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        body: Expr,
        _patterns: &[Expr],
    ) -> Result<Expr, SmtError> {
        let data = m.get_quantifier(expr)?.clone();
        if !data.is_forall {
            let negated = mk_not(m, body)?;
            let quantifier = m.mk_quantifier(QuantifierData {
                is_forall: true,
                body: negated,
                ..data
            })?;
            let result = m.mk_not(quantifier)?;
            m.inc_ref(result);
            return Ok(result);
        }
        if m.kinds[body as usize] != KIND_QUANTIFIER || !m.get_quantifier(body)?.is_forall {
            return Ok(-1);
        }
        let nested = m.get_quantifier(body)?.clone();
        let result = m.mk_quantifier(QuantifierData {
            is_forall: true,
            sorts: [data.sorts, nested.sorts].concat(),
            names: [data.names, nested.names].concat(),
            body: nested.body,
            patterns: Vec::new(),
            weight: data.weight.min(nested.weight),
            qid: data.qid,
        })?;
        m.inc_ref(result);
        Ok(result)
    }

    /// ~rw: the configuration's shifter goes first, then the rewriter.
    fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.var_shifter.release(m)
    }
}

/// pull_quant's operator(), with a pull_quant of its own. The result comes with a reference, which
/// the caller releases.
pub fn pull_quant(m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
    let mut pull = PullQuant::new(m, PullQuantConfig::new(m));
    let result = pull.rewrite(m, expr)?;
    pull.release(m)?;
    Ok(result)
}
