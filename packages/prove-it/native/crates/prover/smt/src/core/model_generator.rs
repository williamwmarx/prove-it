//! Ported from Z3 (src/smt/smt_model_generator.cpp), MIT license, through `model-generator.ts`.
//! Builds a model from the current assignment: every relevant equivalence class gets a value,
//! Booleans from the assignment, integers from the arithmetic theory and other sorts from fresh
//! model values, and each congruence root of an uninterpreted function becomes an entry of its
//! interpretation.

use std::cell::RefCell;
use std::rc::Rc;

use crate::core::ast::{
    AstManager, Expr, FAMILY_MODEL_VALUE, FAMILY_USER, FuncDecl, OP_DIV0, OP_IDIV0, OP_MOD0,
    SORT_BOOL, is_arith_sort,
};
use crate::core::context::Context;
use crate::core::enode::EnodeId;
use crate::core::proto_model::{FuncInterp, ProtoModel, ProtoModelRef};
use crate::util::error::SmtError;
use crate::util::lbool::LBool;
use crate::util::ordered_map::OrderedMap;

pub struct GeneratedModel {
    pub model: ProtoModelRef,
    /// The value of each relevant root, in the order the generator set them.
    pub root2value: OrderedMap<EnodeId, Expr>,
}

// include_func_interp: the model interprets uninterpreted functions, theory_lra's divisions by
// zero, and the decls of a family without a theory, such as model values, which stand for
// themselves.
fn is_included_func_interp(decl: &FuncDecl) -> bool {
    decl.family == FAMILY_USER
        || decl.family == FAMILY_MODEL_VALUE
        || decl.op == OP_DIV0
        || decl.op == OP_IDIV0
        || decl.op == OP_MOD0
}

fn get_bool_value(m: &AstManager, value: LBool) -> Expr {
    if value == LBool::True {
        m.true_expr
    } else {
        m.false_expr
    }
}

// The value of a node's class, or some value of its sort.
fn get_value(
    context: &mut Context,
    model: &mut ProtoModel,
    root2value: &OrderedMap<EnodeId, Expr>,
    node: EnodeId,
) -> Expr {
    match root2value.get(&context.root(node)) {
        Some(value) => *value,
        None => {
            let sort = context.m.sorts[context.node(node).owner as usize];
            model.get_some_value(&mut context.m, sort)
        }
    }
}

/// mkModel: the model of the context's current assignment.
pub fn mk_model(context: &mut Context) -> Result<GeneratedModel, SmtError> {
    let mut model = ProtoModel::new(&context.m);
    if context.theory.is_some() {
        context.theory_init_model(&mut model)?;
    }
    // register_existing_model_values.
    for index in 0..context.enodes.len() {
        let node = context.enodes[index];
        let owner = context.node(node).owner;
        if context.root(node) == node
            && context.is_relevant(owner)
            && context.m.is_model_value(owner)
        {
            model.register_value(&mut context.m, owner);
        }
    }
    // mk_bool_model.
    for bool_var in 0..context.num_bool_vars {
        let expr = context.bool_var2expr[bool_var as usize];
        if context.m.is_uninterpreted_const(expr) && context.is_relevant(expr) {
            let value = get_bool_value(&context.m, context.find_assignment(expr));
            let decl = context.m.decls[expr as usize];
            model.register_const(&mut context.m, decl, value)?;
        }
    }
    // mk_values: the values of the arithmetic classes that the theory does not know are fresh, so
    // they come after all the other values. Like Z3, that includes the class of a numeral without
    // a theory variable, such as a coefficient.
    let mut root2value: OrderedMap<EnodeId, Expr> = OrderedMap::new();
    let mut fresh_roots: Vec<EnodeId> = Vec::new();
    for index in 0..context.enodes.len() {
        let node = context.enodes[index];
        if context.root(node) != node {
            continue;
        }
        let expr = context.node(node).owner;
        if !context.is_relevant(expr) && !context.m.is_unique_value(expr) {
            continue;
        }
        let sort = context.m.sorts[expr as usize];
        if sort == SORT_BOOL {
            let value = get_bool_value(&context.m, context.find_assignment(expr));
            root2value.insert(node, value);
        } else if context.m.is_unique_value(expr) && !is_arith_sort(sort) {
            root2value.insert(node, expr);
        } else if is_arith_sort(sort) {
            let value = if context.theory.is_some() {
                context.theory_mk_value(node)?
            } else {
                None
            };
            match value {
                None => fresh_roots.push(node),
                Some(value) => root2value.insert(node, value),
            }
        } else {
            let value = match model.get_fresh_value(&mut context.m, sort) {
                Some(value) => value,
                None => model.get_some_value(&mut context.m, sort),
            };
            root2value.insert(node, value);
        }
    }
    for value in root2value.values() {
        model.register_value(&mut context.m, *value);
    }
    for node in fresh_roots {
        let sort = context.m.sorts[context.node(node).owner as usize];
        let value = match model.get_fresh_value(&mut context.m, sort) {
            Some(value) => value,
            None => model.get_some_value(&mut context.m, sort),
        };
        root2value.insert(node, value);
    }
    for index in 0..context.enodes.len() {
        let node = context.enodes[index];
        let owner = context.node(node).owner;
        if context.m.is_uninterpreted_const(owner) && context.is_relevant(owner) {
            let value = get_value(context, &mut model, &root2value, node);
            let decl = context.m.decls[owner as usize];
            model.register_const(&mut context.m, decl, value)?;
        }
    }
    // mk_func_interps.
    for index in 0..context.enodes.len() {
        let node = context.enodes[index];
        let (owner, decl, num_args, cg) = {
            let enode = context.node(node);
            (enode.owner, enode.decl, enode.num_args(), enode.cg)
        };
        if !context.is_relevant(owner)
            || !is_included_func_interp(&context.m.func_decls[decl as usize])
        {
            continue;
        }
        if num_args == 0 {
            let value = get_value(context, &mut model, &root2value, node);
            model.register_const(&mut context.m, decl, value)?;
            continue;
        }
        if cg != node {
            continue;
        }
        if model.get_func_interp(&context.m, decl).is_none() {
            model.register_func(&mut context.m, decl, FuncInterp::new(num_args as usize))?;
        }
        let mut args = Vec::with_capacity(num_args as usize);
        for arg_index in 0..num_args {
            let arg = context.node(node).get_arg(arg_index);
            args.push(get_value(context, &mut model, &root2value, arg));
        }
        let has_entry = model
            .get_func_interp(&context.m, decl)
            .is_some_and(|interp| interp.get_entry(&args).is_some());
        if !has_entry {
            let value = get_value(context, &mut model, &root2value, node);
            if let Some(interp) = model.get_func_interp_mut(&context.m, decl) {
                interp.insert_new_entry(&mut context.m, &args, value)?;
            }
        }
    }
    Ok(GeneratedModel {
        model: Rc::new(RefCell::new(model)),
        root2value,
    })
}

#[cfg(test)]
mod tests {
    //! The satisfiable ground problems of `scripts/smt-model-reference.ts`, built in the same
    //! order, against the table it printed (`tests/tables/models.txt`): the model `get_model` makes,
    //! the value of each root, the proto model, its validation and the value of terms under it,
    //! with the TypeScript's ids and steps.

    use prove_decide::Limits;

    use crate::core::ast::{AstManager, Decl, Expr, OP_ITE, SORT_BOOL, SmtSymbol, Sort};
    use crate::core::context::{Context, SmtParams};
    use crate::core::proto_model::tests::{
        assert_section, print_counts, print_evals, print_model, show,
    };
    use crate::util::rlimit::ResourceLimit;

    fn mk_context(relevancy_level: u32) -> Context {
        let m = AstManager::new(ResourceLimit::new(&Limits::new(f64::INFINITY, None, None)));
        let mut context = Context::new(
            m,
            SmtParams {
                is_mbqi: false,
                relevancy_level,
            },
        )
        .unwrap();
        context.setup_context().unwrap();
        context
    }

    fn mk_decl(context: &mut Context, name: &str, domain: &[Sort], range: Sort) -> Decl {
        context
            .m
            .mk_func_decl(SmtSymbol::Name(name.into()), domain, range, false)
    }

    fn mk_const(context: &mut Context, name: &str, sort: Sort) -> Expr {
        let decl = mk_decl(context, name, &[], sort);
        context.m.mk_app(decl, &[], sort).unwrap()
    }

    fn app(context: &mut Context, decl: Decl, args: &[Expr], sort: Sort) -> Expr {
        context.m.mk_app(decl, args, sort).unwrap()
    }

    fn eq(context: &mut Context, lhs: Expr, rhs: Expr) -> Expr {
        context.m.mk_eq(lhs, rhs).unwrap()
    }

    fn not(context: &mut Context, expr: Expr) -> Expr {
        context.m.mk_not(expr).unwrap()
    }

    fn or(context: &mut Context, args: &[Expr]) -> Expr {
        context.m.mk_or(args).unwrap()
    }

    fn and(context: &mut Context, args: &[Expr]) -> Expr {
        context.m.mk_and(args).unwrap()
    }

    fn assert(context: &mut Context, expr: Expr) {
        context.internalize_assertion(expr, 0).unwrap();
    }

    // runProblem.
    fn run_problem(name: &str, context: &mut Context, sorts: &[Sort], terms: &[Expr]) {
        let mut out = Vec::new();
        let result = context.search().unwrap();
        out.push(format!("result={}", result as i32));
        print_counts(&mut out, &context.m, "searched");
        let model = context.get_model().unwrap();
        print_counts(&mut out, &context.m, "modeled");
        print_model(&mut out, &context.m, &model.borrow(), sorts);
        let generated = context.get_generated_model().unwrap();
        for (node, value) in generated.root2value.iter() {
            out.push(format!(
                "root {} = {}",
                show(&context.m, Some(context.node(*node).owner)),
                show(&context.m, Some(*value))
            ));
        }
        out.push("proto:".into());
        print_model(&mut out, &context.m, &generated.model.borrow(), sorts);
        let is_valid = context.validate_model(&model).unwrap();
        out.push(format!("valid={is_valid}"));
        print_counts(&mut out, &context.m, "validated");
        print_evals(&mut out, &mut context.m, &mut model.borrow_mut(), terms);
        print_model(&mut out, &context.m, &model.borrow(), sorts);
        assert_section(name, &out);
    }

    #[test]
    fn models_the_branch_that_congruence_allows() {
        let context = &mut mk_context(2);
        let u = context.m.mk_sort("U");
        let f = mk_decl(context, "f", &[u], u);
        let h = mk_decl(context, "h", &[u], u);
        let a = mk_const(context, "a", u);
        let b = mk_const(context, "b", u);
        let c = mk_const(context, "c", u);
        let ab = eq(context, a, b);
        let ac = eq(context, a, c);
        let either = or(context, &[ab, ac]);
        assert(context, either);
        let fa = app(context, f, &[a], u);
        let fb = app(context, f, &[b], u);
        let fa_fb = eq(context, fa, fb);
        let diseq = not(context, fa_fb);
        assert(context, diseq);
        let d = mk_const(context, "d", u);
        let fa = app(context, f, &[a], u);
        let fb = app(context, f, &[b], u);
        let fc = app(context, f, &[c], u);
        let fa_inner = app(context, f, &[a], u);
        let ffa = app(context, f, &[fa_inner], u);
        let ab = eq(context, a, b);
        let fa_inner = app(context, f, &[a], u);
        let fc_inner = app(context, f, &[c], u);
        let fa_fc = eq(context, fa_inner, fc_inner);
        let fd = app(context, f, &[d], u);
        let ha = app(context, h, &[a], u);
        let ac = eq(context, a, c);
        let ite = app(context, OP_ITE, &[ac, b, a], u);
        run_problem(
            "euf-branch",
            context,
            &[u],
            &[fa, fb, fc, ffa, ab, fa_fc, d, fd, ha, ite],
        );
    }

    #[test]
    fn models_a_propositional_problem() {
        let context = &mut mk_context(2);
        let p = mk_const(context, "p", SORT_BOOL);
        let q = mk_const(context, "q", SORT_BOOL);
        let r = mk_const(context, "r", SORT_BOOL);
        let s = mk_const(context, "s", SORT_BOOL);
        let clause = or(context, &[p, q]);
        assert(context, clause);
        let not_p = not(context, p);
        let clause = or(context, &[not_p, r]);
        assert(context, clause);
        let not_q = not(context, q);
        let not_r = not(context, r);
        let clause = or(context, &[not_q, not_r]);
        assert(context, clause);
        let pr = and(context, &[p, r]);
        let qs = or(context, &[q, s]);
        let not_s = not(context, s);
        let ps = eq(context, p, s);
        run_problem(
            "propositional",
            context,
            &[],
            &[p, q, r, s, pr, qs, not_s, ps],
        );
    }

    #[test]
    fn models_functions_and_predicates() {
        for level in [2, 0] {
            let context = &mut mk_context(level);
            let u = context.m.mk_sort("U");
            let f = mk_decl(context, "f", &[u], u);
            let g = mk_decl(context, "g", &[u, u], u);
            let pred = mk_decl(context, "P", &[u], SORT_BOOL);
            let a = mk_const(context, "a", u);
            let b = mk_const(context, "b", u);
            let c = mk_const(context, "c", u);
            let q = mk_const(context, "q", SORT_BOOL);
            let ab = eq(context, a, b);
            let not_ab = not(context, ab);
            assert(context, not_ab);
            let fa = app(context, f, &[a], u);
            let fa_b = eq(context, fa, b);
            assert(context, fa_b);
            let fb = app(context, f, &[b], u);
            let fb_a = eq(context, fb, a);
            assert(context, fb_a);
            let gab = app(context, g, &[a, b], u);
            let gab_c = eq(context, gab, c);
            assert(context, gab_c);
            let pc = app(context, pred, &[c], SORT_BOOL);
            assert(context, pc);
            let pa = app(context, pred, &[a], SORT_BOOL);
            let not_pa = not(context, pa);
            assert(context, not_pa);
            let pb = app(context, pred, &[b], SORT_BOOL);
            let clause = or(context, &[q, pb]);
            assert(context, clause);
            let fc = app(context, f, &[c], u);
            let fa = app(context, f, &[a], u);
            let ffa = app(context, f, &[fa], u);
            let gba = app(context, g, &[b, a], u);
            let fb = app(context, f, &[b], u);
            let fa = app(context, f, &[a], u);
            let gfbfa = app(context, g, &[fb, fa], u);
            let fb = app(context, f, &[b], u);
            let pfb = app(context, pred, &[fb], SORT_BOOL);
            let pb = app(context, pred, &[b], SORT_BOOL);
            let gab = app(context, g, &[a, b], u);
            let gab_a = eq(context, gab, a);
            let pc = app(context, pred, &[c], SORT_BOOL);
            let q_pc = and(context, &[q, pc]);
            run_problem(
                &format!("euf-functions-{level}"),
                context,
                &[u],
                &[fc, ffa, gba, gfbfa, pfb, pb, gab_a, q_pc],
            );
        }
    }
}
