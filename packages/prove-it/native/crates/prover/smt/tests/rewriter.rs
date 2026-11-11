//! The rewriters against the TypeScript they port: `scripts/smt-rewriter-tables.ts` records a
//! seeded sequence of operations on random terms with quantifiers and de Bruijn variables, with what
//! each returned, the resource limit's step count and the number of ASTs, and this replays them:
//! var_subst, the var shifters, the beta reducer, expr_safe_replace, ast_lt, ast_util and
//! rewriter_tpl's main loop with the default configuration and the script's test configuration.

use prove_decide::Limits;
use prove_num::{Int, Rational};
use prove_smt::core::ast::{
    AstManager, Decl, Expr, OP_AND, OP_NOT, OP_OR, QuantifierData, SORT_BOOL, SmtSymbol, Sort,
};
use prove_smt::core::ast_lt::is_ast_less;
use prove_smt::core::ast_util::{flatten_and_vector, flatten_or_vector, mk_not, push_not_owned};
use prove_smt::core::expr_safe_replace::ExprSafeReplace;
use prove_smt::core::ref_vector::RefVector;
use prove_smt::core::rewriter_tpl::{
    BetaReducer, DefaultRewriterConfig, InvVarShifter, LastResult, Reduced, Rewrite,
    RewriterConfig, RewriterTpl, VarShifter,
};
use prove_smt::core::var_subst::{
    UnusedVarsEliminator, VarSubst, collect_used_vars, elim_unused_vars, get_free_var_sorts,
    replace_free_vars,
};
use prove_smt::util::error::SmtError;
use prove_smt::util::rlimit::ResourceLimit;

fn number<T: std::str::FromStr>(text: &str) -> T
where
    T::Err: std::fmt::Debug,
{
    text.parse().unwrap()
}

fn list<T: std::str::FromStr>(text: &str) -> Vec<T>
where
    T::Err: std::fmt::Debug,
{
    if text == "-" {
        return Vec::new();
    }
    text.split(',').map(number).collect()
}

fn symbol(text: &str) -> SmtSymbol {
    match text.split_at(2) {
        ("n:", rest) => SmtSymbol::Number(number(rest)),
        ("s:", rest) => SmtSymbol::Name(rest.into()),
        _ => panic!("not a symbol: {text}"),
    }
}

fn join<T: ToString>(items: impl Iterator<Item = T>) -> String {
    let items: Vec<String> = items.map(|item| item.to_string()).collect();
    if items.is_empty() {
        "-".into()
    } else {
        items.join(",")
    }
}

// An expression as the table records it, with its text when it is shallow. Like the script, it
// counts the handles it describes, which the reference counts at checkpoints cover.
fn describe(m: &AstManager, num_nodes: &mut usize, expr: Expr) -> String {
    let index = expr as usize;
    *num_nodes = (*num_nodes).max(index + 1);
    let fields = format!("{expr}:{}:{}", m.ids[index], m.hashes[index]);
    if m.depths[index] <= 5 {
        format!("{fields} | {}", m.to_string(expr))
    } else {
        fields
    }
}

// The handles of the script's test configuration.
#[derive(Clone, Copy, Debug)]
struct Handles {
    decl_g: Decl,
    decl_h: Decl,
    decl_m1: Decl,
    decl_m2: Decl,
    decl_p: Decl,
    decl_q: Decl,
    decl_x: Decl,
    const_c: Expr,
    const_d: Expr,
    const_p: Expr,
    const_y: Expr,
    def_m1: Expr,
    def_m2: Expr,
    decl_m3: Decl,
    def_m3: Expr,
}

// The script's test configurations: they flatten and and or, reduce some applications and
// constants, expand m1, m2 and m3, and reduce a quantifier with a constant body. TestRewriter
// (IS_SUBST) also substitutes c for d, and TestRewriterBase substitutes nothing.
#[derive(Clone, Copy, Debug)]
struct TestConfig<const IS_SUBST: bool> {
    handles: Handles,
    is_patterns: bool,
}

impl<const IS_SUBST: bool> RewriterConfig for TestConfig<IS_SUBST> {
    const IS_SUBSTITUTING: bool = IS_SUBST;
    const IS_EXPANDING_MACROS: bool = true;

    fn get_subst(&mut self, _m: &mut AstManager, expr: Expr) -> Result<Option<Expr>, SmtError> {
        Ok((IS_SUBST && expr == self.handles.const_d).then_some(self.handles.const_c))
    }

    fn is_flat_assoc(&self, m: &AstManager, decl: Decl) -> bool {
        let op = m.func_decls[decl as usize].op;
        op == OP_AND || op == OP_OR
    }

    fn is_rewriting_patterns(&self) -> bool {
        self.is_patterns
    }

    fn reduce_app(
        &mut self,
        m: &mut AstManager,
        _last_result: &mut LastResult,
        decl: Decl,
        args: &[Expr],
        _sort: Sort,
    ) -> Result<Reduced, SmtError> {
        let handles = self.handles;
        let op = m.func_decls[decl as usize].op;
        if op == OP_NOT && m.is_not(args[0]) {
            let result = m.get_arg(args[0], 0);
            m.inc_ref(result);
            return Ok(Reduced::Done(result));
        }
        if op == OP_AND && args.iter().any(|arg| m.is_false(*arg)) {
            m.inc_ref(m.false_expr);
            return Ok(Reduced::Done(m.false_expr));
        }
        if op == OP_AND && args.iter().any(|arg| m.is_true(*arg)) {
            let rest: Vec<Expr> = args
                .iter()
                .copied()
                .filter(|arg| !m.is_true(*arg))
                .collect();
            let expr = m.with_temporaries(|m| m.mk_and(&rest))?;
            return Ok(Reduced::Rewrite(Rewrite { expr, depth: 1 }));
        }
        if op == OP_OR && args.iter().any(|arg| m.is_false(*arg)) {
            let rest: Vec<Expr> = args
                .iter()
                .copied()
                .filter(|arg| !m.is_false(*arg))
                .collect();
            let expr = m.with_temporaries(|m| m.mk_or(&rest))?;
            return Ok(Reduced::Rewrite(Rewrite { expr, depth: 1 }));
        }
        if decl == handles.decl_p {
            let expr = m.with_temporaries(|m| {
                let applied = m.mk_app(
                    handles.decl_g,
                    &[handles.const_c, handles.const_d],
                    SORT_BOOL,
                )?;
                m.mk_app(OP_OR, &[handles.const_p, applied], SORT_BOOL)
            })?;
            return Ok(Reduced::Rewrite(Rewrite { expr, depth: 3 }));
        }
        if decl == handles.decl_q {
            m.inc_ref(handles.const_p);
            return Ok(Reduced::Rewrite(Rewrite {
                expr: handles.const_p,
                depth: 2,
            }));
        }
        if decl == handles.decl_x {
            m.inc_ref(handles.const_y);
            return Ok(Reduced::Done(handles.const_y));
        }
        if decl == handles.decl_h && m.is_numeral(args[0]) {
            let value = m.get_numeral_value(args[0]) + Int::from(1);
            let result = m.mk_numeral(&value);
            m.inc_ref(result);
            return Ok(Reduced::Done(result));
        }
        Ok(Reduced::Failed)
    }

    fn get_macro(&mut self, _m: &mut AstManager, decl: Decl) -> Result<Expr, SmtError> {
        Ok(if decl == self.handles.decl_m1 {
            self.handles.def_m1
        } else if decl == self.handles.decl_m2 {
            self.handles.def_m2
        } else if decl == self.handles.decl_m3 {
            self.handles.def_m3
        } else {
            -1
        })
    }

    fn is_reducing_macro(&self) -> bool {
        self.is_patterns
    }

    fn reduce_quantifier(
        &mut self,
        m: &mut AstManager,
        _expr: Expr,
        body: Expr,
        _patterns: &[Expr],
    ) -> Result<Expr, SmtError> {
        if !m.is_true(body) && !m.is_false(body) {
            return Ok(-1);
        }
        m.inc_ref(body);
        Ok(body)
    }

    fn mk_nested(&mut self, _m: &mut AstManager) -> Result<Option<Self>, SmtError> {
        Ok(Some(*self))
    }
}

struct Rewriters {
    default: RewriterTpl<DefaultRewriterConfig>,
    test: Option<RewriterTpl<TestConfig<true>>>,
    test_np: Option<RewriterTpl<TestConfig<false>>>,
}

impl Rewriters {
    fn rewrite(&mut self, m: &mut AstManager, name: &str, expr: Expr) -> Expr {
        match name {
            "default" => self.default.rewrite(m, expr),
            "test" => self.test.as_mut().unwrap().rewrite(m, expr),
            _ => self.test_np.as_mut().unwrap().rewrite(m, expr),
        }
        .unwrap()
    }

    fn reset(&mut self, m: &mut AstManager, name: &str, is_cleanup: bool) {
        match (name, is_cleanup) {
            ("default", false) => self.default.reset(m),
            ("default", true) => self.default.cleanup(m),
            ("test", false) => self.test.as_mut().unwrap().reset(m),
            ("test", true) => self.test.as_mut().unwrap().cleanup(m),
            (_, false) => self.test_np.as_mut().unwrap().reset(m),
            (_, true) => self.test_np.as_mut().unwrap().cleanup(m),
        }
        .unwrap();
    }

    fn release(&mut self, m: &mut AstManager, name: &str) {
        match name {
            "default" => self.default.release(m),
            "test" => self.test.as_mut().unwrap().release(m),
            _ => self.test_np.as_mut().unwrap().release(m),
        }
        .unwrap();
    }
}

#[test]
fn the_rewriters_rewrite_as_the_typescript_does() {
    let limits = Limits::new(f64::INFINITY, None, None);
    let mut m = AstManager::new(ResourceLimit::new(&limits));
    let mut rewriters = Rewriters {
        default: RewriterTpl::new(&m, DefaultRewriterConfig),
        test: None,
        test_np: None,
    };
    let mut subst_std = VarSubst::new(&m, true);
    let mut subst_ns = VarSubst::new(&m, false);
    let mut shifter = VarShifter::new(&m);
    let mut inv_shifter = InvVarShifter::new(&m);
    let mut reducer = BetaReducer::new(&m);
    let mut eliminator = UnusedVarsEliminator::new(&m);
    let mut held: Vec<Expr> = Vec::new();
    let mut shifted: Option<Expr> = None;
    let mut num_nodes = 2;
    let table = include_str!("tables/rewriter.txt");
    for (line_index, line) in table.lines().enumerate() {
        let (operation, expected) = line.split_once(" => ").unwrap();
        let fields: Vec<&str> = operation.split(' ').collect();
        if fields[0] != "inv-shift"
            && let Some(expr) = shifted.take()
        {
            m.dec_ref(expr).unwrap();
        }
        let mut owned = -1;
        // A flattened vector, which the script releases after it records the line.
        let mut flattened: Option<RefVector> = None;
        let result = match fields[0] {
            "sort" => m.mk_sort(fields[1]).to_string(),
            "decl" => m
                .mk_func_decl(
                    SmtSymbol::Name(fields[1].into()),
                    &list::<Sort>(fields[2]),
                    number(fields[3]),
                    fields[4] == "1",
                )
                .to_string(),
            "config" => {
                let handles: Vec<i32> = list(fields[1]);
                let handles = Handles {
                    decl_g: handles[0],
                    decl_h: handles[1],
                    decl_m1: handles[2],
                    decl_m2: handles[3],
                    decl_p: handles[4],
                    decl_q: handles[5],
                    decl_x: handles[6],
                    const_c: handles[7],
                    const_d: handles[8],
                    const_p: handles[9],
                    const_y: handles[10],
                    def_m1: handles[11],
                    def_m2: handles[12],
                    decl_m3: handles[13],
                    def_m3: handles[14],
                };
                rewriters.test = Some(RewriterTpl::new(
                    &m,
                    TestConfig {
                        handles,
                        is_patterns: true,
                    },
                ));
                rewriters.test_np = Some(RewriterTpl::new(
                    &m,
                    TestConfig {
                        handles,
                        is_patterns: false,
                    },
                ));
                "-".into()
            }
            "app" => {
                let expr = m
                    .mk_app(number(fields[1]), &list(fields[2]), number(fields[3]))
                    .unwrap();
                describe(&m, &mut num_nodes, expr)
            }
            "var" => {
                let expr = m.mk_var(number(fields[1]), number(fields[2]));
                describe(&m, &mut num_nodes, expr)
            }
            "int" => {
                let expr = m.mk_numeral(&number::<Int>(fields[1]));
                describe(&m, &mut num_nodes, expr)
            }
            "real" => {
                let value = Rational::of(number(fields[1]), number(fields[2]));
                let expr = m.mk_real_numeral(&value);
                describe(&m, &mut num_nodes, expr)
            }
            "model-value" => {
                let expr = m.mk_model_value(number(fields[1]), number(fields[2]));
                describe(&m, &mut num_nodes, expr)
            }
            "pattern" => {
                let expr = m.mk_pattern(&list(fields[1])).unwrap();
                describe(&m, &mut num_nodes, expr)
            }
            "quant" => {
                let names: Vec<SmtSymbol> = if fields[3] == "-" {
                    Vec::new()
                } else {
                    fields[3].split(',').map(symbol).collect()
                };
                let expr = m
                    .mk_quantifier(QuantifierData {
                        is_forall: fields[1] == "1",
                        sorts: list(fields[2]),
                        names,
                        body: number(fields[4]),
                        patterns: list(fields[5]),
                        weight: 0,
                        qid: "q".into(),
                    })
                    .unwrap();
                describe(&m, &mut num_nodes, expr)
            }
            "hold" => {
                let expr: Expr = number(fields[1]);
                m.inc_ref(expr);
                held.push(expr);
                m.get_ref_count(expr).to_string()
            }
            "begin" => m.begin_temporaries().to_string(),
            "end" => {
                m.end_temporaries(number(fields[1])).unwrap();
                "-".into()
            }
            "subst" => {
                let subst = if fields[1] == "std" {
                    &mut subst_std
                } else {
                    &mut subst_ns
                };
                owned = subst
                    .apply(&mut m, number(fields[2]), &list::<Expr>(fields[3]))
                    .unwrap();
                describe(&m, &mut num_nodes, owned)
            }
            "shift" => {
                let expr = shifter
                    .shift(
                        &mut m,
                        number(fields[1]),
                        number(fields[2]),
                        number(fields[3]),
                        number(fields[4]),
                    )
                    .unwrap();
                shifted = Some(expr);
                describe(&m, &mut num_nodes, expr)
            }
            "inv-shift" => {
                owned = inv_shifter
                    .shift(&mut m, number(fields[1]), number(fields[2]))
                    .unwrap();
                describe(&m, &mut num_nodes, owned)
            }
            "beta" => {
                owned = reducer
                    .rewrite_with_bindings(&mut m, number(fields[1]), &list::<Expr>(fields[2]))
                    .unwrap();
                describe(&m, &mut num_nodes, owned)
            }
            "beta-set" => {
                reducer.reset(&mut m).unwrap();
                reducer.set_bindings(&list::<Expr>(fields[2]));
                owned = reducer.rewrite(&mut m, number(fields[1])).unwrap();
                describe(&m, &mut num_nodes, owned)
            }
            "beta-update" => {
                let expr: Expr = number(fields[1]);
                let first = reducer
                    .rewrite_with_bindings(&mut m, expr, &list::<Expr>(fields[2]))
                    .unwrap();
                m.dec_ref(first).unwrap();
                reducer.update_inv_binding_at(number(fields[3]), number(fields[4]));
                owned = reducer.rewrite(&mut m, expr).unwrap();
                describe(&m, &mut num_nodes, owned)
            }
            "replace" => {
                let sources: Vec<Expr> = list(fields[2]);
                let targets: Vec<Expr> = list(fields[3]);
                let mut replace = ExprSafeReplace::new();
                for (source, target) in sources.iter().zip(&targets) {
                    replace.insert(&mut m, *source, *target);
                }
                owned = replace.apply(&mut m, number(fields[1])).unwrap();
                replace.release(&mut m).unwrap();
                describe(&m, &mut num_nodes, owned)
            }
            "lt" => {
                let is_less = is_ast_less(&m, number(fields[1]), number(fields[2])).unwrap();
                if is_less { "1" } else { "0" }.into()
            }
            "mk-not" => {
                let expr = mk_not(&mut m, number(fields[1])).unwrap();
                describe(&m, &mut num_nodes, expr)
            }
            "flatten-and" | "flatten-or" => {
                let mut vector = RefVector::new();
                for item in list::<Expr>(fields[1]) {
                    vector.push(&mut m, item);
                }
                if fields[0] == "flatten-and" {
                    flatten_and_vector(&mut m, &mut vector).unwrap();
                } else {
                    flatten_or_vector(&mut m, &mut vector).unwrap();
                }
                let result = join(
                    vector
                        .items
                        .iter()
                        .map(|item| describe(&m, &mut num_nodes, *item)),
                );
                flattened = Some(vector);
                result
            }
            "push-not" => {
                owned = push_not_owned(&mut m, number(fields[1])).unwrap();
                describe(&m, &mut num_nodes, owned)
            }
            "rewrite" => {
                owned = rewriters.rewrite(&mut m, fields[1], number(fields[2]));
                describe(&m, &mut num_nodes, owned)
            }
            "rewrite-bind" => {
                owned = rewriters
                    .default
                    .rewrite_with_bindings(&mut m, number(fields[1]), &list::<Expr>(fields[2]))
                    .unwrap();
                describe(&m, &mut num_nodes, owned)
            }
            "reset" | "cleanup" => {
                rewriters.reset(&mut m, fields[1], fields[0] == "cleanup");
                "-".into()
            }
            "elim-unused" => {
                let expr: Expr = number(fields[1]);
                owned = m.with_temporaries(|m| elim_unused_vars(m, expr)).unwrap();
                describe(&m, &mut num_nodes, owned)
            }
            "elim-unused-p" => {
                owned = eliminator.apply(&mut m, number(fields[1])).unwrap();
                describe(&m, &mut num_nodes, owned)
            }
            "free-var-sorts" => {
                let sorts = get_free_var_sorts(&m, number(fields[1]), number(fields[2])).unwrap();
                join(sorts.iter().map(|sort| match sort {
                    Some(sort) => sort.to_string(),
                    None => "-".into(),
                }))
            }
            "collect-used" => {
                let used = collect_used_vars(&m, number(fields[1]), number(fields[2])).unwrap();
                join(used.iter().map(|is_used| if *is_used { 1 } else { 0 }))
            }
            "replace-free" => {
                let expr: Expr = number(fields[1]);
                owned = m
                    .with_temporaries(|m| {
                        replace_free_vars(m, expr, |m, variable, index, shift| {
                            let sort = m.sorts[variable as usize];
                            Ok(if index % 2 == 0 {
                                m.mk_var(index + shift + 1, sort)
                            } else {
                                m.mk_var(m.values[variable as usize], sort)
                            })
                        })
                    })
                    .unwrap();
                describe(&m, &mut num_nodes, owned)
            }
            "refs" => join(
                (0..num_nodes)
                    .map(|handle| format!("{}/{}", m.ids[handle], m.get_ref_count(handle as Expr))),
            ),
            "release" => {
                rewriters.release(&mut m, fields[1]);
                "-".into()
            }
            "release-rest" => {
                subst_std.release(&mut m).unwrap();
                subst_ns.release(&mut m).unwrap();
                shifter.release(&mut m).unwrap();
                inv_shifter.release(&mut m).unwrap();
                reducer.release(&mut m).unwrap();
                eliminator.release(&mut m).unwrap();
                "-".into()
            }
            "dec" => {
                let expr: Expr = number(fields[1]);
                let position = held.iter().position(|item| *item == expr).unwrap();
                held.remove(position);
                m.dec_ref(expr).unwrap();
                m.get_ref_count(expr).to_string()
            }
            other => panic!("unknown operation {other}"),
        };
        let actual = format!(
            "{result} steps={} asts={}",
            m.limit.count(),
            m.get_num_asts()
        );
        assert_eq!(actual, expected, "line {}: {operation}", line_index + 1);
        if owned != -1 {
            m.dec_ref(owned).unwrap();
        }
        if let Some(mut vector) = flattened {
            vector.reset(&mut m).unwrap();
        }
    }
}
