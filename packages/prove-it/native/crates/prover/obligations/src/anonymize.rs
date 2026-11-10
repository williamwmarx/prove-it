//! A port of tlapm's anonymization (Expr.Anon, Elab.desugar and Proof.Anon): names become de Bruijn
//! indices into the context, builtin definitions are inlined, and anonymous steps get names.
//! A port of `src/obligations/anonymize.ts`.
//!
//! `createAnonymizer` closes over the counter, `expandInstance` and `onWarning`. Expanding an
//! INSTANCE re-enters the anonymizer, so the Rust passes the latter two as an `AnonymizerHost` to
//! each call, and the host is handed the anonymizer back when it expands an instance.

use std::rc::Rc;

use crate::equality::is_equal_expr;
use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, Builtin, Channel, Defn, DefnCore, ExceptPoint, ExceptSpec, Expr, ExprCore, ExprNode,
    ExprProps, Hyp, HypCore, HypNode, Hyps, Level, ObligationWarning, ParenForm, Quantifier,
    ScopeRef, Selector, Sequent, Time, Visibility, WhereDefined, XlabelIndex, adjoin, adjoin_all,
    apply_builtin, at, at_expr, at_props, exprify_sequent, find_named, get_bound_fresh,
    get_error_note, get_fresh, get_locus_prefix, get_scope_at, get_scope_size, hyp, map_accumulate,
    map_bound_domains, map_scoped, map_selector_args, to_index,
};
use crate::proof::{
    Counter, Proof, ProofCore, ProofProps, QedStep, Step, StepCore, StepNumber, Usable, UseDef,
    UseDefCore, get_step_name, get_unique,
};
use crate::subexpression::resolve_subexpression;
use crate::substitution::{cons_substitution, normalize_apply, shift, shift_expr, substitute_expr};
use crate::temporal::get_time;

/// What `createAnonymizer` takes besides the counter.
pub trait AnonymizerHost {
    /// `expandInstance`: the definitions an INSTANCE in a LET or DEFINE stands for.
    fn expand_instance(
        &mut self,
        anonymizer: &mut Anonymizer,
        scope: &ScopeRef,
        definition: &Defn,
    ) -> Result<Vec<Defn>>;

    fn on_warning(&mut self, warning: ObligationWarning);
}

/// Elab.desugar's current_at: the value @ stands for inside an EXCEPT, and the context size there.
struct CurrentAt {
    expression: Expr,
    size: usize,
}

pub struct Anonymizer {
    counter: Rc<Counter>,
    current_at: Option<CurrentAt>,
    /// `DUMMY_FACT`, one node shared by every context, as the TypeScript constant is.
    dummy_fact: Hyp,
}

#[derive(Clone)]
struct AnonContext {
    warned_steps: Rc<Vec<String>>,
    scope: ScopeRef,
}

fn bad_expression() -> Expr {
    crate::expression::expr(ExprCore::Opaque {
        name: "$badexp".to_owned(),
    })
}

// Util.set_locus: the node keeps its properties and takes the location of from.
fn with_locus(expression: Expr, from: &ExprNode) -> Expr {
    match &from.location {
        Some(location) => Rc::new(ExprNode {
            core: expression.core.clone(),
            location: Some(location.clone()),
            is_atomic: expression.is_atomic,
        }),
        None => expression,
    }
}

fn get_anon_selector_failure(selector: &Selector) -> &'static str {
    match selector {
        Selector::Number(_) => "1NUM",
        Selector::Down => "1DOWN",
        Selector::At => "1AT",
        Selector::Instance(_) => "1INST",
        Selector::Left | Selector::Right => "1",
        // The TypeScript table has no entry for a label, which resolveBang never looks up.
        Selector::Label { .. } => "undefined",
    }
}

fn get_context(scope: &ScopeRef) -> AnonContext {
    AnonContext {
        warned_steps: Rc::new(Vec::new()),
        scope: scope.clone(),
    }
}

fn get_size(context: &AnonContext) -> usize {
    get_scope_size(&context.scope)
}

fn with_scope(context: &AnonContext, scope: ScopeRef) -> AnonContext {
    AnonContext {
        warned_steps: context.warned_steps.clone(),
        scope,
    }
}

fn adjoin_context(context: &AnonContext, item: &Hyp) -> AnonContext {
    with_scope(context, adjoin(&context.scope, item))
}

fn adjoin_bounds(context: &AnonContext, items: &[Bound]) -> AnonContext {
    let hyps = items.iter().map(get_bound_fresh).collect::<Vec<_>>();
    with_scope(context, adjoin_all(&context.scope, &hyps))
}

fn push_warned_step(context: &AnonContext, step: &StepNumber) -> AnonContext {
    let mut warned_steps = vec![get_step_name(step)];
    warned_steps.extend(context.warned_steps.iter().cloned());
    AnonContext {
        warned_steps: Rc::new(warned_steps),
        scope: context.scope.clone(),
    }
}

fn adjoin_step(context: &AnonContext, step: &StepNumber, body: Expr, from: &Step) -> AnonContext {
    adjoin_context(
        context,
        &Rc::new(HypNode {
            core: HypCore::Defn {
                definition: Defn {
                    core: DefnCore::Operator {
                        name: get_step_name(step),
                        body,
                    },
                    location: from.props.location.clone(),
                },
                where_defined: WhereDefined::Proof(Time::Always),
                visibility: Visibility::Visible,
                is_local: true,
                is_constness_unset: true,
            },
            location: from.props.location.clone(),
        }),
    )
}

fn get_step_props(step: &Step) -> ExprProps {
    ExprProps {
        location: step.props.location.clone(),
        is_atomic: false,
    }
}

fn tuple_form(item: &Sequent) -> Result<Expr> {
    let mut elements = item
        .context
        .iter()
        .enumerate()
        .map(|(index, entry)| {
            let amount = to_index(item.context.len() - index + 1);
            match &entry.core {
                HypCore::Fact { expression, .. } => shift_expr(amount, expression),
                HypCore::Fresh {
                    domain: Some(domain),
                    ..
                } => {
                    let membership = apply_builtin(
                        Builtin::Mem,
                        vec![at(ExprCore::Ix { index: 0 }, domain), domain.clone()],
                        &domain.props(),
                    );
                    shift_expr(amount, &membership)
                }
                _ => Ok(bad_expression()),
            }
        })
        .collect::<Result<Vec<_>>>()?;
    elements.push(shift_expr(1, &item.active)?);
    Ok(if elements.len() == 1 {
        elements.remove(0)
    } else {
        crate::expression::expr(ExprCore::Tuple { elements })
    })
}

fn is_citable(step: &Step) -> bool {
    !matches!(
        step.core,
        StepCore::Use { .. } | StepCore::Hide { .. } | StepCore::Define { .. }
    )
}

/// `createAnonymizer`.
pub fn create_anonymizer(counter: Rc<Counter>) -> Anonymizer {
    Anonymizer {
        counter,
        current_at: None,
        dummy_fact: hyp(HypCore::Fact {
            expression: crate::expression::expr(ExprCore::At { is_except: false }),
            visibility: Visibility::Visible,
            time: Time::Always,
            use_location: None,
        }),
    }
}

impl Anonymizer {
    pub fn expr(
        &mut self,
        host: &mut dyn AnonymizerHost,
        scope: &ScopeRef,
        expression: &Expr,
    ) -> Result<Expr> {
        Pass {
            anonymizer: self,
            host,
        }
        .expr(&get_context(scope), expression)
    }

    pub fn defn(
        &mut self,
        host: &mut dyn AnonymizerHost,
        scope: &ScopeRef,
        definition: &Defn,
    ) -> Result<Defn> {
        Pass {
            anonymizer: self,
            host,
        }
        .defn(&get_context(scope), definition)
    }

    pub fn sequent(
        &mut self,
        host: &mut dyn AnonymizerHost,
        scope: &ScopeRef,
        item: &Sequent,
    ) -> Result<Sequent> {
        Ok(Pass {
            anonymizer: self,
            host,
        }
        .sequent(&get_context(scope), item)?
        .1)
    }

    pub fn usable(
        &mut self,
        host: &mut dyn AnonymizerHost,
        scope: &ScopeRef,
        item: &Usable,
    ) -> Result<Usable> {
        Pass {
            anonymizer: self,
            host,
        }
        .usable(&get_context(scope), item)
    }

    pub fn proof(
        &mut self,
        host: &mut dyn AnonymizerHost,
        scope: &ScopeRef,
        item: &Proof,
    ) -> Result<Proof> {
        Pass {
            anonymizer: self,
            host,
        }
        .proof(&get_context(scope), item)
    }
}

/// One call into the anonymizer, with its host.
struct Pass<'call> {
    anonymizer: &'call mut Anonymizer,
    host: &'call mut dyn AnonymizerHost,
}

impl Pass<'_> {
    fn expr(&mut self, context: &AnonContext, expression: &Expr) -> Result<Expr> {
        if let ExprCore::At { is_except: true } = expression.core {
            let Some(current_at) = &self.anonymizer.current_at else {
                return Ok(expression.clone());
            };
            return shift_expr(
                to_index(get_size(context)) - to_index(current_at.size),
                &current_at.expression,
            );
        }
        let ExprCore::Except { function, specs } = &expression.core else {
            return self.anon_core(context, expression);
        };
        let base = self.expr(context, function)?;
        specs.iter().try_fold(base, |result, spec| {
            let (path, trail) =
                map_accumulate(result.clone(), &spec.trail, |current, point| match point {
                    ExceptPoint::Dot(field) => Ok((
                        at(
                            ExprCore::Dot {
                                expression: current.clone(),
                                field: field.clone(),
                            },
                            &current,
                        ),
                        point.clone(),
                    )),
                    ExceptPoint::Apply(inner) => {
                        let key = self.expr(context, inner)?;
                        Ok((
                            at(
                                ExprCore::FcnApp {
                                    function: current.clone(),
                                    args: vec![key.clone()],
                                },
                                &current,
                            ),
                            ExceptPoint::Apply(key),
                        ))
                    }
                })?;
            let saved = self.anonymizer.current_at.replace(CurrentAt {
                expression: path,
                size: get_size(context),
            });
            let value = self.expr(context, &spec.value)?;
            self.anonymizer.current_at = saved;
            Ok(at(
                ExprCore::Except {
                    function: result,
                    specs: vec![ExceptSpec { trail, value }],
                },
                expression,
            ))
        })
    }

    fn anon_apply(index: isize, args: Vec<Expr>, from: &ExprNode) -> Expr {
        let indexed = at(ExprCore::Ix { index }, from);
        if args.is_empty() {
            return indexed;
        }
        at(
            ExprCore::Apply {
                operator: indexed,
                args,
            },
            from,
        )
    }

    fn standard_form(
        index: isize,
        where_defined: WhereDefined,
        body: &Expr,
        args: Vec<Expr>,
        from: &ExprNode,
    ) -> Result<Expr> {
        if where_defined != WhereDefined::Builtin {
            return Ok(Self::anon_apply(index, args, from));
        }
        let shifted = shift_expr(index, body)?;
        Ok(if args.is_empty() {
            at_expr(&shifted, &from.props())
        } else {
            at(normalize_apply(&shifted, args)?, from)
        })
    }

    fn resolve_name(
        &mut self,
        context: &AnonContext,
        name: &str,
        args: Vec<Expr>,
        from: &ExprNode,
    ) -> Result<Expr> {
        let Some((depth, found)) = find_named(&context.scope, name) else {
            let message = format!("Operator \"{name}\" not found");
            self.host
                .on_warning(get_error_note(from.location.as_ref(), &message));
            return Err(ObligationError::proof_failure(message, "Expr.Anon: 4"));
        };
        let index = to_index(depth) + 1;
        match &found.core {
            HypCore::Defn {
                definition,
                where_defined,
                ..
            } => match &definition.core {
                DefnCore::Operator { body, .. } => {
                    Self::standard_form(index, *where_defined, body, args, from)
                }
                DefnCore::Recursive { .. } => Err(ObligationError::proof_failure(
                    "Recursive operators not supported by TLAPS",
                    "Expr.Anon: Recursive",
                )),
                _ => Ok(Self::anon_apply(index, args, from)),
            },
            HypCore::Fresh { .. } => Ok(Self::anon_apply(index, args, from)),
            HypCore::Flex { .. } => Ok(at(ExprCore::Ix { index }, from)),
            HypCore::Fact { .. } => Err(ObligationError::bug(
                "File \"src/expr/e_anon.ml\", line 230, characters 24-36: Assertion failed",
            )),
        }
    }

    // Expr.Anon's check: a prefix that names nothing joins the next label, as in an instance path.
    fn resolve_bang(
        &mut self,
        context: &AnonContext,
        prefix: &str,
        args: Vec<Expr>,
        selectors: &[Selector],
        is_instance: bool,
        from: &ExprNode,
    ) -> Result<Expr> {
        let Some((depth, found)) = find_named(&context.scope, prefix) else {
            let selector = selectors.first();
            if let Some(Selector::Label {
                label,
                args: label_args,
            }) = selector
            {
                let label_args = label_args
                    .iter()
                    .map(|arg| self.expr(context, arg))
                    .collect::<Result<Vec<_>>>()?;
                return self.resolve_bang(
                    context,
                    &format!("{prefix}!{label}"),
                    args.into_iter().chain(label_args).collect(),
                    &selectors[1..],
                    true,
                    from,
                );
            }
            let message = format!("Operator \"{prefix}\" not found");
            if selector.is_some() {
                self.host
                    .on_warning(get_error_note(from.location.as_ref(), &message));
            }
            return Err(ObligationError::proof_failure(
                message,
                format!(
                    "Expr.Anon: {}",
                    selector.map_or("1EMPTY", get_anon_selector_failure)
                ),
            ));
        };
        let HypCore::Defn {
            definition,
            where_defined,
            ..
        } = &found.core
        else {
            return Err(ObligationError::proof("invalid subexpression reference"));
        };
        let body = match &definition.core {
            DefnCore::Operator { body, .. } | DefnCore::Bpragma { body, .. } => body,
            _ => return Err(ObligationError::proof("invalid subexpression reference")),
        };
        let index = to_index(depth) + 1;
        if selectors.is_empty() && is_instance {
            return if args.is_empty() {
                Ok(at(ExprCore::Ix { index }, from))
            } else {
                Self::standard_form(index, *where_defined, body, args, from)
            };
        }
        let body = with_locus(shift_expr(index, body)?, from);
        let host = &mut *self.host;
        Ok(with_locus(
            resolve_subexpression(
                &mut |warning| host.on_warning(warning),
                &body,
                &args,
                selectors,
            )?,
            from,
        ))
    }

    fn anon_core(&mut self, context: &AnonContext, expression: &Expr) -> Result<Expr> {
        match &expression.core {
            ExprCore::Bang {
                expression: inner,
                selectors,
            } => {
                if let ExprCore::Apply { operator, args } = &inner.core
                    && let ExprCore::Opaque { name } = &operator.core
                {
                    let selectors = selectors
                        .iter()
                        .map(|selector| {
                            map_selector_args(selector, &mut |arg| self.expr(context, arg))
                        })
                        .collect::<Result<Vec<_>>>()?;
                    let args = args
                        .iter()
                        .map(|arg| self.expr(context, arg))
                        .collect::<Result<Vec<_>>>()?;
                    let bang_context = get_context(&context.scope);
                    return self.resolve_bang(
                        &bang_context,
                        name,
                        args,
                        &selectors,
                        false,
                        expression,
                    );
                }
                self.expr(
                    context,
                    &expression.with_core(ExprCore::Bang {
                        expression: at(
                            ExprCore::Apply {
                                operator: inner.clone(),
                                args: Vec::new(),
                            },
                            inner,
                        ),
                        selectors: selectors.clone(),
                    }),
                )
            }
            ExprCore::Apply { operator, args } => {
                let ExprCore::Opaque { name } = &operator.core else {
                    return self.visit(context, expression);
                };
                if context.warned_steps.contains(name) {
                    self.host.on_warning(ObligationWarning {
                        text: format!(
                            "{}Warning: {name} does not introduce any assumptions. It does not make sense to use it here.\n",
                            get_locus_prefix(expression.location.as_ref())
                        ),
                        channel: Channel::Toolbox,
                    });
                    return Ok(at(
                        ExprCore::Internal {
                            builtin: Builtin::TRUE,
                        },
                        expression,
                    ));
                }
                let args = args
                    .iter()
                    .map(|arg| self.expr(context, arg))
                    .collect::<Result<Vec<_>>>()?;
                self.resolve_name(context, name, args, expression)
            }
            ExprCore::Opaque { .. } => self.expr(
                context,
                &at(
                    ExprCore::Apply {
                        operator: expression.clone(),
                        args: Vec::new(),
                    },
                    expression,
                ),
            ),
            ExprCore::Parens {
                expression: inner,
                form,
            } => {
                if *form == ParenForm::Syntax {
                    return self.expr(context, inner);
                }
                let inner = self.expr(context, inner)?;
                Ok(expression.with_core(ExprCore::Parens {
                    expression: inner,
                    form: anon_paren_form(context, form)?,
                }))
            }
            _ => self.visit(context, expression),
        }
    }

    fn bounds(
        &mut self,
        context: &AnonContext,
        items: &[Bound],
    ) -> Result<(AnonContext, Vec<Bound>)> {
        let mapped = map_bound_domains(items, &mut |domain| self.expr(context, domain))?;
        Ok((adjoin_bounds(context, &mapped), mapped))
    }

    // Visit.map, apart from the definitions an ASSUME or a LET binds.
    fn visit(&mut self, context: &AnonContext, expression: &Expr) -> Result<Expr> {
        match &expression.core {
            ExprCore::Sequent { sequent } => Ok(expression.with_core(ExprCore::Sequent {
                sequent: self.sequent(context, sequent)?.1,
            })),
            ExprCore::Let { definitions, body } => {
                let (inner, definitions) = self.defns(context, definitions)?;
                Ok(expression.with_core(ExprCore::Let {
                    definitions,
                    body: self.expr(&inner, body)?,
                }))
            }
            _ => map_scoped(
                context,
                expression,
                &mut |current, inner| self.expr(current, inner),
                &mut adjoin_context,
                Hyps::Visible,
            ),
        }
    }

    // Expr.Anon's defn turns a recursive function definition into a CHOOSE over its own equation.
    fn defn(&mut self, context: &AnonContext, definition: &Defn) -> Result<Defn> {
        let DefnCore::Operator { name, body } = &definition.core else {
            return Ok(definition.clone());
        };
        let with_body = |body| Defn {
            core: DefnCore::Operator {
                name: name.clone(),
                body,
            },
            location: definition.location.clone(),
        };
        if !matches!(body.core, ExprCore::Fcn { .. }) {
            return Ok(with_body(self.expr(context, body)?));
        }
        let inner = self.expr(
            &adjoin_context(context, &get_fresh(name, Level::Constant, 0)),
            body,
        )?;
        let marker = crate::expression::expr(ExprCore::Opaque {
            name: "%%%".to_owned(),
        });
        let is_recursive = !is_equal_expr(
            &*substitute_expr(&cons_substitution(marker, shift(1)), &inner)?,
            &inner,
        );
        if !is_recursive {
            return Ok(with_body(shift_expr(-1, &inner)?));
        }
        let equation = apply_builtin(
            Builtin::Eq,
            vec![at(ExprCore::Ix { index: 1 }, &inner), inner.clone()],
            &inner.props(),
        );
        Ok(with_body(at(
            ExprCore::Choose {
                name: name.clone(),
                domain: None,
                body: equation,
            },
            &inner,
        )))
    }

    // Module.Elab.anon#defns: an INSTANCE stands for the definitions it instantiates.
    fn defns(
        &mut self,
        context: &AnonContext,
        definitions: &[Defn],
    ) -> Result<(AnonContext, Vec<Defn>)> {
        let mut current = context.clone();
        let mut queue = definitions.to_vec();
        let mut mapped = Vec::new();
        let mut index = 0;
        while index < queue.len() {
            let definition = queue[index].clone();
            index += 1;
            if let DefnCore::Instance { .. } = definition.core {
                let expanded =
                    self.host
                        .expand_instance(self.anonymizer, &current.scope, &definition)?;
                queue.splice(index..index, expanded);
                continue;
            }
            let result = self.defn(&current, &definition)?;
            current = adjoin_context(
                &current,
                &hyp(HypCore::Defn {
                    definition: result.clone(),
                    where_defined: WhereDefined::User,
                    visibility: Visibility::Visible,
                    is_local: true,
                    is_constness_unset: true,
                }),
            );
            mapped.push(result);
        }
        Ok((current, mapped))
    }

    fn hyp(&mut self, context: &AnonContext, item: &Hyp) -> Result<(AnonContext, Hyp)> {
        let mapped = match &item.core {
            HypCore::Fresh {
                name,
                shape,
                level,
                domain: Some(domain),
                domain_visibility,
            } => item.with_core(HypCore::Fresh {
                name: name.clone(),
                shape: *shape,
                level: *level,
                domain: Some(self.expr(context, domain)?),
                domain_visibility: *domain_visibility,
            }),
            HypCore::Fresh { .. } | HypCore::Flex { .. } => item.clone(),
            HypCore::Defn {
                definition,
                where_defined,
                visibility,
                is_local,
                is_constness_unset,
            } => item.with_core(HypCore::Defn {
                definition: self.defn(context, definition)?,
                where_defined: *where_defined,
                visibility: *visibility,
                is_local: *is_local,
                is_constness_unset: *is_constness_unset,
            }),
            HypCore::Fact {
                expression,
                visibility,
                use_location,
                ..
            } => {
                let expression = self.expr(context, expression)?;
                let time = get_time(&context.scope, &expression)?;
                item.with_core(HypCore::Fact {
                    expression,
                    visibility: *visibility,
                    time,
                    use_location: use_location.clone(),
                })
            }
        };
        Ok((adjoin_context(context, &mapped), mapped))
    }

    fn sequent(&mut self, context: &AnonContext, item: &Sequent) -> Result<(AnonContext, Sequent)> {
        let (inner, hyps) = map_accumulate(context.clone(), &item.context, |current, entry| {
            self.hyp(&current, entry)
        })?;
        let active = self.expr(&inner, &item.active)?;
        Ok((
            inner,
            Sequent {
                context: hyps,
                active,
            },
        ))
    }

    fn bump_context(&self, context: &AnonContext, count: usize) -> AnonContext {
        let dummies = vec![self.anonymizer.dummy_fact.clone(); count];
        with_scope(context, adjoin_all(&context.scope, &dummies))
    }

    fn usable(&mut self, context: &AnonContext, item: &Usable) -> Result<Usable> {
        let facts = item
            .facts
            .iter()
            .map(|fact| self.expr(context, fact))
            .collect::<Result<Vec<_>>>()?;
        let mut defs = Vec::new();
        for def in &item.defs {
            let UseDefCore::Dvar { name } = &def.core else {
                defs.push(def.clone());
                continue;
            };
            let resolved = self.expr(
                context,
                &at_props(
                    ExprCore::Opaque { name: name.clone() },
                    &ExprProps {
                        location: def.location.clone(),
                        is_atomic: false,
                    },
                ),
            )?;
            let ExprCore::Ix { index } = resolved.core else {
                self.host.on_warning(ObligationWarning {
                    text: format!(
                        "{}Ignored unexpandable identifier {} in BY DEF.",
                        get_locus_prefix(def.location.as_ref()),
                        crate::errors::quote_json(name)
                    ),
                    channel: Channel::Stderr,
                });
                continue;
            };
            let is_definition = get_scope_at(&context.scope, index - 1)
                .is_some_and(|scope| matches!(scope.hyp.core, HypCore::Defn { .. }));
            if !is_definition {
                self.host.on_warning(ObligationWarning {
                    text: format!(
                        "{}{} is not a definition and cannot be used in a DEF clause.",
                        get_locus_prefix(def.location.as_ref()),
                        crate::errors::quote_json(name)
                    ),
                    channel: Channel::Toolbox,
                });
                continue;
            }
            defs.push(UseDef {
                core: UseDefCore::Dx { index },
                location: def.location.clone(),
            });
        }
        Ok(Usable { facts, defs })
    }

    fn proof(&mut self, context: &AnonContext, item: &Proof) -> Result<Proof> {
        let core = match &item.core {
            ProofCore::Steps { steps, qed } => {
                let (inner, steps) = map_accumulate(context.clone(), steps, |current, entry| {
                    self.step(&current, entry)
                })?;
                let qed_context = match &item.props.step {
                    Some(step) => push_warned_step(&inner, step),
                    None => inner,
                };
                let qed_proof = self.proof(&qed_context, &qed.proof)?;
                ProofCore::Steps {
                    steps,
                    qed: Box::new(QedStep {
                        proof: qed_proof,
                        props: qed.props.clone(),
                    }),
                }
            }
            ProofCore::By { usable, is_only } => ProofCore::By {
                usable: self.usable(context, usable)?,
                is_only: *is_only,
            },
            _ => return Ok(item.clone()),
        };
        Ok(Proof {
            core,
            props: item.props.clone(),
        })
    }

    fn step(&mut self, context: &AnonContext, original: &Step) -> Result<(AnonContext, Step)> {
        let number = match &original.props.step {
            Some(StepNumber::Unnamed { level, .. }) if is_citable(original) => {
                Some(StepNumber::Named {
                    level: *level,
                    label: format!("_a{}", get_unique(&self.anonymizer.counter)),
                    is_anonymous: true,
                })
            }
            other => other.clone(),
        };
        let Some(number) = number else {
            return Err(ObligationError::assert_failure());
        };
        let item = Step {
            core: original.core.clone(),
            props: ProofProps {
                step: Some(number.clone()),
                ..original.props.clone()
            },
        };
        let props = get_step_props(&item);
        let with_core = |core| Step {
            core,
            props: item.props.clone(),
        };
        let tuple = |elements| at_props(ExprCore::Tuple { elements }, &props);
        match &item.core {
            StepCore::Assert { sequent, proof } => {
                let (_, mapped) = self.sequent(context, sequent)?;
                let assumptions = mapped
                    .context
                    .iter()
                    .fold(context.clone(), |current, entry| {
                        adjoin_context(&current, entry)
                    });
                let fact = at_expr(&tuple_form(&mapped)?, &props);
                let with_tuple = self.bump_context(
                    &adjoin_step(&self.bump_context(&assumptions, 1), &number, fact, &item),
                    1,
                );
                let inner = if mapped.context.is_empty() {
                    push_warned_step(&with_tuple, &number)
                } else {
                    with_tuple
                };
                let proof = self.proof(&inner, proof)?;
                let after = adjoin_step(
                    context,
                    &number,
                    at_expr(&exprify_sequent(&mapped), &props),
                    &item,
                );
                Ok((
                    self.bump_context(&after, 1),
                    with_core(StepCore::Assert {
                        sequent: mapped,
                        proof,
                    }),
                ))
            }
            StepCore::Pcase { expression, proof } => {
                let expression = self.expr(context, expression)?;
                let shifted = tuple(vec![shift_expr(2, &expression)?]);
                let inner = self.bump_context(
                    &adjoin_step(&self.bump_context(context, 2), &number, shifted, &item),
                    1,
                );
                let proof = self.proof(&inner, proof)?;
                let after = adjoin_step(context, &number, tuple(vec![expression.clone()]), &item);
                Ok((
                    self.bump_context(&after, 1),
                    with_core(StepCore::Pcase { expression, proof }),
                ))
            }
            StepCore::Suffices { sequent, proof } => {
                let (_, mapped) = self.sequent(context, sequent)?;
                let fact = tuple(vec![at_expr(&exprify_sequent(&mapped), &props)]);
                let inner = self.bump_context(&adjoin_step(context, &number, fact, &item), 1);
                let proof = self.proof(&inner, proof)?;
                let assumptions = mapped
                    .context
                    .iter()
                    .fold(context.clone(), |current, entry| {
                        adjoin_context(&current, entry)
                    });
                let form = tuple(vec![at_expr(&tuple_form(&mapped)?, &props)]);
                Ok((
                    self.bump_context(
                        &adjoin_step(&self.bump_context(&assumptions, 1), &number, form, &item),
                        1,
                    ),
                    with_core(StepCore::Suffices {
                        sequent: mapped,
                        proof,
                    }),
                ))
            }
            StepCore::Have { expression } => {
                let expression = self.expr(context, expression)?;
                let shifted = tuple(vec![shift_expr(2, &expression)?]);
                Ok((
                    self.bump_context(
                        &adjoin_step(&self.bump_context(context, 2), &number, shifted, &item),
                        1,
                    ),
                    with_core(StepCore::Have { expression }),
                ))
            }
            StepCore::Take { bounds } => {
                let (inner, mapped) = self.bounds(context, bounds)?;
                let universal = at_props(
                    ExprCore::Quant {
                        quantifier: Quantifier::Forall,
                        bounds: mapped.clone(),
                        body: bad_expression(),
                    },
                    &props,
                );
                Ok((
                    self.bump_context(
                        &adjoin_step(&self.bump_context(&inner, 1), &number, universal, &item),
                        1,
                    ),
                    with_core(StepCore::Take { bounds: mapped }),
                ))
            }
            StepCore::Witness { expressions } => {
                let expressions = expressions
                    .iter()
                    .map(|expression| self.expr(context, expression))
                    .collect::<Result<Vec<_>>>()?;
                let witnessed = tuple(expressions.clone());
                Ok((
                    self.bump_context(
                        &adjoin_step(&self.bump_context(context, 1), &number, witnessed, &item),
                        1,
                    ),
                    with_core(StepCore::Witness { expressions }),
                ))
            }
            StepCore::Pick {
                bounds,
                expression,
                proof,
            } => {
                let (bound_context, mapped) = self.bounds(context, bounds)?;
                let expression = self.expr(&bound_context, expression)?;
                let existential = at_props(
                    ExprCore::Quant {
                        quantifier: Quantifier::Exists,
                        bounds: mapped.clone(),
                        body: expression.clone(),
                    },
                    &props,
                );
                let inner = push_warned_step(
                    &self.bump_context(
                        &adjoin_step(
                            &self.bump_context(context, 1),
                            &number,
                            existential.clone(),
                            &item,
                        ),
                        1,
                    ),
                    &number,
                );
                let proof = self.proof(&inner, proof)?;
                let declared = adjoin_bounds(&self.bump_context(context, 2), &mapped);
                let shifted = shift_expr(4 + to_index(mapped.len()), &existential)?;
                Ok((
                    self.bump_context(
                        &adjoin_step(&self.bump_context(&declared, 2), &number, shifted, &item),
                        1,
                    ),
                    with_core(StepCore::Pick {
                        bounds: mapped,
                        expression,
                        proof,
                    }),
                ))
            }
            StepCore::Use { usable, is_only } => {
                let mapped = self.usable(context, usable)?;
                Ok((
                    self.bump_context(context, mapped.facts.len()),
                    with_core(StepCore::Use {
                        usable: mapped,
                        is_only: *is_only,
                    }),
                ))
            }
            StepCore::Hide { usable } => Ok((
                context.clone(),
                with_core(StepCore::Hide {
                    usable: self.usable(context, usable)?,
                }),
            )),
            StepCore::Define { definitions } => {
                let (inner, definitions) = self.defns(context, definitions)?;
                Ok((inner, with_core(StepCore::Define { definitions })))
            }
            StepCore::Forget { .. } => Ok((context.clone(), item.clone())),
        }
    }
}

fn anon_paren_form(context: &AnonContext, form: &ParenForm) -> Result<ParenForm> {
    let ParenForm::Nlabel { label, names } = form else {
        return Ok(form.clone());
    };
    Ok(ParenForm::Xlabel {
        label: label.clone(),
        indices: names
            .iter()
            .map(|name| {
                let Some((depth, _)) = find_named(&context.scope, name) else {
                    return Err(ObligationError::proof(format!(
                        "Identifier \"{name}\" in label parameters not found"
                    )));
                };
                Ok(XlabelIndex {
                    name: name.clone(),
                    index: depth + 1,
                })
            })
            .collect::<Result<_>>()?,
    })
}

#[cfg(test)]
mod tests {
    // Each case builds its input as `anonymize.ts`'s would be, and expects what the TypeScript gives
    // under Bun for it, printed by the same printer.
    use super::*;
    use crate::expression::{BoundDomain, InstanceDefinition, Locus, Modal, Param};

    fn locus(line: u32) -> Option<Locus> {
        Some(Locus {
            file: "M.tla".into(),
            start_line: line,
            start_column: 3,
            end_line: line,
            end_column: 9,
        })
    }

    fn located_at(line: u32) -> Option<Locus> {
        if line == 0 { None } else { locus(line) }
    }

    fn node(core: ExprCore, line: u32, is_atomic: bool) -> Expr {
        Rc::new(ExprNode {
            core,
            location: located_at(line),
            is_atomic,
        })
    }

    fn defn(core: DefnCore, line: u32) -> Defn {
        Defn {
            core,
            location: located_at(line),
        }
    }

    fn hyp_at(core: HypCore, line: u32) -> Hyp {
        Rc::new(HypNode {
            core,
            location: located_at(line),
        })
    }

    fn props(line: u32, step: Option<StepNumber>) -> ProofProps {
        ProofProps {
            location: located_at(line),
            step,
            ..ProofProps::default()
        }
    }

    struct TestHost {
        instances: Option<Vec<Defn>>,
        warnings: Vec<String>,
    }

    impl AnonymizerHost for TestHost {
        fn expand_instance(
            &mut self,
            _anonymizer: &mut Anonymizer,
            _scope: &ScopeRef,
            _definition: &Defn,
        ) -> Result<Vec<Defn>> {
            self.instances
                .clone()
                .ok_or_else(ObligationError::assert_failure)
        }

        fn on_warning(&mut self, warning: ObligationWarning) {
            let channel = match warning.channel {
                Channel::Toolbox => "toolbox",
                Channel::ToolboxOnly => "toolboxOnly",
                Channel::Stderr => "stderr",
                Channel::Stdout => "stdout",
            };
            self.warnings.push(format!("{channel}: {}", warning.text));
        }
    }

    fn run(
        scope: Vec<Hyp>,
        instances: Option<Vec<Defn>>,
        counter: usize,
        call: impl FnOnce(&mut Anonymizer, &mut TestHost, &ScopeRef) -> Result<String>,
    ) -> (String, Vec<String>) {
        let mut anonymizer = create_anonymizer(Rc::new(Counter {
            value: counter.into(),
        }));
        let mut host = TestHost {
            instances,
            warnings: Vec::new(),
        };
        let result = call(&mut anonymizer, &mut host, &adjoin_all(&None, &scope));
        let shown = result.unwrap_or_else(|error| match error {
            ObligationError::Proof {
                message,
                failure,
                exception,
            } => format!(
                "ERR TlaProofError|{message}|{}|{exception}",
                failure.as_deref().unwrap_or("-")
            ),
            other => format!("ERR {}|{}", other.name(), other.message()),
        });
        (shown, host.warnings)
    }

    fn show_props(location: Option<&Locus>, is_atomic: bool) -> String {
        let line = location.map_or_else(String::new, |locus| format!("@{}", locus.start_line));
        format!("{line}{}", if is_atomic { "!" } else { "" })
    }

    fn show_list<Item>(items: &[Item], show_item: impl Fn(&Item) -> String) -> String {
        items.iter().map(show_item).collect::<Vec<_>>().join(" ")
    }

    fn show_bound(bound: &Bound) -> String {
        let domain = match &bound.domain {
            BoundDomain::Domain(domain) => format!(":{}", show_expr(domain)),
            BoundDomain::Ditto => ":ditto".to_owned(),
            BoundDomain::NoDomain => String::new(),
        };
        format!("{}:{:?}{domain}", bound.name, bound.level)
    }

    fn show_selector(selector: &Selector) -> String {
        match selector {
            Selector::Number(value) => value.to_string(),
            Selector::Instance(args) => format!("(inst {})", show_list(args, show_expr)),
            Selector::Label { label, args } => {
                format!("(label {label} {})", show_list(args, show_expr))
            }
            Selector::Down => "Down".to_owned(),
            Selector::Left => "Left".to_owned(),
            Selector::Right => "Right".to_owned(),
            Selector::At => "At".to_owned(),
        }
    }

    fn show_form(form: &ParenForm) -> String {
        match form {
            ParenForm::Syntax => "syntax".to_owned(),
            ParenForm::Nlabel { label, names } => format!("nlabel {label} [{}]", names.join(" ")),
            ParenForm::Xlabel { label, indices } => format!(
                "xlabel {label} [{}]",
                show_list(indices, |entry| format!("{}:{}", entry.name, entry.index))
            ),
        }
    }

    fn show_core(core: &ExprCore) -> String {
        match core {
            ExprCore::Ix { index } => format!("#{index}"),
            ExprCore::Opaque { name } => name.clone(),
            ExprCore::Internal { builtin } => format!("${}", builtin.name()),
            ExprCore::Apply { operator, args } => {
                format!("({} {})", show_expr(operator), show_list(args, show_expr))
            }
            ExprCore::Lambda { params, body } => format!(
                "(lambda [{}] {})",
                show_list(params, |param: &Param| param.name.clone()),
                show_expr(body)
            ),
            ExprCore::Sequent { sequent } => show_sequent(sequent),
            ExprCore::Bang {
                expression,
                selectors,
            } => format!(
                "(bang {} {})",
                show_expr(expression),
                show_list(selectors, show_selector)
            ),
            ExprCore::Let { definitions, body } => format!(
                "(let [{}] {})",
                show_list(definitions, show_defn),
                show_expr(body)
            ),
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => format!(
                "({quantifier:?} [{}] {})",
                show_list(bounds, show_bound),
                show_expr(body)
            ),
            ExprCore::Tquant {
                quantifier,
                names,
                body,
            } => format!(
                "(t{quantifier:?} [{}] {})",
                names.join(" "),
                show_expr(body)
            ),
            ExprCore::Fcn { bounds, body } => format!(
                "(fcn [{}] {})",
                show_list(bounds, show_bound),
                show_expr(body)
            ),
            ExprCore::FcnApp { function, args } => format!(
                "(fcnapp {} {})",
                show_expr(function),
                show_list(args, show_expr)
            ),
            ExprCore::Except { function, specs } => format!(
                "(except {} {})",
                show_expr(function),
                show_list(specs, |spec: &ExceptSpec| format!(
                    "[{}]={}",
                    show_list(&spec.trail, |point| match point {
                        ExceptPoint::Dot(field) => format!(".{field}"),
                        ExceptPoint::Apply(inner) => show_expr(inner),
                    }),
                    show_expr(&spec.value)
                ))
            ),
            ExprCore::Dot { expression, field } => {
                format!("(dot {} {field})", show_expr(expression))
            }
            ExprCore::At { is_except } => if *is_except { "@except" } else { "@" }.to_owned(),
            ExprCore::Parens { expression, form } => {
                format!("(parens {} {})", show_expr(expression), show_form(form))
            }
            ExprCore::Tuple { elements } => format!("(tuple {})", show_list(elements, show_expr)),
            ExprCore::Num { integer, .. } => integer.clone(),
            ExprCore::Choose { name, domain, body } => format!(
                "(choose {name}{} {})",
                domain
                    .as_ref()
                    .map_or_else(String::new, |domain| format!(":{}", show_expr(domain))),
                show_expr(body)
            ),
            ExprCore::Sub {
                modal,
                action,
                subscript,
            } => format!(
                "(sub {modal:?} {} {})",
                show_expr(action),
                show_expr(subscript)
            ),
            _ => "(other)".to_owned(),
        }
    }

    fn show_expr(expression: &Expr) -> String {
        show_core(&expression.core)
            + &show_props(expression.location.as_ref(), expression.is_atomic)
    }

    fn show_defn(definition: &Defn) -> String {
        let body = match &definition.core {
            DefnCore::Operator { name, body } => format!("(op {name} {})", show_expr(body)),
            DefnCore::Recursive { name, .. } => format!("(rec {name})"),
            DefnCore::Bpragma { name, body, .. } => {
                format!("(bpragma {name} {})", show_expr(body))
            }
            DefnCore::Instance { name, instance } => {
                format!("(instance {name} {})", instance.module)
            }
        };
        body + &show_props(definition.location.as_ref(), false)
    }

    fn show_hyp(item: &Hyp) -> String {
        let body = match &item.core {
            HypCore::Fresh {
                name,
                shape,
                level,
                domain,
                ..
            } => format!(
                "(fresh {name} {level:?} {shape}{})",
                domain
                    .as_ref()
                    .map_or_else(String::new, |domain| format!(" {}", show_expr(domain)))
            ),
            HypCore::Flex { name } => format!("(flex {name})"),
            HypCore::Defn {
                definition,
                where_defined,
                visibility,
                is_local,
                is_constness_unset,
            } => format!(
                "(defn {} {visibility:?}{}{} {})",
                match where_defined {
                    WhereDefined::Proof(time) => format!("Proof:{time:?}"),
                    other => format!("{other:?}"),
                },
                if *is_local { " local" } else { "" },
                if *is_constness_unset { " unset" } else { "" },
                show_defn(definition)
            ),
            HypCore::Fact {
                expression,
                visibility,
                time,
                ..
            } => format!("(fact {visibility:?} {time:?} {})", show_expr(expression)),
        };
        body + &show_props(item.location.as_ref(), false)
    }

    fn show_sequent(sequent: &Sequent) -> String {
        format!(
            "(sequent [{}] {})",
            show_list(&sequent.context, show_hyp),
            show_expr(&sequent.active)
        )
    }

    fn show_usable(usable: &Usable) -> String {
        format!(
            "facts [{}] defs [{}]",
            show_list(&usable.facts, show_expr),
            show_list(&usable.defs, |def| {
                let body = match &def.core {
                    UseDefCore::Dx { index } => format!("#{index}"),
                    UseDefCore::Dvar { name } => name.clone(),
                };
                body + &show_props(def.location.as_ref(), false)
            })
        )
    }

    fn show_step_number(number: &StepNumber) -> String {
        match number {
            StepNumber::Named {
                level,
                label,
                is_anonymous,
            } => format!("<{level}>{label}{}", if *is_anonymous { "~" } else { "" }),
            StepNumber::Unnamed { level, id } => format!("<{level}>#{id}"),
        }
    }

    fn show_proof_props(props: &ProofProps) -> String {
        let step = props.step.as_ref().map_or_else(String::new, |number| {
            format!("{{{}}}", show_step_number(number))
        });
        step + &show_props(props.location.as_ref(), false)
    }

    fn show_proof(proof: &Proof) -> String {
        let body = match &proof.core {
            ProofCore::Obvious => "(obvious)".to_owned(),
            ProofCore::By { usable, is_only } => format!(
                "(by{} {})",
                if *is_only { " only" } else { "" },
                show_usable(usable)
            ),
            ProofCore::Steps { steps, qed } => format!(
                "(steps [{}] qed{} {})",
                show_list(steps, show_step),
                show_proof_props(&qed.props),
                show_proof(&qed.proof)
            ),
            _ => "(other)".to_owned(),
        };
        body + &show_proof_props(&proof.props)
    }

    fn show_step(step: &Step) -> String {
        let body = match &step.core {
            StepCore::Assert { sequent, proof } => {
                format!("(assert {} {})", show_sequent(sequent), show_proof(proof))
            }
            StepCore::Suffices { sequent, proof } => {
                format!("(suffices {} {})", show_sequent(sequent), show_proof(proof))
            }
            StepCore::Pcase { expression, proof } => {
                format!("(pcase {} {})", show_expr(expression), show_proof(proof))
            }
            StepCore::Pick {
                bounds,
                expression,
                proof,
            } => format!(
                "(pick [{}] {} {})",
                show_list(bounds, show_bound),
                show_expr(expression),
                show_proof(proof)
            ),
            StepCore::Use { usable, is_only } => format!(
                "(use{} {})",
                if *is_only { " only" } else { "" },
                show_usable(usable)
            ),
            StepCore::Hide { usable } => format!("(hide {})", show_usable(usable)),
            StepCore::Have { expression } => format!("(have {})", show_expr(expression)),
            StepCore::Take { bounds } => format!("(take [{}])", show_list(bounds, show_bound)),
            StepCore::Witness { expressions } => {
                format!("(witness {})", show_list(expressions, show_expr))
            }
            StepCore::Define { definitions } => {
                format!("(define [{}])", show_list(definitions, show_defn))
            }
            StepCore::Forget { count } => format!("(forget {count})"),
        };
        body + &show_proof_props(&step.props)
    }

    #[test]
    fn name_to_index() {
        let input = node(
            ExprCore::Opaque {
                name: "x".to_owned(),
            },
            20,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "#10@20");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn user_operator() {
        let input = node(
            ExprCore::Apply {
                operator: node(
                    ExprCore::Opaque {
                        name: "F".to_owned(),
                    },
                    21,
                    false,
                ),
                args: vec![node(
                    ExprCore::Opaque {
                        name: "x".to_owned(),
                    },
                    22,
                    false,
                )],
            },
            20,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "(#9@20 #10@22)@20");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn builtin_operator_beta() {
        let input = node(
            ExprCore::Apply {
                operator: node(
                    ExprCore::Opaque {
                        name: "Plus2".to_owned(),
                    },
                    0,
                    false,
                ),
                args: vec![
                    node(
                        ExprCore::Opaque {
                            name: "x".to_owned(),
                        },
                        22,
                        false,
                    ),
                    node(
                        ExprCore::Opaque {
                            name: "S".to_owned(),
                        },
                        0,
                        false,
                    ),
                ],
            },
            20,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "($Plus #10 #11)@20");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn builtin_constant() {
        let input = node(
            ExprCore::Opaque {
                name: "T".to_owned(),
            },
            23,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "$TRUE@23");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn builtin_constant_unlocated() {
        let input = node(
            ExprCore::Opaque {
                name: "T".to_owned(),
            },
            0,
            true,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "$TRUE@7!");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn unknown_operator() {
        let input = node(
            ExprCore::Apply {
                operator: node(
                    ExprCore::Opaque {
                        name: "Nope".to_owned(),
                    },
                    0,
                    false,
                ),
                args: vec![node(
                    ExprCore::Opaque {
                        name: "x".to_owned(),
                    },
                    0,
                    false,
                )],
            },
            24,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"Nope\" not found|Expr.Anon: 4|Failure(\"Expr.Anon: 4\")"
        );
        assert_eq!(
            warnings,
            [
                "stderr: File \"M.tla\", line 24, characters 3-8:\nError: Operator \"Nope\" not found"
            ]
        );
    }

    #[test]
    fn unknown_in_args_first() {
        let input = node(
            ExprCore::Apply {
                operator: node(
                    ExprCore::Opaque {
                        name: "Nope".to_owned(),
                    },
                    25,
                    false,
                ),
                args: vec![node(
                    ExprCore::Opaque {
                        name: "Gone".to_owned(),
                    },
                    26,
                    false,
                )],
            },
            24,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"Gone\" not found|Expr.Anon: 4|Failure(\"Expr.Anon: 4\")"
        );
        assert_eq!(
            warnings,
            [
                "stderr: File \"M.tla\", line 26, characters 3-8:\nError: Operator \"Gone\" not found"
            ]
        );
    }

    #[test]
    fn recursive_operator() {
        let input = node(
            ExprCore::Opaque {
                name: "R".to_owned(),
            },
            27,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Recursive operators not supported by TLAPS|Expr.Anon: Recursive|Failure(\"Expr.Anon: Recursive\")"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn flex_variable() {
        let input = node(
            ExprCore::Apply {
                operator: node(
                    ExprCore::Opaque {
                        name: "v".to_owned(),
                    },
                    0,
                    false,
                ),
                args: vec![node(
                    ExprCore::Opaque {
                        name: "x".to_owned(),
                    },
                    0,
                    false,
                )],
            },
            28,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "#5@28");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn quantifier() {
        let input = node(
            ExprCore::Quant {
                quantifier: Quantifier::Forall,
                bounds: vec![
                    Bound {
                        name: "y".to_owned(),
                        level: Level::Constant,
                        domain: BoundDomain::Domain(node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )),
                    },
                    Bound {
                        name: "z".to_owned(),
                        level: Level::Constant,
                        domain: BoundDomain::NoDomain,
                    },
                ],
                body: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Internal {
                                builtin: Builtin::Eq,
                            },
                            0,
                            false,
                        ),
                        args: vec![
                            node(
                                ExprCore::Opaque {
                                    name: "y".to_owned(),
                                },
                                0,
                                false,
                            ),
                            node(
                                ExprCore::Opaque {
                                    name: "x".to_owned(),
                                },
                                30,
                                false,
                            ),
                        ],
                    },
                    0,
                    false,
                ),
            },
            29,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "(Forall [y:Constant:#11 z:Constant] ($Eq #2 #12@30))@29"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn except_at() {
        let input = node(
            ExprCore::Except {
                function: node(
                    ExprCore::Opaque {
                        name: "x".to_owned(),
                    },
                    31,
                    false,
                ),
                specs: vec![
                    ExceptSpec {
                        trail: vec![
                            ExceptPoint::Apply(node(
                                ExprCore::Opaque {
                                    name: "S".to_owned(),
                                },
                                0,
                                false,
                            )),
                            ExceptPoint::Dot("a".to_owned()),
                        ],
                        value: node(
                            ExprCore::Apply {
                                operator: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::Plus,
                                    },
                                    0,
                                    false,
                                ),
                                args: vec![
                                    node(ExprCore::At { is_except: true }, 32, false),
                                    node(
                                        ExprCore::Num {
                                            integer: "1".to_owned(),
                                            fraction: "".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                ],
                            },
                            0,
                            false,
                        ),
                    },
                    ExceptSpec {
                        trail: vec![ExceptPoint::Dot("b".to_owned())],
                        value: node(
                            ExprCore::Quant {
                                quantifier: Quantifier::Exists,
                                bounds: vec![Bound {
                                    name: "w".to_owned(),
                                    level: Level::Constant,
                                    domain: BoundDomain::NoDomain,
                                }],
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Eq,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(
                                                ExprCore::Opaque {
                                                    name: "w".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                            node(ExprCore::At { is_except: true }, 0, false),
                                        ],
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                            false,
                        ),
                    },
                ],
            },
            33,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "(except (except #10@31 [#11 .a]=($Plus (dot (fcnapp #10@31 #11)@31 a)@31 1))@33 [.b]=(Exists [w:Constant] ($Eq #1 (dot (except #11@31 [#12 .a]=($Plus (dot (fcnapp #11@31 #12)@31 a)@31 1))@33 b)@33)))@33"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn at_outside_except() {
        let input = node(ExprCore::At { is_except: true }, 34, false);
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "@except@34");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn bang_number() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "G".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![node(
                            ExprCore::Opaque {
                                name: "x".to_owned(),
                            },
                            0,
                            false,
                        )],
                    },
                    0,
                    false,
                ),
                selectors: vec![Selector::Number(1)],
            },
            35,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "($Mem #10 #10)@35!");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn bang_label_path() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "I".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![],
                    },
                    0,
                    false,
                ),
                selectors: vec![Selector::Label {
                    label: "L".to_owned(),
                    args: vec![node(
                        ExprCore::Opaque {
                            name: "x".to_owned(),
                        },
                        0,
                        false,
                    )],
                }],
            },
            36,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "(#3@36 #10)@36");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn bang_label_path_constant() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "I".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![],
                    },
                    0,
                    false,
                ),
                selectors: vec![Selector::Label {
                    label: "K".to_owned(),
                    args: vec![],
                }],
            },
            37,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "#2@37");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn bang_label_path_builtin_args() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "I".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )],
                    },
                    0,
                    false,
                ),
                selectors: vec![Selector::Label {
                    label: "K".to_owned(),
                    args: vec![],
                }],
            },
            37,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "($Cup #11 #11 #11)@37");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn bang_unknown_number() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "H".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![],
                    },
                    0,
                    false,
                ),
                selectors: vec![Selector::Number(2)],
            },
            38,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"H\" not found|Expr.Anon: 1NUM|Failure(\"Expr.Anon: 1NUM\")"
        );
        assert_eq!(
            warnings,
            ["stderr: File \"M.tla\", line 38, characters 3-8:\nError: Operator \"H\" not found"]
        );
    }

    #[test]
    fn bang_unknown_down() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "H".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![],
                    },
                    0,
                    false,
                ),
                selectors: vec![Selector::Down],
            },
            38,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"H\" not found|Expr.Anon: 1DOWN|Failure(\"Expr.Anon: 1DOWN\")"
        );
        assert_eq!(
            warnings,
            ["stderr: File \"M.tla\", line 38, characters 3-8:\nError: Operator \"H\" not found"]
        );
    }

    #[test]
    fn bang_unknown_at() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "H".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![],
                    },
                    0,
                    false,
                ),
                selectors: vec![Selector::At],
            },
            38,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"H\" not found|Expr.Anon: 1AT|Failure(\"Expr.Anon: 1AT\")"
        );
        assert_eq!(
            warnings,
            ["stderr: File \"M.tla\", line 38, characters 3-8:\nError: Operator \"H\" not found"]
        );
    }

    #[test]
    fn bang_unknown_left() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "H".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![],
                    },
                    0,
                    false,
                ),
                selectors: vec![Selector::Left],
            },
            38,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"H\" not found|Expr.Anon: 1|Failure(\"Expr.Anon: 1\")"
        );
        assert_eq!(
            warnings,
            ["stderr: File \"M.tla\", line 38, characters 3-8:\nError: Operator \"H\" not found"]
        );
    }

    #[test]
    fn bang_unknown_instance() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "H".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![],
                    },
                    0,
                    false,
                ),
                selectors: vec![Selector::Instance(vec![node(
                    ExprCore::Opaque {
                        name: "x".to_owned(),
                    },
                    0,
                    false,
                )])],
            },
            38,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"H\" not found|Expr.Anon: 1INST|Failure(\"Expr.Anon: 1INST\")"
        );
        assert_eq!(
            warnings,
            ["stderr: File \"M.tla\", line 38, characters 3-8:\nError: Operator \"H\" not found"]
        );
    }

    #[test]
    fn bang_unknown_empty() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "H".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![],
                    },
                    0,
                    false,
                ),
                selectors: vec![],
            },
            39,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"H\" not found|Expr.Anon: 1EMPTY|Failure(\"Expr.Anon: 1EMPTY\")"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn bang_unknown_after_label() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "H".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![],
                    },
                    0,
                    false,
                ),
                selectors: vec![Selector::Label {
                    label: "M".to_owned(),
                    args: vec![],
                }],
            },
            39,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"H!M\" not found|Expr.Anon: 1EMPTY|Failure(\"Expr.Anon: 1EMPTY\")"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn bang_not_operator() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "x".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![],
                    },
                    0,
                    false,
                ),
                selectors: vec![Selector::Number(1)],
            },
            40,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|invalid subexpression reference|invalid subexpression reference|Failure(\"invalid subexpression reference\")"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn bang_bpragma() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "Zenon".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![],
                    },
                    0,
                    false,
                ),
                selectors: vec![],
            },
            40,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "$TRUE@40!");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn bang_wraps_opaque() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Opaque {
                        name: "G".to_owned(),
                    },
                    41,
                    false,
                ),
                selectors: vec![Selector::Number(2)],
            },
            42,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "(lambda [q] ($Eq #1 #10)@12)@42!");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn bang_bad_arg() {
        let input = node(
            ExprCore::Bang {
                expression: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "G".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![node(
                            ExprCore::Opaque {
                                name: "Nope".to_owned(),
                            },
                            43,
                            false,
                        )],
                    },
                    0,
                    false,
                ),
                selectors: vec![Selector::Number(1)],
            },
            42,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"Nope\" not found|Expr.Anon: 4|Failure(\"Expr.Anon: 4\")"
        );
        assert_eq!(
            warnings,
            [
                "stderr: File \"M.tla\", line 43, characters 3-8:\nError: Operator \"Nope\" not found"
            ]
        );
    }

    #[test]
    fn parens_syntax() {
        let input = node(
            ExprCore::Parens {
                expression: node(
                    ExprCore::Opaque {
                        name: "x".to_owned(),
                    },
                    0,
                    false,
                ),
                form: ParenForm::Syntax,
            },
            44,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "#10");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn parens_label() {
        let input = node(
            ExprCore::Parens {
                expression: node(
                    ExprCore::Opaque {
                        name: "x".to_owned(),
                    },
                    0,
                    false,
                ),
                form: ParenForm::Nlabel {
                    label: "lab".to_owned(),
                    names: vec!["x".to_owned(), "S".to_owned()],
                },
            },
            45,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "(parens #10 xlabel lab [x:10 S:11])@45");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn parens_label_unknown() {
        let input = node(
            ExprCore::Parens {
                expression: node(
                    ExprCore::Opaque {
                        name: "x".to_owned(),
                    },
                    0,
                    false,
                ),
                form: ParenForm::Nlabel {
                    label: "lab".to_owned(),
                    names: vec!["Q".to_owned()],
                },
            },
            45,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Identifier \"Q\" in label parameters not found|Identifier \"Q\" in label parameters not found|Failure(\"Identifier \\\"Q\\\" in label parameters not found\")"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn let_definitions() {
        let input = node(
            ExprCore::Let {
                definitions: vec![
                    defn(
                        DefnCore::Operator {
                            name: "f".to_owned(),
                            body: node(
                                ExprCore::Fcn {
                                    bounds: vec![Bound {
                                        name: "n".to_owned(),
                                        level: Level::Constant,
                                        domain: BoundDomain::Domain(node(
                                            ExprCore::Opaque {
                                                name: "S".to_owned(),
                                            },
                                            0,
                                            false,
                                        )),
                                    }],
                                    body: node(
                                        ExprCore::FcnApp {
                                            function: node(
                                                ExprCore::Opaque {
                                                    name: "f".to_owned(),
                                                },
                                                47,
                                                false,
                                            ),
                                            args: vec![node(
                                                ExprCore::Opaque {
                                                    name: "n".to_owned(),
                                                },
                                                0,
                                                false,
                                            )],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                46,
                                false,
                            ),
                        },
                        46,
                    ),
                    defn(
                        DefnCore::Operator {
                            name: "g".to_owned(),
                            body: node(
                                ExprCore::Fcn {
                                    bounds: vec![Bound {
                                        name: "n".to_owned(),
                                        level: Level::Constant,
                                        domain: BoundDomain::Domain(node(
                                            ExprCore::Opaque {
                                                name: "S".to_owned(),
                                            },
                                            0,
                                            false,
                                        )),
                                    }],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Plus,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "n".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "x".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                48,
                                false,
                            ),
                        },
                        0,
                    ),
                    defn(
                        DefnCore::Instance {
                            name: "Inst".to_owned(),
                            instance: InstanceDefinition {
                                args: Vec::new(),
                                module: "N".to_owned(),
                                substitutions: Vec::new(),
                                location: None,
                            },
                        },
                        0,
                    ),
                    defn(
                        DefnCore::Operator {
                            name: "h".to_owned(),
                            body: node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Opaque {
                                            name: "f".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![],
                                },
                                0,
                                false,
                            ),
                        },
                        0,
                    ),
                ],
                body: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Internal {
                                builtin: Builtin::Conj,
                            },
                            0,
                            false,
                        ),
                        args: vec![
                            node(
                                ExprCore::Opaque {
                                    name: "f".to_owned(),
                                },
                                0,
                                false,
                            ),
                            node(
                                ExprCore::Opaque {
                                    name: "g".to_owned(),
                                },
                                0,
                                false,
                            ),
                            node(
                                ExprCore::Opaque {
                                    name: "Inst!B".to_owned(),
                                },
                                0,
                                false,
                            ),
                            node(
                                ExprCore::Opaque {
                                    name: "h".to_owned(),
                                },
                                0,
                                false,
                            ),
                        ],
                    },
                    0,
                    false,
                ),
            },
            51,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            Some(vec![
                defn(
                    DefnCore::Operator {
                        name: "Inst!A".to_owned(),
                        body: node(
                            ExprCore::Opaque {
                                name: "x".to_owned(),
                            },
                            50,
                            false,
                        ),
                    },
                    49,
                ),
                defn(
                    DefnCore::Operator {
                        name: "Inst!B".to_owned(),
                        body: node(
                            ExprCore::Opaque {
                                name: "Inst!A".to_owned(),
                            },
                            0,
                            false,
                        ),
                    },
                    0,
                ),
            ]),
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "(let [(op f (choose f ($Eq@46 #1@46 (fcn [n:Constant:#12] (fcnapp #2@47 #1))@46)@46)@46)@46 (op g (fcn [n:Constant:#12] ($Plus #1 #12))@48) (op Inst!A #12@50)@49 (op Inst!B #1) (op h #4)] ($Conj #5 #4 #2 #1))@51"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn sequent_expression() {
        let input = node(
            ExprCore::Sequent {
                sequent: Sequent {
                    context: vec![
                        hyp_at(
                            HypCore::Fresh {
                                name: "y".to_owned(),
                                shape: 0,
                                level: Level::Constant,
                                domain: Some(node(
                                    ExprCore::Opaque {
                                        name: "S".to_owned(),
                                    },
                                    0,
                                    false,
                                )),
                                domain_visibility: Visibility::Visible,
                            },
                            52,
                        ),
                        hyp_at(
                            HypCore::Fact {
                                expression: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Mem,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(
                                                ExprCore::Opaque {
                                                    name: "y".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                            node(
                                                ExprCore::Opaque {
                                                    name: "S".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                        ],
                                    },
                                    0,
                                    false,
                                ),
                                visibility: Visibility::Visible,
                                time: Time::Now,
                                use_location: None,
                            },
                            53,
                        ),
                        hyp_at(
                            HypCore::Fact {
                                expression: node(
                                    ExprCore::Sub {
                                        modal: Modal::Box,
                                        action: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Prime,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Opaque {
                                                        name: "x".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                        subscript: node(
                                            ExprCore::Opaque {
                                                name: "x".to_owned(),
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                                visibility: Visibility::Visible,
                                time: Time::Now,
                                use_location: None,
                            },
                            0,
                        ),
                    ],
                    active: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(
                                    ExprCore::Opaque {
                                        name: "y".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                node(
                                    ExprCore::Opaque {
                                        name: "y".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                            ],
                        },
                        0,
                        false,
                    ),
                },
            },
            54,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "(sequent [(fresh y Constant 0 #11)@52 (fact Visible Always ($Mem #1 #12))@53 (fact Visible Always (sub Box ($Prime #12) #12))] ($Eq #3 #3))@54"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn choose_and_tquant() {
        let input = node(
            ExprCore::Choose {
                name: "c".to_owned(),
                domain: Some(node(
                    ExprCore::Opaque {
                        name: "S".to_owned(),
                    },
                    0,
                    false,
                )),
                body: node(
                    ExprCore::Tquant {
                        quantifier: Quantifier::Exists,
                        names: vec!["u".to_owned()],
                        body: node(
                            ExprCore::Apply {
                                operator: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::Eq,
                                    },
                                    0,
                                    false,
                                ),
                                args: vec![
                                    node(
                                        ExprCore::Opaque {
                                            name: "u".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    node(
                                        ExprCore::Opaque {
                                            name: "c".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                ],
                            },
                            0,
                            false,
                        ),
                    },
                    0,
                    false,
                ),
            },
            0,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(result, "(choose c:#11 (tExists [u] ($Eq #1 #2)))");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn defn_recursive_function() {
        let input = defn(
            DefnCore::Operator {
                name: "fact".to_owned(),
                body: node(
                    ExprCore::Fcn {
                        bounds: vec![Bound {
                            name: "n".to_owned(),
                            level: Level::Constant,
                            domain: BoundDomain::Domain(node(
                                ExprCore::Opaque {
                                    name: "S".to_owned(),
                                },
                                0,
                                false,
                            )),
                        }],
                        body: node(
                            ExprCore::FcnApp {
                                function: node(
                                    ExprCore::Opaque {
                                        name: "fact".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                args: vec![node(
                                    ExprCore::Opaque {
                                        name: "n".to_owned(),
                                    },
                                    0,
                                    false,
                                )],
                            },
                            0,
                            false,
                        ),
                    },
                    60,
                    false,
                ),
            },
            59,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .defn(host, scope, &input)
                    .map(|output| show_defn(&output))
            },
        );
        assert_eq!(
            result,
            "(op fact (choose fact ($Eq@60 #1@60 (fcn [n:Constant:#12] (fcnapp #2 #1))@60)@60)@60)@59"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn defn_plain() {
        let input = defn(
            DefnCore::Operator {
                name: "plain".to_owned(),
                body: node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "F".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![node(
                            ExprCore::Opaque {
                                name: "x".to_owned(),
                            },
                            0,
                            false,
                        )],
                    },
                    0,
                    false,
                ),
            },
            61,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .defn(host, scope, &input)
                    .map(|output| show_defn(&output))
            },
        );
        assert_eq!(result, "(op plain (#9 #10))@61");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn defn_untouched() {
        let input = defn(
            DefnCore::Bpragma {
                name: "P".to_owned(),
                body: node(
                    ExprCore::Opaque {
                        name: "Nope".to_owned(),
                    },
                    0,
                    false,
                ),
                methods: Vec::new(),
            },
            0,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .defn(host, scope, &input)
                    .map(|output| show_defn(&output))
            },
        );
        assert_eq!(result, "(bpragma P Nope)");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn sequent_hyps() {
        let input = Sequent {
            context: vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "a".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: Some(node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )),
                        domain_visibility: Visibility::Visible,
                    },
                    62,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "b".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "c".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "D".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Opaque {
                                                name: "F".to_owned(),
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![node(
                                            ExprCore::Opaque {
                                                name: "a".to_owned(),
                                            },
                                            0,
                                            false,
                                        )],
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fact {
                        expression: node(
                            ExprCore::Apply {
                                operator: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::Mem,
                                    },
                                    0,
                                    false,
                                ),
                                args: vec![
                                    node(
                                        ExprCore::Opaque {
                                            name: "a".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    node(
                                        ExprCore::Opaque {
                                            name: "x".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                ],
                            },
                            0,
                            false,
                        ),
                        visibility: Visibility::Visible,
                        time: Time::Now,
                        use_location: None,
                    },
                    63,
                ),
                hyp_at(
                    HypCore::Fact {
                        expression: node(
                            ExprCore::Apply {
                                operator: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::Prime,
                                    },
                                    0,
                                    false,
                                ),
                                args: vec![node(
                                    ExprCore::Opaque {
                                        name: "c".to_owned(),
                                    },
                                    0,
                                    false,
                                )],
                            },
                            0,
                            false,
                        ),
                        visibility: Visibility::Visible,
                        time: Time::Now,
                        use_location: None,
                    },
                    0,
                ),
            ],
            active: node(
                ExprCore::Apply {
                    operator: node(
                        ExprCore::Opaque {
                            name: "D".to_owned(),
                        },
                        0,
                        false,
                    ),
                    args: vec![],
                },
                0,
                false,
            ),
        };
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .sequent(host, scope, &input)
                    .map(|output| show_sequent(&output))
            },
        );
        assert_eq!(
            result,
            "(sequent [(fresh a Constant 0 #11)@62 (fresh b Constant 0) (flex c) (defn User Visible (op D (#12 #3))) (fact Visible Always ($Mem #4 #14))@63 (fact Visible Now ($Prime #3))] #3)"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn usable_defs() {
        let input = Usable {
            facts: vec![
                node(
                    ExprCore::Opaque {
                        name: "x".to_owned(),
                    },
                    64,
                    false,
                ),
                node(
                    ExprCore::Apply {
                        operator: node(
                            ExprCore::Opaque {
                                name: "F".to_owned(),
                            },
                            0,
                            false,
                        ),
                        args: vec![node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )],
                    },
                    0,
                    false,
                ),
            ],
            defs: vec![
                UseDef {
                    core: UseDefCore::Dvar {
                        name: "F".to_owned(),
                    },
                    location: locus(65),
                },
                UseDef {
                    core: UseDefCore::Dvar {
                        name: "x".to_owned(),
                    },
                    location: locus(66),
                },
                UseDef {
                    core: UseDefCore::Dvar {
                        name: "T".to_owned(),
                    },
                    location: locus(67),
                },
                UseDef {
                    core: UseDefCore::Dvar {
                        name: "Plus2".to_owned(),
                    },
                    location: None,
                },
                UseDef {
                    core: UseDefCore::Dx { index: 3 },
                    location: locus(68),
                },
                UseDef {
                    core: UseDefCore::Dvar {
                        name: "Zenon".to_owned(),
                    },
                    location: None,
                },
            ],
        };
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .usable(host, scope, &input)
                    .map(|output| show_usable(&output))
            },
        );
        assert_eq!(result, "facts [#10@64 (#9 #11)] defs [#9@65 #3@68 #1]");
        assert_eq!(
            warnings,
            [
                "toolbox: File \"M.tla\", line 66, characters 3-8 :\n\"x\" is not a definition and cannot be used in a DEF clause.",
                "stderr: File \"M.tla\", line 67, characters 3-8 :\nIgnored unexpandable identifier \"T\" in BY DEF.",
                "stderr: Ignored unexpandable identifier \"Plus2\" in BY DEF."
            ]
        );
    }

    #[test]
    fn usable_unknown_def() {
        let input = Usable {
            facts: vec![],
            defs: vec![UseDef {
                core: UseDefCore::Dvar {
                    name: "Nope".to_owned(),
                },
                location: locus(69),
            }],
        };
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .usable(host, scope, &input)
                    .map(|output| show_usable(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"Nope\" not found|Expr.Anon: 4|Failure(\"Expr.Anon: 4\")"
        );
        assert_eq!(
            warnings,
            [
                "stderr: File \"M.tla\", line 69, characters 3-8:\nError: Operator \"Nope\" not found"
            ]
        );
    }

    #[test]
    fn proof_all_steps() {
        let input = Proof {
            core: ProofCore::Steps {
                steps: vec![
                    Step {
                        core: StepCore::Assert {
                            sequent: Sequent {
                                context: vec![],
                                active: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Eq,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(
                                                ExprCore::Opaque {
                                                    name: "x".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                            node(
                                                ExprCore::Opaque {
                                                    name: "x".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                        ],
                                    },
                                    0,
                                    false,
                                ),
                            },
                            proof: Proof {
                                core: ProofCore::By {
                                    usable: Usable {
                                        facts: vec![node(
                                            ExprCore::Opaque {
                                                name: "<1>_a6".to_owned(),
                                            },
                                            71,
                                            false,
                                        )],
                                        defs: vec![],
                                    },
                                    is_only: false,
                                },
                                props: props(70, None),
                            },
                        },
                        props: props(70, Some(StepNumber::Unnamed { level: 1, id: 1 })),
                    },
                    Step {
                        core: StepCore::Assert {
                            sequent: Sequent {
                                context: vec![
                                    hyp_at(
                                        HypCore::Fresh {
                                            name: "y".to_owned(),
                                            shape: 0,
                                            level: Level::Constant,
                                            domain: Some(node(
                                                ExprCore::Opaque {
                                                    name: "S".to_owned(),
                                                },
                                                0,
                                                false,
                                            )),
                                            domain_visibility: Visibility::Visible,
                                        },
                                        0,
                                    ),
                                    hyp_at(
                                        HypCore::Fact {
                                            expression: node(
                                                ExprCore::Apply {
                                                    operator: node(
                                                        ExprCore::Internal {
                                                            builtin: Builtin::Mem,
                                                        },
                                                        0,
                                                        false,
                                                    ),
                                                    args: vec![
                                                        node(
                                                            ExprCore::Opaque {
                                                                name: "y".to_owned(),
                                                            },
                                                            0,
                                                            false,
                                                        ),
                                                        node(
                                                            ExprCore::Opaque {
                                                                name: "x".to_owned(),
                                                            },
                                                            0,
                                                            false,
                                                        ),
                                                    ],
                                                },
                                                0,
                                                false,
                                            ),
                                            visibility: Visibility::Visible,
                                            time: Time::Now,
                                            use_location: None,
                                        },
                                        0,
                                    ),
                                ],
                                active: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Eq,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(
                                                ExprCore::Opaque {
                                                    name: "y".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                            node(
                                                ExprCore::Opaque {
                                                    name: "y".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                        ],
                                    },
                                    0,
                                    false,
                                ),
                            },
                            proof: Proof {
                                core: ProofCore::By {
                                    usable: Usable {
                                        facts: vec![
                                            node(
                                                ExprCore::Opaque {
                                                    name: "y".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                            node(
                                                ExprCore::Opaque {
                                                    name: "<1>_a6".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                        ],
                                        defs: vec![UseDef {
                                            core: UseDefCore::Dvar {
                                                name: "<1>_a6".to_owned(),
                                            },
                                            location: locus(72),
                                        }],
                                    },
                                    is_only: false,
                                },
                                props: props(0, None),
                            },
                        },
                        props: props(
                            71,
                            Some(StepNumber::Named {
                                level: 1,
                                label: "a".to_owned(),
                                is_anonymous: false,
                            }),
                        ),
                    },
                    Step {
                        core: StepCore::Pcase {
                            expression: node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Internal {
                                            builtin: Builtin::Mem,
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![
                                        node(
                                            ExprCore::Opaque {
                                                name: "x".to_owned(),
                                            },
                                            0,
                                            false,
                                        ),
                                        node(
                                            ExprCore::Opaque {
                                                name: "S".to_owned(),
                                            },
                                            0,
                                            false,
                                        ),
                                    ],
                                },
                                0,
                                false,
                            ),
                            proof: Proof {
                                core: ProofCore::By {
                                    usable: Usable {
                                        facts: vec![
                                            node(
                                                ExprCore::Opaque {
                                                    name: "<1>a".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                            node(
                                                ExprCore::Opaque {
                                                    name: "<1>_a7".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                        ],
                                        defs: vec![],
                                    },
                                    is_only: false,
                                },
                                props: props(0, None),
                            },
                        },
                        props: props(73, Some(StepNumber::Unnamed { level: 1, id: 2 })),
                    },
                    Step {
                        core: StepCore::Suffices {
                            sequent: Sequent {
                                context: vec![hyp_at(
                                    HypCore::Fresh {
                                        name: "w".to_owned(),
                                        shape: 0,
                                        level: Level::Constant,
                                        domain: Some(node(
                                            ExprCore::Opaque {
                                                name: "S".to_owned(),
                                            },
                                            0,
                                            false,
                                        )),
                                        domain_visibility: Visibility::Visible,
                                    },
                                    0,
                                )],
                                active: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Eq,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(
                                                ExprCore::Opaque {
                                                    name: "w".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                            node(
                                                ExprCore::Opaque {
                                                    name: "x".to_owned(),
                                                },
                                                0,
                                                false,
                                            ),
                                        ],
                                    },
                                    0,
                                    false,
                                ),
                            },
                            proof: Proof {
                                core: ProofCore::By {
                                    usable: Usable {
                                        facts: vec![node(
                                            ExprCore::Opaque {
                                                name: "<1>s".to_owned(),
                                            },
                                            0,
                                            false,
                                        )],
                                        defs: vec![UseDef {
                                            core: UseDefCore::Dvar {
                                                name: "<1>s".to_owned(),
                                            },
                                            location: None,
                                        }],
                                    },
                                    is_only: false,
                                },
                                props: props(0, None),
                            },
                        },
                        props: props(
                            74,
                            Some(StepNumber::Named {
                                level: 1,
                                label: "s".to_owned(),
                                is_anonymous: false,
                            }),
                        ),
                    },
                    Step {
                        core: StepCore::Have {
                            expression: node(
                                ExprCore::Opaque {
                                    name: "x".to_owned(),
                                },
                                0,
                                false,
                            ),
                        },
                        props: props(75, Some(StepNumber::Unnamed { level: 1, id: 3 })),
                    },
                    Step {
                        core: StepCore::Take {
                            bounds: vec![
                                Bound {
                                    name: "t".to_owned(),
                                    level: Level::Constant,
                                    domain: BoundDomain::Domain(node(
                                        ExprCore::Opaque {
                                            name: "S".to_owned(),
                                        },
                                        0,
                                        false,
                                    )),
                                },
                                Bound {
                                    name: "u".to_owned(),
                                    level: Level::Constant,
                                    domain: BoundDomain::NoDomain,
                                },
                            ],
                        },
                        props: props(76, Some(StepNumber::Unnamed { level: 1, id: 4 })),
                    },
                    Step {
                        core: StepCore::Witness {
                            expressions: vec![
                                node(
                                    ExprCore::Opaque {
                                        name: "t".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                node(
                                    ExprCore::Opaque {
                                        name: "u".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                            ],
                        },
                        props: props(
                            77,
                            Some(StepNumber::Named {
                                level: 1,
                                label: "w".to_owned(),
                                is_anonymous: false,
                            }),
                        ),
                    },
                    Step {
                        core: StepCore::Pick {
                            bounds: vec![Bound {
                                name: "p".to_owned(),
                                level: Level::Constant,
                                domain: BoundDomain::Domain(node(
                                    ExprCore::Opaque {
                                        name: "S".to_owned(),
                                    },
                                    0,
                                    false,
                                )),
                            }],
                            expression: node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Internal {
                                            builtin: Builtin::Eq,
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![
                                        node(
                                            ExprCore::Opaque {
                                                name: "p".to_owned(),
                                            },
                                            0,
                                            false,
                                        ),
                                        node(
                                            ExprCore::Opaque {
                                                name: "t".to_owned(),
                                            },
                                            0,
                                            false,
                                        ),
                                    ],
                                },
                                0,
                                false,
                            ),
                            proof: Proof {
                                core: ProofCore::By {
                                    usable: Usable {
                                        facts: vec![node(
                                            ExprCore::Opaque {
                                                name: "<1>p".to_owned(),
                                            },
                                            0,
                                            false,
                                        )],
                                        defs: vec![],
                                    },
                                    is_only: false,
                                },
                                props: props(0, None),
                            },
                        },
                        props: props(
                            78,
                            Some(StepNumber::Named {
                                level: 1,
                                label: "p".to_owned(),
                                is_anonymous: false,
                            }),
                        ),
                    },
                    Step {
                        core: StepCore::Use {
                            usable: Usable {
                                facts: vec![
                                    node(
                                        ExprCore::Opaque {
                                            name: "<1>p".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    node(
                                        ExprCore::Opaque {
                                            name: "p".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                ],
                                defs: vec![UseDef {
                                    core: UseDefCore::Dvar {
                                        name: "F".to_owned(),
                                    },
                                    location: None,
                                }],
                            },
                            is_only: true,
                        },
                        props: props(79, Some(StepNumber::Unnamed { level: 1, id: 5 })),
                    },
                    Step {
                        core: StepCore::Hide {
                            usable: Usable {
                                facts: vec![node(
                                    ExprCore::Opaque {
                                        name: "<1>w".to_owned(),
                                    },
                                    0,
                                    false,
                                )],
                                defs: vec![UseDef {
                                    core: UseDefCore::Dvar {
                                        name: "<1>w".to_owned(),
                                    },
                                    location: None,
                                }],
                            },
                        },
                        props: props(80, Some(StepNumber::Unnamed { level: 1, id: 6 })),
                    },
                    Step {
                        core: StepCore::Define {
                            definitions: vec![defn(
                                DefnCore::Operator {
                                    name: "Loc".to_owned(),
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Plus,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "p".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "t".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                            )],
                        },
                        props: props(81, Some(StepNumber::Unnamed { level: 1, id: 7 })),
                    },
                    Step {
                        core: StepCore::Forget { count: 2 },
                        props: props(82, Some(StepNumber::Unnamed { level: 1, id: 8 })),
                    },
                ],
                qed: Box::new(QedStep {
                    proof: Proof {
                        core: ProofCore::By {
                            usable: Usable {
                                facts: vec![
                                    node(
                                        ExprCore::Opaque {
                                            name: "Loc".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    node(
                                        ExprCore::Opaque {
                                            name: "<1>a".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    node(
                                        ExprCore::Opaque {
                                            name: "<1>_a6".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    node(
                                        ExprCore::Opaque {
                                            name: "<0>top".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                ],
                                defs: vec![
                                    UseDef {
                                        core: UseDefCore::Dvar {
                                            name: "Loc".to_owned(),
                                        },
                                        location: None,
                                    },
                                    UseDef {
                                        core: UseDefCore::Dvar {
                                            name: "<1>s".to_owned(),
                                        },
                                        location: None,
                                    },
                                ],
                            },
                            is_only: false,
                        },
                        props: props(0, None),
                    },
                    props: props(0, Some(StepNumber::Unnamed { level: 1, id: 99 })),
                }),
            },
            props: props(
                83,
                Some(StepNumber::Named {
                    level: 0,
                    label: "top".to_owned(),
                    is_anonymous: false,
                }),
            ),
        };
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            5,
            |anonymizer, host, scope| {
                anonymizer
                    .proof(host, scope, &input)
                    .map(|output| show_proof(&output))
            },
        );
        assert_eq!(
            result,
            "(steps [(assert (sequent [] ($Eq #10 #10)) (by facts [$TRUE@71] defs [])@70){<1>_a6~}@70 (assert (sequent [(fresh y Constant 0 #13) (fact Visible Always ($Mem #1 #13))] ($Eq #2 #2)) (by facts [#5 #7] defs [#7@72])){<1>a}@71 (pcase ($Mem #14 #15) (by facts [#6 #2] defs [])){<1>_a7~}@73 (suffices (sequent [(fresh w Constant 0 #17)] ($Eq #1 #17)) (by facts [#2] defs [#2])){<1>s}@74 (have #20){<1>_a8~}@75 (take [t:Constant:#25 u:Constant]){<1>_a9~}@76 (witness #5 #4){<1>w}@77 (pick [p:Constant:#33] ($Eq #1 #9) (by facts [$TRUE] defs [])){<1>p}@78 (use only facts [#2 #5] defs [#38]){<1>#5}@79 (hide facts [#11] defs [#11]){<1>#6}@80 (define [(op Loc ($Plus #7 #17))]){<1>#7}@81 (forget 2){<1>_a10~}@82] qed{<1>#99} (by facts [#1 #30 #32 $TRUE] defs [#1 #24])){<0>top}@83"
        );
        assert_eq!(
            warnings,
            [
                "toolbox: File \"M.tla\", line 71, characters 3-8 :\nWarning: <1>_a6 does not introduce any assumptions. It does not make sense to use it here.\n",
                "toolbox: Warning: <1>p does not introduce any assumptions. It does not make sense to use it here.\n",
                "toolbox: Warning: <0>top does not introduce any assumptions. It does not make sense to use it here.\n"
            ]
        );
    }

    #[test]
    fn proof_instance_define() {
        let input = Proof {
            core: ProofCore::Steps {
                steps: vec![Step {
                    core: StepCore::Define {
                        definitions: vec![
                            defn(
                                DefnCore::Instance {
                                    name: "J".to_owned(),
                                    instance: InstanceDefinition {
                                        args: Vec::new(),
                                        module: "N".to_owned(),
                                        substitutions: Vec::new(),
                                        location: None,
                                    },
                                },
                                0,
                            ),
                            defn(
                                DefnCore::Operator {
                                    name: "Z".to_owned(),
                                    body: node(
                                        ExprCore::Opaque {
                                            name: "J!A".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                            ),
                        ],
                    },
                    props: props(0, Some(StepNumber::Unnamed { level: 1, id: 1 })),
                }],
                qed: Box::new(QedStep {
                    proof: Proof {
                        core: ProofCore::By {
                            usable: Usable {
                                facts: vec![node(
                                    ExprCore::Opaque {
                                        name: "Z".to_owned(),
                                    },
                                    0,
                                    false,
                                )],
                                defs: vec![UseDef {
                                    core: UseDefCore::Dvar {
                                        name: "J!A".to_owned(),
                                    },
                                    location: None,
                                }],
                            },
                            is_only: false,
                        },
                        props: props(0, None),
                    },
                    props: props(0, Some(StepNumber::Unnamed { level: 1, id: 99 })),
                }),
            },
            props: props(0, None),
        };
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            Some(vec![defn(
                DefnCore::Operator {
                    name: "J!A".to_owned(),
                    body: node(
                        ExprCore::Opaque {
                            name: "S".to_owned(),
                        },
                        0,
                        false,
                    ),
                },
                0,
            )]),
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .proof(host, scope, &input)
                    .map(|output| show_proof(&output))
            },
        );
        assert_eq!(
            result,
            "(steps [(define [(op J!A #11) (op Z #1)]){<1>#1}] qed{<1>#99} (by facts [#1] defs [#2]))"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn proof_missing_step_number() {
        let input = Proof {
            core: ProofCore::Steps {
                steps: vec![Step {
                    core: StepCore::Have {
                        expression: node(
                            ExprCore::Opaque {
                                name: "x".to_owned(),
                            },
                            0,
                            false,
                        ),
                    },
                    props: props(0, None),
                }],
                qed: Box::new(QedStep {
                    proof: Proof {
                        core: ProofCore::Obvious,
                        props: props(0, None),
                    },
                    props: props(0, Some(StepNumber::Unnamed { level: 1, id: 99 })),
                }),
            },
            props: props(0, None),
        };
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .proof(host, scope, &input)
                    .map(|output| show_proof(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Oops, this seems to be a bug in TLAPM.|-|Assert_failure"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn proof_error_in_step() {
        let input = Proof {
            core: ProofCore::Steps {
                steps: vec![Step {
                    core: StepCore::Have {
                        expression: node(
                            ExprCore::Opaque {
                                name: "Nope".to_owned(),
                            },
                            84,
                            false,
                        ),
                    },
                    props: props(0, Some(StepNumber::Unnamed { level: 1, id: 1 })),
                }],
                qed: Box::new(QedStep {
                    proof: Proof {
                        core: ProofCore::Obvious,
                        props: props(0, None),
                    },
                    props: props(0, Some(StepNumber::Unnamed { level: 1, id: 99 })),
                }),
            },
            props: props(0, None),
        };
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .proof(host, scope, &input)
                    .map(|output| show_proof(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"Nope\" not found|Expr.Anon: 4|Failure(\"Expr.Anon: 4\")"
        );
        assert_eq!(
            warnings,
            [
                "stderr: File \"M.tla\", line 84, characters 3-8:\nError: Operator \"Nope\" not found"
            ]
        );
    }

    #[test]
    fn proof_obvious() {
        let input = Proof {
            core: ProofCore::Obvious,
            props: props(85, None),
        };
        let (result, warnings) = run(Vec::new(), None, 0, |anonymizer, host, scope| {
            anonymizer
                .proof(host, scope, &input)
                .map(|output| show_proof(&output))
        });
        assert_eq!(result, "(obvious)@85");
        assert_eq!(warnings, Vec::<String>::new());
    }

    #[test]
    fn empty_scope_unknown() {
        let input = node(
            ExprCore::Opaque {
                name: "x".to_owned(),
            },
            86,
            false,
        );
        let (result, warnings) = run(vec![], None, 0, |anonymizer, host, scope| {
            anonymizer
                .expr(host, scope, &input)
                .map(|output| show_expr(&output))
        });
        assert_eq!(
            result,
            "ERR TlaProofError|Operator \"x\" not found|Expr.Anon: 4|Failure(\"Expr.Anon: 4\")"
        );
        assert_eq!(
            warnings,
            ["stderr: File \"M.tla\", line 86, characters 3-8:\nError: Operator \"x\" not found"]
        );
    }

    #[test]
    fn instance_without_expansion() {
        let input = node(
            ExprCore::Let {
                definitions: vec![defn(
                    DefnCore::Instance {
                        name: "K".to_owned(),
                        instance: InstanceDefinition {
                            args: Vec::new(),
                            module: "N".to_owned(),
                            substitutions: Vec::new(),
                            location: None,
                        },
                    },
                    0,
                )],
                body: node(
                    ExprCore::Opaque {
                        name: "x".to_owned(),
                    },
                    0,
                    false,
                ),
            },
            0,
            false,
        );
        let (result, warnings) = run(
            vec![
                hyp_at(
                    HypCore::Fresh {
                        name: "S".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Fresh {
                        name: "x".to_owned(),
                        shape: 0,
                        level: Level::Constant,
                        domain: None,
                        domain_visibility: Visibility::Visible,
                    },
                    2,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "F".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "p".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Mem,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                    node(ExprCore::Ix { index: 3 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    3,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "Plus2".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![
                                            Param {
                                                name: "a".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                            Param {
                                                name: "b".to_owned(),
                                                shape: 0,
                                                location: None,
                                            },
                                        ],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Plus,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(ExprCore::Ix { index: 2 }, 0, false),
                                                    node(ExprCore::Ix { index: 1 }, 0, false),
                                                ],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "T".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    7,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Recursive {
                                name: "R".to_owned(),
                                shape: 1,
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Flex {
                        name: "v".to_owned(),
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "G".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "q".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Conj,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Mem,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 7 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        11,
                                                        false,
                                                    ),
                                                    node(
                                                        ExprCore::Apply {
                                                            operator: node(
                                                                ExprCore::Internal {
                                                                    builtin: Builtin::Eq,
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                            args: vec![
                                                                node(
                                                                    ExprCore::Ix { index: 1 },
                                                                    0,
                                                                    false,
                                                                ),
                                                                node(
                                                                    ExprCore::Ix { index: 6 },
                                                                    0,
                                                                    false,
                                                                ),
                                                            ],
                                                        },
                                                        12,
                                                        false,
                                                    ),
                                                ],
                                            },
                                            10,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    9,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!L".to_owned(),
                                body: node(
                                    ExprCore::Lambda {
                                        params: vec![Param {
                                            name: "r".to_owned(),
                                            shape: 0,
                                            location: None,
                                        }],
                                        body: node(
                                            ExprCore::Apply {
                                                operator: node(
                                                    ExprCore::Internal {
                                                        builtin: Builtin::Neg,
                                                    },
                                                    0,
                                                    false,
                                                ),
                                                args: vec![node(
                                                    ExprCore::Ix { index: 1 },
                                                    0,
                                                    false,
                                                )],
                                            },
                                            0,
                                            false,
                                        ),
                                    },
                                    0,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Operator {
                                name: "I!K".to_owned(),
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(
                                            ExprCore::Internal {
                                                builtin: Builtin::Cup,
                                            },
                                            0,
                                            false,
                                        ),
                                        args: vec![
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                            node(ExprCore::Ix { index: 9 }, 0, false),
                                        ],
                                    },
                                    14,
                                    false,
                                ),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
                hyp_at(
                    HypCore::Defn {
                        definition: defn(
                            DefnCore::Bpragma {
                                name: "Zenon".to_owned(),
                                body: node(
                                    ExprCore::Internal {
                                        builtin: Builtin::TRUE,
                                    },
                                    0,
                                    false,
                                ),
                                methods: Vec::new(),
                            },
                            0,
                        ),
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Visible,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    0,
                ),
            ],
            None,
            0,
            |anonymizer, host, scope| {
                anonymizer
                    .expr(host, scope, &input)
                    .map(|output| show_expr(&output))
            },
        );
        assert_eq!(
            result,
            "ERR TlaProofError|Oops, this seems to be a bug in TLAPM.|-|Assert_failure"
        );
        assert_eq!(warnings, Vec::<String>::new());
    }
}
