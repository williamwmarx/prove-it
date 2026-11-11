//! A port of tlapm's Proof.Simplify, which rewrites each proof into the steps Proof.Gen handles:
//! BY becomes USE steps and an OBVIOUS QED, and HAVE, TAKE, WITNESS, CASE and PICK become
//! assertions.
//! A port of `src/obligations/simplify.ts`.

use std::rc::Rc;

use crate::equality::is_equal_expr;
use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, BoundDomain, Builtin, DefnCore, Expr, ExprCore, ExprNode, ExprProps, Hyp, HypCore,
    HypNode, Level, Quantifier, Sequent, Time, Visibility, WhereDefined, apply_builtin, at,
    at_expr, at_props, expr, get_fact, get_hyp_name, hyp, is_builtin_apply, map_accumulate,
    map_bound_domains, map_children, strip_props, to_index,
};
use crate::format::{FormatArg, format, render_doc};
use crate::generate::{at_nowhere, get_true, prove_assertion, use_assertion};
use crate::ocaml::succ;
use crate::printer::print_expression;
use crate::proof::{
    Counter, Omission, Proof, ProofCore, ProofProps, QedStep, Step, StepCore, StepNumber, Usable,
    UseDefCore, get_unique,
};
use crate::substitution::{
    cons_substitution, normalize_apply, shift, shift_expr, substitute_bounds, substitute_expr,
};

/// tlapm builds nodes with x @@ step, which copies all of the step's properties.
fn get_props(from: &ProofProps) -> ProofProps {
    ProofProps {
        location: from.location.clone(),
        step: from.step.clone(),
        method: from.method.clone(),
        ..ProofProps::default()
    }
}

/// The properties `at` takes from a step: its location.
fn get_step_expr_props(from: &ProofProps) -> ExprProps {
    ExprProps {
        location: from.location.clone(),
        is_atomic: false,
    }
}

fn get_level(step: Option<&StepNumber>) -> i64 {
    match step {
        Some(StepNumber::Named { level, .. } | StepNumber::Unnamed { level, .. }) => *level,
        None => 0,
    }
}

/// `isBinary`: the two arguments when the expression applies the builtin to two.
fn is_binary(expression: &ExprNode, builtin: Builtin) -> Option<(&Expr, &Expr)> {
    match is_builtin_apply(expression, builtin)? {
        [left, right] => Some((left, right)),
        _ => None,
    }
}

fn get_message(pattern: &str, args: Vec<FormatArg>) -> Result<String> {
    render_doc(&format(pattern, args), 68)
}

/// Visit.hyps_of_bounds_unditto: dittos repeat the previous domain, and each domain shifts past the
/// names bound before it.
fn get_bound_hyps(bounds: &[Bound]) -> Result<Vec<Hyp>> {
    expand_dittoes(bounds)
        .iter()
        .enumerate()
        .map(|(index, bound)| {
            let domain = match &bound.domain {
                BoundDomain::Domain(expression) => Some(shift_expr(to_index(index), expression)?),
                _ => None,
            };
            Ok(hyp(HypCore::Fresh {
                name: bound.name.clone(),
                shape: 0,
                level: if domain.is_some() {
                    Level::Constant
                } else {
                    bound.level
                },
                domain,
                domain_visibility: Visibility::Visible,
            }))
        })
        .collect()
}

fn expand_dittoes(bounds: &[Bound]) -> Vec<Bound> {
    let mut domain = BoundDomain::NoDomain;
    bounds
        .iter()
        .map(|bound| {
            if matches!(bound.domain, BoundDomain::Ditto) {
                return Bound {
                    domain: domain.clone(),
                    ..bound.clone()
                };
            }
            domain = bound.domain.clone();
            bound.clone()
        })
        .collect()
}

/// The bounds after a witnessed one, where a ditto takes the witnessed domain.
fn get_remaining_bounds(first: &Bound, rest: &[Bound]) -> Result<Vec<Bound>> {
    let mut shifted = substitute_bounds(&shift(1), rest)?.1;
    if let (Some(head), BoundDomain::Domain(expression)) = (shifted.first_mut(), &first.domain)
        && matches!(head.domain, BoundDomain::Ditto)
    {
        head.domain = BoundDomain::Domain(shift_expr(1, expression)?);
    }
    Ok(shifted)
}

/// A WITNESS proves each membership and subset it relies on, then the goal from them.
fn get_witness_proof(step: &Step, side_facts: &[Expr]) -> Result<Proof> {
    if side_facts.is_empty() {
        return Ok(Proof {
            core: ProofCore::Obvious,
            props: get_props(&step.props),
        });
    }
    let steps = side_facts
        .iter()
        .enumerate()
        .map(|(index, item)| {
            let active = shift_expr(to_index(2 * index + 2), item)?;
            Ok(Step {
                core: StepCore::Assert {
                    proof: Proof {
                        core: ProofCore::By {
                            usable: Usable {
                                facts: vec![shift_expr(3, &active)?],
                                defs: Vec::new(),
                            },
                            is_only: false,
                        },
                        props: ProofProps {
                            location: item.location.clone(),
                            method: step.props.method.clone(),
                            ..ProofProps::default()
                        },
                    },
                    sequent: Sequent {
                        context: Vec::new(),
                        active,
                    },
                },
                props: ProofProps {
                    location: item.location.clone(),
                    ..ProofProps::default()
                },
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let from = get_step_expr_props(&step.props);
    let count = side_facts.len();
    let facts = std::iter::once(to_index(2 * count + 2))
        .chain((0..count).map(|index| to_index(2 * (count - index))))
        .map(|index| at_props(ExprCore::Ix { index }, &from))
        .collect();
    // tlapm removes the method from the QED.
    let qed_proof = Proof {
        core: ProofCore::By {
            usable: Usable {
                facts,
                defs: Vec::new(),
            },
            is_only: true,
        },
        props: ProofProps {
            method: None,
            ..get_props(&step.props)
        },
    };
    let qed_location = qed_proof.props.location.clone();
    Ok(Proof {
        core: ProofCore::Steps {
            steps,
            qed: Box::new(QedStep {
                proof: qed_proof,
                props: ProofProps {
                    location: qed_location,
                    ..ProofProps::default()
                },
            }),
        },
        props: get_props(&step.props),
    })
}

fn replace_at(expression: &Expr, replacement: &Expr) -> Result<Expr> {
    match expression.core {
        ExprCore::At { is_except: false } => {
            Ok(at_expr(&strip_props(replacement), &expression.props()))
        }
        _ => map_children(expression, &mut |inner| replace_at(inner, replacement)),
    }
}

/// `{...step, proof}` on a step that has a proof.
fn with_step_proof(step: &Step, proof: Proof) -> Step {
    let core = match &step.core {
        StepCore::Assert { sequent, .. } => StepCore::Assert {
            sequent: sequent.clone(),
            proof,
        },
        StepCore::Suffices { sequent, .. } => StepCore::Suffices {
            sequent: sequent.clone(),
            proof,
        },
        StepCore::Pcase { expression, .. } => StepCore::Pcase {
            expression: expression.clone(),
            proof,
        },
        StepCore::Pick {
            bounds, expression, ..
        } => StepCore::Pick {
            bounds: bounds.clone(),
            expression: expression.clone(),
            proof,
        },
        other => other.clone(),
    };
    Step {
        core,
        props: step.props.clone(),
    }
}

fn get_step_proof(step: &Step) -> Option<&Proof> {
    match &step.core {
        StepCore::Assert { proof, .. }
        | StepCore::Suffices { proof, .. }
        | StepCore::Pcase { proof, .. }
        | StepCore::Pick { proof, .. } => Some(proof),
        _ => None,
    }
}

/// What `stripBounds` gives: the side facts and the goal left, or an error message.
enum Stripped {
    Goal { side_facts: Vec<Expr>, goal: Expr },
    Error(String),
}

/// `createSimplifier`: the simplifier shares the counter with anonymization.
pub struct Simplifier {
    counter: Rc<Counter>,
}

pub fn create_simplifier(counter: Rc<Counter>) -> Simplifier {
    Simplifier { counter }
}

impl Simplifier {
    fn get_anonymous(&self, level: i64) -> StepNumber {
        StepNumber::Named {
            level,
            label: format!("_a{}", get_unique(&self.counter)),
            is_anonymous: true,
        }
    }

    fn renumber_number(&self, level: i64, step: Option<&StepNumber>) -> StepNumber {
        match step {
            Some(StepNumber::Named {
                label,
                is_anonymous,
                ..
            }) => StepNumber::Named {
                level,
                label: label.clone(),
                is_anonymous: *is_anonymous,
            },
            _ => self.get_anonymous(level),
        }
    }

    fn renumber(&self, level: i64, proof: &Proof) -> Proof {
        let props = ProofProps {
            step: Some(self.renumber_number(level, proof.props.step.as_ref())),
            ..proof.props.clone()
        };
        let ProofCore::Steps { steps, qed } = &proof.core else {
            return Proof {
                core: proof.core.clone(),
                props,
            };
        };
        let steps = steps
            .iter()
            .map(|step| self.renumber_step(level, step))
            .collect();
        let qed = QedStep {
            proof: self.renumber(succ(level), &qed.proof),
            props: qed.props.clone(),
        };
        Proof {
            core: ProofCore::Steps {
                steps,
                qed: Box::new(qed),
            },
            props,
        }
    }

    fn renumber_step(&self, level: i64, step: &Step) -> Step {
        let renumbered = Step {
            core: step.core.clone(),
            props: ProofProps {
                step: Some(self.renumber_number(level, step.props.step.as_ref())),
                ..step.props.clone()
            },
        };
        match get_step_proof(&renumbered) {
            Some(proof) => {
                let proof = self.renumber(succ(level), proof);
                with_step_proof(&renumbered, proof)
            }
            None => renumbered,
        }
    }

    fn expose_connective(&self, context: &[Hyp], goal: &Expr) -> Result<Expr> {
        let head = match &goal.core {
            ExprCore::Apply { operator, .. } => operator,
            _ => goal,
        };
        if let ExprCore::Ix { index } = head.core {
            let hyp = to_index(context.len())
                .checked_sub(index)
                .and_then(|position| usize::try_from(position).ok())
                .and_then(|position| context.get(position));
            let Some(hyp) = hyp else {
                return Err(ObligationError::proof("expose_connective"));
            };
            let HypCore::Defn { definition, .. } = &hyp.core else {
                return Ok(goal.clone());
            };
            let DefnCore::Operator { body, .. } = &definition.core else {
                return Ok(goal.clone());
            };
            let body = shift_expr(index, body)?;
            let ExprCore::Apply { args, .. } = &goal.core else {
                return self.expose_connective(context, &body);
            };
            let operator: Expr = Rc::new(ExprNode {
                core: body.core.clone(),
                location: goal.location.clone(),
                is_atomic: body.is_atomic,
            });
            let applied = at(normalize_apply(&operator, args.clone())?, &operator);
            return self.expose_connective(context, &applied);
        }
        if let Some([argument, ..]) = is_builtin_apply(goal, Builtin::Prime) {
            let inner = self.expose_connective(context, argument)?;
            let prime = |expression: &Expr| {
                apply_builtin(
                    Builtin::Prime,
                    vec![expression.clone()],
                    &expression.props(),
                )
            };
            if let ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } = &inner.core
            {
                return Ok(at(
                    ExprCore::Quant {
                        quantifier: *quantifier,
                        bounds: map_bound_domains(bounds, &mut |domain| Ok(prime(domain)))?,
                        body: prime(body),
                    },
                    goal,
                ));
            }
            let binary =
                is_binary(&inner, Builtin::Implies).or_else(|| is_binary(&inner, Builtin::Mem));
            if let (ExprCore::Apply { operator, .. }, Some((left, right))) = (&inner.core, binary) {
                return Ok(at(
                    ExprCore::Apply {
                        operator: operator.clone(),
                        args: vec![prime(left), prime(right)],
                    },
                    goal,
                ));
            }
            return Ok(prime(&inner));
        }
        if let ExprCore::Parens { expression, .. } = &goal.core {
            return self.expose_connective(context, expression);
        }
        Ok(goal.clone())
    }

    /// at_expand: @ in a step stands for the right side of the previous step's assertion.
    fn expand_at(&self, proof: &Proof) -> Result<Proof> {
        let ProofCore::Steps {
            steps: original,
            qed,
        } = &proof.core
        else {
            return Ok(proof.clone());
        };
        let mut steps: Vec<Step> = Vec::new();
        for step in original {
            let right = steps.last().and_then(get_right_operand);
            let (StepCore::Assert { sequent, proof }, Some(right)) = (&step.core, right) else {
                steps.push(step.clone());
                continue;
            };
            let active = replace_at(&sequent.active, &shift_expr(2, &right)?)?;
            steps.push(Step {
                core: StepCore::Assert {
                    sequent: Sequent {
                        context: sequent.context.clone(),
                        active,
                    },
                    proof: proof.clone(),
                },
                props: step.props.clone(),
            });
        }
        Ok(Proof {
            core: ProofCore::Steps {
                steps,
                qed: qed.clone(),
            },
            props: proof.props.clone(),
        })
    }

    pub fn simplify(
        &self,
        context: &[Hyp],
        goal: &Expr,
        original: &Proof,
        time: Time,
    ) -> Result<Proof> {
        let proof = self.expand_at(original)?;
        match &proof.core {
            ProofCore::Obvious | ProofCore::Omitted(_) | ProofCore::Error(_) => Ok(proof),
            ProofCore::By { usable, is_only } => {
                let mut cores = Vec::new();
                if !usable.defs.is_empty() {
                    cores.push((
                        StepCore::Use {
                            usable: Usable {
                                facts: Vec::new(),
                                defs: usable.defs.clone(),
                            },
                            is_only: false,
                        },
                        ProofProps {
                            location: proof.props.location.clone(),
                            ..ProofProps::default()
                        },
                    ));
                }
                for (index, fact) in usable.facts.iter().enumerate() {
                    cores.push((
                        StepCore::Use {
                            usable: Usable {
                                facts: vec![shift_expr(to_index(index), fact)?],
                                defs: Vec::new(),
                            },
                            is_only: false,
                        },
                        ProofProps {
                            location: fact.location.clone(),
                            use_location: proof.props.location.clone(),
                            ..ProofProps::default()
                        },
                    ));
                }
                if *is_only {
                    cores.push((
                        StepCore::Forget {
                            count: usable.facts.len(),
                        },
                        ProofProps {
                            location: proof.props.location.clone(),
                            ..ProofProps::default()
                        },
                    ));
                }
                let level = get_level(proof.props.step.as_ref());
                let steps = cores
                    .into_iter()
                    .map(|(core, props)| Step {
                        core,
                        props: ProofProps {
                            step: Some(self.get_anonymous(level)),
                            ..props
                        },
                    })
                    .collect();
                let qed_step = self.get_anonymous(level);
                let qed_proof = Proof {
                    core: ProofCore::Obvious,
                    props: ProofProps {
                        location: proof.props.location.clone(),
                        step: Some(qed_step.clone()),
                        method: proof.props.method.clone(),
                        ..ProofProps::default()
                    },
                };
                Ok(Proof {
                    core: ProofCore::Steps {
                        steps,
                        qed: Box::new(QedStep {
                            props: ProofProps {
                                location: qed_proof.props.location.clone(),
                                step: Some(qed_step),
                                ..ProofProps::default()
                            },
                            proof: qed_proof,
                        }),
                    },
                    props: ProofProps {
                        location: proof.props.location.clone(),
                        step: proof.props.step.clone(),
                        ..ProofProps::default()
                    },
                })
            }
            ProofCore::Steps { steps, qed } => {
                let ((inner_context, inner_goal, inner_time), steps) = map_accumulate(
                    (context.to_vec(), goal.clone(), time),
                    steps,
                    |(context, goal, time), step| {
                        let (next_context, next_goal, simplified, next_time) =
                            self.simplify_step(&context, &goal, step, time)?;
                        Ok(((next_context, next_goal, next_time), simplified))
                    },
                )?;
                let qed_proof =
                    self.simplify(&inner_context, &inner_goal, &qed.proof, inner_time)?;
                Ok(Proof {
                    core: ProofCore::Steps {
                        steps: steps.into_iter().flatten().collect(),
                        qed: Box::new(QedStep {
                            proof: qed_proof,
                            props: qed.props.clone(),
                        }),
                    },
                    props: proof.props.clone(),
                })
            }
        }
    }

    fn simplify_step(
        &self,
        context: &[Hyp],
        goal: &Expr,
        step: &Step,
        time: Time,
    ) -> Result<(Vec<Hyp>, Expr, Vec<Step>, Time)> {
        let level = get_level(step.props.step.as_ref());
        match &step.core {
            StepCore::Forget { .. } => {
                Ok((context.to_vec(), goal.clone(), vec![step.clone()], time))
            }
            StepCore::Assert { sequent, proof } => {
                let (inner, inner_time) = prove_assertion(context, sequent, step, time)?;
                let simplified = with_step_proof(
                    step,
                    self.simplify(&inner.context, &inner.active, proof, inner_time)?,
                );
                let next = use_assertion(false, context, goal, sequent, &simplified, time)?;
                Ok((next.context, next.active, vec![simplified], time))
            }
            StepCore::Suffices { sequent, proof } => {
                let inner = use_assertion(true, context, goal, sequent, step, time)?;
                let simplified = with_step_proof(
                    step,
                    self.simplify(&inner.context, &inner.active, proof, time)?,
                );
                let (next, next_time) = prove_assertion(context, sequent, &simplified, time)?;
                Ok((next.context, next.active, vec![simplified], next_time))
            }
            StepCore::Use { usable, is_only } => {
                let by_proof = Proof {
                    core: ProofCore::By {
                        usable: usable.clone(),
                        is_only: *is_only,
                    },
                    props: ProofProps {
                        location: step.props.location.clone(),
                        step: step.props.step.clone(),
                        method: step.props.method.clone(),
                        ..ProofProps::default()
                    },
                };
                let simplified = self.simplify(context, goal, &by_proof, time)?;
                let ProofCore::Steps { steps, .. } = simplified.core else {
                    return Err(ObligationError::proof(
                        "simplifying BY does not produce a non-leaf proof!",
                    ));
                };
                let nowhere = at_nowhere();
                let assumed = usable.facts.iter().map(|_| {
                    get_fact(
                        nowhere.clone(),
                        Visibility::Visible,
                        time,
                        step.props.location.clone(),
                    )
                });
                Ok((
                    context.iter().cloned().chain(assumed).collect(),
                    shift_expr(to_index(usable.facts.len()), goal)?,
                    steps,
                    time,
                ))
            }
            StepCore::Hide { usable } => {
                let mut hidden = context.to_vec();
                for def in &usable.defs {
                    let UseDefCore::Dx { index } = def.core else {
                        return Err(ObligationError::proof("set_vis"));
                    };
                    let position = to_index(hidden.len())
                        .checked_sub(index)
                        .and_then(|position| usize::try_from(position).ok());
                    let found =
                        position.and_then(|position| Some((position, hidden.get(position)?)));
                    let replaced = match found {
                        Some((position, current))
                            if matches!(current.core, HypCore::Defn { .. }) =>
                        {
                            (position, hide_definition(current, step))
                        }
                        _ => {
                            let name = found.map_or("", |(_, current)| match current.core {
                                HypCore::Fact { .. } => "??? FACT ???",
                                _ => get_hyp_name(current).unwrap_or_default(),
                            });
                            return Err(ObligationError::proof(format!(
                                "USE DEF {name} invalid because {name} is not a defined operator"
                            )));
                        }
                    };
                    hidden[replaced.0] = replaced.1;
                }
                Ok((hidden, goal.clone(), vec![step.clone()], time))
            }
            StepCore::Define { definitions } => Ok((
                context
                    .iter()
                    .cloned()
                    .chain(definitions.iter().map(|definition| {
                        Rc::new(HypNode {
                            core: HypCore::Defn {
                                definition: definition.clone(),
                                where_defined: WhereDefined::Proof(time),
                                visibility: Visibility::Visible,
                                is_local: true,
                                is_constness_unset: false,
                            },
                            location: step.props.location.clone(),
                        })
                    }))
                    .collect(),
                shift_expr(to_index(definitions.len()), goal)?,
                vec![step.clone()],
                time,
            )),
            StepCore::Have { expression } => {
                let connective = self.expose_connective(context, goal)?;
                let implication = is_binary(&connective, Builtin::Implies);
                let sequent = Sequent {
                    context: vec![get_fact(
                        expression.clone(),
                        Visibility::Visible,
                        time,
                        step.props.location.clone(),
                    )],
                    active: match implication {
                        Some((_, right)) => shift_expr(1, right)?,
                        None => connective.clone(),
                    },
                };
                let proof = match implication {
                    Some(_) => Proof {
                        core: ProofCore::By {
                            usable: Usable {
                                facts: vec![at_props(
                                    ExprCore::Ix { index: 2 },
                                    &get_step_expr_props(&step.props),
                                )],
                                defs: Vec::new(),
                            },
                            is_only: true,
                        },
                        props: get_props(&step.props),
                    },
                    None => Proof {
                        core: ProofCore::Error(get_message(
                            "@.@[<v2>@[%s@ %s@]@,%a@]@.",
                            vec![
                                "Error: this HAVE step is applied to the following goal,".into(),
                                "which is not an implication:".into(),
                                print_expression(context, goal)?.into(),
                            ],
                        )?),
                        props: get_props(&step.props),
                    },
                };
                let suffices = self.renumber_step(
                    level,
                    &Step {
                        core: StepCore::Suffices { sequent, proof },
                        props: ProofProps {
                            location: step.props.location.clone(),
                            step: step.props.step.clone(),
                            ..ProofProps::default()
                        },
                    },
                );
                self.simplify_step(context, goal, &suffices, time)
            }
            StepCore::Take { bounds } => {
                let suffices = self.get_take_suffices(context, goal, step, bounds)?;
                self.simplify_step(context, goal, &self.renumber_step(level, &suffices), time)
            }
            StepCore::Witness { expressions } => {
                let suffices = self.get_witness_suffices(context, goal, step, expressions)?;
                self.simplify_step(context, goal, &self.renumber_step(level, &suffices), time)
            }
            StepCore::Pcase { expression, proof } => {
                let assertion = Step {
                    core: StepCore::Assert {
                        sequent: Sequent {
                            context: vec![get_fact(
                                expression.clone(),
                                Visibility::Visible,
                                time,
                                step.props.location.clone(),
                            )],
                            active: shift_expr(1, goal)?,
                        },
                        proof: proof.clone(),
                    },
                    props: get_props(&step.props),
                };
                self.simplify_step(context, goal, &self.renumber_step(level, &assertion), time)
            }
            StepCore::Pick {
                bounds,
                expression,
                proof,
            } => {
                let existential = at_props(
                    ExprCore::Quant {
                        quantifier: Quantifier::Exists,
                        bounds: bounds.clone(),
                        body: expression.clone(),
                    },
                    &get_step_expr_props(&step.props),
                );
                let salted = self.get_salted(step.props.step.as_ref(), "ex");
                let (assert_context, assert_goal, asserted, assert_time) = self.simplify_step(
                    context,
                    goal,
                    &Step {
                        core: StepCore::Assert {
                            sequent: Sequent {
                                context: Vec::new(),
                                active: existential.clone(),
                            },
                            proof: proof.clone(),
                        },
                        props: ProofProps {
                            step: Some(salted),
                            ..get_props(&step.props)
                        },
                    },
                    time,
                )?;
                let shifted = shift_expr(2, &existential)?;
                let ExprCore::Quant { bounds, body, .. } = &shifted.core else {
                    return Err(ObligationError::proof("Proof.Simplify.simplify_step/PICK"));
                };
                let mut hyps = get_bound_hyps(bounds)?;
                hyps.push(get_fact(
                    body.clone(),
                    Visibility::Visible,
                    assert_time,
                    body.location.clone(),
                ));
                let active = shift_expr(to_index(hyps.len()), &assert_goal)?;
                let (next_context, next_goal, sufficed, next_time) = self.simplify_step(
                    &assert_context,
                    &assert_goal,
                    &Step {
                        core: StepCore::Suffices {
                            sequent: Sequent {
                                context: hyps,
                                active,
                            },
                            proof: Proof {
                                core: ProofCore::Omitted(Omission::Elsewhere),
                                props: get_props(&step.props),
                            },
                        },
                        props: get_props(&step.props),
                    },
                    assert_time,
                )?;
                Ok((
                    next_context,
                    next_goal,
                    asserted.into_iter().chain(sufficed).collect(),
                    next_time,
                ))
            }
        }
    }

    fn get_salted(&self, step: Option<&StepNumber>, salt: &str) -> StepNumber {
        let label = match step {
            Some(StepNumber::Named { label, .. }) => label.as_str(),
            _ => "_a",
        };
        StepNumber::Named {
            level: get_level(step),
            label: format!("{label}{salt}{}", get_unique(&self.counter)),
            is_anonymous: false,
        }
    }

    fn strip_bounds(
        &self,
        context: &[Hyp],
        amount: isize,
        side_facts: Vec<Expr>,
        current: &Expr,
        rest: &[Bound],
    ) -> Result<Stripped> {
        let Some(bound) = rest.first() else {
            return Ok(Stripped::Goal {
                side_facts,
                goal: current.clone(),
            });
        };
        let exposed = self.expose_connective(context, current)?;
        let ExprCore::Quant {
            quantifier: Quantifier::Forall,
            bounds: exposed_bounds,
            body,
        } = &exposed.core
        else {
            return self.not_universal(context, current);
        };
        let Some(goal_bound) = exposed_bounds.first() else {
            return self.not_universal(context, current);
        };
        let goal_bounds = expand_dittoes(exposed_bounds).split_off(1);
        let domain = &bound.domain;
        let goal_domain = &goal_bound.domain;
        if let (BoundDomain::NoDomain, BoundDomain::Domain(goal_expression)) = (domain, goal_domain)
        {
            return Ok(Stripped::Error(get_message(
                "@.@[<b0>%s (%s)@ %s (%s \\in %a)@]@.",
                vec![
                    "Error: the TAKE argument".into(),
                    bound.name.as_str().into(),
                    "does not match the pattern".into(),
                    goal_bound.name.as_str().into(),
                    print_expression(context, goal_expression)?.into(),
                ],
            )?));
        }
        if let (BoundDomain::Domain(expression), BoundDomain::NoDomain) = (domain, goal_domain) {
            return Ok(Stripped::Error(get_message(
                "@.@[<b0>%s (%s \\in %a)@ %s (%s)@]@.",
                vec![
                    "Error: the TAKE argument".into(),
                    bound.name.as_str().into(),
                    print_expression(context, expression)?.into(),
                    "does not match the pattern".into(),
                    goal_bound.name.as_str().into(),
                ],
            )?));
        }
        let next_side_facts = match (domain, goal_domain) {
            (BoundDomain::Domain(expression), BoundDomain::Domain(goal_expression))
                if !is_equal_expr(expression, goal_expression) =>
            {
                std::iter::once(expr(ExprCore::Apply {
                    operator: expr(ExprCore::Internal {
                        builtin: Builtin::Subseteq,
                    }),
                    args: vec![goal_expression.clone(), expression.clone()],
                }))
                .chain(side_facts)
                .collect()
            }
            _ => side_facts,
        };
        if goal_bounds.is_empty() {
            return self.strip_bounds(context, 1, next_side_facts, body, &rest[1..]);
        }
        let shifted_bounds = if rest.len() == 1 {
            goal_bounds
                .iter()
                .map(|item| {
                    let mut shifted =
                        substitute_bounds(&shift(amount), std::slice::from_ref(item))?.1;
                    shifted.pop().ok_or_else(ObligationError::assert_failure)
                })
                .collect::<Result<Vec<_>>>()?
        } else {
            goal_bounds
        };
        self.strip_bounds(
            context,
            amount + 1,
            next_side_facts,
            &at(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: shifted_bounds,
                    body: body.clone(),
                },
                &exposed,
            ),
            &rest[1..],
        )
    }

    fn not_universal(&self, context: &[Hyp], current: &Expr) -> Result<Stripped> {
        Ok(Stripped::Error(get_message(
            "@.@[<v2>@[<b0>%s@ %s@]@,%a@]@.",
            vec![
                "Error: this TAKE step is applied to the following goal,".into(),
                "which is not a universal formula:".into(),
                print_expression(context, current)?.into(),
            ],
        )?))
    }

    fn get_take_suffices(
        &self,
        context: &[Hyp],
        goal: &Expr,
        step: &Step,
        take_bounds: &[Bound],
    ) -> Result<Step> {
        let bounds = expand_dittoes(take_bounds);
        let (side_facts, stripped_goal) =
            match self.strip_bounds(context, 1, Vec::new(), goal, &bounds)? {
                Stripped::Error(message) => {
                    return Ok(Step {
                        core: StepCore::Suffices {
                            sequent: Sequent {
                                context: vec![get_fact(
                                    get_true(&goal.props()),
                                    Visibility::Visible,
                                    Time::Now,
                                    step.props.location.clone(),
                                )],
                                active: goal.clone(),
                            },
                            proof: Proof {
                                core: ProofCore::Error(message),
                                props: get_props(&step.props),
                            },
                        },
                        props: get_props(&step.props),
                    });
                }
                Stripped::Goal { side_facts, goal } => (side_facts, goal),
            };
        let unique = side_facts.iter().enumerate().filter(|(index, item)| {
            side_facts
                .iter()
                .position(|other| is_equal_expr(item, other))
                == Some(*index)
        });
        let facts = std::iter::once(Ok(at_props(
            ExprCore::Ix { index: 2 },
            &get_step_expr_props(&step.props),
        )))
        .chain(unique.map(|(_, item)| shift_expr(2, item)))
        .collect::<Result<Vec<_>>>()?;
        Ok(Step {
            core: StepCore::Suffices {
                sequent: Sequent {
                    context: get_bound_hyps(&bounds)?,
                    active: stripped_goal,
                },
                proof: Proof {
                    core: ProofCore::By {
                        usable: Usable {
                            facts,
                            defs: Vec::new(),
                        },
                        is_only: true,
                    },
                    props: get_props(&step.props),
                },
            },
            props: get_props(&step.props),
        })
    }

    fn get_witness_suffices(
        &self,
        context: &[Hyp],
        goal: &Expr,
        step: &Step,
        expressions: &[Expr],
    ) -> Result<Step> {
        let mut side_facts: Vec<Expr> = Vec::new();
        let mut error = String::new();
        let mut current = goal.clone();
        for witness in expressions {
            let exposed = self.expose_connective(context, &current)?;
            let (first, rest, body) = match &exposed.core {
                ExprCore::Quant {
                    quantifier: Quantifier::Exists,
                    bounds,
                    body,
                } if !bounds.is_empty() => (&bounds[0], &bounds[1..], body),
                _ => {
                    if error.is_empty() {
                        error = get_message(
                            "@.@[<v2>@[<b0>%s@ %s@]@,%a@]@.",
                            vec![
                                "Error: this WITNESS step is applied to the following goal,".into(),
                                "which is not an existential formula:".into(),
                                print_expression(context, &exposed)?.into(),
                            ],
                        )?;
                    }
                    current = exposed;
                    break;
                }
            };
            let next = if rest.is_empty() {
                body.clone()
            } else {
                at(
                    ExprCore::Quant {
                        quantifier: Quantifier::Exists,
                        bounds: get_remaining_bounds(first, rest)?,
                        body: body.clone(),
                    },
                    &exposed,
                )
            };
            let mut value = witness.clone();
            if let BoundDomain::Domain(domain) = &first.domain {
                let membership = self.expose_connective(context, witness)?;
                if let Some((term, term_domain)) = is_binary(&membership, Builtin::Mem) {
                    if !is_equal_expr(term_domain, domain) {
                        side_facts.push(apply_builtin(
                            Builtin::Subseteq,
                            vec![term_domain.clone(), domain.clone()],
                            &term_domain.props(),
                        ));
                    }
                    value = term.clone();
                    side_facts.push(membership.clone());
                } else {
                    if error.is_empty() {
                        error = get_message(
                            "@.@[<b0>%s (%a)@ %s (%s \\in %a)@]@.",
                            vec![
                                "Error: the WITNESS argument".into(),
                                print_expression(context, &membership)?.into(),
                                "does not match the pattern".into(),
                                first.name.as_str().into(),
                                print_expression(context, domain)?.into(),
                            ],
                        )?;
                    }
                    value = membership;
                }
            }
            let unprimable =
                apply_builtin(Builtin::Unprimable, vec![value.clone()], &value.props());
            current = substitute_expr(&cons_substitution(unprimable, shift(0)), &next)?;
        }
        let proof = if error.is_empty() {
            get_witness_proof(step, &side_facts)?
        } else {
            Proof {
                core: ProofCore::Error(error),
                props: get_props(&step.props),
            }
        };
        Ok(Step {
            core: StepCore::Suffices {
                sequent: Sequent {
                    context: Vec::new(),
                    active: current,
                },
                proof,
            },
            props: get_props(&step.props),
        })
    }
}

/// `{...hyp, visibility: "Hidden", location: step.location}` on a definition.
fn hide_definition(current: &Hyp, step: &Step) -> Hyp {
    let core = match &current.core {
        HypCore::Defn {
            definition,
            where_defined,
            is_local,
            is_constness_unset,
            ..
        } => HypCore::Defn {
            definition: definition.clone(),
            where_defined: *where_defined,
            visibility: Visibility::Hidden,
            is_local: *is_local,
            is_constness_unset: *is_constness_unset,
        },
        other => other.clone(),
    };
    Rc::new(HypNode {
        core,
        location: step.props.location.clone(),
    })
}

fn get_right_operand(step: &Step) -> Option<Expr> {
    let StepCore::Assert { sequent, .. } = &step.core else {
        return None;
    };
    match &sequent.active.core {
        ExprCore::Apply { args, .. } if args.len() == 2 => Some(args[1].clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::errors::quote_json;
    use crate::expression::{Defn, Locus, Param, ParenForm};
    use crate::pragma::OldMethod;
    use crate::proof::UseDef;

    // The fixtures are the inputs `simplify.ts` received under Bun: those of `getObligations` on
    // small modules with proofs of every step kind, and hand-built ones for the error paths, methods
    // and atomic nodes. Each is `(case counter time context goal proof)` as an S-expression, and the
    // expected values are what the TypeScript returned for it: the simplified proof as the same kind
    // of S-expression, by its length and FNV-1a hash, and the counter after; or the error.

    #[derive(Debug)]
    enum Sexp {
        Atom(String),
        Text(String),
        List(Vec<Sexp>),
    }

    fn parse(source: &str) -> Sexp {
        let characters: Vec<char> = source.chars().collect();
        let mut position = 0;
        let parsed = parse_at(&characters, &mut position);
        skip_spaces(&characters, &mut position);
        assert_eq!(position, characters.len(), "trailing input");
        parsed
    }

    fn skip_spaces(characters: &[char], position: &mut usize) {
        while characters
            .get(*position)
            .is_some_and(|character| character.is_whitespace())
        {
            *position += 1;
        }
    }

    fn parse_at(characters: &[char], position: &mut usize) -> Sexp {
        skip_spaces(characters, position);
        match characters[*position] {
            '(' => {
                *position += 1;
                let mut items = Vec::new();
                loop {
                    skip_spaces(characters, position);
                    if characters[*position] == ')' {
                        *position += 1;
                        return Sexp::List(items);
                    }
                    items.push(parse_at(characters, position));
                }
            }
            '"' => {
                *position += 1;
                let mut text = String::new();
                loop {
                    let character = characters[*position];
                    *position += 1;
                    match character {
                        '"' => return Sexp::Text(text),
                        '\\' => {
                            let escaped = characters[*position];
                            *position += 1;
                            match escaped {
                                'n' => text.push('\n'),
                                'u' => {
                                    let digits: String =
                                        characters[*position..*position + 4].iter().collect();
                                    *position += 4;
                                    let code = u32::from_str_radix(&digits, 16).expect("hex");
                                    text.push(char::from_u32(code).expect("character"));
                                }
                                other => text.push(other),
                            }
                        }
                        other => text.push(other),
                    }
                }
            }
            _ => {
                let start = *position;
                while characters.get(*position).is_some_and(|character| {
                    !character.is_whitespace() && !"()".contains(*character)
                }) {
                    *position += 1;
                }
                Sexp::Atom(characters[start..*position].iter().collect())
            }
        }
    }

    fn items(sexp: &Sexp) -> &[Sexp] {
        match sexp {
            Sexp::List(items) => items,
            other => panic!("expected a list: {other:?}"),
        }
    }

    fn atom(sexp: &Sexp) -> &str {
        match sexp {
            Sexp::Atom(text) => text,
            other => panic!("expected an atom: {other:?}"),
        }
    }

    fn text(sexp: &Sexp) -> String {
        match sexp {
            Sexp::Text(text) => text.clone(),
            other => panic!("expected a string: {other:?}"),
        }
    }

    fn number<Number: std::str::FromStr>(sexp: &Sexp) -> Number {
        atom(sexp).parse().ok().expect("number")
    }

    fn boolean(sexp: &Sexp) -> bool {
        atom(sexp) == "true"
    }

    fn optional<Value>(sexp: &Sexp, read: impl Fn(&Sexp) -> Value) -> Option<Value> {
        match sexp {
            Sexp::Atom(text) if text == "_" => None,
            _ => Some(read(sexp)),
        }
    }

    fn list<Value>(sexp: &Sexp, read: impl Fn(&Sexp) -> Value) -> Vec<Value> {
        items(sexp).iter().map(read).collect()
    }

    /// `@line:column-line:column`, in M.tla.
    fn read_locus(sexp: &Sexp) -> Option<Locus> {
        optional(sexp, |sexp| {
            let numbers: Vec<u32> = atom(sexp)
                .trim_start_matches('@')
                .split(['-', ':'])
                .map(|part| part.parse().expect("line or column"))
                .collect();
            Locus {
                file: Rc::from("M.tla"),
                start_line: numbers[0],
                start_column: numbers[1],
                end_line: numbers[2],
                end_column: numbers[3],
            }
        })
    }

    const BUILTINS: [Builtin; 10] = [
        Builtin::TRUE,
        Builtin::Mem,
        Builtin::Eq,
        Builtin::Subseteq,
        Builtin::Conj,
        Builtin::SUBSET,
        Builtin::Implies,
        Builtin::Prime,
        Builtin::BoxTrue,
        Builtin::Unprimable,
    ];

    fn read_level(sexp: &Sexp) -> Level {
        match atom(sexp) {
            "Constant" => Level::Constant,
            "State" => Level::State,
            "Action" => Level::Action,
            "Temporal" => Level::Temporal,
            _ => Level::Unknown,
        }
    }

    fn read_visibility(sexp: &Sexp) -> Visibility {
        if atom(sexp) == "Visible" {
            Visibility::Visible
        } else {
            Visibility::Hidden
        }
    }

    fn read_time(sexp: &Sexp) -> Time {
        if atom(sexp) == "Now" {
            Time::Now
        } else {
            Time::Always
        }
    }

    fn read_bound(sexp: &Sexp) -> Bound {
        let fields = items(sexp);
        let domain = items(&fields[2]);
        Bound {
            name: text(&fields[0]),
            level: read_level(&fields[1]),
            domain: match atom(&domain[0]) {
                "Domain" => BoundDomain::Domain(read_expr(&domain[1])),
                "Ditto" => BoundDomain::Ditto,
                _ => BoundDomain::NoDomain,
            },
        }
    }

    fn read_expr(sexp: &Sexp) -> Expr {
        let mut fields = items(sexp);
        let is_atomic = matches!(fields.last(), Some(Sexp::Atom(text)) if text == "!");
        if is_atomic {
            fields = &fields[..fields.len() - 1];
        }
        let mut location = None;
        if let Some(Sexp::Atom(text)) = fields.last()
            && text.starts_with('@')
        {
            location = read_locus(&fields[fields.len() - 1]);
            fields = &fields[..fields.len() - 1];
        }
        let core = match atom(&fields[0]) {
            "Ix" => ExprCore::Ix {
                index: number(&fields[1]),
            },
            "Opaque" => ExprCore::Opaque {
                name: text(&fields[1]),
            },
            "Internal" => ExprCore::Internal {
                builtin: *BUILTINS
                    .iter()
                    .find(|builtin| builtin.name() == atom(&fields[1]))
                    .expect("builtin"),
            },
            "Apply" => ExprCore::Apply {
                operator: read_expr(&fields[1]),
                args: list(&fields[2], read_expr),
            },
            "Quant" => ExprCore::Quant {
                quantifier: if atom(&fields[1]) == "Forall" {
                    Quantifier::Forall
                } else {
                    Quantifier::Exists
                },
                bounds: list(&fields[2], read_bound),
                body: read_expr(&fields[3]),
            },
            "Lambda" => ExprCore::Lambda {
                params: list(&fields[1], |sexp| {
                    let param = items(sexp);
                    Param {
                        name: text(&param[0]),
                        shape: number(&param[1]),
                        location: read_locus(&param[2]),
                    }
                }),
                body: read_expr(&fields[2]),
            },
            "Sequent" => ExprCore::Sequent {
                sequent: read_sequent(&fields[1]),
            },
            "At" => ExprCore::At {
                is_except: boolean(&fields[1]),
            },
            "Parens" => ExprCore::Parens {
                expression: read_expr(&fields[1]),
                form: ParenForm::Syntax,
            },
            other => panic!("expression {other}"),
        };
        Rc::new(ExprNode {
            core,
            location,
            is_atomic,
        })
    }

    fn read_defn(sexp: &Sexp) -> Defn {
        let fields = items(sexp);
        assert_eq!(atom(&fields[0]), "Operator");
        Defn {
            core: DefnCore::Operator {
                name: text(&fields[1]),
                body: read_expr(&fields[2]),
            },
            location: read_locus(&fields[3]),
        }
    }

    fn read_where(sexp: &Sexp) -> WhereDefined {
        match sexp {
            Sexp::List(fields) => WhereDefined::Proof(read_time(&fields[1])),
            other if atom(other) == "User" => WhereDefined::User,
            _ => WhereDefined::Builtin,
        }
    }

    fn read_hyp(sexp: &Sexp) -> Hyp {
        let fields = items(sexp);
        let core = match atom(&fields[0]) {
            "Fresh" => HypCore::Fresh {
                name: text(&fields[1]),
                shape: number(&fields[2]),
                level: read_level(&fields[3]),
                domain: optional(&fields[4], read_expr),
                domain_visibility: read_visibility(&fields[5]),
            },
            "Flex" => HypCore::Flex {
                name: text(&fields[1]),
            },
            "Defn" => HypCore::Defn {
                definition: read_defn(&fields[1]),
                where_defined: read_where(&fields[2]),
                visibility: read_visibility(&fields[3]),
                is_local: boolean(&fields[4]),
                is_constness_unset: boolean(&fields[5]),
            },
            "Fact" => HypCore::Fact {
                expression: read_expr(&fields[1]),
                visibility: read_visibility(&fields[2]),
                time: read_time(&fields[3]),
                use_location: read_locus(&fields[4]),
            },
            other => panic!("hypothesis {other}"),
        };
        Rc::new(HypNode {
            core,
            location: read_locus(&fields[fields.len() - 1]),
        })
    }

    fn read_sequent(sexp: &Sexp) -> Sequent {
        let fields = items(sexp);
        Sequent {
            context: list(&fields[1], read_hyp),
            active: read_expr(&fields[2]),
        }
    }

    fn read_props(sexp: &Sexp) -> ProofProps {
        let fields = items(sexp);
        ProofProps {
            location: read_locus(&fields[1]),
            step: optional(&fields[2], |sexp| {
                let number_fields = items(sexp);
                if atom(&number_fields[0]) == "Named" {
                    StepNumber::Named {
                        level: number(&number_fields[1]),
                        label: text(&number_fields[2]),
                        is_anonymous: boolean(&number_fields[3]),
                    }
                } else {
                    StepNumber::Unnamed {
                        level: number(&number_fields[1]),
                        id: number(&number_fields[2]),
                    }
                }
            }),
            obligations: None,
            method: optional(&fields[3], |sexp| {
                let method = items(sexp);
                OldMethod {
                    name: text(&method[1]),
                    tactic: optional(&method[2], text),
                    timeout: optional(&method[3], number),
                }
            }),
            use_location: read_locus(&fields[4]),
        }
    }

    fn read_usable(sexp: &Sexp) -> Usable {
        let fields = items(sexp);
        Usable {
            facts: list(&fields[1], read_expr),
            defs: list(&fields[2], |sexp| {
                let def_fields = items(sexp);
                UseDef {
                    core: if atom(&def_fields[0]) == "Dx" {
                        UseDefCore::Dx {
                            index: number(&def_fields[1]),
                        }
                    } else {
                        UseDefCore::Dvar {
                            name: text(&def_fields[1]),
                        }
                    },
                    location: read_locus(&def_fields[2]),
                }
            }),
        }
    }

    fn read_proof(sexp: &Sexp) -> Proof {
        let fields = items(sexp);
        let core = match atom(&fields[0]) {
            "Obvious" => ProofCore::Obvious,
            "Omitted" => ProofCore::Omitted(match atom(&fields[1]) {
                "Implicit" => Omission::Implicit,
                "Explicit" => Omission::Explicit,
                _ => Omission::Elsewhere,
            }),
            "Error" => ProofCore::Error(text(&fields[1])),
            "By" => ProofCore::By {
                usable: read_usable(&fields[1]),
                is_only: boolean(&fields[2]),
            },
            "Steps" => ProofCore::Steps {
                steps: list(&fields[1], read_step),
                qed: Box::new(QedStep {
                    proof: read_proof(&fields[2]),
                    props: read_props(&fields[3]),
                }),
            },
            other => panic!("proof {other}"),
        };
        Proof {
            core,
            props: read_props(&fields[fields.len() - 1]),
        }
    }

    fn read_step(sexp: &Sexp) -> Step {
        let fields = items(sexp);
        let core = match atom(&fields[0]) {
            "Hide" => StepCore::Hide {
                usable: read_usable(&fields[1]),
            },
            "Define" => StepCore::Define {
                definitions: list(&fields[1], read_defn),
            },
            "Assert" => StepCore::Assert {
                sequent: read_sequent(&fields[1]),
                proof: read_proof(&fields[2]),
            },
            "Suffices" => StepCore::Suffices {
                sequent: read_sequent(&fields[1]),
                proof: read_proof(&fields[2]),
            },
            "Pcase" => StepCore::Pcase {
                expression: read_expr(&fields[1]),
                proof: read_proof(&fields[2]),
            },
            "Pick" => StepCore::Pick {
                bounds: list(&fields[1], read_bound),
                expression: read_expr(&fields[2]),
                proof: read_proof(&fields[3]),
            },
            "Use" => StepCore::Use {
                usable: read_usable(&fields[1]),
                is_only: boolean(&fields[2]),
            },
            "Have" => StepCore::Have {
                expression: read_expr(&fields[1]),
            },
            "Take" => StepCore::Take {
                bounds: list(&fields[1], read_bound),
            },
            "Witness" => StepCore::Witness {
                expressions: list(&fields[1], read_expr),
            },
            "Forget" => StepCore::Forget {
                count: number(&fields[1]),
            },
            other => panic!("step {other}"),
        };
        Step {
            core,
            props: read_props(&fields[fields.len() - 1]),
        }
    }

    // The writer of `emit.ts`'s S-expressions, whose strings escape spaces.

    fn str(value: &str) -> String {
        quote_json(value).replace(' ', "\\u0020")
    }

    fn node(parts: &[String]) -> String {
        format!("({})", parts.join(" "))
    }

    fn opt<Value: ?Sized>(value: Option<&Value>, emit: impl Fn(&Value) -> String) -> String {
        value.map_or_else(|| "_".to_owned(), emit)
    }

    fn emit_list<Value>(values: &[Value], emit: impl Fn(&Value) -> String) -> String {
        node(&values.iter().map(emit).collect::<Vec<_>>())
    }

    fn emit_locus(locus: Option<&Locus>) -> String {
        opt(locus, |locus| {
            format!(
                "@{}:{}-{}:{}",
                locus.start_line, locus.start_column, locus.end_line, locus.end_column
            )
        })
    }

    fn emit_bound(bound: &Bound) -> String {
        let domain = match &bound.domain {
            BoundDomain::Domain(expression) => node(&["Domain".into(), emit_expr(expression)]),
            BoundDomain::NoDomain => "(NoDomain)".into(),
            BoundDomain::Ditto => "(Ditto)".into(),
        };
        node(&[str(&bound.name), format!("{:?}", bound.level), domain])
    }

    fn emit_expr(expression: &Expr) -> String {
        let mut parts: Vec<String> = match &expression.core {
            ExprCore::Ix { index } => vec!["Ix".into(), index.to_string()],
            ExprCore::Opaque { name } => vec!["Opaque".into(), str(name)],
            ExprCore::Internal { builtin } => vec!["Internal".into(), builtin.name().into()],
            ExprCore::Apply { operator, args } => {
                vec![
                    "Apply".into(),
                    emit_expr(operator),
                    emit_list(args, emit_expr),
                ]
            }
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => vec![
                "Quant".into(),
                format!("{quantifier:?}"),
                emit_list(bounds, emit_bound),
                emit_expr(body),
            ],
            ExprCore::At { is_except } => vec!["At".into(), is_except.to_string()],
            ExprCore::Parens { expression, .. } => {
                vec!["Parens".into(), emit_expr(expression), "(Syntax)".into()]
            }
            other => panic!("expression {other:?}"),
        };
        if expression.location.is_some() {
            parts.push(emit_locus(expression.location.as_ref()));
        }
        if expression.is_atomic {
            parts.push("!".into());
        }
        node(&parts)
    }

    fn emit_defn(definition: &Defn) -> String {
        let DefnCore::Operator { name, body } = &definition.core else {
            panic!("definition {definition:?}");
        };
        node(&[
            "Operator".into(),
            str(name),
            emit_expr(body),
            emit_locus(definition.location.as_ref()),
        ])
    }

    fn emit_hyp(hyp: &Hyp) -> String {
        let location = emit_locus(hyp.location.as_ref());
        match &hyp.core {
            HypCore::Fresh {
                name,
                shape,
                level,
                domain,
                domain_visibility,
            } => node(&[
                "Fresh".into(),
                str(name),
                shape.to_string(),
                format!("{level:?}"),
                opt(domain.as_ref(), emit_expr),
                format!("{domain_visibility:?}"),
                location,
            ]),
            HypCore::Fact {
                expression,
                visibility,
                time,
                use_location,
            } => node(&[
                "Fact".into(),
                emit_expr(expression),
                format!("{visibility:?}"),
                format!("{time:?}"),
                emit_locus(use_location.as_ref()),
                location,
            ]),
            other => panic!("hypothesis {other:?}"),
        }
    }

    fn emit_sequent(sequent: &Sequent) -> String {
        node(&[
            "sequent".into(),
            emit_list(&sequent.context, emit_hyp),
            emit_expr(&sequent.active),
        ])
    }

    fn emit_props(props: &ProofProps) -> String {
        assert!(props.obligations.is_none());
        node(&[
            "props".into(),
            emit_locus(props.location.as_ref()),
            opt(props.step.as_ref(), |step| match step {
                StepNumber::Named {
                    level,
                    label,
                    is_anonymous,
                } => node(&[
                    "Named".into(),
                    level.to_string(),
                    str(label),
                    is_anonymous.to_string(),
                ]),
                StepNumber::Unnamed { level, id } => {
                    node(&["Unnamed".into(), level.to_string(), id.to_string()])
                }
            }),
            opt(props.method.as_ref(), |method| {
                node(&[
                    "method".into(),
                    str(&method.name),
                    opt(method.tactic.as_deref(), str),
                    opt(method.timeout.as_ref(), f64::to_string),
                ])
            }),
            emit_locus(props.use_location.as_ref()),
        ])
    }

    fn emit_usable(usable: &Usable) -> String {
        node(&[
            "usable".into(),
            emit_list(&usable.facts, emit_expr),
            emit_list(&usable.defs, |def| {
                let (kind, value) = match &def.core {
                    UseDefCore::Dx { index } => ("Dx", index.to_string()),
                    UseDefCore::Dvar { name } => ("Dvar", str(name)),
                };
                node(&[kind.into(), value, emit_locus(def.location.as_ref())])
            }),
        ])
    }

    fn emit_proof(proof: &Proof) -> String {
        let mut parts: Vec<String> = match &proof.core {
            ProofCore::Obvious => vec!["Obvious".into()],
            ProofCore::Omitted(omission) => vec!["Omitted".into(), format!("{omission:?}")],
            ProofCore::Error(message) => vec!["Error".into(), str(message)],
            ProofCore::By { usable, is_only } => {
                vec!["By".into(), emit_usable(usable), is_only.to_string()]
            }
            ProofCore::Steps { steps, qed } => vec![
                "Steps".into(),
                emit_list(steps, emit_step),
                emit_proof(&qed.proof),
                emit_props(&qed.props),
            ],
        };
        parts.push(emit_props(&proof.props));
        node(&parts)
    }

    fn emit_step(step: &Step) -> String {
        let mut parts: Vec<String> = match &step.core {
            StepCore::Hide { usable } => vec!["Hide".into(), emit_usable(usable)],
            StepCore::Define { definitions } => {
                vec!["Define".into(), emit_list(definitions, emit_defn)]
            }
            StepCore::Assert { sequent, proof } => {
                vec!["Assert".into(), emit_sequent(sequent), emit_proof(proof)]
            }
            StepCore::Suffices { sequent, proof } => {
                vec!["Suffices".into(), emit_sequent(sequent), emit_proof(proof)]
            }
            StepCore::Use { usable, is_only } => {
                vec!["Use".into(), emit_usable(usable), is_only.to_string()]
            }
            StepCore::Forget { count } => vec!["Forget".into(), count.to_string()],
            other => panic!("simplified step {other:?}"),
        };
        parts.push(emit_props(&step.props));
        node(&parts)
    }

    fn fnv(text: &str) -> String {
        let hash = text.bytes().fold(0xcbf2_9ce4_8422_2325_u64, |hash, byte| {
            (hash ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3)
        });
        format!("0x{hash:016x}")
    }

    fn run(fixture: &str) -> (Result<Proof>, usize) {
        let case = parse(fixture);
        let fields = items(&case);
        let counter = Rc::new(Counter::default());
        counter.value.set(number(&fields[1]));
        let result = create_simplifier(counter.clone()).simplify(
            &list(&fields[3], read_hyp),
            &read_expr(&fields[4]),
            &read_proof(&fields[5]),
            read_time(&fields[2]),
        );
        (result, counter.value.get())
    }

    fn check(fixture: &str, length: usize, hash: &str, after: usize) {
        let (result, counter) = run(fixture);
        let emitted = emit_proof(&result.expect("simplified"));
        assert_eq!(
            (emitted.len(), fnv(&emitted).as_str(), counter),
            (length, hash, after),
            "{emitted}"
        );
    }

    fn check_error(fixture: &str, expected: ObligationError) {
        assert_eq!(run(fixture).0.err(), Some(expected));
    }

    #[test]
    fn simplifies_every_step_kind() {
        check(A1, 2540, "0x35db7b215b356acf", 17);
        check(B1, 2494, "0xc12d466727393f0a", 21);
        check(B2, 2319, "0x5830d05f7ed46634", 29);
        check(C1, 2563, "0xb191b2d259b35fd4", 31);
        check(C2, 1065, "0x662396fed9fe812b", 33);
        check(C3, 446, "0xb3a3c8b23d167060", 34);
        check(C4, 2036, "0xa5ab99571a44932e", 41);
        check(D1, 1252, "0xa94765768fdbeb9b", 26);
        check(D2, 863, "0x28f5e67ccb391c5f", 28);
        check(D3, 872, "0xb2eca2de53e31331", 33);
        check(D4, 834, "0x11436adfb8e52298", 37);
        check(D5, 2072, "0xdb1ccf9b3e4c5d40", 51);
        check(D6, 2804, "0xbc1823f09c8204ad", 63);
        check(D7, 1623, "0x88489a608982a215", 69);
        check(HAVE_PARENS, 540, "0x247db61637b21150", 43);
        check(HAVE_PRIME_OTHER, 490, "0xb93d660e10fd7dde", 40);
        check(METHODS, 5196, "0xdc35e44fa2e731e5", 82);
    }

    #[test]
    fn reports_errors_as_the_typescript_does() {
        check_error(
            HAVE_OUT_OF_RANGE,
            ObligationError::proof("expose_connective"),
        );
        check_error(HAVE_ARITY, ObligationError::proof("Arity mismatch"));
        check_error(HIDE_DVAR, ObligationError::proof("set_vis"));
        check_error(
            HIDE_FACT,
            ObligationError::proof(
                "USE DEF ??? FACT ??? invalid because ??? FACT ??? is not a defined operator",
            ),
        );
        check_error(
            HIDE_FRESH,
            ObligationError::proof("USE DEF S invalid because S is not a defined operator"),
        );
        check_error(
            HIDE_OUT_OF_RANGE,
            ObligationError::proof("USE DEF  invalid because  is not a defined operator"),
        );
        check_error(ASSERT_UNNUMBERED, ObligationError::assert_failure());
    }

    const A1: &str = r#"
        (case 3 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "P" 1 Constant _ Visible @2:11-2:12) (Defn (Operator "Def" (Apply (Internal
        Subseteq) ((Ix 3 @3:8-3:9) (Ix 2 @3:20-3:21)) @3:8-3:21) @3:1-3:21) User Hidden false false
        @3:1-3:21) (Defn (Operator "Ax" (Apply (Internal Eq) ((Ix 4 @4:13-4:14) (Ix 3 @4:17-4:18))
        @4:13-4:18) @4:1-4:18) User Visible false false @4:1-4:18) (Fact (Ix 1 @4:1-4:18) Hidden Always _
        @4:1-4:18) (Defn (Operator "L1" (Sequent (sequent ((Fresh "a" 0 Constant (Ix 6 @6:30-6:31) Visible
        @6:20-6:31) (Fact (Apply (Ix 5 @6:33-6:37) ((Ix 1 @6:35-6:36)) @6:33-6:37) Visible Always _
        @6:33-6:37)) (Apply (Internal Conj) ((Apply (Ix 6 @6:44-6:48) ((Ix 2 @6:46-6:47)) @6:44-6:48) (Ix 5
        @6:52-6:55)) @6:44-6:55)) @6:1-18:21) @6:1-18:21) (Proof Always) Visible false true @6:1-18:21)
        (Fresh "a" 0 Constant (Ix 7 @6:30-6:31) Visible @6:20-6:31) (Fact (Apply (Ix 6 @6:33-6:37) ((Ix 1
        @6:35-6:36)) @6:33-6:37) Visible Always _ @6:33-6:37)) (Apply (Internal Conj) ((Apply (Ix 7
        @6:44-6:48) ((Ix 2 @6:46-6:47)) @6:44-6:48) (Ix 6 @6:52-6:55)) @6:44-6:55) (Steps ((Assert (sequent
        () (Ix 6 @7:7-7:10)) (By (usable ((Ix 8 @8:6-8:8)) ((Dx 9 @8:13-8:16))) false (props @8:3-8:5
        (Unnamed 2 0) _ _)) (props @7:1-8:5 (Named 1 "1" false) _ _)) (Suffices (sequent () (Apply (Ix 9
        @9:16-9:20) ((Ix 4 @9:18-9:19)) @9:16-9:20)) (By (usable ((Ix 4 @9:24-9:28)) ()) false (props
        @9:21-9:23 (Unnamed 2 0) _ _)) (props @9:1-9:23 (Named 1 "2" false) _ _)) (Use (usable ((Ix 5
        @10:9-10:13)) ((Dx 11 @10:18-10:21))) false (props @10:1-10:21 (Unnamed 1 1) _ _)) (Pcase (Apply
        (Internal Eq) ((Ix 8 @11:12-11:13) (Ix 8 @11:16-11:17)) @11:12-11:17) (Obvious (props @12:3-12:10 _
        _ _)) (props @11:1-12:10 (Named 1 "3" false) _ _)) (Pick (("b" Constant (Domain (Ix 17
        @13:18-13:19)))) (Apply (Internal Eq) ((Ix 1 @13:22-13:23) (Ix 11 @13:26-13:27)) @13:22-13:27)
        (Omitted Explicit (props @14:3-14:10 _ _ _)) (props @13:1-14:10 (Named 1 "4" false) _ _)) (Hide
        (usable () ((Dx 21 @15:14-15:17))) (props @15:1-15:17 (Unnamed 1 2) _ _)) (Define ((Operator "R" (Ix
        17 @16:17-16:18) @16:12-16:18)) (props @16:1-16:18 (Unnamed 1 3) _ _))) (By (usable ((Ix 3
        @18:11-18:15)) ((Dx 1 @18:20-18:21))) true (props @18:3-18:5 (Unnamed 2 0) _ _)) (props @17:1-18:5
        (Named 1 "6" false) _ _) (props @7:1-18:5 (Named 1 "6" false) _ _)))
    "#;

    const B1: &str = r#"
        (case 11 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "Q" 2 Constant _ Visible @2:11-2:12)) (Quant Forall (("y" Constant (Domain (Ix 3
        @4:16-4:17))) ("z" Constant (Domain (Ix 2 @4:25-4:26)))) (Quant Forall (("v" Constant (NoDomain)))
        (Apply (Ix 4 @4:36-4:43) ((Ix 3 @4:38-4:39) (Ix 2 @4:41-4:42)) @4:36-4:43) @4:29-4:43) @4:7-4:43)
        (Steps ((Take (("y" Constant (Domain (Ix 3 @5:16-5:17))) ("z" Constant (Domain (Ix 2 @5:25-5:26))))
        (props @5:1-5:26 (Named 1 "_a10" true) _ _)) (Assert (sequent () (Apply (Internal Eq) ((Ix 5
        @6:7-6:8) (Ix 5 @6:11-6:12)) @6:7-6:12)) (Obvious (props @6:13-6:20 _ _ _)) (props @6:1-6:20 (Named
        1 "1" false) _ _)) (Assert (sequent () (Apply (Internal Eq) ((At false @7:7-7:8) (Ix 7 @7:11-7:12))
        @7:7-7:12)) (By (usable ((Ix 5 @7:16-7:20)) ()) false (props @7:13-7:15 (Unnamed 2 0) _ _)) (props
        @7:1-7:15 (Named 1 "2" false) _ _)) (Pcase (Apply (Internal Mem) ((Ix 9 @8:12-8:13) (Ix 11
        @8:18-8:19)) @8:12-8:19) (Steps () (Obvious (props @9:11-9:18 _ _ _)) (props @9:3-9:18 (Unnamed 2 2)
        _ _) (props @9:3-9:18 (Unnamed 2 2) _ _)) (props @8:1-9:18 (Named 1 "3" false) _ _)) (Take (("v"
        Constant (NoDomain)) ("w" Constant (NoDomain))) (props @10:1-10:14 (Named 1 "_a11" true) _ _))) (By
        (usable ((Ix 9 @11:17-11:21)) ()) true (props @11:9-11:11 (Unnamed 2 0) _ _)) (props @11:1-11:11
        (Unnamed 1 4) _ _) (props @5:1-11:11 (Unnamed 1 4) _ _)))
    "#;

    const B2: &str = r#"
        (case 25 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "Q" 2 Constant _ Visible @2:11-2:12) (Fact (Quant Forall (("y" Constant (Domain
        (Ix 3 @4:16-4:17))) ("z" Constant (Domain (Ix 2 @4:25-4:26)))) (Quant Forall (("v" Constant
        (NoDomain))) (Apply (Ix 4 @4:36-4:43) ((Ix 3 @4:38-4:39) (Ix 2 @4:41-4:42)) @4:36-4:43) @4:29-4:43)
        @4:1-11:21) Hidden Always _ @4:1-11:21)) (Quant Forall (("y" Constant (Domain (Ix 4 @13:16-13:17)))
        ("z" Constant (Domain (Ix 4 @13:25-13:26))) ("w" Constant (Domain (Ix 3 @13:34-13:35)))) (Apply (Ix
        5 @13:38-13:45) ((Ix 3 @13:40-13:41) (Ix 2 @13:43-13:44)) @13:38-13:45) @13:7-13:45) (Steps ((Take
        (("y" Constant (Domain (Ix 4 @14:19-14:20))) ("z" Constant (Ditto)) ("w" Constant (Domain (Ix 4
        @14:28-14:29)))) (props @14:1-14:29 (Named 1 "_a22" true) _ _)) (Take (("y" Constant (Domain (Ix 9
        @15:16-15:17))) ("z" Constant (Domain (Ix 9 @15:25-15:26))) ("w" Constant (Domain (Ix 10
        @15:34-15:35)))) (props @15:1-15:35 (Named 1 "_a23" true) _ _)) (Take (("y" Constant (Domain (Ix 15
        @16:16-16:17)))) (props @16:1-16:17 (Named 1 "_a24" true) _ _)) (Take (("z" Constant (NoDomain))
        ("w" Constant (NoDomain))) (props @17:1-17:14 (Named 1 "_a25" true) _ _))) (Obvious (props
        @18:9-18:16 _ _ _)) (props @18:1-18:16 (Unnamed 1 9) _ _) (props @14:1-18:16 (Unnamed 1 9) _ _)))
    "#;

    const C1: &str = r#"
        (case 13 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "P" 1 Constant _ Visible @2:11-2:12) (Fresh "Q" 2 Constant _ Visible @2:11-2:12))
        (Quant Exists (("y" Constant (Domain (Ix 4 @4:16-4:17))) ("z" Constant (Domain (Ix 4 @4:25-4:26))))
        (Quant Exists (("v" Constant (NoDomain))) (Apply (Ix 4 @4:36-4:43) ((Ix 3 @4:38-4:39) (Ix 2
        @4:41-4:42)) @4:36-4:43) @4:29-4:43) @4:7-4:43) (Steps ((Witness ((Apply (Internal Mem) ((Ix 3
        @5:13-5:14) (Ix 4 @5:19-5:20)) @5:13-5:20) (Apply (Internal Mem) ((Ix 4 @5:22-5:23) (Apply (Internal
        SUBSET) ((Ix 4 @5:35-5:36)) @5:28-5:36)) @5:22-5:36) (Ix 3 @5:38-5:39)) (props @5:1-5:39 (Named 1
        "_a13" true) _ _))) (Obvious (props @6:9-6:16 _ _ _)) (props @6:1-6:16 (Unnamed 1 2) _ _) (props
        @5:1-6:16 (Unnamed 1 2) _ _)))
    "#;

    const C2: &str = r#"
        (case 33 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "P" 1 Constant _ Visible @2:11-2:12) (Fresh "Q" 2 Constant _ Visible @2:11-2:12)
        (Fact (Quant Exists (("y" Constant (Domain (Ix 4 @4:16-4:17))) ("z" Constant (Domain (Ix 4
        @4:25-4:26)))) (Quant Exists (("v" Constant (NoDomain))) (Apply (Ix 4 @4:36-4:43) ((Ix 3 @4:38-4:39)
        (Ix 2 @4:41-4:42)) @4:36-4:43) @4:29-4:43) @4:1-6:16) Hidden Always _ @4:1-6:16)) (Quant Exists
        (("y" Constant (Domain (Ix 5 @8:16-8:17))) ("z" Constant (Domain (Ix 4 @8:25-8:26)))) (Apply (Ix 4
        @8:29-8:36) ((Ix 2 @8:31-8:32) (Ix 1 @8:34-8:35)) @8:29-8:36) @8:7-8:36) (Steps ((Witness ((Apply
        (Internal Mem) ((Ix 4 @9:14-9:15) (Ix 4 @9:20-9:21)) @9:14-9:21) (Ix 5 @9:24-9:25)) (props @9:1-9:25
        (Named 1 "_a32" true) _ _)) (Witness ((Apply (Internal Mem) ((Ix 8 @10:13-10:14) (Ix 8
        @10:19-10:20)) @10:13-10:20) (Apply (Internal Mem) ((Ix 7 @10:22-10:23) (Ix 7 @10:28-10:29))
        @10:22-10:29) (Ix 7 @10:31-10:32)) (props @10:1-10:32 (Named 1 "_a33" true) _ _))) (Obvious (props
        @11:9-11:16 _ _ _)) (props @11:1-11:16 (Unnamed 1 5) _ _) (props @9:1-11:16 (Unnamed 1 5) _ _)))
    "#;

    const C3: &str = r#"
        (case 34 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "P" 1 Constant _ Visible @2:11-2:12) (Fresh "Q" 2 Constant _ Visible @2:11-2:12)
        (Fact (Quant Exists (("y" Constant (Domain (Ix 4 @4:16-4:17))) ("z" Constant (Domain (Ix 4
        @4:25-4:26)))) (Quant Exists (("v" Constant (NoDomain))) (Apply (Ix 4 @4:36-4:43) ((Ix 3 @4:38-4:39)
        (Ix 2 @4:41-4:42)) @4:36-4:43) @4:29-4:43) @4:1-6:16) Hidden Always _ @4:1-6:16) (Fact (Quant Exists
        (("y" Constant (Domain (Ix 5 @8:16-8:17))) ("z" Constant (Domain (Ix 4 @8:25-8:26)))) (Apply (Ix 4
        @8:29-8:36) ((Ix 2 @8:31-8:32) (Ix 1 @8:34-8:35)) @8:29-8:36) @8:1-11:16) Hidden Always _
        @8:1-11:16)) (Quant Exists (("y" Constant (NoDomain)) ("z" Constant (NoDomain))) (Apply (Ix 5
        @13:17-13:24) ((Ix 2 @13:19-13:20) (Ix 1 @13:22-13:23)) @13:17-13:24) @13:7-13:24) (Steps ((Witness
        ((Ix 5 @14:13-14:14) (Ix 6 @14:16-14:17)) (props @14:1-14:17 (Named 1 "_a34" true) _ _))) (Obvious
        (props @15:9-15:16 _ _ _)) (props @15:1-15:16 (Unnamed 1 7) _ _) (props @14:1-15:16 (Unnamed 1 7) _
        _)))
    "#;

    const C4: &str = r#"
        (case 38 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "P" 1 Constant _ Visible @2:11-2:12) (Fresh "Q" 2 Constant _ Visible @2:11-2:12)
        (Fact (Quant Exists (("y" Constant (Domain (Ix 4 @4:16-4:17))) ("z" Constant (Domain (Ix 4
        @4:25-4:26)))) (Quant Exists (("v" Constant (NoDomain))) (Apply (Ix 4 @4:36-4:43) ((Ix 3 @4:38-4:39)
        (Ix 2 @4:41-4:42)) @4:36-4:43) @4:29-4:43) @4:1-6:16) Hidden Always _ @4:1-6:16) (Fact (Quant Exists
        (("y" Constant (Domain (Ix 5 @8:16-8:17))) ("z" Constant (Domain (Ix 4 @8:25-8:26)))) (Apply (Ix 4
        @8:29-8:36) ((Ix 2 @8:31-8:32) (Ix 1 @8:34-8:35)) @8:29-8:36) @8:1-11:16) Hidden Always _
        @8:1-11:16) (Fact (Quant Exists (("y" Constant (NoDomain)) ("z" Constant (NoDomain))) (Apply (Ix 5
        @13:17-13:24) ((Ix 2 @13:19-13:20) (Ix 1 @13:22-13:23)) @13:17-13:24) @13:1-15:16) Hidden Always _
        @13:1-15:16)) (Quant Forall (("y" Constant (NoDomain))) (Apply (Ix 6 @17:14-17:18) ((Ix 1
        @17:16-17:17)) @17:14-17:18) @17:7-17:18) (Steps ((Take (("y" Constant (Domain (Ix 7
        @18:16-18:17)))) (props @18:1-18:17 (Named 1 "_a35" true) _ _)) (Witness ((Ix 11 @19:13-19:14))
        (props @19:1-19:14 (Named 1 "_a36" true) _ _)) (Have (Apply (Ix 12 @20:10-20:14) ((Ix 14
        @20:12-20:13)) @20:10-20:14) (props @20:1-20:14 (Named 1 "_a37" true) _ _)) (Take (("y" Constant
        (NoDomain))) (props @21:1-21:11 (Named 1 "_a38" true) _ _))) (Obvious (props @22:9-22:16 _ _ _))
        (props @22:1-22:16 (Unnamed 1 12) _ _) (props @18:1-22:16 (Unnamed 1 12) _ _)))
    "#;

    const D1: &str = r#"
        (case 20 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "P" 1 Constant _ Visible @2:11-2:12) (Flex "x" @3:10-3:11) (Defn (Operator "Imp"
        (Lambda (("a" 0 @4:5-4:6) ("b" 0 @4:8-4:9)) (Apply (Internal Implies) ((Ix 2 @4:14-4:15) (Ix 1
        @4:19-4:20)) @4:14-4:20) @4:1-4:20) @4:1-4:20) User Hidden false false @4:1-4:20) (Defn (Operator
        "All" (Quant Forall (("u" Constant (Domain (Ix 5 @5:17-5:18)))) (Apply (Ix 4 @5:21-5:25) ((Ix 1
        @5:23-5:24)) @5:21-5:25) @5:8-5:25) @5:1-5:25) User Hidden false false @5:1-5:25)) (Apply (Ix 2
        @7:7-7:32) ((Apply (Ix 4 @7:11-7:15) ((Ix 6 @7:13-7:14)) @7:11-7:15) (Apply (Internal Implies)
        ((Apply (Ix 4 @7:18-7:22) ((Ix 5 @7:20-7:21)) @7:18-7:22) (Apply (Ix 4 @7:26-7:30) ((Ix 6
        @7:28-7:29)) @7:26-7:30)) @7:18-7:30)) @7:7-7:32) (Steps ((Have (Apply (Ix 4 @8:10-8:14) ((Ix 6
        @8:12-8:13)) @8:10-8:14) (props @8:1-8:14 (Named 1 "_a19" true) _ _)) (Have (Apply (Ix 8 @9:10-9:14)
        ((Ix 9 @9:12-9:13)) @9:10-9:14) (props @9:1-9:14 (Named 1 "_a20" true) _ _))) (Obvious (props
        @10:9-10:16 _ _ _)) (props @10:1-10:16 (Unnamed 1 3) _ _) (props @8:1-10:16 (Unnamed 1 3) _ _)))
    "#;

    const D2: &str = r#"
        (case 28 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "P" 1 Constant _ Visible @2:11-2:12) (Flex "x" @3:10-3:11) (Defn (Operator "Imp"
        (Lambda (("a" 0 @4:5-4:6) ("b" 0 @4:8-4:9)) (Apply (Internal Implies) ((Ix 2 @4:14-4:15) (Ix 1
        @4:19-4:20)) @4:14-4:20) @4:1-4:20) @4:1-4:20) User Hidden false false @4:1-4:20) (Defn (Operator
        "All" (Quant Forall (("u" Constant (Domain (Ix 5 @5:17-5:18)))) (Apply (Ix 4 @5:21-5:25) ((Ix 1
        @5:23-5:24)) @5:21-5:25) @5:8-5:25) @5:1-5:25) User Hidden false false @5:1-5:25) (Fact (Apply (Ix 2
        @7:7-7:32) ((Apply (Ix 4 @7:11-7:15) ((Ix 6 @7:13-7:14)) @7:11-7:15) (Apply (Internal Implies)
        ((Apply (Ix 4 @7:18-7:22) ((Ix 5 @7:20-7:21)) @7:18-7:22) (Apply (Ix 4 @7:26-7:30) ((Ix 6
        @7:28-7:29)) @7:26-7:30)) @7:18-7:30)) @7:1-10:16) Hidden Always _ @7:1-10:16)) (Ix 2 @12:7-12:10)
        (Steps ((Take (("u" Constant (NoDomain))) (props @13:1-13:11 (Named 1 "_a27" true) _ _)) (Take (("u"
        Constant (Domain (Ix 11 @14:16-14:17)))) (props @14:1-14:17 (Named 1 "_a28" true) _ _))) (Obvious
        (props @15:9-15:16 _ _ _)) (props @15:1-15:16 (Unnamed 1 6) _ _) (props @13:1-15:16 (Unnamed 1 6) _
        _)))
    "#;

    const D3: &str = r#"
        (case 29 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "P" 1 Constant _ Visible @2:11-2:12) (Flex "x" @3:10-3:11) (Defn (Operator "Imp"
        (Lambda (("a" 0 @4:5-4:6) ("b" 0 @4:8-4:9)) (Apply (Internal Implies) ((Ix 2 @4:14-4:15) (Ix 1
        @4:19-4:20)) @4:14-4:20) @4:1-4:20) @4:1-4:20) User Hidden false false @4:1-4:20) (Defn (Operator
        "All" (Quant Forall (("u" Constant (Domain (Ix 5 @5:17-5:18)))) (Apply (Ix 4 @5:21-5:25) ((Ix 1
        @5:23-5:24)) @5:21-5:25) @5:8-5:25) @5:1-5:25) User Hidden false false @5:1-5:25) (Fact (Apply (Ix 2
        @7:7-7:32) ((Apply (Ix 4 @7:11-7:15) ((Ix 6 @7:13-7:14)) @7:11-7:15) (Apply (Internal Implies)
        ((Apply (Ix 4 @7:18-7:22) ((Ix 5 @7:20-7:21)) @7:18-7:22) (Apply (Ix 4 @7:26-7:30) ((Ix 6
        @7:28-7:29)) @7:26-7:30)) @7:18-7:30)) @7:1-10:16) Hidden Always _ @7:1-10:16) (Fact (Ix 2
        @12:1-15:16) Hidden Always _ @12:1-15:16)) (Apply (Internal Prime) ((Quant Forall (("y" Constant
        (Domain (Ix 8 @17:17-17:18)))) (Apply (Ix 7 @17:21-17:25) ((Ix 1 @17:23-17:24)) @17:21-17:25)
        @17:8-17:25)) @17:8-17:27) (Steps ((Take (("y" Constant (Domain (Ix 8 @18:16-18:17)))) (props
        @18:1-18:17 (Named 1 "_a29" true) _ _))) (Obvious (props @19:9-19:16 _ _ _)) (props @19:1-19:16
        (Unnamed 1 8) _ _) (props @18:1-19:16 (Unnamed 1 8) _ _)))
    "#;

    const D4: &str = r#"
        (case 34 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "P" 1 Constant _ Visible @2:11-2:12) (Flex "x" @3:10-3:11) (Defn (Operator "Imp"
        (Lambda (("a" 0 @4:5-4:6) ("b" 0 @4:8-4:9)) (Apply (Internal Implies) ((Ix 2 @4:14-4:15) (Ix 1
        @4:19-4:20)) @4:14-4:20) @4:1-4:20) @4:1-4:20) User Hidden false false @4:1-4:20) (Defn (Operator
        "All" (Quant Forall (("u" Constant (Domain (Ix 5 @5:17-5:18)))) (Apply (Ix 4 @5:21-5:25) ((Ix 1
        @5:23-5:24)) @5:21-5:25) @5:8-5:25) @5:1-5:25) User Hidden false false @5:1-5:25) (Fact (Apply (Ix 2
        @7:7-7:32) ((Apply (Ix 4 @7:11-7:15) ((Ix 6 @7:13-7:14)) @7:11-7:15) (Apply (Internal Implies)
        ((Apply (Ix 4 @7:18-7:22) ((Ix 5 @7:20-7:21)) @7:18-7:22) (Apply (Ix 4 @7:26-7:30) ((Ix 6
        @7:28-7:29)) @7:26-7:30)) @7:18-7:30)) @7:1-10:16) Hidden Always _ @7:1-10:16) (Fact (Ix 2
        @12:1-15:16) Hidden Always _ @12:1-15:16) (Fact (Apply (Internal Prime) ((Quant Forall (("y"
        Constant (Domain (Ix 8 @17:17-17:18)))) (Apply (Ix 7 @17:21-17:25) ((Ix 1 @17:23-17:24))
        @17:21-17:25) @17:8-17:25)) @17:1-19:16) Hidden Always _ @17:1-19:16)) (Apply (Internal Prime)
        ((Apply (Internal Implies) ((Apply (Internal Mem) ((Ix 6 @21:8-21:9) (Ix 9 @21:14-21:15))
        @21:8-21:15) (Apply (Internal Mem) ((Apply (Internal Prime) ((Ix 6 @21:19-21:20)) @21:19-21:21) (Ix
        9 @21:26-21:27)) @21:19-21:27)) @21:8-21:27)) @21:8-21:29) (Steps ((Have (Apply (Internal Mem)
        ((Apply (Internal Prime) ((Ix 6 @22:10-22:11)) @22:10-22:12) (Ix 9 @22:17-22:18)) @22:10-22:18)
        (props @22:1-22:18 (Named 1 "_a34" true) _ _))) (Obvious (props @23:9-23:16 _ _ _)) (props
        @23:1-23:16 (Unnamed 1 10) _ _) (props @22:1-23:16 (Unnamed 1 10) _ _)))
    "#;

    const D5: &str = r#"
        (case 38 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "P" 1 Constant _ Visible @2:11-2:12) (Flex "x" @3:10-3:11) (Defn (Operator "Imp"
        (Lambda (("a" 0 @4:5-4:6) ("b" 0 @4:8-4:9)) (Apply (Internal Implies) ((Ix 2 @4:14-4:15) (Ix 1
        @4:19-4:20)) @4:14-4:20) @4:1-4:20) @4:1-4:20) User Hidden false false @4:1-4:20) (Defn (Operator
        "All" (Quant Forall (("u" Constant (Domain (Ix 5 @5:17-5:18)))) (Apply (Ix 4 @5:21-5:25) ((Ix 1
        @5:23-5:24)) @5:21-5:25) @5:8-5:25) @5:1-5:25) User Hidden false false @5:1-5:25) (Fact (Apply (Ix 2
        @7:7-7:32) ((Apply (Ix 4 @7:11-7:15) ((Ix 6 @7:13-7:14)) @7:11-7:15) (Apply (Internal Implies)
        ((Apply (Ix 4 @7:18-7:22) ((Ix 5 @7:20-7:21)) @7:18-7:22) (Apply (Ix 4 @7:26-7:30) ((Ix 6
        @7:28-7:29)) @7:26-7:30)) @7:18-7:30)) @7:1-10:16) Hidden Always _ @7:1-10:16) (Fact (Ix 2
        @12:1-15:16) Hidden Always _ @12:1-15:16) (Fact (Apply (Internal Prime) ((Quant Forall (("y"
        Constant (Domain (Ix 8 @17:17-17:18)))) (Apply (Ix 7 @17:21-17:25) ((Ix 1 @17:23-17:24))
        @17:21-17:25) @17:8-17:25)) @17:1-19:16) Hidden Always _ @17:1-19:16) (Fact (Apply (Internal Prime)
        ((Apply (Internal Implies) ((Apply (Internal Mem) ((Ix 6 @21:8-21:9) (Ix 9 @21:14-21:15))
        @21:8-21:15) (Apply (Internal Mem) ((Apply (Internal Prime) ((Ix 6 @21:19-21:20)) @21:19-21:21) (Ix
        9 @21:26-21:27)) @21:19-21:27)) @21:8-21:27)) @21:1-23:16) Hidden Always _ @21:1-23:16)) (Apply
        (Internal Prime) ((Quant Exists (("y" Constant (Domain (Ix 10 @25:17-25:18)))) (Apply (Internal Mem)
        ((Ix 8 @25:21-25:22) (Ix 1 @25:27-25:28)) @25:21-25:28) @25:8-25:28)) @25:8-25:30) (Steps ((Witness
        ((Apply (Internal Mem) ((Ix 7 @26:13-26:14) (Ix 10 @26:19-26:20)) @26:13-26:20)) (props @26:1-26:20
        (Named 1 "_a38" true) _ _))) (Obvious (props @27:9-27:16 _ _ _)) (props @27:1-27:16 (Unnamed 1 12) _
        _) (props @26:1-27:16 (Unnamed 1 12) _ _)))
    "#;

    const D6: &str = r#"
        (case 52 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "P" 1 Constant _ Visible @2:11-2:12) (Flex "x" @3:10-3:11) (Defn (Operator "Imp"
        (Lambda (("a" 0 @4:5-4:6) ("b" 0 @4:8-4:9)) (Apply (Internal Implies) ((Ix 2 @4:14-4:15) (Ix 1
        @4:19-4:20)) @4:14-4:20) @4:1-4:20) @4:1-4:20) User Hidden false false @4:1-4:20) (Defn (Operator
        "All" (Quant Forall (("u" Constant (Domain (Ix 5 @5:17-5:18)))) (Apply (Ix 4 @5:21-5:25) ((Ix 1
        @5:23-5:24)) @5:21-5:25) @5:8-5:25) @5:1-5:25) User Hidden false false @5:1-5:25) (Fact (Apply (Ix 2
        @7:7-7:32) ((Apply (Ix 4 @7:11-7:15) ((Ix 6 @7:13-7:14)) @7:11-7:15) (Apply (Internal Implies)
        ((Apply (Ix 4 @7:18-7:22) ((Ix 5 @7:20-7:21)) @7:18-7:22) (Apply (Ix 4 @7:26-7:30) ((Ix 6
        @7:28-7:29)) @7:26-7:30)) @7:18-7:30)) @7:1-10:16) Hidden Always _ @7:1-10:16) (Fact (Ix 2
        @12:1-15:16) Hidden Always _ @12:1-15:16) (Fact (Apply (Internal Prime) ((Quant Forall (("y"
        Constant (Domain (Ix 8 @17:17-17:18)))) (Apply (Ix 7 @17:21-17:25) ((Ix 1 @17:23-17:24))
        @17:21-17:25) @17:8-17:25)) @17:1-19:16) Hidden Always _ @17:1-19:16) (Fact (Apply (Internal Prime)
        ((Apply (Internal Implies) ((Apply (Internal Mem) ((Ix 6 @21:8-21:9) (Ix 9 @21:14-21:15))
        @21:8-21:15) (Apply (Internal Mem) ((Apply (Internal Prime) ((Ix 6 @21:19-21:20)) @21:19-21:21) (Ix
        9 @21:26-21:27)) @21:19-21:27)) @21:8-21:27)) @21:1-23:16) Hidden Always _ @21:1-23:16) (Fact (Apply
        (Internal Prime) ((Quant Exists (("y" Constant (Domain (Ix 10 @25:17-25:18)))) (Apply (Internal Mem)
        ((Ix 8 @25:21-25:22) (Ix 1 @25:27-25:28)) @25:21-25:28) @25:8-25:28)) @25:1-27:16) Hidden Always _
        @25:1-27:16)) (Quant Exists (("y" Constant (Domain (Ix 11 @29:16-29:17)))) (Apply (Ix 10
        @29:20-29:24) ((Ix 1 @29:22-29:23)) @29:20-29:24) @29:7-29:24) (Steps ((Pick (("z" Constant (Domain
        (Ix 11 @30:18-30:19)))) (Apply (Ix 10 @30:22-30:26) ((Ix 1 @30:24-30:25)) @30:22-30:26) (Steps
        ((Take (("w" Constant (Domain (Ix 14 @31:20-31:21)))) (props @31:3-31:21 (Named 2 "1" false) _ _)))
        (Obvious (props @32:11-32:18 _ _ _)) (props @32:3-32:18 (Unnamed 2 13) _ _) (props @31:3-32:18
        (Unnamed 2 13) _ _)) (props @30:1-32:18 (Named 1 "1" false) _ _)) (Witness ((Apply (Internal Mem)
        ((Ix 5 @33:13-33:14) (Ix 18 @33:19-33:20)) @33:13-33:20)) (props @33:1-33:20 (Named 1 "_a52" true) _
        _))) (By (usable ((Ix 5 @34:12-34:16)) ()) false (props @34:9-34:11 (Unnamed 2 0) _ _)) (props
        @34:1-34:11 (Unnamed 1 15) _ _) (props @30:1-34:11 (Unnamed 1 15) _ _)))
    "#;

    const D7: &str = r#"
        (case 64 Always ((Fresh "S" 0 Constant _ Visible @2:11-2:12) (Fresh "T" 0 Constant _ Visible
        @2:11-2:12) (Fresh "P" 1 Constant _ Visible @2:11-2:12) (Flex "x" @3:10-3:11) (Defn (Operator "Imp"
        (Lambda (("a" 0 @4:5-4:6) ("b" 0 @4:8-4:9)) (Apply (Internal Implies) ((Ix 2 @4:14-4:15) (Ix 1
        @4:19-4:20)) @4:14-4:20) @4:1-4:20) @4:1-4:20) User Hidden false false @4:1-4:20) (Defn (Operator
        "All" (Quant Forall (("u" Constant (Domain (Ix 5 @5:17-5:18)))) (Apply (Ix 4 @5:21-5:25) ((Ix 1
        @5:23-5:24)) @5:21-5:25) @5:8-5:25) @5:1-5:25) User Hidden false false @5:1-5:25) (Fact (Apply (Ix 2
        @7:7-7:32) ((Apply (Ix 4 @7:11-7:15) ((Ix 6 @7:13-7:14)) @7:11-7:15) (Apply (Internal Implies)
        ((Apply (Ix 4 @7:18-7:22) ((Ix 5 @7:20-7:21)) @7:18-7:22) (Apply (Ix 4 @7:26-7:30) ((Ix 6
        @7:28-7:29)) @7:26-7:30)) @7:18-7:30)) @7:1-10:16) Hidden Always _ @7:1-10:16) (Fact (Ix 2
        @12:1-15:16) Hidden Always _ @12:1-15:16) (Fact (Apply (Internal Prime) ((Quant Forall (("y"
        Constant (Domain (Ix 8 @17:17-17:18)))) (Apply (Ix 7 @17:21-17:25) ((Ix 1 @17:23-17:24))
        @17:21-17:25) @17:8-17:25)) @17:1-19:16) Hidden Always _ @17:1-19:16) (Fact (Apply (Internal Prime)
        ((Apply (Internal Implies) ((Apply (Internal Mem) ((Ix 6 @21:8-21:9) (Ix 9 @21:14-21:15))
        @21:8-21:15) (Apply (Internal Mem) ((Apply (Internal Prime) ((Ix 6 @21:19-21:20)) @21:19-21:21) (Ix
        9 @21:26-21:27)) @21:19-21:27)) @21:8-21:27)) @21:1-23:16) Hidden Always _ @21:1-23:16) (Fact (Apply
        (Internal Prime) ((Quant Exists (("y" Constant (Domain (Ix 10 @25:17-25:18)))) (Apply (Internal Mem)
        ((Ix 8 @25:21-25:22) (Ix 1 @25:27-25:28)) @25:21-25:28) @25:8-25:28)) @25:1-27:16) Hidden Always _
        @25:1-27:16) (Fact (Quant Exists (("y" Constant (Domain (Ix 11 @29:16-29:17)))) (Apply (Ix 10
        @29:20-29:24) ((Ix 1 @29:22-29:23)) @29:20-29:24) @29:1-34:16) Hidden Always _ @29:1-34:16) (Fresh
        "c" 0 Constant _ Visible @36:16-36:21) (Fact (Apply (Internal Mem) ((Ix 1 @36:23-36:24) (Ix 13
        @36:29-36:30)) @36:23-36:30) Visible Always _ @36:23-36:30)) (Apply (Internal BoxTrue) ((Apply (Ix
        12 @36:39-36:43) ((Ix 2 @36:41-36:42)) @36:39-36:43)) @36:37-36:43) (Steps ((Assert (sequent ()
        (Apply (Ix 12 @37:7-37:11) ((Ix 2 @37:9-37:10)) @37:7-37:11)) (Steps ((Pick (("d" Constant (Domain
        (Ix 17 @38:21-38:22))) ("e" Constant (Ditto)) ("f" Constant (Domain (Ix 16 @38:30-38:31)))) (Apply
        (Internal Eq) ((Ix 3 @38:34-38:35) (Ix 8 @38:38-38:39)) @38:34-38:39) (Obvious (props @39:5-39:12 _
        _ _)) (props @38:3-39:12 (Named 2 "_a64" true) _ _))) (By (usable ((Internal TRUE @40:14-40:18)) ())
        false (props @40:11-40:13 (Unnamed 3 0) _ _)) (props @40:3-40:13 (Unnamed 2 17) _ _) (props
        @38:3-40:13 (Unnamed 2 17) _ _)) (props @37:1-40:13 (Named 1 "a" false) _ _))) (By (usable ((Ix 2
        @41:12-41:16)) ()) false (props @41:9-41:11 (Unnamed 2 0) _ _)) (props @41:1-41:11 (Unnamed 1 18) _
        _) (props @37:1-41:11 (Unnamed 1 18) _ _)))
    "#;

    const HAVE_OUT_OF_RANGE: &str = r#"
        (case 40 Always ((Fresh "S" 0 Constant _ Visible _) (Fresh "T" 0 Constant _ Visible _) (Defn
        (Operator "Imp" (Lambda (("a" 0 _) ("b" 0 _)) (Apply (Internal Implies) ((Ix 2) (Ix 1)))) @1:1-1:5)
        User Visible false false @1:1-1:5) (Fact (Opaque "f") Visible Always _ @2:1-2:5)) (Ix 9) (Steps
        ((Have (Opaque "h") (props @4:1-4:5 (Named 1 "1" false) _ _))) (Obvious (props @9:1-9:5 _ _ _))
        (props @9:1-9:5 (Named 1 "q" false) _ _) (props @3:1-3:5 (Named 0 "0" false) _ _)))
    "#;

    const HAVE_ARITY: &str = r#"
        (case 40 Always ((Fresh "S" 0 Constant _ Visible _) (Fresh "T" 0 Constant _ Visible _) (Defn
        (Operator "Imp" (Lambda (("a" 0 _) ("b" 0 _)) (Apply (Internal Implies) ((Ix 2) (Ix 1)))) @1:1-1:5)
        User Visible false false @1:1-1:5) (Fact (Opaque "f") Visible Always _ @2:1-2:5)) (Apply (Ix 2) ((Ix
        4))) (Steps ((Have (Opaque "h") (props @4:1-4:5 (Named 1 "1" false) _ _))) (Obvious (props @9:1-9:5
        _ _ _)) (props @9:1-9:5 (Named 1 "q" false) _ _) (props @3:1-3:5 (Named 0 "0" false) _ _)))
    "#;

    const HIDE_DVAR: &str = r#"
        (case 40 Always ((Fresh "S" 0 Constant _ Visible _) (Fresh "T" 0 Constant _ Visible _) (Defn
        (Operator "Imp" (Lambda (("a" 0 _) ("b" 0 _)) (Apply (Internal Implies) ((Ix 2) (Ix 1)))) @1:1-1:5)
        User Visible false false @1:1-1:5) (Fact (Opaque "f") Visible Always _ @2:1-2:5)) (Ix 4) (Steps
        ((Hide (usable () ((Dvar "D" _))) (props @4:1-4:5 _ _ _))) (Obvious (props @9:1-9:5 _ _ _)) (props
        @9:1-9:5 (Named 1 "q" false) _ _) (props @3:1-3:5 (Named 0 "0" false) _ _)))
    "#;

    const HIDE_FACT: &str = r#"
        (case 40 Always ((Fresh "S" 0 Constant _ Visible _) (Fresh "T" 0 Constant _ Visible _) (Defn
        (Operator "Imp" (Lambda (("a" 0 _) ("b" 0 _)) (Apply (Internal Implies) ((Ix 2) (Ix 1)))) @1:1-1:5)
        User Visible false false @1:1-1:5) (Fact (Opaque "f") Visible Always _ @2:1-2:5)) (Ix 4) (Steps
        ((Hide (usable () ((Dx 2 _) (Dx 1 _))) (props @4:1-4:5 _ _ _))) (Obvious (props @9:1-9:5 _ _ _))
        (props @9:1-9:5 (Named 1 "q" false) _ _) (props @3:1-3:5 (Named 0 "0" false) _ _)))
    "#;

    const HIDE_FRESH: &str = r#"
        (case 40 Always ((Fresh "S" 0 Constant _ Visible _) (Fresh "T" 0 Constant _ Visible _) (Defn
        (Operator "Imp" (Lambda (("a" 0 _) ("b" 0 _)) (Apply (Internal Implies) ((Ix 2) (Ix 1)))) @1:1-1:5)
        User Visible false false @1:1-1:5) (Fact (Opaque "f") Visible Always _ @2:1-2:5)) (Ix 4) (Steps
        ((Hide (usable () ((Dx 4 _))) (props @4:1-4:5 _ _ _))) (Obvious (props @9:1-9:5 _ _ _)) (props
        @9:1-9:5 (Named 1 "q" false) _ _) (props @3:1-3:5 (Named 0 "0" false) _ _)))
    "#;

    const HIDE_OUT_OF_RANGE: &str = r#"
        (case 40 Always ((Fresh "S" 0 Constant _ Visible _) (Fresh "T" 0 Constant _ Visible _) (Defn
        (Operator "Imp" (Lambda (("a" 0 _) ("b" 0 _)) (Apply (Internal Implies) ((Ix 2) (Ix 1)))) @1:1-1:5)
        User Visible false false @1:1-1:5) (Fact (Opaque "f") Visible Always _ @2:1-2:5)) (Ix 4) (Steps
        ((Hide (usable () ((Dx 0 _))) (props @4:1-4:5 _ _ _))) (Obvious (props @9:1-9:5 _ _ _)) (props
        @9:1-9:5 (Named 1 "q" false) _ _) (props @3:1-3:5 (Named 0 "0" false) _ _)))
    "#;

    const ASSERT_UNNUMBERED: &str = r#"
        (case 40 Always ((Fresh "S" 0 Constant _ Visible _) (Fresh "T" 0 Constant _ Visible _) (Defn
        (Operator "Imp" (Lambda (("a" 0 _) ("b" 0 _)) (Apply (Internal Implies) ((Ix 2) (Ix 1)))) @1:1-1:5)
        User Visible false false @1:1-1:5) (Fact (Opaque "f") Visible Always _ @2:1-2:5)) (Ix 4) (Steps
        ((Assert (sequent () (Opaque "a")) (Obvious (props _ _ _ _)) (props @4:1-4:5 _ _ _))) (Obvious
        (props @9:1-9:5 _ _ _)) (props @9:1-9:5 (Named 1 "q" false) _ _) (props @3:1-3:5 (Named 0 "0" false)
        _ _)))
    "#;

    const HAVE_PARENS: &str = r#"
        (case 40 Always ((Fresh "S" 0 Constant _ Visible _) (Fresh "T" 0 Constant _ Visible _) (Defn
        (Operator "Imp" (Lambda (("a" 0 _) ("b" 0 _)) (Apply (Internal Implies) ((Ix 2) (Ix 1)))) @1:1-1:5)
        User Visible false false @1:1-1:5) (Fact (Opaque "f") Visible Always _ @2:1-2:5)) (Parens (Parens
        (Apply (Internal Implies) ((Opaque "l") (Opaque "r"))) (Syntax)) (Syntax) @5:1-5:5) (Steps ((Have
        (Opaque "h") (props @4:1-4:5 (Named 1 "1" false) _ _))) (Obvious (props @9:1-9:5 _ _ _)) (props
        @9:1-9:5 (Named 1 "q" false) _ _) (props @3:1-3:5 (Named 0 "0" false) _ _)))
    "#;

    const HAVE_PRIME_OTHER: &str = r#"
        (case 40 Always ((Fresh "S" 0 Constant _ Visible _) (Fresh "T" 0 Constant _ Visible _) (Defn
        (Operator "Imp" (Lambda (("a" 0 _) ("b" 0 _)) (Apply (Internal Implies) ((Ix 2) (Ix 1)))) @1:1-1:5)
        User Visible false false @1:1-1:5) (Fact (Opaque "f") Visible Always _ @2:1-2:5)) (Apply (Internal
        Prime) ((Ix 4)) @5:1-5:5) (Steps ((Have (Opaque "h") (props @4:1-4:5 (Named 1 "1" false) _ _)))
        (Obvious (props @9:1-9:5 _ _ _)) (props @9:1-9:5 (Named 1 "q" false) _ _) (props @3:1-3:5 (Named 0
        "0" false) _ _)))
    "#;

    const METHODS: &str = r#"
        (case 40 Always ((Fresh "S" 0 Constant _ Visible _) (Fresh "T" 0 Constant _ Visible _) (Defn
        (Operator "Imp" (Lambda (("a" 0 _) ("b" 0 _)) (Apply (Internal Implies) ((Ix 2) (Ix 1)))) @1:1-1:5)
        User Visible false false @1:1-1:5) (Fact (Opaque "f") Visible Always _ @2:1-2:5)) (Quant Exists
        (("y" Constant (Domain (Ix 4 @5:1-5:5))) ("z" Constant (Ditto))) (Apply (Internal Eq) ((Ix 1) (Ix
        2))) @5:1-5:5) (Steps ((Witness ((Apply (Internal Mem) ((Ix 4) (Ix 5 @6:1-6:5))) (Apply (Internal
        Mem) ((Opaque "w") (Ix 5)) @6:1-6:5 !)) (props @6:1-6:5 (Unnamed 1 0) (method "zenon" _ 7) _))
        (Assert (sequent () (Apply (Internal Eq) ((Opaque "a") (Opaque "b")))) (By (usable ((Ix 1)) ((Dx 3
        _))) true (props @7:1-7:5 (Unnamed 2 0) (method "zenon" _ 7) _)) (props @7:1-7:5 (Named 1 "1" false)
        _ _)) (Forget 1 (props @8:1-8:5 (Named 1 "f" false) _ _)) (Assert (sequent () (At false @8:1-8:5 !))
        (Omitted Explicit (props _ _ _ _)) (props @8:1-8:5 (Named 1 "2" false) _ _)) (Assert (sequent ()
        (Apply (Internal Eq) ((At true) (At false)))) (Error "e" (props _ _ _ _)) (props @8:1-8:5 (Named 1
        "3" false) _ _)) (Pcase (Opaque "c") (By (usable ((Ix 1)) ()) false (props @8:1-8:5 _ (method
        "zenon" _ 7) _)) (props @8:1-8:5 (Unnamed 1 0) (method "zenon" _ 7) _)) (Use (usable ((Ix 1
        @8:1-8:5) (Ix 2)) ((Dx 3 @8:1-8:5))) true (props @8:1-8:5 (Named 1 "u" false) (method "zenon" _ 7)
        _)) (Define ((Operator "D" (Opaque "d") @8:1-8:5)) (props @8:1-8:5 (Named 1 "d" false) _ _)) (Pick
        (("p" Constant (NoDomain)) ("r" Constant (Domain (Ix 2))) ("s" Constant (Ditto))) (Opaque "pk")
        (Obvious (props _ _ _ _)) (props @8:1-8:5 (Unnamed 1 0) (method "zenon" _ 7) _))) (By (usable () ())
        true (props @9:1-9:5 _ (method "zenon" _ 7) _)) (props @9:1-9:5 (Named 1 "q" false) _ _) (props
        @3:1-3:5 (Named 0 "0" false) _ _)))
    "#;
}
