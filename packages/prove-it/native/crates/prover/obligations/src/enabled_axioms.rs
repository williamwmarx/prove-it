//! Module.Elab's check_enabled_axioms_usage and check_enabled_axioms_map (`m_elab.ml`): whether a
//! theorem's simplified proof cites the ENABLEDaxioms directive anywhere, and if so, at each leaf,
//! the level of the assumptions the leaf depends on, which the directive's rule is sound for only
//! up to level 1. A leaf that cites the directive among assumptions of a higher level gets an
//! error note at its location and the property `enabledaxioms` false, which Prep.expand_enabled_cdot
//! refuses; every other leaf gets it true.
//! A port of `src/obligations/enabled-axioms.ts`.

use std::cell::Cell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::errors::{ObligationError, Result};
use crate::expression::{
    DefnCore, Expr, ExprCore, Hyp, HypCore, ScopeRef, Sequent, Time, Visibility, Warn,
    WhereDefined, adjoin, adjoin_all, get_error_note, get_fact,
};
use crate::generate::{at_nowhere, get_step_definition, set_definition, set_expression};
use crate::levels::{get_context_level, get_level_info};
use crate::proof::{Proof, ProofCore, QedStep, Step, StepCore, get_step_name};

/// The visitor's state: the context, the level of the enclosing proof (`level`, a reference an
/// assertion's proof writes and a SUFFICES replaces) and `sm`, the level each step name stands
/// for.
struct State {
    context: Vec<Hyp>,
    level: Rc<Cell<usize>>,
    step_levels: HashMap<String, usize>,
}

/// Expr.Visit.bump's dummy hypothesis: a fact that is `At`, which the level checks skip.
fn dummy_fact() -> Hyp {
    get_fact(at_nowhere(), Visibility::Visible, Time::Always, None)
}

/// The hypothesis a fact at `index` of `context` refers to, where the fact is a reference.
fn get_target<'context>(
    context: &'context [Hyp],
    index: usize,
    expression: &Expr,
) -> Option<&'context Hyp> {
    match &expression.core {
        ExprCore::Ix { index: offset } => usize::try_from(index as isize - offset)
            .ok()
            .and_then(|at| context.get(at)),
        _ => None,
    }
}

fn is_directive(target: Option<&Hyp>) -> bool {
    matches!(
        target.map(|hyp| &hyp.core),
        Some(HypCore::Defn {
            definition,
            ..
        }) if matches!(&definition.core, DefnCore::Bpragma { name, .. } if name == "ENABLEDaxioms")
    )
}

fn get_define_hyp(definition: &crate::expression::Defn) -> Hyp {
    Rc::new(crate::expression::HypNode {
        core: HypCore::Defn {
            definition: definition.clone(),
            where_defined: WhereDefined::User,
            visibility: Visibility::Visible,
            is_local: true,
            is_constness_unset: false,
        },
        location: definition.location.clone(),
    })
}

struct Checker<'warn, 'sink> {
    warn: &'sink mut Warn<'warn>,
    /// check_enabled_axioms_usage: only find the directive, assign nothing.
    is_checking: bool,
    is_used: bool,
}

impl Checker<'_, '_> {
    /// The levels an assertion's sequent gives its step: of its context's hypotheses alone
    /// (`hyps_level`), and of the whole sequent (`Expr.Levels.get_level`).
    fn get_levels(&self, context: &[Hyp], sequent: &Sequent) -> Result<(usize, usize)> {
        if !self.is_checking {
            return Ok((0, 0));
        }
        let (scope, hyps) = get_context_level(&adjoin_all(&None, context), &sequent.context)?;
        let active = get_level_info(&scope, &sequent.active)?.level;
        Ok((hyps, hyps.max(active)))
    }

    /// check_usable: a leaf proof, whose usable facts simplification has made context facts.
    fn check_leaf(&mut self, state: &State, proof: &Proof, is_only: bool) -> Result<Proof> {
        let context = &state.context;
        if !self.is_checking {
            // check_enabled_axioms_usage#check_usable looks at facts of every visibility.
            self.is_used = self.is_used
                || context.iter().enumerate().any(|(index, hyp)| {
                    matches!(&hyp.core, HypCore::Fact { expression, .. }
                        if is_directive(get_target(context, index, expression)))
                });
            return Ok(proof.clone());
        }
        let mut scopes: Vec<ScopeRef> = Vec::with_capacity(context.len());
        let mut scope: ScopeRef = None;
        for hyp in context {
            scopes.push(scope.clone());
            scope = adjoin(&scope, hyp);
        }
        let facts = context
            .iter()
            .enumerate()
            .filter_map(|(index, hyp)| match &hyp.core {
                HypCore::Fact {
                    expression,
                    visibility: Visibility::Visible,
                    ..
                } if !matches!(expression.core, ExprCore::At { .. }) => Some((index, expression)),
                _ => None,
            })
            .collect::<Vec<_>>();
        let is_found = facts
            .iter()
            .any(|(index, expression)| is_directive(get_target(context, *index, expression)));
        if is_only && !is_found {
            return Ok(with_soundness(proof, true));
        }
        // check_steps, and check_assumptions where the proof's level is to be updated: a fact
        // that names a step takes the level stored for it, a fact that names nothing else takes
        // nothing, and any other fact its expression's level.
        let mut level = 0;
        for (index, expression) in &facts {
            let fact_level = match get_target(context, *index, expression) {
                None => get_level_info(&scopes[*index], expression)?.level,
                Some(target) => match &target.core {
                    HypCore::Fact {
                        visibility: Visibility::Visible,
                        ..
                    } if !is_only => return Err(ObligationError::assert_failure()),
                    HypCore::Defn {
                        definition,
                        visibility: Visibility::Visible,
                        ..
                    } => match &definition.core {
                        DefnCore::Operator { name, .. } => {
                            state.step_levels.get(name).copied().unwrap_or(0)
                        }
                        _ => 0,
                    },
                    _ => 0,
                },
            };
            level = level.max(fact_level);
        }
        if !is_only {
            state.level.set(state.level.get().max(level));
        }
        if !is_found || level <= 1 {
            return Ok(with_soundness(proof, true));
        }
        (self.warn)(get_error_note(
            proof.props.location.as_ref(),
            "ENABLEDaxioms depends on assumption of expression level > 1",
        ));
        Ok(with_soundness(proof, false))
    }

    fn visit_step(&mut self, state: State, step: &Step) -> Result<(State, Step)> {
        let Some(number) = &step.props.step else {
            return Err(ObligationError::assert_failure());
        };
        let name = get_step_name(number);
        let mut step_levels = state.step_levels;
        // check_enabled_axioms_map asserts that only an unlabeled step's name is stored already.
        if step_levels.remove(&name).is_some() && self.is_checking && !name.ends_with('>') {
            return Err(ObligationError::assert_failure());
        }
        let definition = get_step_definition(step, at_nowhere(), Time::Always)?;
        match &step.core {
            StepCore::Forget { count } => {
                let total = state.context.len();
                let context = state
                    .context
                    .iter()
                    .enumerate()
                    .map(|(index, hyp)| match &hyp.core {
                        HypCore::Fact {
                            expression,
                            visibility: Visibility::Visible,
                            time,
                            use_location,
                        } if count + index < total => hyp.with_core(HypCore::Fact {
                            expression: expression.clone(),
                            visibility: Visibility::Hidden,
                            time: *time,
                            use_location: use_location.clone(),
                        }),
                        _ => hyp.clone(),
                    })
                    .collect();
                Ok((
                    State {
                        context,
                        level: state.level,
                        step_levels,
                    },
                    step.clone(),
                ))
            }
            StepCore::Hide { usable } => {
                let mut context = state.context;
                for def in &usable.defs {
                    context = set_definition(Visibility::Hidden, context, def)?;
                }
                for fact in usable.facts.iter().rev() {
                    context = set_expression(self.warn, Visibility::Hidden, fact, context)?;
                }
                Ok((
                    State {
                        context,
                        level: state.level,
                        step_levels,
                    },
                    step.clone(),
                ))
            }
            StepCore::Assert {
                sequent: asserted,
                proof,
            } => {
                let (hyps_level, sequent_level) = self.get_levels(&state.context, asserted)?;
                let proof_level = Rc::new(Cell::new(0));
                let mut inner_levels = step_levels.clone();
                inner_levels.insert(name.clone(), hyps_level);
                let mut inner_context = state.context.clone();
                inner_context.extend(asserted.context.iter().cloned());
                inner_context.push(dummy_fact());
                inner_context.push(definition.clone());
                inner_context.push(dummy_fact());
                let proved = self.visit_proof(
                    &State {
                        context: inner_context,
                        level: proof_level.clone(),
                        step_levels: inner_levels,
                    },
                    proof,
                )?;
                let proof_level = proof_level.get();
                state.level.set(if proof_level < 2 {
                    proof_level
                } else {
                    sequent_level.min(proof_level)
                });
                step_levels.insert(name, state.level.get());
                let mut context = state.context;
                context.push(definition);
                context.push(dummy_fact());
                Ok((
                    State {
                        context,
                        level: state.level,
                        step_levels,
                    },
                    Step {
                        core: StepCore::Assert {
                            sequent: asserted.clone(),
                            proof: proved,
                        },
                        props: step.props.clone(),
                    },
                ))
            }
            StepCore::Suffices {
                sequent: asserted,
                proof,
            } => {
                let (hyps_level, sequent_level) = self.get_levels(&state.context, asserted)?;
                state.level.set(sequent_level);
                let proof_level = Rc::new(Cell::new(0));
                let mut inner_levels = step_levels.clone();
                inner_levels.insert(name.clone(), sequent_level);
                let mut inner_context = state.context.clone();
                inner_context.push(definition.clone());
                inner_context.push(dummy_fact());
                let proved = self.visit_proof(
                    &State {
                        context: inner_context,
                        level: proof_level.clone(),
                        step_levels: inner_levels,
                    },
                    proof,
                )?;
                step_levels.insert(name, hyps_level);
                let mut context = state.context;
                context.extend(asserted.context.iter().cloned());
                context.push(dummy_fact());
                context.push(definition);
                context.push(dummy_fact());
                Ok((
                    State {
                        context,
                        // The steps after a SUFFICES contribute to its proof's level.
                        level: proof_level,
                        step_levels,
                    },
                    Step {
                        core: StepCore::Suffices {
                            sequent: asserted.clone(),
                            proof: proved,
                        },
                        props: step.props.clone(),
                    },
                ))
            }
            StepCore::Use { usable, .. } => {
                let mut context = state.context;
                if usable.defs.is_empty() && usable.facts.len() == 1 {
                    let fact = &usable.facts[0];
                    context.push(get_fact(
                        fact.clone(),
                        Visibility::Visible,
                        Time::Always,
                        fact.location.clone(),
                    ));
                } else {
                    // Proof.Visit's step bumps the context by the facts.
                    context.extend(usable.facts.iter().map(|_| dummy_fact()));
                    step_levels.insert(name, 1);
                }
                Ok((
                    State {
                        context,
                        level: state.level,
                        step_levels,
                    },
                    step.clone(),
                ))
            }
            StepCore::Define { definitions } => {
                let mut context = state.context;
                context.extend(definitions.iter().map(get_define_hyp));
                step_levels.insert(name, 1);
                Ok((
                    State {
                        context,
                        level: state.level,
                        step_levels,
                    },
                    step.clone(),
                ))
            }
            // Proof.Simplify.simplify has removed these.
            StepCore::Pcase { .. }
            | StepCore::Have { .. }
            | StepCore::Take { .. }
            | StepCore::Witness { .. }
            | StepCore::Pick { .. } => Err(ObligationError::assert_failure()),
        }
    }

    fn visit_proof(&mut self, state: &State, proof: &Proof) -> Result<Proof> {
        match &proof.core {
            ProofCore::Omitted(_) | ProofCore::Error(_) => Ok(proof.clone()),
            ProofCore::Obvious => self.check_leaf(state, proof, false),
            ProofCore::By { is_only, .. } => self.check_leaf(state, proof, *is_only),
            ProofCore::Steps { steps, qed } => {
                let mut current = State {
                    context: state.context.clone(),
                    level: state.level.clone(),
                    step_levels: state.step_levels.clone(),
                };
                let mut visited = Vec::with_capacity(steps.len());
                for step in steps {
                    let (next, generated) = self.visit_step(current, step)?;
                    current = next;
                    visited.push(generated);
                }
                let qed_proof = self.visit_proof(&current, &qed.proof)?;
                Ok(Proof {
                    core: ProofCore::Steps {
                        steps: visited,
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
}

fn with_soundness(proof: &Proof, is_sound: bool) -> Proof {
    let mut props = proof.props.clone();
    props.is_enabled_axioms_sound = Some(is_sound);
    Proof {
        core: proof.core.clone(),
        props,
    }
}

fn visit_theorem(
    context: &[Hyp],
    proof: &Proof,
    warn: &mut Warn,
    is_checking: bool,
) -> Result<(bool, Proof)> {
    let mut checker = Checker {
        warn,
        is_checking,
        is_used: false,
    };
    let visited = checker.visit_proof(
        &State {
            context: context.to_vec(),
            level: Rc::new(Cell::new(0)),
            step_levels: HashMap::new(),
        },
        proof,
    )?;
    Ok((checker.is_used, visited))
}

/// The theorem's proof with the `enabledaxioms` property on each leaf, where the proof cites the
/// directive (Module.Elab's normalize, after Proof.Simplify.simplify).
pub fn check_enabled_axioms(context: &[Hyp], proof: Proof, warn: &mut Warn) -> Result<Proof> {
    if visit_theorem(context, &proof, warn, false)?.0 {
        Ok(visit_theorem(context, &proof, warn, true)?.1)
    } else {
        Ok(proof)
    }
}
