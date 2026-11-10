//! A port of tlapm's obligation generation (Proof.Gen and Module.Gen): leaf proofs become
//! obligations whose context is everything the proof may use at that point.
//! A port of `src/obligations/generate.ts`.

use std::collections::HashSet;
use std::rc::Rc;

use crate::equality::is_equal_expr;
use crate::errors::{ObligationError, Result};
use crate::expression::{
    Builtin, Bullet, Defn, DefnCore, Expr, ExprCore, ExprNode, ExprProps, Hyp, HypCore, HypNode,
    Locus, Sequent, Time, Visibility, Warn, WhereDefined, at_expr, at_props, exprify_sequent,
    get_error_note, get_fact, is_builtin_apply, located, map_accumulate, to_index,
};
use crate::module::{ModuleUnitCore, Mule, MutateMode, bind_theorem_name, get_unit_hyps};
use crate::proof::{
    Obligation, ObligationKind, Omission, Proof, ProofCore, ProofProps, QedStep, Step, StepCore,
    StepNumber, Usable, UseDef, UseDefCore, get_step_name,
};
use crate::substitution::shift_expr;
use crate::temporal::get_scope_time;

/// `AT_NOWHERE`.
pub fn at_nowhere() -> Expr {
    located(ExprCore::At { is_except: false }, None)
}

fn is_anonymous(step: Option<&StepNumber>) -> bool {
    matches!(
        step,
        Some(StepNumber::Named {
            is_anonymous: true,
            ..
        })
    )
}

pub fn get_true(from: &ExprProps) -> Expr {
    at_props(
        ExprCore::Internal {
            builtin: Builtin::TRUE,
        },
        from,
    )
}

/// The properties `at` takes from a step: its location.
fn get_step_props(props: &ProofProps) -> ExprProps {
    ExprProps {
        location: props.location.clone(),
        is_atomic: false,
    }
}

/// `context[context.length - index]`, which is undefined out of range.
fn get_from_end(context: &[Hyp], index: isize) -> Option<(usize, &Hyp)> {
    let position = usize::try_from(to_index(context.len()).checked_sub(index)?).ok()?;
    context.get(position).map(|hyp| (position, hyp))
}

/// `{...hyp, visibility}` on a fact or a definition.
fn with_visibility(hyp: &HypNode, visibility: Visibility) -> Hyp {
    let core = match &hyp.core {
        HypCore::Fact {
            expression,
            time,
            use_location,
            ..
        } => HypCore::Fact {
            expression: expression.clone(),
            visibility,
            time: *time,
            use_location: use_location.clone(),
        },
        HypCore::Defn {
            definition,
            where_defined,
            is_local,
            is_constness_unset,
            ..
        } => HypCore::Defn {
            definition: definition.clone(),
            where_defined: *where_defined,
            visibility,
            is_local: *is_local,
            is_constness_unset: *is_constness_unset,
        },
        other => other.clone(),
    };
    hyp.with_core(core)
}

// Each visible fact of the sequent, shifted past the hypotheses after it.
fn get_assumed_facts(offset: usize, sequent: &Sequent) -> Result<Vec<Expr>> {
    let length = sequent.context.len();
    let mut facts = Vec::new();
    for (index, hyp) in sequent.context.iter().enumerate() {
        if let HypCore::Fact {
            expression,
            visibility: Visibility::Visible,
            ..
        } = &hyp.core
        {
            facts.push(shift_expr(
                to_index(offset + length - 1 - index),
                expression,
            )?);
        }
    }
    Ok(facts)
}

fn get_step_definition(step: &Step, body: Expr, time: Time) -> Result<Hyp> {
    let Some(number) = &step.props.step else {
        return Err(ObligationError::assert_failure());
    };
    Ok(Rc::new(HypNode {
        core: HypCore::Defn {
            definition: Defn {
                core: DefnCore::Operator {
                    name: get_step_name(number),
                    body,
                },
                location: step.props.location.clone(),
            },
            where_defined: WhereDefined::Proof(time),
            visibility: Visibility::Visible,
            is_local: true,
            is_constness_unset: false,
        },
        location: step.props.location.clone(),
    }))
}

/// `proveAssertion`: the sequent that proves the step's assertion, and its time. The proof of an
/// assertion leaves the always scope when the assertion assumes a fact that holds only now.
pub fn prove_assertion(
    context: &[Hyp],
    sequent: &Sequent,
    step: &Step,
    time: Time,
) -> Result<(Sequent, Time)> {
    let visibility = if is_anonymous(step.props.step.as_ref()) {
        Visibility::Visible
    } else {
        Visibility::Hidden
    };
    let hyps = sequent.context.iter().map(|hyp| match hyp.core {
        HypCore::Fact { .. } => with_visibility(hyp, visibility),
        _ => hyp.clone(),
    });
    let props = get_step_props(&step.props);
    let body = at_props(
        ExprCore::List {
            bullet: Bullet::Refs,
            items: get_assumed_facts(2, sequent)?,
        },
        &props,
    );
    let scope_time = get_scope_time(&sequent.context, time);
    let mut extended: Vec<Hyp> = context.iter().cloned().chain(hyps).collect();
    extended.push(get_fact(
        get_true(&props),
        Visibility::Hidden,
        time,
        step.props.location.clone(),
    ));
    extended.push(get_step_definition(step, body, scope_time)?);
    extended.push(get_fact(
        at_props(ExprCore::Ix { index: 1 }, &props),
        Visibility::Hidden,
        scope_time,
        step.props.location.clone(),
    ));
    Ok((
        Sequent {
            context: extended,
            active: shift_expr(3, &sequent.active)?,
        },
        scope_time,
    ))
}

/// `useAssertion`: the sequent after the step, which may use its assertion.
pub fn use_assertion(
    is_suffices: bool,
    context: &[Hyp],
    goal: &Expr,
    sequent: &Sequent,
    step: &Step,
    time: Time,
) -> Result<Sequent> {
    let visibility = if is_suffices || is_anonymous(step.props.step.as_ref()) {
        Visibility::Visible
    } else {
        Visibility::Hidden
    };
    let props = get_step_props(&step.props);
    let mut extended = context.to_vec();
    extended.push(get_step_definition(
        step,
        at_expr(&exprify_sequent(sequent), &props),
        time,
    )?);
    extended.push(get_fact(
        at_props(ExprCore::Ix { index: 1 }, &props),
        visibility,
        time,
        step.props.location.clone(),
    ));
    Ok(Sequent {
        context: extended,
        active: shift_expr(2, goal)?,
    })
}

// A cited step or definition keeps the scope it was proved in, and any other fact takes the
// current one.
fn get_fact_time(context: &[Hyp], fact: &ExprNode, time: Time) -> Time {
    let ExprCore::Ix { index } = fact.core else {
        return time;
    };
    match get_from_end(context, index).map(|found| &found.1.core) {
        Some(HypCore::Fact { time, .. }) => *time,
        Some(HypCore::Defn {
            where_defined: WhereDefined::Proof(time),
            ..
        }) => *time,
        _ => Time::Always,
    }
}

fn set_definition(visibility: Visibility, context: Vec<Hyp>, def: &UseDef) -> Result<Vec<Hyp>> {
    let index = match &def.core {
        UseDefCore::Dx { index } => *index,
        UseDefCore::Dvar { name } => {
            return Err(ObligationError::proof(format!("Unknown definition {name}")));
        }
    };
    let Some((position, hyp)) = get_from_end(&context, index) else {
        return Ok(context);
    };
    if !matches!(hyp.core, HypCore::Defn { .. }) {
        return Err(ObligationError::proof(
            "Indicated point is not a definition",
        ));
    }
    let changed = with_visibility(hyp, visibility);
    let mut result = context;
    result[position] = changed;
    Ok(result)
}

/// A `Mem` of a second argument TypeScript would read as undefined, which tlapm never makes, does
/// not match.
fn is_domain_match(fact: &ExprNode, domain: &ExprNode) -> bool {
    is_builtin_apply(fact, Builtin::Mem).is_some_and(|args| {
        matches!(
            args.first().map(|first| &first.core),
            Some(ExprCore::Ix { index: 0 })
        ) && args
            .get(1)
            .is_some_and(|second| is_equal_expr(domain, second))
    })
}

fn set_expression(
    on_warning: &mut Warn,
    visibility: Visibility,
    fact: &Expr,
    context: Vec<Hyp>,
) -> Result<Vec<Hyp>> {
    let mut is_found = false;
    let mut current = fact.clone();
    let mut result = context;
    for index in (0..result.len()).rev() {
        current = shift_expr(-1, &current)?;
        let hyp = result[index].clone();
        if let HypCore::Fact { expression, .. } = &hyp.core
            && is_equal_expr(expression, &current)
        {
            is_found = true;
            result[index] = with_visibility(&hyp, visibility);
            continue;
        }
        if let HypCore::Fresh {
            name,
            shape,
            level,
            domain: Some(domain),
            ..
        } = &hyp.core
            && is_domain_match(&current, domain)
        {
            is_found = true;
            result[index] = hyp.with_core(HypCore::Fresh {
                name: name.clone(),
                shape: *shape,
                level: *level,
                domain: Some(domain.clone()),
                domain_visibility: visibility,
            });
        }
    }
    if !is_found {
        let message = "This expression does not appear in the context and cannot be hidden.";
        on_warning(get_error_note(
            fact.location.as_ref(),
            &format!("{message}\n"),
        ));
        return Err(ObligationError::proof_failure(
            message,
            "proof.Gen.set_expr",
        ));
    }
    Ok(result)
}

/// The lines of tlapm's --toolbox and --line options, which select the proofs to generate.
/// `end` may be infinite, as the TypeScript's `Infinity`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct LineRange {
    pub start: f64,
    pub end: f64,
}

fn obligate(sequent: Sequent, from: &ProofProps, kind: ObligationKind) -> Obligation {
    Obligation {
        sequent,
        location: from.location.clone(),
        kind,
        method: from.method.clone(),
    }
}

#[derive(Clone, Debug, Default)]
struct ProofSummary {
    total: usize,
    absent: Vec<Locus>,
    omitted: Vec<Locus>,
}

fn join_summaries(left: ProofSummary, right: ProofSummary) -> ProofSummary {
    ProofSummary {
        total: left.total + right.total,
        absent: [left.absent, right.absent].concat(),
        omitted: [left.omitted, right.omitted].concat(),
    }
}

fn get_obligation_count(props: &ProofProps) -> usize {
    props.obligations.as_ref().map_or(0, Vec::len)
}

/// A step's proof, for the steps that have one.
fn get_step_proof(step: &Step) -> Option<&Proof> {
    match &step.core {
        StepCore::Assert { proof, .. }
        | StepCore::Suffices { proof, .. }
        | StepCore::Pcase { proof, .. }
        | StepCore::Pick { proof, .. } => Some(proof),
        _ => None,
    }
}

fn get_step_summary(step: &Step) -> ProofSummary {
    if let StepCore::Use { .. } = step.core {
        return ProofSummary {
            total: get_obligation_count(&step.props),
            ..ProofSummary::default()
        };
    }
    get_step_proof(step).map_or_else(ProofSummary::default, get_proof_summary)
}

fn get_proof_summary(proof: &Proof) -> ProofSummary {
    if let ProofCore::Steps { steps, qed } = &proof.core {
        let mut summaries = steps
            .iter()
            .map(get_step_summary)
            .chain([get_proof_summary(&qed.proof)]);
        let first = summaries.next().unwrap_or_default();
        return summaries.fold(first, join_summaries);
    }
    let (ProofCore::Omitted(omission), Some(obligations), Some(location)) =
        (&proof.core, &proof.props.obligations, &proof.props.location)
    else {
        return ProofSummary {
            total: get_obligation_count(&proof.props),
            ..ProofSummary::default()
        };
    };
    ProofSummary {
        total: obligations.len(),
        absent: if *omission == Omission::Implicit {
            vec![location.clone()]
        } else {
            Vec::new()
        },
        omitted: if *omission == Omission::Explicit {
            vec![location.clone()]
        } else {
            Vec::new()
        },
    }
}

#[derive(Clone, Debug)]
pub struct TheoremSummary {
    pub total: usize,
    pub absent: Vec<Locus>,
    pub omitted: Vec<Locus>,
    pub location: Option<Locus>,
}

#[derive(Clone, Debug)]
pub struct ModuleSummary {
    pub total: usize,
    pub absent: Vec<Locus>,
    pub omitted: Vec<Locus>,
    pub theorems: Vec<TheoremSummary>,
}

/// What `generateModule` returns.
#[derive(Clone, Debug)]
pub struct GeneratedModule {
    pub obligations: Vec<Obligation>,
    pub summary: ModuleSummary,
}

/// `createGenerator`'s closure. It takes `on_warning` with each module, so the caller can lend it
/// to others between modules.
pub struct Generator {
    input_files: HashSet<String>,
    lines: LineRange,
}

pub fn create_generator(input_files: HashSet<String>, lines: LineRange) -> Generator {
    Generator { input_files, lines }
}

impl Generator {
    fn generate(
        &self,
        on_warning: &mut Warn,
        sequent: Sequent,
        proof: &Proof,
        time: Time,
    ) -> Result<Proof> {
        let Some(location) = &proof.props.location else {
            return Ok(proof.clone());
        };
        if !self.input_files.contains(&*location.file)
            || f64::from(location.end_line) < self.lines.start
            || f64::from(location.start_line) > self.lines.end
        {
            return Ok(proof.clone());
        }
        let kind = match &proof.core {
            ProofCore::Obvious => ObligationKind::Main,
            ProofCore::Omitted(omission) => ObligationKind::Omitted(*omission),
            ProofCore::Error(message) => ObligationKind::Error(message.clone()),
            ProofCore::By { .. } => return Err(ObligationError::proof("Proof.Gen.generate")),
            ProofCore::Steps { steps, qed } => {
                let ((inner_sequent, inner_time), generated) =
                    map_accumulate((sequent, time), steps, |state, step| {
                        let (next, generated, next_time) =
                            self.generate_step(on_warning, state.0, step, state.1)?;
                        Ok(((next, next_time), generated))
                    })?;
                let qed_proof = self.generate(on_warning, inner_sequent, &qed.proof, inner_time)?;
                return Ok(Proof {
                    core: ProofCore::Steps {
                        steps: generated,
                        qed: Box::new(QedStep {
                            proof: qed_proof,
                            props: qed.props.clone(),
                        }),
                    },
                    props: proof.props.clone(),
                });
            }
        };
        let mut props = proof.props.clone();
        props.obligations = Some(vec![obligate(sequent, &proof.props, kind)]);
        Ok(Proof {
            core: proof.core.clone(),
            props,
        })
    }

    fn generate_step(
        &self,
        on_warning: &mut Warn,
        sequent: Sequent,
        step: &Step,
        time: Time,
    ) -> Result<(Sequent, Step, Time)> {
        match &step.core {
            StepCore::Forget { count } => {
                let length = sequent.context.len();
                let context = sequent
                    .context
                    .iter()
                    .enumerate()
                    .map(|(index, hyp)| match hyp.core {
                        HypCore::Fact {
                            visibility: Visibility::Visible,
                            ..
                        } if count + index < length => with_visibility(hyp, Visibility::Hidden),
                        _ => hyp.clone(),
                    })
                    .collect();
                Ok((
                    Sequent {
                        context,
                        active: sequent.active,
                    },
                    step.clone(),
                    time,
                ))
            }
            StepCore::Use { usable, .. } => {
                if let ([fact], []) = (usable.facts.as_slice(), usable.defs.as_slice()) {
                    let obligation = obligate(
                        Sequent {
                            context: sequent.context.clone(),
                            active: fact.clone(),
                        },
                        &step.props,
                        ObligationKind::Support,
                    );
                    let mut context = sequent.context.clone();
                    context.push(Rc::new(HypNode {
                        core: HypCore::Fact {
                            expression: fact.clone(),
                            visibility: Visibility::Visible,
                            time: get_fact_time(&sequent.context, fact, time),
                            use_location: step.props.use_location.clone(),
                        },
                        location: fact.location.clone(),
                    }));
                    let mut generated = step.clone();
                    generated.props.obligations = Some(vec![obligation]);
                    return Ok((
                        Sequent {
                            context,
                            active: shift_expr(1, &sequent.active)?,
                        },
                        generated,
                        time,
                    ));
                }
                if !usable.facts.is_empty() {
                    return Err(ObligationError::proof(
                        "Proof.Gen.gen_step: USE with facts and definitions",
                    ));
                }
                let mut context = sequent.context;
                for def in &usable.defs {
                    context = set_definition(Visibility::Visible, context, def)?;
                }
                Ok((
                    Sequent {
                        context,
                        active: sequent.active,
                    },
                    step.clone(),
                    time,
                ))
            }
            StepCore::Hide { usable } => {
                let mut context = sequent.context;
                for def in &usable.defs {
                    context = set_definition(Visibility::Hidden, context, def)?;
                }
                for fact in usable.facts.iter().rev() {
                    context = set_expression(on_warning, Visibility::Hidden, fact, context)?;
                }
                Ok((
                    Sequent {
                        context,
                        active: sequent.active,
                    },
                    step.clone(),
                    time,
                ))
            }
            StepCore::Define { definitions } => {
                let mut context = sequent.context;
                context.extend(definitions.iter().map(|definition| {
                    Rc::new(HypNode {
                        core: HypCore::Defn {
                            definition: definition.clone(),
                            where_defined: WhereDefined::User,
                            visibility: Visibility::Visible,
                            is_local: true,
                            is_constness_unset: false,
                        },
                        location: definition.location.clone(),
                    })
                }));
                Ok((
                    Sequent {
                        context,
                        active: shift_expr(to_index(definitions.len()), &sequent.active)?,
                    },
                    step.clone(),
                    time,
                ))
            }
            StepCore::Assert {
                sequent: asserted,
                proof,
            } => {
                let (inner, inner_time) = prove_assertion(&sequent.context, asserted, step, time)?;
                let proved = self.generate(on_warning, inner, proof, inner_time)?;
                let generated = Step {
                    core: StepCore::Assert {
                        sequent: asserted.clone(),
                        proof: proved,
                    },
                    props: step.props.clone(),
                };
                Ok((
                    use_assertion(
                        false,
                        &sequent.context,
                        &sequent.active,
                        asserted,
                        &generated,
                        time,
                    )?,
                    generated,
                    time,
                ))
            }
            StepCore::Suffices {
                sequent: asserted,
                proof,
            } => {
                let proved = self.generate(
                    on_warning,
                    use_assertion(
                        true,
                        &sequent.context,
                        &sequent.active,
                        asserted,
                        step,
                        time,
                    )?,
                    proof,
                    time,
                )?;
                let generated = Step {
                    core: StepCore::Suffices {
                        sequent: asserted.clone(),
                        proof: proved,
                    },
                    props: step.props.clone(),
                };
                let (next, next_time) =
                    prove_assertion(&sequent.context, asserted, &generated, time)?;
                Ok((next, generated, next_time))
            }
            _ => Err(ObligationError::proof("Proof.Gen.gen_step")),
        }
    }

    fn mutate_one(
        &self,
        on_warning: &mut Warn,
        context: Vec<Hyp>,
        mode: MutateMode,
        usable: Usable,
        location: &Option<Locus>,
    ) -> Result<(Vec<Hyp>, Vec<Obligation>)> {
        let props = ProofProps {
            location: location.clone(),
            step: Some(StepNumber::Unnamed { level: 0, id: 0 }),
            use_location: if mode == MutateMode::Use {
                location.clone()
            } else {
                None
            },
            ..ProofProps::default()
        };
        let core = match mode {
            MutateMode::Use => StepCore::Use {
                usable,
                is_only: false,
            },
            MutateMode::Hide => StepCore::Hide { usable },
        };
        let (sequent, generated, _) = self.generate_step(
            on_warning,
            Sequent {
                context,
                active: located(ExprCore::At { is_except: false }, location.clone()),
            },
            &Step { core, props },
            Time::Always,
        )?;
        Ok((
            sequent.context,
            generated.props.obligations.unwrap_or_default(),
        ))
    }

    // The definitions go first, then each fact on its own, shifting the facts after it.
    fn mutate(
        &self,
        on_warning: &mut Warn,
        context: Vec<Hyp>,
        mode: MutateMode,
        usable: &Usable,
        location: &Option<Locus>,
    ) -> Result<(Vec<Hyp>, Vec<Obligation>)> {
        if usable.defs.is_empty() && usable.facts.is_empty() {
            return Ok((context, Vec::new()));
        }
        let is_defs = !usable.defs.is_empty();
        let (once, facts) = match usable.facts.split_first() {
            Some((fact, facts)) if !is_defs => (
                Usable {
                    defs: Vec::new(),
                    facts: vec![fact.clone()],
                },
                facts,
            ),
            _ => (
                Usable {
                    defs: usable.defs.clone(),
                    facts: Vec::new(),
                },
                usable.facts.as_slice(),
            ),
        };
        let (next, first) = self.mutate_one(on_warning, context, mode, once, location)?;
        let rest = if is_defs {
            usable.facts.clone()
        } else {
            facts
                .iter()
                .map(|inner| shift_expr(1, inner))
                .collect::<Result<_>>()?
        };
        let (last, others) = self.mutate(
            on_warning,
            next,
            mode,
            &Usable {
                defs: Vec::new(),
                facts: rest,
            },
            location,
        )?;
        Ok((last, [first, others].concat()))
    }

    /// Module.Gen.generate.
    pub fn generate_module(
        &self,
        on_warning: &mut Warn,
        context: &[Hyp],
        module: &Mule,
    ) -> Result<GeneratedModule> {
        let mut obligations = Vec::new();
        let mut theorems = Vec::new();
        let mut summary = ProofSummary::default();
        let mut current = context.to_vec();
        for unit in &module.body {
            match &unit.core {
                ModuleUnitCore::Theorem {
                    name,
                    sequent,
                    proof,
                    ..
                } => {
                    let (hyps, bound) =
                        bind_theorem_name(name.as_deref(), sequent, &unit.location)?;
                    let named = [current, hyps].concat();
                    let context = [named.as_slice(), &bound.context].concat();
                    let time = get_scope_time(&context, Time::Always);
                    let generated = self.generate(
                        on_warning,
                        Sequent {
                            context,
                            active: bound.active,
                        },
                        proof,
                        time,
                    )?;
                    obligations.extend(collect(&generated));
                    let theorem = get_proof_summary(&generated);
                    theorems.push(TheoremSummary {
                        total: theorem.total,
                        absent: theorem.absent.clone(),
                        omitted: theorem.omitted.clone(),
                        location: unit.location.clone(),
                    });
                    summary = join_summaries(summary, theorem);
                    let fact = if name.is_none() {
                        at_expr(
                            &exprify_sequent(sequent),
                            &ExprProps {
                                location: unit.location.clone(),
                                is_atomic: false,
                            },
                        )
                    } else {
                        located(ExprCore::Ix { index: 1 }, unit.location.clone())
                    };
                    current = named;
                    current.push(get_fact(
                        fact,
                        Visibility::Hidden,
                        Time::Always,
                        unit.location.clone(),
                    ));
                }
                ModuleUnitCore::Submod { module } => {
                    let generated = self.generate_module(on_warning, &current, module)?;
                    obligations.extend(generated.obligations);
                    summary = join_summaries(
                        summary,
                        ProofSummary {
                            total: generated.summary.total,
                            absent: generated.summary.absent,
                            omitted: generated.summary.omitted,
                        },
                    );
                }
                ModuleUnitCore::Mutate { mode, usable } => {
                    let (next, generated) =
                        self.mutate(on_warning, current, *mode, usable, &unit.location)?;
                    obligations.extend(generated);
                    current = next;
                }
                _ => current.extend(get_unit_hyps(unit)?),
            }
        }
        Ok(GeneratedModule {
            obligations,
            summary: ModuleSummary {
                total: summary.total,
                absent: summary.absent,
                omitted: summary.omitted,
                theorems,
            },
        })
    }
}

// collect: a QED's obligations come before its sibling steps', and a step's own before its proof's.
fn collect(proof: &Proof) -> Vec<Obligation> {
    fn visit_proof(item: &Proof, obligations: &mut Vec<Obligation>) {
        if let ProofCore::Steps { steps, qed } = &item.core {
            visit_proof(&qed.proof, obligations);
            for step in steps {
                visit_step(step, obligations);
            }
            return;
        }
        if let Some(own) = &item.props.obligations {
            obligations.extend(own.iter().cloned());
        }
    }
    fn visit_step(step: &Step, obligations: &mut Vec<Obligation>) {
        if let (StepCore::Use { .. }, Some(own)) = (&step.core, &step.props.obligations) {
            obligations.extend(own.iter().cloned());
        }
        if let Some(proof) = get_step_proof(step) {
            visit_proof(proof, obligations);
        }
    }
    let mut obligations = Vec::new();
    visit_proof(proof, &mut obligations);
    obligations
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::errors::quote_json;
    use crate::expression::{Bound, BoundDomain, Level, Modal, ObligationWarning, Quantifier};
    use crate::module::{Declaration, ModuleUnit};
    use crate::pragma::OldMethod;

    // The fixtures are the inputs `generate.ts` received under Bun: the Mules normalize made from
    // small modules with proofs of every step kind, and hand-built ones. They are S-expressions,
    // read below, and the expected values are what `generate.ts` returned for them, compared as a
    // canonical JSON dump (sorted keys, no undefined), by its length and FNV-1a hash.

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
                                't' => text.push('\t'),
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

    fn is_none(sexp: &Sexp) -> bool {
        matches!(sexp, Sexp::Atom(text) if text == "_")
    }

    fn optional<Value>(sexp: &Sexp, read: impl Fn(&Sexp) -> Value) -> Option<Value> {
        if is_none(sexp) {
            None
        } else {
            Some(read(sexp))
        }
    }

    fn list<Value>(sexp: &Sexp, read: impl Fn(&Sexp) -> Value) -> Vec<Value> {
        items(sexp).iter().map(read).collect()
    }

    fn locus_at(line: u32, start_column: u32, end_line: u32, end_column: u32) -> Locus {
        Locus {
            file: Rc::from("M.tla"),
            start_line: line,
            start_column,
            end_line,
            end_column,
        }
    }

    /// `@line:column-line:column`, then `@file` when the file is not M.tla.
    fn read_locus(sexp: &Sexp) -> Option<Locus> {
        optional(sexp, |sexp| {
            let mut parts = atom(sexp).trim_start_matches('@').split('@');
            let numbers: Vec<u32> = parts
                .next()
                .expect("position")
                .split(['-', ':'])
                .map(|part| part.parse().expect("line or column"))
                .collect();
            let mut locus = locus_at(numbers[0], numbers[1], numbers[2], numbers[3]);
            if let Some(file) = parts.next() {
                locus.file = Rc::from(file);
            }
            locus
        })
    }

    fn read_builtin(sexp: &Sexp) -> Builtin {
        match atom(sexp) {
            "TRUE" => Builtin::TRUE,
            "Mem" => Builtin::Mem,
            "Eq" => Builtin::Eq,
            "Subseteq" => Builtin::Subseteq,
            "Conj" => Builtin::Conj,
            "SUBSET" => Builtin::SUBSET,
            "Implies" => Builtin::Implies,
            "Prime" => Builtin::Prime,
            "BoxTrue" => Builtin::BoxTrue,
            "Unprimable" => Builtin::Unprimable,
            other => panic!("builtin {other}"),
        }
    }

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

    fn read_modal(sexp: &Sexp) -> Modal {
        if atom(sexp) == "Box" {
            Modal::Box
        } else {
            Modal::Dia
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
                builtin: read_builtin(&fields[1]),
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
            kind @ ("Sub" | "Tsub") => {
                let modal = read_modal(&fields[1]);
                let action = read_expr(&fields[2]);
                let subscript = read_expr(&fields[3]);
                if kind == "Sub" {
                    ExprCore::Sub {
                        modal,
                        action,
                        subscript,
                    }
                } else {
                    ExprCore::Tsub {
                        modal,
                        action,
                        subscript,
                    }
                }
            }
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
        let core = match atom(&fields[0]) {
            "Operator" => DefnCore::Operator {
                name: text(&fields[1]),
                body: read_expr(&fields[2]),
            },
            other => panic!("definition {other}"),
        };
        Defn {
            core,
            location: read_locus(&fields[fields.len() - 1]),
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

    fn read_method(sexp: &Sexp) -> OldMethod {
        let fields = items(sexp);
        OldMethod {
            name: text(&fields[1]),
            tactic: optional(&fields[2], text),
            timeout: optional(&fields[3], number),
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
            method: optional(&fields[3], read_method),
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

    fn read_omission(sexp: &Sexp) -> Omission {
        match atom(sexp) {
            "Implicit" => Omission::Implicit,
            "Explicit" => Omission::Explicit,
            _ => Omission::Elsewhere,
        }
    }

    fn read_proof(sexp: &Sexp) -> Proof {
        let fields = items(sexp);
        let core = match atom(&fields[0]) {
            "Obvious" => ProofCore::Obvious,
            "Omitted" => ProofCore::Omitted(read_omission(&fields[1])),
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
            "Use" => StepCore::Use {
                usable: read_usable(&fields[1]),
                is_only: boolean(&fields[2]),
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

    fn read_unit(sexp: &Sexp) -> ModuleUnit {
        let fields = items(sexp);
        let core = match atom(&fields[0]) {
            "Constants" => ModuleUnitCore::Constants {
                declarations: list(&fields[1], |sexp| {
                    let declaration = items(sexp);
                    Declaration {
                        name: text(&declaration[0]),
                        shape: number(&declaration[1]),
                    }
                }),
            },
            "Variables" => ModuleUnitCore::Variables {
                names: list(&fields[1], text),
            },
            "Definition" => ModuleUnitCore::Definition {
                definition: read_defn(&fields[1]),
                where_defined: read_where(&fields[2]),
                visibility: read_visibility(&fields[3]),
                is_local: boolean(&fields[4]),
            },
            "Axiom" => ModuleUnitCore::Axiom {
                name: optional(&fields[1], text),
                expression: read_expr(&fields[2]),
            },
            "Theorem" => ModuleUnitCore::Theorem {
                name: optional(&fields[1], text),
                sequent: read_sequent(&fields[2]),
                axiom_count: number(&fields[3]),
                proof: read_proof(&fields[4]),
            },
            "Submod" => ModuleUnitCore::Submod {
                module: Box::new(read_mule(&fields[1])),
            },
            "Mutate" => ModuleUnitCore::Mutate {
                mode: if atom(&fields[1]) == "Use" {
                    MutateMode::Use
                } else {
                    MutateMode::Hide
                },
                usable: read_usable(&fields[2]),
            },
            other => panic!("unit {other}"),
        };
        ModuleUnit {
            core,
            location: read_locus(&fields[fields.len() - 1]),
        }
    }

    fn read_mule(sexp: &Sexp) -> Mule {
        Mule {
            body: list(&items(sexp)[1], read_unit),
            ..Mule::default()
        }
    }

    /// JSON as `JSON.stringify` writes it, with each object's keys sorted and absent ones left out.
    enum Json {
        Raw(String),
        Array(Vec<Json>),
        Object(Vec<(&'static str, Json)>),
    }

    fn json_text(value: &str) -> Json {
        Json::Raw(quote_json(value))
    }

    fn json_number(value: impl std::fmt::Display) -> Json {
        Json::Raw(value.to_string())
    }

    fn json_kind(kind: &str, mut fields: Vec<(&'static str, Json)>) -> Json {
        fields.push(("kind", json_text(kind)));
        Json::Object(fields)
    }

    fn json_list<Value>(values: &[Value], dump: impl Fn(&Value) -> Json) -> Json {
        Json::Array(values.iter().map(dump).collect())
    }

    fn with_location(
        mut fields: Vec<(&'static str, Json)>,
        location: &Option<Locus>,
    ) -> Vec<(&'static str, Json)> {
        if let Some(locus) = location {
            fields.push(("location", dump_locus(locus)));
        }
        fields
    }

    fn write_json(value: &Json, output: &mut String) {
        match value {
            Json::Raw(text) => output.push_str(text),
            Json::Array(values) => {
                output.push('[');
                for (index, inner) in values.iter().enumerate() {
                    if index > 0 {
                        output.push(',');
                    }
                    write_json(inner, output);
                }
                output.push(']');
            }
            Json::Object(fields) => {
                let mut sorted: Vec<&(&str, Json)> = fields.iter().collect();
                sorted.sort_by(|left, right| left.0.cmp(right.0));
                output.push('{');
                for (index, (key, inner)) in sorted.into_iter().enumerate() {
                    if index > 0 {
                        output.push(',');
                    }
                    output.push_str(&quote_json(key));
                    output.push(':');
                    write_json(inner, output);
                }
                output.push('}');
            }
        }
    }

    fn dump_locus(locus: &Locus) -> Json {
        Json::Object(vec![
            ("file", json_text(&locus.file)),
            ("startLine", json_number(locus.start_line)),
            ("startColumn", json_number(locus.start_column)),
            ("endLine", json_number(locus.end_line)),
            ("endColumn", json_number(locus.end_column)),
        ])
    }

    fn dump_bound(bound: &Bound) -> Json {
        let domain = match &bound.domain {
            BoundDomain::NoDomain => json_kind("NoDomain", vec![]),
            BoundDomain::Ditto => json_kind("Ditto", vec![]),
            BoundDomain::Domain(expression) => {
                json_kind("Domain", vec![("expression", dump_expr(expression))])
            }
        };
        Json::Object(vec![
            ("name", json_text(&bound.name)),
            ("level", json_text(&format!("{:?}", bound.level))),
            ("domain", domain),
        ])
    }

    fn dump_expr(expression: &ExprNode) -> Json {
        let (kind, mut fields) = match &expression.core {
            ExprCore::Ix { index } => ("Ix", vec![("index", json_number(index))]),
            ExprCore::Opaque { name } => ("Opaque", vec![("name", json_text(name))]),
            ExprCore::Internal { builtin } => {
                ("Internal", vec![("builtin", json_text(builtin.name()))])
            }
            ExprCore::Apply { operator, args } => (
                "Apply",
                vec![
                    ("operator", dump_expr(operator)),
                    ("args", json_list(args, |arg| dump_expr(arg))),
                ],
            ),
            ExprCore::Sequent { sequent } => ("Sequent", vec![("sequent", dump_sequent(sequent))]),
            ExprCore::List { bullet, items } => (
                "List",
                vec![
                    ("bullet", json_text(&format!("{bullet:?}"))),
                    ("items", json_list(items, |item| dump_expr(item))),
                ],
            ),
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => (
                "Quant",
                vec![
                    ("quantifier", json_text(&format!("{quantifier:?}"))),
                    ("bounds", json_list(bounds, dump_bound)),
                    ("body", dump_expr(body)),
                ],
            ),
            ExprCore::Sub {
                modal,
                action,
                subscript,
            } => (
                "Sub",
                vec![
                    ("modal", json_text(&format!("{modal:?}"))),
                    ("action", dump_expr(action)),
                    ("subscript", dump_expr(subscript)),
                ],
            ),
            ExprCore::Tsub {
                modal,
                action,
                subscript,
            } => (
                "Tsub",
                vec![
                    ("modal", json_text(&format!("{modal:?}"))),
                    ("action", dump_expr(action)),
                    ("subscript", dump_expr(subscript)),
                ],
            ),
            ExprCore::At { is_except } => ("At", vec![("isExcept", json_number(is_except))]),
            other => panic!("expression {other:?}"),
        };
        if expression.is_atomic {
            fields.push(("isAtomic", json_number(true)));
        }
        json_kind(kind, with_location(fields, &expression.location))
    }

    fn dump_method(method: &OldMethod) -> Json {
        let mut fields = vec![("name", json_text(&method.name))];
        if let Some(tactic) = &method.tactic {
            fields.push(("tactic", json_text(tactic)));
        }
        if let Some(timeout) = method.timeout {
            fields.push(("timeout", json_number(timeout)));
        }
        Json::Object(fields)
    }

    fn dump_defn(definition: &Defn) -> Json {
        let (kind, fields) = match &definition.core {
            DefnCore::Operator { name, body } => (
                "Operator",
                vec![("name", json_text(name)), ("body", dump_expr(body))],
            ),
            other => panic!("definition {other:?}"),
        };
        json_kind(kind, with_location(fields, &definition.location))
    }

    fn dump_hyp(hyp: &HypNode) -> Json {
        let (kind, fields) = match &hyp.core {
            HypCore::Fresh {
                name,
                shape,
                level,
                domain,
                domain_visibility,
            } => {
                let mut fields = vec![
                    ("name", json_text(name)),
                    ("shape", json_number(shape)),
                    ("level", json_text(&format!("{level:?}"))),
                    (
                        "domainVisibility",
                        json_text(&format!("{domain_visibility:?}")),
                    ),
                ];
                if let Some(domain) = domain {
                    fields.push(("domain", dump_expr(domain)));
                }
                ("Fresh", fields)
            }
            HypCore::Flex { name } => ("Flex", vec![("name", json_text(name))]),
            HypCore::Defn {
                definition,
                where_defined,
                visibility,
                is_local,
                is_constness_unset,
            } => {
                let mut fields = vec![
                    ("definition", dump_defn(definition)),
                    (
                        "whereDefined",
                        match where_defined {
                            WhereDefined::Proof(time) => {
                                json_kind("Proof", vec![("time", json_text(&format!("{time:?}")))])
                            }
                            other => json_text(&format!("{other:?}")),
                        },
                    ),
                    ("visibility", json_text(&format!("{visibility:?}"))),
                    ("isLocal", json_number(is_local)),
                ];
                if *is_constness_unset {
                    fields.push(("isConstnessUnset", json_number(true)));
                }
                ("Defn", fields)
            }
            HypCore::Fact {
                expression,
                visibility,
                time,
                use_location,
            } => {
                let mut fields = vec![
                    ("expression", dump_expr(expression)),
                    ("visibility", json_text(&format!("{visibility:?}"))),
                    ("time", json_text(&format!("{time:?}"))),
                ];
                if let Some(locus) = use_location {
                    fields.push(("useLocation", dump_locus(locus)));
                }
                ("Fact", fields)
            }
        };
        json_kind(kind, with_location(fields, &hyp.location))
    }

    fn dump_sequent(sequent: &Sequent) -> Json {
        Json::Object(vec![
            ("context", json_list(&sequent.context, |hyp| dump_hyp(hyp))),
            ("active", dump_expr(&sequent.active)),
        ])
    }

    fn dump_obligation(obligation: &Obligation) -> Json {
        let kind = match &obligation.kind {
            ObligationKind::Main => json_kind("Main", vec![]),
            ObligationKind::Support => json_kind("Support", vec![]),
            ObligationKind::Error(message) => {
                json_kind("Error", vec![("message", json_text(message))])
            }
            ObligationKind::Omitted(omission) => json_kind(
                "Omitted",
                vec![("omission", json_text(&format!("{omission:?}")))],
            ),
        };
        let mut fields = vec![
            ("sequent", dump_sequent(&obligation.sequent)),
            ("kind", kind),
        ];
        if let Some(method) = &obligation.method {
            fields.push(("method", dump_method(method)));
        }
        Json::Object(with_location(fields, &obligation.location))
    }

    fn dump_loci(loci: &[Locus]) -> Json {
        json_list(loci, dump_locus)
    }

    fn dump_summary(summary: &ModuleSummary) -> Json {
        Json::Object(vec![
            ("total", json_number(summary.total)),
            ("absent", dump_loci(&summary.absent)),
            ("omitted", dump_loci(&summary.omitted)),
            (
                "theorems",
                json_list(&summary.theorems, |theorem| {
                    Json::Object(with_location(
                        vec![
                            ("total", json_number(theorem.total)),
                            ("absent", dump_loci(&theorem.absent)),
                            ("omitted", dump_loci(&theorem.omitted)),
                        ],
                        &theorem.location,
                    ))
                }),
            ),
        ])
    }

    fn to_text(value: &Json) -> String {
        let mut output = String::new();
        write_json(value, &mut output);
        output
    }

    /// The length and FNV-1a hash of a dump, as the expectations give them.
    fn digest(value: &Json) -> (usize, String) {
        let text = to_text(value);
        let hash = text.bytes().fold(0xcbf2_9ce4_8422_2325_u64, |hash, byte| {
            (hash ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3)
        });
        (text.len(), format!("{hash:#018x}"))
    }

    const WHOLE: LineRange = LineRange {
        start: 0.0,
        end: f64::INFINITY,
    };

    fn run(
        fixture: &str,
        files: &[&str],
        lines: LineRange,
    ) -> (Result<GeneratedModule>, Vec<ObligationWarning>) {
        let parsed = parse(fixture);
        let (context, module) = match atom(&items(&parsed)[0]) {
            "case" => (
                list(&items(&parsed)[1], read_hyp),
                read_mule(&items(&parsed)[2]),
            ),
            _ => (Vec::new(), read_mule(&parsed)),
        };
        let generator =
            create_generator(files.iter().map(|file| (*file).to_owned()).collect(), lines);
        let mut warnings = Vec::new();
        let result =
            generator.generate_module(&mut |warning| warnings.push(warning), &context, &module);
        (result, warnings)
    }

    fn get_shape(obligations: &[Obligation]) -> Vec<String> {
        obligations
            .iter()
            .map(|obligation| {
                let kind = match obligation.kind {
                    ObligationKind::Main => "Main",
                    ObligationKind::Support => "Support",
                    ObligationKind::Error(_) => "Error",
                    ObligationKind::Omitted(_) => "Omitted",
                };
                let line = obligation
                    .location
                    .as_ref()
                    .map_or_else(|| "-".to_owned(), |locus| locus.start_line.to_string());
                format!("{kind}@{line}")
            })
            .collect()
    }

    /// Checks a module's obligations and summary against the TypeScript's.
    fn check(
        fixture: &str,
        files: &[&str],
        lines: LineRange,
        shape: &[&str],
        obligations: (usize, &str),
        summary: (usize, &str),
    ) {
        let (result, warnings) = run(fixture, files, lines);
        let generated = result.expect("generated");
        assert!(warnings.is_empty());
        assert_eq!(get_shape(&generated.obligations), shape);
        let dumped = json_list(&generated.obligations, dump_obligation);
        let (length, hash) = digest(&dumped);
        assert_eq!((length, hash.as_str()), obligations, "{}", to_text(&dumped));
        let (length, hash) = digest(&dump_summary(&generated.summary));
        assert_eq!((length, hash.as_str()), summary);
    }

    fn check_error(fixture: &str, expected: ObligationError, warning: Option<&str>) {
        let (result, warnings) = run(fixture, &["M.tla"], WHOLE);
        assert_eq!(result.err(), Some(expected));
        assert_eq!(
            warnings,
            warning
                .map(|text| ObligationWarning {
                    text: text.to_owned(),
                    channel: crate::expression::Channel::Stderr,
                })
                .into_iter()
                .collect::<Vec<_>>()
        );
    }

    const STEPS: &str = r#"
        (mule ((Constants (("S" 0) ("T" 0) ("P" 1)) @2:11-2:12) (Variables ("x") @3:10-3:11) (Definition
        (Operator "Def" (Apply (Internal Subseteq) ((Ix 4 @4:8-4:9) (Ix 3 @4:20-4:21)) @4:8-4:21)
        @4:1-4:21) User Hidden false @4:1-4:21) (Definition (Operator "Inv" (Apply (Internal Mem) ((Ix 2
        @5:8-5:9) (Ix 5 @5:14-5:15)) @5:8-5:15) @5:1-5:15) User Hidden false @5:1-5:15) (Axiom "Ax"
        (Apply (Internal Eq) ((Ix 6 @7:13-7:14) (Ix 5 @7:17-7:18)) @7:13-7:18) @7:1-7:18) (Theorem "L1"
        (sequent () (Apply (Internal Eq) ((Ix 8 @9:13-9:14) (Ix 8 @9:17-9:18)) @9:13-9:18)) 0 (Obvious
        (props @10:1-10:8 _ _ _)) @9:1-10:8) (Theorem "L2" (sequent ((Fresh "a" 0 Constant (Ix 10
        @12:30-12:31) Visible @12:20-12:31) (Fact (Apply (Ix 9 @12:33-12:37) ((Ix 1 @12:35-12:36))
        @12:33-12:37) Visible Always _ @12:33-12:37)) (Apply (Internal Conj) ((Apply (Ix 10
        @12:44-12:48) ((Ix 2 @12:46-12:47)) @12:44-12:48) (Ix 8 @12:52-12:55)) @12:44-12:55)) 0 (Steps
        ((Assert (sequent () (Ix 9 @13:7-13:10)) (Steps ((Use (usable () ((Dx 12 @14:13-14:16))) false
        (props @14:3-14:5 (Named 2 "_a7" true) _ _)) (Use (usable ((Ix 10 @14:6-14:8)) ()) false (props
        @14:6-14:8 (Named 2 "_a8" true) _ @14:3-14:5))) (Obvious (props @14:3-14:5 (Named 2 "_a9" true)
        _ _)) (props @14:3-14:5 (Named 2 "_a9" true) _ _) (props @14:3-14:5 (Unnamed 2 0) _ _)) (props
        @13:1-14:5 (Named 1 "1" false) _ _)) (Suffices (sequent () (Apply (Ix 13 @15:16-15:20) ((Ix 4
        @15:18-15:19)) @15:16-15:20)) (Steps ((Use (usable ((Ix 4 @15:24-15:28)) ()) false (props
        @15:24-15:28 (Named 2 "_a10" true) _ @15:21-15:23))) (Obvious (props @15:21-15:23 (Named 2
        "_a11" true) _ _)) (props @15:21-15:23 (Named 2 "_a11" true) _ _) (props @15:21-15:23 (Unnamed 2
        0) _ _)) (props @15:1-15:23 (Named 1 "2" false) _ _)) (Use (usable () ((Dx 14 @16:18-16:21)))
        false (props @16:1-16:21 (Named 1 "_a12" true) _ _)) (Use (usable ((Ix 5 @16:9-16:13)) ()) false
        (props @16:9-16:13 (Named 1 "_a13" true) _ @16:1-16:21)) (Assert (sequent ((Fact (Apply
        (Internal Eq) ((Ix 8 @17:12-17:13) (Ix 8 @17:16-17:17)) @17:12-17:17) Visible Always _
        @17:1-18:10)) (Apply (Ix 18 @15:16-15:20) ((Ix 9 @15:18-15:19)) @15:16-15:20)) (Obvious (props
        @18:3-18:10 (Named 2 "_a15" true) _ _)) (props @17:1-18:10 (Named 1 "3" false) _ _)) (Assert
        (sequent () (Quant Exists (("b" Constant (Domain (Ix 21 @19:18-19:19)))) (Apply (Internal Eq)
        ((Ix 1 @19:22-19:23) (Ix 11 @19:26-19:27)) @19:22-19:27) @19:1-20:10)) (Omitted Explicit (props
        @20:3-20:10 _ _ _)) (props @19:1-20:10 (Named 1 "4ex16" false) _ _)) (Suffices (sequent ((Fresh
        "b" 0 Constant (Ix 23 @19:18-19:19) Visible _) (Fact (Apply (Internal Eq) ((Ix 1 @19:22-19:23)
        (Ix 13 @19:26-19:27)) @19:22-19:27) Visible Always _ @19:22-19:27)) (Apply (Ix 23 @15:16-15:20)
        ((Ix 14 @15:18-15:19)) @15:16-15:20)) (Omitted Elsewhere (props @19:1-20:10 (Named 1 "4" false)
        _ _)) (props @19:1-20:10 (Named 1 "4" false) _ _)) (Hide (usable ((Ix 15 @21:10-21:14)) ())
        (props @21:1-21:9 (Unnamed 1 2) _ _)) (Suffices (sequent ((Fact (Internal TRUE @22:12-22:16)
        Visible Always _ @22:1-22:16)) (Apply (Ix 26 @15:16-15:20) ((Ix 17 @15:18-15:19)) @15:16-15:20))
        (Error
        "\nError:\u0020this\u0020HAVE\u0020step\u0020is\u0020applied\u0020to\u0020the\u0020following\u0020goal,\nwhich\u0020is\u0020not\u0020an\u0020implication:\n\u0020\u0020P(a)\n"
        (props @22:1-22:16 (Named 2 "5" false) _ _)) (props @22:1-22:16 (Named 1 "5" false) _ _))
        (Define ((Operator "Q" (Ix 21 @23:17-23:18) @23:12-23:18)) (props @23:1-23:18 (Unnamed 1 3) _
        _))) (Steps ((Use (usable () ((Dx 1 @25:20-25:21))) false (props @25:3-25:5 (Named 2 "_a17"
        true) _ _)) (Use (usable ((Ix 7 @25:11-25:15)) ()) false (props @25:11-25:15 (Named 2 "_a18"
        true) _ @25:3-25:5)) (Forget 1 (props @25:3-25:5 (Named 2 "_a19" true) _ _))) (Obvious (props
        @25:3-25:5 (Named 2 "_a20" true) _ _)) (props @25:3-25:5 (Named 2 "_a20" true) _ _) (props
        @25:3-25:5 (Unnamed 2 0) _ _)) (props @24:1-25:5 (Named 1 "6" false) _ _) (props @13:1-25:5
        (Named 1 "6" false) _ _)) @12:1-25:21) (Theorem "T3" (sequent () (Quant Forall (("y" Constant
        (Domain (Ix 12 @27:24-27:25)))) (Apply (Internal Mem) ((Ix 1 @27:28-27:29) (Ix 13 @27:34-27:35))
        @27:28-27:35) @27:15-27:35)) 0 (Steps ((Suffices (sequent ((Fresh "y" 0 Constant (Ix 13
        @28:16-28:17) Visible _)) (Apply (Internal Mem) ((Ix 1 @27:28-27:29) (Ix 14 @27:34-27:35))
        @27:28-27:35)) (Steps ((Use (usable ((Ix 2 @28:1-28:17)) ()) false (props @28:1-28:17 (Named 2
        "_a23" true) _ @28:1-28:17)) (Forget 1 (props @28:1-28:17 (Named 2 "_a24" true) _ _))) (Obvious
        (props @28:1-28:17 (Named 2 "_a25" true) _ _)) (props @28:1-28:17 (Named 2 "_a25" true) _ _)
        (props @28:1-28:17 (Named 2 "_a21" true) _ _)) (props @28:1-28:17 (Named 1 "_a21" true) _ _))
        (Suffices (sequent () (Apply (Internal Mem) ((Ix 4 @27:28-27:29) (Ix 17 @27:34-27:35))
        @27:28-27:35)) (Error
        "\nError:\u0020this\u0020WITNESS\u0020step\u0020is\u0020applied\u0020to\u0020the\u0020following\u0020goal,\nwhich\u0020is\u0020not\u0020an\u0020existential\u0020formula:\n\u0020\u0020y\u0020\\in\u0020S\n"
        (props @29:1-29:27 (Named 2 "_a22" true) _ _)) (props @29:1-29:27 (Named 1 "_a22" true) _ _)))
        (Obvious (props @31:9-31:16 _ _ _)) (props @30:1-31:16 (Named 1 "q" false) _ _) (props
        @28:1-31:16 (Named 1 "q" false) _ _)) @27:1-31:16) (Theorem _ (sequent () (Apply (Internal Mem)
        ((Ix 14 @33:9-33:10) (Apply (Internal SUBSET) ((Ix 13 @33:22-33:23)) @33:15-33:23))
        @33:9-33:23)) 0 (Omitted Explicit (props @34:7-34:14 _ _ _)) @33:1-34:14) (Theorem "T5" (sequent
        () (Apply (Internal Eq) ((Ix 15 @36:15-36:16) (Ix 14 @36:19-36:20)) @36:15-36:20)) 0 (Steps
        ((Assert (sequent () (Apply (Internal Eq) ((Ix 16 @37:7-37:8) (Ix 15 @37:11-37:12))
        @37:7-37:12)) (Omitted Implicit (props @37:1-37:12 _ _ _)) (props @37:1-37:12 (Named 1 "1"
        false) _ _))) (Steps ((Use (usable ((Ix 2 @38:14-38:18)) ()) false (props @38:14-38:18 (Named 2
        "_a26" true) _ @38:11-38:13))) (Obvious (props @38:11-38:13 (Named 2 "_a27" true) _ _)) (props
        @38:11-38:13 (Named 2 "_a27" true) _ _) (props @38:11-38:13 (Unnamed 2 0) _ _)) (props
        @38:1-38:13 (Named 1 "2" false) _ _) (props @37:1-38:13 (Named 1 "2" false) _ _)) @36:1-38:18)
        (Mutate Use (usable ((Ix 11 @40:5-40:7)) ((Dx 13 @40:12-40:15))) @40:1-40:15) (Mutate Hide
        (usable () ((Dx 14 @41:10-41:13))) @41:1-41:13) (Mutate Use (usable ((Ix 12 @42:5-42:7) (Ix 10
        @42:9-42:11)) ()) @42:1-42:4) (Theorem _ (sequent ((Fresh "c" 0 Constant _ Visible @44:16-44:21)
        (Fact (Apply (Internal Mem) ((Ix 1 @44:23-44:24) (Ix 21 @44:29-44:30)) @44:23-44:30) Visible
        Always _ @44:23-44:30)) (Apply (Internal BoxTrue) ((Ix 17 @44:39-44:42)) @44:37-44:42)) 0 (Steps
        ((Assert (sequent () (Ix 17 @45:7-45:10)) (Obvious (props @46:3-46:10 _ _ _)) (props @45:1-46:10
        (Named 1 "a" false) _ _))) (Steps ((Use (usable ((Ix 2 @47:12-47:16)) ()) false (props
        @47:12-47:16 (Named 2 "_a28" true) _ @47:9-47:11))) (Obvious (props @47:9-47:11 (Named 2 "_a29"
        true) _ _)) (props @47:9-47:11 (Named 2 "_a29" true) _ _) (props @47:9-47:11 (Unnamed 2 0) _ _))
        (props @47:1-47:11 (Unnamed 1 6) _ _) (props @45:1-47:11 (Unnamed 1 6) _ _)) @44:1-47:16)))
    "#;

    const NESTED: &str = r#"
        (mule ((Constants (("N" 0)) @2:10-2:11) (Variables ("v") @3:10-3:11) (Submod (mule ((Constants
        (("K" 0)) @6:10-6:11) (Theorem "InnerL" (sequent () (Apply (Internal Eq) ((Ix 1 @7:17-7:18) (Ix
        1 @7:21-7:22)) @7:17-7:22)) 0 (Steps ((Assert (sequent () (Apply (Internal Eq) ((Ix 2 @8:7-8:8)
        (Ix 2 @8:11-8:12)) @8:7-8:12)) (Obvious (props @8:13-8:42 _ (method "zenon" _ 10) _)) (props
        @8:1-8:42 (Named 1 "1" false) _ _))) (Steps ((Use (usable ((Ix 2 @9:14-9:18)) ()) false (props
        @9:14-9:18 (Named 2 "_a10" true) _ @9:11-9:13))) (Obvious (props @9:11-9:13 (Named 2 "_a11"
        true) _ _)) (props @9:11-9:13 (Named 2 "_a11" true) _ _) (props @9:11-9:13 (Unnamed 2 0) _ _))
        (props @9:1-9:13 (Named 1 "2" false) _ _) (props @8:1-9:13 (Named 1 "2" false) _ _))
        @7:1-9:18))) _) (Definition (Operator "Init" (Apply (Internal Eq) ((Ix 1 @12:9-12:10) (Ix 2
        @12:13-12:14)) @12:9-12:14) @12:1-12:14) User Hidden false @12:1-12:14) (Definition (Operator
        "Next" (Apply (Internal Eq) ((Apply (Internal Prime) ((Ix 2 @13:9-13:10)) @13:9-13:11) (Ix 2
        @13:14-13:15)) @13:9-13:15) @13:1-13:15) User Hidden false @13:1-13:15) (Theorem "Spec" (sequent
        () (Apply (Internal Implies) ((Apply (Internal Conj) ((Ix 2 @15:17-15:21) (Tsub Box (Ix 1
        @15:28-15:32) (Ix 3 @15:34-15:35) @15:25-15:35)) @15:17-15:35) (Apply (Internal BoxTrue) ((Ix 2
        @15:41-15:45)) @15:39-15:45)) @15:17-15:45)) 0 (Steps ((Assert (sequent () (Apply (Internal
        Implies) ((Ix 3 @16:7-16:11) (Ix 3 @16:15-16:19)) @16:7-16:19)) (Steps ((Use (usable () ((Dx 6
        @17:10-17:14))) false (props @17:3-17:5 (Named 2 "_a12" true) _ _))) (Obvious (props @17:3-17:5
        (Named 2 "_a13" true) _ _)) (props @17:3-17:5 (Named 2 "_a13" true) _ _) (props @17:3-17:5
        (Unnamed 2 0) _ _)) (props @16:1-17:5 (Named 1 "1" false) _ _)) (Assert (sequent ((Fact (Ix 5
        @18:14-18:18) Visible Now _ @18:14-18:18) (Fact (Sub Box (Ix 5 @18:21-18:25) (Ix 7 @18:27-18:28)
        @18:20-18:28) Visible Now _ @18:20-18:28)) (Apply (Internal Prime) ((Ix 7 @18:35-18:39))
        @18:35-18:40)) (Steps ((Assert (sequent ((Fresh "w" 0 Constant _ Visible @19:16-19:21)) (Apply
        (Internal Eq) ((Ix 1 @19:28-19:29) (Ix 1 @19:32-19:33)) @19:28-19:33)) (Obvious (props
        @20:5-20:41 _ (method "isabelle" "auto" _) _)) (props @19:3-20:41 (Named 2 "1" false) _ _)))
        (Steps ((Use (usable () ((Dx 12 @21:23-21:27) (Dx 11 @21:29-21:33))) false (props @21:11-21:13
        (Named 3 "_a14" true) _ _)) (Use (usable ((Ix 4 @21:14-21:18)) ()) false (props @21:14-21:18
        (Named 3 "_a15" true) _ @21:11-21:13))) (Obvious (props @21:11-21:13 (Named 3 "_a16" true) _ _))
        (props @21:11-21:13 (Named 3 "_a16" true) _ _) (props @21:11-21:13 (Unnamed 3 0) _ _)) (props
        @21:3-21:13 (Unnamed 2 1) _ _) (props @19:3-21:13 (Unnamed 2 1) _ _)) (props @18:1-21:13 (Named
        1 "2" false) _ _)) (Hide (usable () ((Dx 7 @22:14-22:18))) (props @22:1-22:18 (Unnamed 1 2) _
        _))) (Omitted Explicit (props @24:9-24:16 _ _ _)) (props @23:1-24:16 (Named 1 "3" false) _ _)
        (props @16:1-24:16 (Named 1 "3" false) _ _)) @15:1-24:16) (Theorem _ (sequent () (Apply
        (Internal Eq) ((Ix 6 @26:9-26:10) (Ix 6 @26:13-26:14)) @26:9-26:14)) 0 (Omitted Implicit (props
        @26:14-26:14 _ _ _)) @26:1-26:14) (Theorem "Foo" (sequent () (Quant Exists (("z" Constant
        (NoDomain))) (Apply (Internal Eq) ((Ix 1 @28:21-28:22) (Ix 8 @28:25-28:26)) @28:21-28:26)
        @28:14-28:26)) 0 (Steps ((Suffices (sequent () (Apply (Internal Eq) ((Apply (Internal Unprimable
        @29:13-29:14) ((Ix 8 @29:13-29:14)) @28:21-28:22) (Ix 8 @28:25-28:26)) @28:21-28:26)) (Obvious
        (props @29:1-29:14 (Named 2 "_a17" true) _ _)) (props @29:1-29:14 (Named 1 "_a17" true) _ _)))
        (Obvious (props @30:9-30:16 _ _ _)) (props @30:1-30:16 (Unnamed 1 4) _ _) (props @29:1-30:16
        (Unnamed 1 4) _ _)) @28:1-30:16) (Theorem "Bar" (sequent ((Fresh "Y" 0 Constant _ Visible
        @32:21-32:26) (Fresh "X" 0 Constant (Ix 1 @32:38-32:39) Visible @32:28-32:39)) (Apply (Internal
        Mem) ((Ix 1 @32:46-32:47) (Ix 2 @32:52-32:53)) @32:46-32:53)) 0 (Steps ((Hide (usable ((Apply
        (Internal Mem) ((Ix 1 @33:10-33:11) (Ix 2 @33:16-33:17)) @33:10-33:17)) ()) (props @33:1-33:9
        (Unnamed 1 5) _ _)) (Use (usable ((Apply (Internal Mem) ((Ix 1 @34:9-34:10) (Ix 2 @34:15-34:16))
        @34:9-34:16)) ()) false (props @34:9-34:16 (Named 1 "_a18" true) _ @34:1-34:8))) (Obvious (props
        @35:9-35:16 _ _ _)) (props @35:1-35:16 (Unnamed 1 7) _ _) (props @33:1-35:16 (Unnamed 1 7) _ _))
        @32:1-35:16)))
    "#;

    const HIDE_MISSING: &str = r#"
        (case () (mule ((Constants (("S" 0)) @1:1-1:5) (Theorem _ (sequent () (Ix 1 @2:1-2:5)) 0 (Steps
        ((Hide (usable ((Opaque "nope" @3:1-3:5)) ()) (props @3:1-3:5 (Named 1 "1" false) _ _)))
        (Obvious (props @4:1-4:5 _ _ _)) (props @3:1-3:5 _ _ _) (props @3:1-3:5 _ _ _)) @2:1-2:5))))
    "#;
    const USE_DVAR: &str = r#"
        (case () (mule ((Constants (("S" 0)) @1:1-1:5) (Mutate Use (usable () ((Dvar "Foo" _)))
        @2:1-2:5))))
    "#;
    const NOT_DEFINITION: &str = r#"
        (case () (mule ((Constants (("S" 0)) @1:1-1:5) (Mutate Hide (usable () ((Dx 1 _))) @2:1-2:5))))
    "#;
    const DEFINITIONS_OUT_OF_RANGE: &str = r#"
        (case ((Defn (Operator "D" (Opaque "d") @1:1-1:5) User Hidden false false @1:1-1:5)) (mule
        ((Constants (("S" 0)) @2:1-2:5) (Mutate Use (usable () ((Dx 5 _) (Dx 0 _) (Dx -1 _) (Dx 2
        @3:1-3:5))) @3:1-3:5) (Theorem "T" (sequent () (Ix 2 @4:1-4:5)) 0 (Obvious (props @5:1-5:5 _ _
        _)) @4:1-4:5) (Mutate Hide (usable () ((Dx 4 _))) @6:1-6:5) (Theorem _ (sequent () (Ix 3
        @7:1-7:5)) 0 (Obvious (props @8:1-8:5 _ _ _)) @7:1-7:5))))
    "#;
    const USE_FACTS_AND_DEFS: &str = r#"
        (case () (mule ((Constants (("S" 0) ("T" 0)) @1:1-1:5) (Theorem _ (sequent () (Ix 1 @2:1-2:5)) 0
        (Steps ((Use (usable ((Ix 1) (Ix 2)) ()) false (props @3:1-3:5 (Named 1 "1" false) _ _)))
        (Obvious (props @4:1-4:5 _ _ _)) (props @3:1-3:5 _ _ _) (props @3:1-3:5 _ _ _)) @2:1-2:5))))
    "#;
    const PCASE_STEP: &str = r#"
        (case () (mule ((Theorem _ (sequent () (Opaque "g" @2:1-2:5)) 0 (Steps ((Pcase (Opaque "c")
        (Obvious (props @3:1-3:5 _ _ _)) (props @3:1-3:5 (Named 1 "1" false) _ _))) (Obvious (props
        @4:1-4:5 _ _ _)) (props @3:1-3:5 _ _ _) (props @3:1-3:5 _ _ _)) @2:1-2:5))))
    "#;
    const BY_PROOF: &str = r#"
        (case () (mule ((Theorem _ (sequent () (Opaque "g" @2:1-2:5)) 0 (By (usable () ()) false (props
        @3:1-3:5 _ _ _)) @2:1-2:5))))
    "#;
    const BY_ELSEWHERE: &str = r#"
        (case () (mule ((Theorem _ (sequent () (Opaque "g" @2:1-2:5)) 0 (By (usable () ()) false (props
        @3:1-3:5@Other.tla _ _ _)) @2:1-2:5) (Theorem _ (sequent () (Opaque "h" @4:1-4:5)) 0 (By (usable
        () ()) false (props @40:1-40:5 _ _ _)) @4:1-4:5) (Theorem _ (sequent () (Opaque "k" @5:1-5:5)) 0
        (Obvious (props _ _ _ _)) @5:1-5:5))))
    "#;
    const MISSING_STEP_NUMBER: &str = r#"
        (case () (mule ((Theorem _ (sequent () (Opaque "g" @2:1-2:5)) 0 (Steps ((Assert (sequent ()
        (Opaque "a")) (Obvious (props @3:1-3:5 _ _ _)) (props @3:1-3:5 _ _ _))) (Obvious (props @4:1-4:5
        _ _ _)) (props @3:1-3:5 _ _ _) (props @3:1-3:5 _ _ _)) @2:1-2:5))))
    "#;
    const MUTATE_FACTS: &str = r#"
        (case ((Fact (Opaque "p" @1:1-1:5) Visible Now _ @1:1-1:5) (Defn (Operator "Q" (Opaque "q")
        @1:1-1:5) User Hidden false false @1:1-1:5)) (mule ((Constants (("S" 0)) @2:1-2:5) (Mutate Use
        (usable ((Ix 3 @3:1-3:5) (Ix 2 @3:1-3:5) (Opaque "r" @3:1-3:5)) ()) @3:1-3:5) (Mutate Use
        (usable ((Ix 1 @4:1-4:5)) ((Dx 5 _))) @4:1-4:5) (Mutate Hide (usable ((Opaque "r" @5:1-5:5) (Ix
        6 @5:1-5:5)) ()) @5:1-5:5) (Theorem "Last" (sequent () (Ix 1 @6:1-6:5)) 0 (Obvious (props
        @7:1-7:5 _ _ _)) @6:1-6:5))))
    "#;
    const PROOF_KINDS: &str = r#"
        (case () (mule ((Constants (("S" 0)) @1:1-1:5) (Theorem _ (sequent ((Fact (Opaque "now"
        @2:1-2:5) Visible Now _ @2:1-2:5)) (Ix 1 @2:1-2:5)) 0 (Steps ((Define ((Operator "D" (Ix 1)
        @3:1-3:5)) (props @3:1-3:5 (Named 1 "2" true) _ _)) (Assert (sequent ((Fact (Opaque "h") Visible
        Always _ _)) (Opaque "a" @4:1-4:5)) (Omitted Implicit (props @4:1-4:5 _ _ _)) (props @4:1-4:5
        (Named 1 "1" false) _ _)) (Suffices (sequent () (Opaque "s" @5:1-5:5)) (Omitted Explicit (props
        @5:1-5:5 _ _ _)) (props @5:1-5:5 (Named 1 "3" true) _ _)) (Assert (sequent () (Opaque "b"
        @6:1-6:5)) (Omitted Elsewhere (props @6:1-6:5 _ _ _)) (props @6:1-6:5 (Unnamed 2 7) _ _)) (Use
        (usable ((Ix 2 @7:1-7:5)) ()) false (props @7:1-7:5 (Named 1 "4" false) (method "zenon" _ 5)
        @7:1-7:5)) (Forget 2 (props @8:1-8:5 _ _ _)) (Assert (sequent () (Opaque "c" @9:1-9:5)) (Error
        "broken" (props @9:1-9:5 _ _ _)) (props @9:1-9:5 (Named 1 "5" false) _ _))) (Obvious (props
        @10:1-10:5 _ (method "isabelle" "auto" _) _)) (props @10:1-10:5 _ _ _) (props @3:1-3:5 _ _ _))
        @2:1-2:5) (Theorem _ (sequent () (Ix 1 @11:1-11:5)) 0 (Omitted Implicit (props _ _ _ _))
        @11:1-11:5))))
    "#;
    const OTHER_FILE: &str = r#"
        (case () (mule ((Theorem _ (sequent () (Opaque "g" @2:1-2:5)) 0 (Obvious (props @3:1-3:5 _ _ _))
        @2:1-2:5))))
    "#;
    const SUBMODULE: &str = r#"
        (case ((Fact (Opaque "outer" @1:1-1:5) Visible Always _ @1:1-1:5)) (mule ((Constants (("S" 0))
        @1:1-1:5) (Submod (mule ((Theorem "Inner" (sequent () (Ix 2 @2:1-2:5)) 0 (Omitted Explicit
        (props @3:1-3:5 _ _ _)) @2:1-2:5))) @2:1-2:5) (Theorem _ (sequent () (Ix 1 @4:1-4:5)) 0 (Obvious
        (props @5:1-5:5 _ _ _)) @4:1-4:5))))
    "#;
    const HELPER_CONTEXT: &str = r#"((Fact (Opaque "before" @1:1-1:5) Visible Always _ @1:1-1:5))"#;
    const HELPER_GOAL: &str = r#"(Ix 2 @3:1-3:5 !)"#;
    const HELPER_STEP_0: &str = r#"
        (Assert (sequent ((Fact (Opaque "h" @1:1-1:5) Visible Always _ @1:1-1:5) (Fresh "y" 0 Constant _
        Visible _) (Fact (Ix 1 @1:1-1:5) Hidden Now _ @1:1-1:5) (Fact (Opaque "v" @1:1-1:5) Visible
        Always _ @1:1-1:5)) (Opaque "goal" @2:1-2:5)) (Obvious (props @4:1-4:5 _ _ _)) (props @4:1-4:5
        (Named 1 "1" false) _ _))
    "#;
    const HELPER_STEP_1: &str = r#"
        (Assert (sequent ((Fact (Opaque "h" @1:1-1:5) Visible Always _ @1:1-1:5) (Fresh "y" 0 Constant _
        Visible _) (Fact (Ix 1 @1:1-1:5) Hidden Now _ @1:1-1:5) (Fact (Opaque "v" @1:1-1:5) Visible
        Always _ @1:1-1:5)) (Opaque "goal" @2:1-2:5)) (Obvious (props @5:1-5:5 _ _ _)) (props @5:1-5:5
        (Named 1 "2" true) _ _))
    "#;
    const HELPER_STEP_2: &str = r#"
        (Suffices (sequent () (Opaque "only" @6:1-6:5 !)) (Obvious (props @6:1-6:5 _ _ _)) (props _
        (Unnamed 3 4) _ _))
    "#;

    #[test]
    fn generates_every_step_kind() {
        check(
            STEPS,
            &["M.tla"],
            WHOLE,
            &[
                "Main@10",
                "Main@25",
                "Support@25",
                "Main@14",
                "Support@14",
                "Main@15",
                "Support@15",
                "Support@16",
                "Main@18",
                "Omitted@20",
                "Omitted@19",
                "Error@22",
                "Main@31",
                "Main@28",
                "Support@28",
                "Error@29",
                "Omitted@34",
                "Main@38",
                "Support@38",
                "Omitted@37",
                "Support@40",
                "Support@42",
                "Support@42",
                "Main@47",
                "Support@47",
                "Main@46",
            ],
            (273_809, "0xac5360d70517bedc"),
            (1244, "0x856a717f092fd500"),
        );
    }

    #[test]
    fn generates_only_the_proofs_within_the_lines() {
        check(
            STEPS,
            &["M.tla"],
            LineRange {
                start: 13.0,
                end: 20.0,
            },
            &[
                "Main@14",
                "Support@14",
                "Main@15",
                "Support@15",
                "Support@16",
                "Main@18",
                "Omitted@20",
                "Omitted@19",
                "Support@40",
                "Support@42",
                "Support@42",
            ],
            (108_505, "0x504068149e4838bd"),
            (941, "0x79e1d2d327000ec9"),
        );
    }

    #[test]
    fn generates_submodules_methods_and_temporal_scopes() {
        check(
            NESTED,
            &["M.tla"],
            WHOLE,
            &[
                "Main@9",
                "Support@9",
                "Main@8",
                "Omitted@24",
                "Main@17",
                "Main@21",
                "Support@21",
                "Main@20",
                "Omitted@26",
                "Main@30",
                "Main@29",
                "Main@35",
                "Support@34",
            ],
            (78_213, "0x3c4f95507d9dd327"),
            (848, "0xb5573e2e47c8be45"),
        );
    }

    #[test]
    fn generates_hand_built_modules() {
        check(
            DEFINITIONS_OUT_OF_RANGE,
            &["M.tla"],
            WHOLE,
            &["Main@5", "Main@8"],
            (2609, "0xc97b2b770da490a7"),
            (291, "0xdc56ef3f767b56f3"),
        );
        check(
            BY_ELSEWHERE,
            &["M.tla"],
            LineRange {
                start: 2.0,
                end: 30.0,
            },
            &[],
            (2, "0x09612b07b5ecb5a5"),
            (412, "0xc077e32d8b953c3b"),
        );
        check(
            MUTATE_FACTS,
            &["M.tla"],
            WHOLE,
            &["Support@3", "Support@3", "Support@3", "Support@4", "Main@7"],
            (8949, "0x4197365a325dc466"),
            (170, "0x7bcc0dd1bb4e1ec9"),
        );
        check(
            PROOF_KINDS,
            &["M.tla"],
            WHOLE,
            &[
                "Main@10",
                "Omitted@4",
                "Omitted@5",
                "Omitted@6",
                "Support@7",
                "Error@9",
            ],
            (21_906, "0x80f3bd638dba3add"),
            (581, "0xda22430347e6e5d7"),
        );
        check(
            OTHER_FILE,
            &["Other.tla"],
            WHOLE,
            &[],
            (2, "0x09612b07b5ecb5a5"),
            (170, "0xb99e654624621a59"),
        );
        check(
            SUBMODULE,
            &["M.tla"],
            WHOLE,
            &["Omitted@3", "Main@5"],
            (1838, "0x0078694a65d54048"),
            (242, "0xf392332890e737c4"),
        );
    }

    #[test]
    fn reports_errors_as_the_typescript_does() {
        let message = "This expression does not appear in the context and cannot be hidden.";
        check_error(
            HIDE_MISSING,
            ObligationError::proof_failure(message, "proof.Gen.set_expr"),
            Some(&format!(
                "File \"M.tla\", line 3, characters 1-4:\nError: {message}\n"
            )),
        );
        check_error(
            USE_DVAR,
            ObligationError::proof("Unknown definition Foo"),
            None,
        );
        check_error(
            NOT_DEFINITION,
            ObligationError::proof("Indicated point is not a definition"),
            None,
        );
        check_error(
            USE_FACTS_AND_DEFS,
            ObligationError::proof("Proof.Gen.gen_step: USE with facts and definitions"),
            None,
        );
        check_error(
            PCASE_STEP,
            ObligationError::proof("Proof.Gen.gen_step"),
            None,
        );
        check_error(BY_PROOF, ObligationError::proof("Proof.Gen.generate"), None);
        check_error(MISSING_STEP_NUMBER, ObligationError::assert_failure(), None);
    }

    #[test]
    fn proves_and_uses_assertions() {
        let context = list(&parse(HELPER_CONTEXT), read_hyp);
        let goal = read_expr(&parse(HELPER_GOAL));
        // Per step, then per time: the proving sequent's time and digest, and the using sequent's
        // digest without and with SUFFICES.
        let expected = [
            [
                (
                    "Now",
                    "0xc5d69fce343fcf56",
                    "0xaaf2da8a679aca8a",
                    "0x1234abebb4d63f12",
                ),
                (
                    "Now",
                    "0x2f911d889b2d1bc3",
                    "0x48b25d09b5e1e8fa",
                    "0xc25ec120a4139ae2",
                ),
            ],
            [
                (
                    "Now",
                    "0xa045fd7aa0771c23",
                    "0x2a3698a158388cab",
                    "0x2a3698a158388cab",
                ),
                (
                    "Now",
                    "0x1c6d8e3805790942",
                    "0x00ddc6eb78509273",
                    "0x00ddc6eb78509273",
                ),
            ],
            [
                (
                    "Always",
                    "0xf050f2a9ca11bf68",
                    "0xd3baeb5e8a4538ad",
                    "0x3948fb3503497003",
                ),
                (
                    "Now",
                    "0x9bfe55da7047204d",
                    "0x78e8a613eaae452d",
                    "0x4f09bd67d5c9ad83",
                ),
            ],
        ];
        for (fixture, expected) in [HELPER_STEP_0, HELPER_STEP_1, HELPER_STEP_2]
            .iter()
            .zip(expected)
        {
            let step = read_step(&parse(fixture));
            let (StepCore::Assert { sequent, .. } | StepCore::Suffices { sequent, .. }) =
                &step.core
            else {
                panic!("an assertion");
            };
            for (time, expected) in [Time::Always, Time::Now].into_iter().zip(expected) {
                let (proved, proved_time) =
                    prove_assertion(&context, sequent, &step, time).expect("proved");
                assert_eq!(format!("{proved_time:?}"), expected.0);
                assert_eq!(digest(&dump_sequent(&proved)).1, expected.1);
                for (is_suffices, hash) in [(false, expected.2), (true, expected.3)] {
                    let used = use_assertion(is_suffices, &context, &goal, sequent, &step, time)
                        .expect("used");
                    assert_eq!(digest(&dump_sequent(&used)).1, hash);
                }
            }
        }
        let mut unnumbered = read_step(&parse(HELPER_STEP_0));
        unnumbered.props.step = None;
        let StepCore::Assert { sequent, .. } = &unnumbered.core else {
            panic!("an assertion");
        };
        assert_eq!(
            prove_assertion(&context, sequent, &unnumbered, Time::Always).err(),
            Some(ObligationError::assert_failure())
        );
    }

    #[test]
    fn makes_true_and_the_nowhere_reference() {
        let located = get_true(&ExprProps {
            location: Some(locus_at(9, 1, 9, 5)),
            is_atomic: true,
        });
        assert_eq!(
            to_text(&dump_expr(&located)),
            r#"{"builtin":"TRUE","isAtomic":true,"kind":"Internal","location":{"endColumn":5,"endLine":9,"file":"M.tla","startColumn":1,"startLine":9}}"#
        );
        assert_eq!(
            to_text(&dump_expr(&get_true(&ExprProps::default()))),
            r#"{"builtin":"TRUE","kind":"Internal"}"#
        );
        assert_eq!(
            to_text(&dump_expr(&at_nowhere())),
            r#"{"isExcept":false,"kind":"At"}"#
        );
    }
}
