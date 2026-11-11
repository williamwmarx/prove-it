//! A port of tlapm's Module.Elab: normalization anonymizes a module unit by unit and expands each
//! instance into the units of the module it instantiates.
//! A port of `src/obligations/normalize.ts`.
//!
//! The TypeScript's anonymizer calls back into `expandInstance` with the pipeline. The Rust lends
//! the pipeline's other fields to the anonymizer as an `AnonymizerHost`, which `Expander` is, and
//! the warning sink sits in a `RefCell` so that `lambdify` and the host can both report to it.
//! The module maps are only looked up, so they are `HashMap`s, and they hold each module in an
//! `Rc` so that copying one, as each axiom, theorem and USE does, is cheap.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::action::lambdify;
use crate::anonymize::{Anonymizer, AnonymizerHost};
use crate::equality::is_equal_hyp;
use crate::errors::{ObligationError, Result, quote_json};
use crate::expression::{
    Builtin, Channel, Defn, DefnCore, Expr, ExprCore, ExprProps, Hyp, HypCore, InstanceDefinition,
    Level, Locus, ObligationWarning, Param, ScopeRef, Sequent, Time, Visibility, Warn,
    WhereDefined, adjoin_all, at, at_expr, at_props, expr, exprify_sequent, find_named,
    get_at_prefix, get_fact, get_fresh, get_location_text, get_locus_prefix, get_scope_hyps,
    get_scope_size, map_accumulate, to_index,
};
use crate::module::{
    ModuleUnit, ModuleUnitCore, Mule, MutateMode, bind_theorem_name, compare_names, get_hyp_size,
    get_unit_hyps, substitute_units,
};
use crate::proof::{Counter, Omission, Proof, ProofCore, ProofProps, get_unique};
use crate::simplify::Simplifier;
use crate::substitution::{
    Substitution, cons_all, cons_substitution, shift, shift_expr, substitute_expr, substitute_hyp,
    substitute_sequent,
};
use crate::temporal::get_scope_time;

/// `latest_modules` is the module context of the latest anonymization of an axiom, theorem or USE,
/// which tlapm's anonymizer keeps using for the instances inside later definitions.
pub struct Pipeline<'sink, 'warn> {
    pub anonymizer: Anonymizer,
    pub simplify: Simplifier,
    pub salts: Counter,
    pub latest_modules: HashMap<String, Rc<Mule>>,
    pub on_warning: RefCell<&'sink mut Warn<'warn>>,
}

/// The pipeline without its anonymizer: what the anonymizer calls back with.
struct Expander<'pipeline, 'sink, 'warn> {
    salts: &'pipeline Counter,
    latest_modules: &'pipeline HashMap<String, Rc<Mule>>,
    on_warning: &'pipeline RefCell<&'sink mut Warn<'warn>>,
    // The modules whose instantiated body is being expanded, innermost last.
    instantiating: Vec<String>,
}

impl AnonymizerHost for Expander<'_, '_, '_> {
    fn expand_instance(
        &mut self,
        anonymizer: &mut Anonymizer,
        scope: &ScopeRef,
        definition: &Defn,
    ) -> Result<Vec<Defn>> {
        expand_instance_with(anonymizer, self, scope, definition)
    }

    fn on_warning(&mut self, warning: ObligationWarning) {
        warn(self.on_warning, warning);
    }
}

fn warn(sink: &RefCell<&mut Warn>, warning: ObligationWarning) {
    (sink.borrow_mut())(warning);
}

fn split<'pipeline, 'sink, 'warn>(
    pipeline: &'pipeline mut Pipeline<'sink, 'warn>,
) -> (&'pipeline mut Anonymizer, Expander<'pipeline, 'sink, 'warn>) {
    (
        &mut pipeline.anonymizer,
        Expander {
            salts: &pipeline.salts,
            latest_modules: &pipeline.latest_modules,
            on_warning: &pipeline.on_warning,
            instantiating: Vec::new(),
        },
    )
}

/// `{...unit, ...changes}`: the unit's location on another core.
fn with_core(unit: &ModuleUnit, core: ModuleUnitCore) -> ModuleUnit {
    ModuleUnit {
        core,
        location: unit.location.clone(),
    }
}

fn locate(location: &Option<Locus>) -> ExprProps {
    ExprProps {
        location: location.clone(),
        is_atomic: false,
    }
}

fn located_proof(core: ProofCore, location: &Option<Locus>) -> Proof {
    Proof {
        core,
        props: ProofProps {
            location: location.clone(),
            ..ProofProps::default()
        },
    }
}

fn lambdify_theorem(
    anonymizer: &mut Anonymizer,
    expander: &mut Expander,
    scope: &ScopeRef,
    name: Option<&str>,
    sequent: &Sequent,
) -> Result<Sequent> {
    let sink = expander.on_warning;
    let lambdified = lambdify(
        anonymizer,
        expander,
        &mut |warning| warn(sink, warning),
        scope,
        &expr(ExprCore::Sequent {
            sequent: sequent.clone(),
        }),
        None,
    )
    .and_then(|lambdified| match &lambdified.core {
        ExprCore::Sequent { sequent } => Ok(sequent.clone()),
        _ => Err(ObligationError::assert_failure()),
    });
    let Err(ObligationError::Proof {
        failure: Some(failure),
        ..
    }) = &lambdified
    else {
        return lambdified;
    };
    let location = sequent.active.location.as_ref();
    let named = name.map_or_else(String::new, |name| format!("named: {name}, "));
    let message = format!(
        "{failure}\nCould not instantiate the theorem {named}at: {}",
        get_location_text(location)
    );
    warn(
        sink,
        ObligationWarning {
            text: format!("{}[ERROR]{message}", get_at_prefix(location)),
            channel: Channel::Stdout,
        },
    );
    warn(
        sink,
        ObligationWarning {
            text: message,
            channel: Channel::ToolboxOnly,
        },
    );
    Ok(Sequent {
        context: Vec::new(),
        active: at(
            ExprCore::Internal {
                builtin: Builtin::TRUE,
            },
            &sequent.active,
        ),
    })
}

fn lambdify_unit(
    anonymizer: &mut Anonymizer,
    expander: &mut Expander,
    scope: &ScopeRef,
    unit: &ModuleUnit,
) -> Result<ModuleUnit> {
    match &unit.core {
        ModuleUnitCore::Theorem {
            name,
            sequent,
            axiom_count,
            proof,
        } => Ok(with_core(
            unit,
            ModuleUnitCore::Theorem {
                name: name.clone(),
                sequent: lambdify_theorem(anonymizer, expander, scope, name.as_deref(), sequent)?,
                axiom_count: *axiom_count,
                proof: proof.clone(),
            },
        )),
        ModuleUnitCore::Definition {
            definition,
            where_defined,
            visibility,
            is_local,
        } => {
            let core = match &definition.core {
                DefnCore::Operator { name, body } => DefnCore::Operator {
                    name: name.clone(),
                    body: lambdify_body(anonymizer, expander, scope, body)?,
                },
                DefnCore::Bpragma {
                    name,
                    body,
                    methods,
                } => DefnCore::Bpragma {
                    name: name.clone(),
                    body: lambdify_body(anonymizer, expander, scope, body)?,
                    methods: methods.clone(),
                },
                DefnCore::Recursive { .. } | DefnCore::Instance { .. } => return Ok(unit.clone()),
            };
            Ok(with_core(
                unit,
                ModuleUnitCore::Definition {
                    definition: Defn {
                        core,
                        location: definition.location.clone(),
                    },
                    where_defined: *where_defined,
                    visibility: *visibility,
                    is_local: *is_local,
                },
            ))
        }
        _ => Ok(unit.clone()),
    }
}

fn lambdify_body(
    anonymizer: &mut Anonymizer,
    expander: &mut Expander,
    scope: &ScopeRef,
    body: &Expr,
) -> Result<Expr> {
    let sink = expander.on_warning;
    lambdify(
        anonymizer,
        expander,
        &mut |warning| warn(sink, warning),
        scope,
        body,
        None,
    )
}

// lambdify_enabled_cdot: the ENABLED and \cdot of each definition and theorem statement bind
// their variables before instantiation substitutes for them. A theorem that cannot be lambdified
// states TRUE.
fn lambdify_units(
    anonymizer: &mut Anonymizer,
    expander: &mut Expander,
    scope: &ScopeRef,
    units: &[ModuleUnit],
) -> Result<(ScopeRef, Vec<ModuleUnit>)> {
    map_accumulate(scope.clone(), units, |current, unit| {
        if let ModuleUnitCore::Submod { module } = &unit.core {
            let (inner, body) = lambdify_units(anonymizer, expander, &current, &module.body)?;
            return Ok((
                inner,
                with_core(
                    unit,
                    ModuleUnitCore::Submod {
                        module: Box::new(Mule {
                            body,
                            ..(**module).clone()
                        }),
                    },
                ),
            ));
        }
        let lambdified = lambdify_unit(anonymizer, expander, &current, unit)?;
        Ok((
            adjoin_all(&current, &get_unit_hyps(&lambdified)?),
            lambdified,
        ))
    })
}

/// The first parameter a parameter declaration declares, and the declaration without it.
fn split_parameter(unit: &ModuleUnit) -> Result<Option<(String, ModuleUnit)>> {
    Ok(match &unit.core {
        ModuleUnitCore::Constants { declarations } => {
            let (first, remaining) = declarations
                .split_first()
                .ok_or_else(ObligationError::assert_failure)?;
            Some((
                first.name.clone(),
                with_core(
                    unit,
                    ModuleUnitCore::Constants {
                        declarations: remaining.to_vec(),
                    },
                ),
            ))
        }
        ModuleUnitCore::Variables { names } => {
            let (first, remaining) = names
                .split_first()
                .ok_or_else(ObligationError::assert_failure)?;
            Some((
                first.clone(),
                with_core(
                    unit,
                    ModuleUnitCore::Variables {
                        names: remaining.to_vec(),
                    },
                ),
            ))
        }
        _ => None,
    })
}

// apply_subst: each parameter declaration of the instancee gives way to its substitute.
fn apply_parameters(
    units: Vec<ModuleUnit>,
    substitutes: &[(String, Expr)],
) -> Result<Vec<ModuleUnit>> {
    let mut body = Vec::new();
    let mut size = 0;
    let mut rest = units;
    let mut position = 0;
    while position < rest.len() {
        let unit = &rest[position];
        if let Some((name, remaining)) = split_parameter(unit)? {
            let substitute = substitutes
                .iter()
                .find(|entry| entry.0 == name)
                .ok_or_else(|| {
                    ObligationError::proof(format!("Parameter {name} has no substitute"))
                })?;
            let is_empty = get_hyp_size(&remaining)? == 0;
            let tail = &rest[position + 1..];
            let next = if is_empty {
                tail.to_vec()
            } else {
                std::iter::once(remaining)
                    .chain(tail.iter().cloned())
                    .collect()
            };
            rest = substitute_units(
                &cons_substitution(shift_expr(to_index(size), &substitute.1)?, shift(0)),
                &next,
            )?;
            position = 0;
            continue;
        }
        size += get_hyp_size(unit)?;
        body.push(unit.clone());
        position += 1;
    }
    Ok(body)
}

// resub_for: references to the instancee's own units become applications to the instance
// arguments, which the definitions now bind themselves.
fn get_local_substitution(
    count: usize,
    argument_count: usize,
    location: &Option<Locus>,
) -> Substitution {
    let props = locate(location);
    let args: Vec<Expr> = (0..argument_count)
        .map(|index| {
            at_props(
                ExprCore::Ix {
                    index: to_index(argument_count - index),
                },
                &props,
            )
        })
        .collect();
    let parameters = (0..argument_count).map(|index| {
        at_props(
            ExprCore::Ix {
                index: to_index(index + 1),
            },
            &props,
        )
    });
    let locals = (0..count).map(|index| {
        let operator = at_props(
            ExprCore::Ix {
                index: to_index(index + argument_count + 1),
            },
            &props,
        );
        if argument_count > 0 {
            at_props(
                ExprCore::Apply {
                    operator,
                    args: args.clone(),
                },
                &props,
            )
        } else {
            operator
        }
    });
    let mut bound: Vec<Expr> = locals.chain(parameters).collect();
    bound.reverse();
    cons_all(&bound, shift(to_index(count + argument_count)))
}

fn add_parameters(expression: &Expr, args: &[String]) -> Expr {
    let params: Vec<Param> = args
        .iter()
        .map(|name| Param {
            name: name.clone(),
            shape: 0,
            location: None,
        })
        .collect();
    if let ExprCore::Lambda {
        params: inner,
        body,
    } = &expression.core
    {
        return expression.with_core(ExprCore::Lambda {
            params: params.into_iter().chain(inner.iter().cloned()).collect(),
            body: body.clone(),
        });
    }
    if args.is_empty() {
        expression.clone()
    } else {
        at(
            ExprCore::Lambda {
                params,
                body: expression.clone(),
            },
            expression,
        )
    }
}

fn get_localized_name(prefix: &str, name: &str) -> String {
    if prefix.is_empty() {
        name.to_owned()
    } else {
        format!("{prefix}!{name}")
    }
}

// localize: names the instancee's units under the instance name, salting its local definitions, and
// abstracts each over the instance arguments.
fn localize(
    expander: &Expander,
    units: Vec<ModuleUnit>,
    prefix: &str,
    instance: &InstanceDefinition,
    is_local: bool,
    location: &Option<Locus>,
) -> Result<Vec<ModuleUnit>> {
    let argument_count = instance.args.len();
    let mut body = Vec::new();
    let mut size = 0;
    let mut rest = units;
    let mut position = 0;
    let mut is_complained = argument_count == 0;
    let mut complain = |text: String| {
        if is_complained {
            return;
        }
        is_complained = true;
        warn(
            expander.on_warning,
            ObligationWarning {
                text,
                channel: Channel::Stderr,
            },
        );
    };
    while position < rest.len() {
        let unit = rest[position].clone();
        position += 1;
        let localized = |size: usize, expression: &Expr| -> Result<Expr> {
            Ok(add_parameters(
                &substitute_expr(
                    &get_local_substitution(size, argument_count, location),
                    expression,
                )?,
                &instance.args,
            ))
        };
        match &unit.core {
            ModuleUnitCore::Definition {
                definition,
                where_defined,
                is_local: is_unit_local,
                visibility,
            } => {
                let salted = |name: &str| {
                    if *is_unit_local {
                        format!("{name}${}", get_unique(expander.salts))
                    } else {
                        name.to_owned()
                    }
                };
                let core = match &definition.core {
                    DefnCore::Operator { name, body } => DefnCore::Operator {
                        name: get_localized_name(prefix, &salted(name)),
                        body: localized(size, body)?,
                    },
                    DefnCore::Bpragma {
                        name,
                        body,
                        methods,
                    } => DefnCore::Bpragma {
                        name: get_localized_name(prefix, &salted(name)),
                        body: localized(size, body)?,
                        methods: methods.clone(),
                    },
                    DefnCore::Recursive { .. } | DefnCore::Instance { .. } => {
                        return Err(ObligationError::proof("Module.Elab.localize"));
                    }
                };
                body.push(with_core(
                    &unit,
                    ModuleUnitCore::Definition {
                        definition: Defn {
                            core,
                            location: definition.location.clone(),
                        },
                        where_defined: if *is_unit_local {
                            WhereDefined::Builtin
                        } else {
                            *where_defined
                        },
                        visibility: *visibility,
                        is_local: *is_unit_local || is_local,
                    },
                ));
                size += 1;
            }
            ModuleUnitCore::Axiom { name, expression } => {
                complain(format!(
                    "{}Instancing produces parametric axioms.\nSuch axioms will be forcibly hidden and cannot be cited.\n(This warning appears at-most once per INSTANCE declaration.)",
                    get_locus_prefix(location.as_ref())
                ));
                let axiom = with_core(
                    &unit,
                    ModuleUnitCore::Axiom {
                        name: name.as_deref().map(|name| get_localized_name(prefix, name)),
                        expression: localized(size, expression)?,
                    },
                );
                size += get_hyp_size(&axiom)?;
                body.push(axiom);
            }
            ModuleUnitCore::Theorem {
                name,
                sequent,
                axiom_count,
                ..
            } => {
                complain(format!(
                    "{}Warning: Instancing produces parametric theorems.\nSuch theorems will be forcibly hidden and cannot be cited.\n(This warning appears at-most once per INSTANCE declaration.)",
                    get_at_prefix(location.as_ref())
                ));
                let expression = localized(
                    size,
                    &at_expr(&exprify_sequent(sequent), &locate(&unit.location)),
                )?;
                let sequent = match &expression.core {
                    ExprCore::Sequent { sequent } => sequent.clone(),
                    _ => Sequent {
                        context: Vec::new(),
                        active: expression,
                    },
                };
                body.push(with_core(
                    &unit,
                    ModuleUnitCore::Theorem {
                        name: name.as_deref().map(|name| get_localized_name(prefix, name)),
                        sequent,
                        axiom_count: *axiom_count,
                        proof: located_proof(
                            ProofCore::Omitted(Omission::Elsewhere),
                            &unit.location,
                        ),
                    },
                ));
                size += 1;
            }
            ModuleUnitCore::Mutate { mode, usable } => {
                if *mode == MutateMode::Use {
                    rest =
                        substitute_units(&shift(-to_index(usable.facts.len())), &rest[position..])?;
                    position = 0;
                }
            }
            ModuleUnitCore::Submod { .. } => {}
            _ => return Err(ObligationError::proof("Module.Elab.localize")),
        }
    }
    Ok(body)
}

// localize_axioms: an axiom becomes a hypothesis of each theorem after it, and a named one also a
// definition.
fn localize_axioms(units: Vec<ModuleUnit>) -> Result<Vec<ModuleUnit>> {
    let mut body = Vec::new();
    let mut rest = units;
    let mut position = 0;
    while position < rest.len() {
        let unit = &rest[position];
        let ModuleUnitCore::Axiom { name, expression } = &unit.core else {
            body.push(unit.clone());
            position += 1;
            continue;
        };
        let location = &unit.location;
        if let Some(name) = name {
            body.push(ModuleUnit {
                core: ModuleUnitCore::Definition {
                    definition: Defn {
                        core: DefnCore::Operator {
                            name: name.clone(),
                            body: expression.clone(),
                        },
                        location: location.clone(),
                    },
                    where_defined: WhereDefined::Proof(Time::Always),
                    visibility: Visibility::Visible,
                    is_local: false,
                },
                location: location.clone(),
            });
        }
        let hyp = get_fact(
            match name {
                None => shift_expr(1, expression)?,
                Some(_) => at_props(ExprCore::Ix { index: 2 }, &locate(location)),
            },
            Visibility::Visible,
            Time::Always,
            location.clone(),
        );
        let mut distance = 0;
        let inserted = rest[position + 1..]
            .iter()
            .map(|next| {
                let size = distance;
                distance += get_hyp_size(next)?;
                let ModuleUnitCore::Theorem {
                    name,
                    sequent,
                    axiom_count,
                    proof,
                } = &next.core
                else {
                    return Ok(next.clone());
                };
                let sequent = substitute_sequent(&shift(1), sequent)?;
                let context = std::iter::once(substitute_hyp(&shift(to_index(size)), &hyp)?)
                    .chain(sequent.context)
                    .collect();
                Ok(with_core(
                    next,
                    ModuleUnitCore::Theorem {
                        name: name.clone(),
                        sequent: Sequent {
                            context,
                            active: sequent.active,
                        },
                        axiom_count: axiom_count + 1,
                        proof: proof.clone(),
                    },
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        rest = substitute_units(&shift(-1), &inserted)?;
        position = 0;
    }
    Ok(body)
}

/// The names the module declares as constants or variables, once each, in order.
fn get_parameters(module: &Mule) -> Vec<String> {
    let mut parameters: Vec<String> = Vec::new();
    for unit in &module.body {
        let names: Vec<&String> = match &unit.core {
            ModuleUnitCore::Constants { declarations } => declarations
                .iter()
                .map(|declaration| &declaration.name)
                .collect(),
            ModuleUnitCore::Variables { names } => names.iter().collect(),
            _ => Vec::new(),
        };
        for name in names {
            if !parameters.contains(name) {
                parameters.push(name.clone());
            }
        }
    }
    parameters
}

/// `Map.set` on the insertion-ordered entries.
fn set_entry(entries: &mut Vec<(String, Expr)>, name: &str, expression: Expr) {
    match entries.iter_mut().find(|entry| entry.0 == name) {
        Some(entry) => entry.1 = expression,
        None => entries.push((name.to_owned(), expression)),
    }
}

// Module.Elab.instantiate: the units of an instantiated module, in the context of the instance.
#[allow(clippy::too_many_arguments)]
fn instantiate(
    anonymizer: &mut Anonymizer,
    expander: &mut Expander,
    modules: &HashMap<String, Rc<Mule>>,
    scope: &ScopeRef,
    instance: &InstanceDefinition,
    is_local: bool,
    prefix: &str,
    location: &Option<Locus>,
) -> Result<Vec<ModuleUnit>> {
    let module = modules
        .get(&instance.module)
        .ok_or_else(|| ObligationError::proof(format!("Module \"{}\" unknown", instance.module)))?;
    let parameters = get_parameters(module);
    for substitution in &instance.substitutions {
        if !parameters.contains(&substitution.name) {
            return Err(ObligationError::proof(format!(
                "Parameter {} occurs in the statement `INSTANCE {} WITH`, and is not declared in the module {}",
                substitution.name, instance.module, instance.module
            )));
        }
    }
    let instance_scope = adjoin_all(
        scope,
        &instance
            .args
            .iter()
            .map(|name| get_fresh(name, Level::Unknown, 0))
            .collect::<Vec<_>>(),
    );
    let mut substitutes = Vec::new();
    for entry in &instance.substitutions {
        set_entry(&mut substitutes, &entry.name, entry.expression.clone());
    }
    let mut sorted = parameters;
    sorted.sort_by(|left, right| compare_names(left, right));
    for name in &sorted {
        if substitutes.iter().any(|entry| &entry.0 == name) {
            continue;
        }
        if find_named(&instance_scope, name).is_none() {
            return Err(ObligationError::proof(format!(
                "Required parameter {name} for module {} could not be inferred.",
                instance.module
            )));
        }
        set_entry(
            &mut substitutes,
            name,
            at_props(ExprCore::Opaque { name: name.clone() }, &locate(location)),
        );
    }
    let anonymized = substitutes
        .iter()
        .map(|(name, expression)| {
            Ok((
                name.clone(),
                anonymizer.expr(expander, &instance_scope, expression)?,
            ))
        })
        .collect::<Result<Vec<_>>>()?;
    let body = substitute_units(
        &shift(to_index(get_scope_size(&instance_scope)) - to_index(module.depth.unwrap_or(0))),
        &module
            .body
            .iter()
            .map(|unit| match &unit.core {
                ModuleUnitCore::Theorem {
                    name,
                    sequent,
                    axiom_count,
                    proof,
                } => with_core(
                    unit,
                    ModuleUnitCore::Theorem {
                        name: name.clone(),
                        sequent: sequent.clone(),
                        axiom_count: *axiom_count,
                        proof: located_proof(
                            ProofCore::Omitted(Omission::Implicit),
                            &proof.props.location,
                        ),
                    },
                ),
                _ => unit.clone(),
            })
            .collect::<Vec<_>>(),
    )?;
    // The body of a module whose body is being expanded reaches the same INSTANCE again, so tlapm
    // recurses until its stack overflows, as it does on a module that extends itself. Substitutes
    // are no part of the body: an INSTANCE of the module inside one expands once.
    if expander.instantiating.contains(&instance.module) {
        return Err(ObligationError::bug("Stack overflow"));
    }
    expander.instantiating.push(instance.module.clone());
    let lambdified = lambdify_units(anonymizer, expander, &instance_scope, &body);
    expander.instantiating.pop();
    let (_, lambdified) = lambdified?;
    localize_axioms(localize(
        expander,
        apply_parameters(lambdified, &anonymized)?,
        prefix,
        instance,
        is_local,
        location,
    )?)
}

fn expand_instance_with(
    anonymizer: &mut Anonymizer,
    expander: &mut Expander,
    scope: &ScopeRef,
    definition: &Defn,
) -> Result<Vec<Defn>> {
    let DefnCore::Instance { name, instance } = &definition.core else {
        return Err(ObligationError::assert_failure());
    };
    let module = &instance.module;
    let modules = expander.latest_modules;
    if !modules.contains_key(module) {
        warn(
            expander.on_warning,
            ObligationWarning {
                text: format!(
                    "{}Module {} unknown\n",
                    get_locus_prefix(instance.location.as_ref()),
                    quote_json(module)
                ),
                channel: Channel::Toolbox,
            },
        );
        return Err(ObligationError::proof_failure(
            format!("Module {} unknown", quote_json(module)),
            "Module.Elab.anon#defns",
        ));
    }
    let units = instantiate(
        anonymizer,
        expander,
        modules,
        scope,
        instance,
        true,
        name,
        &definition.location,
    )?;
    let mut definitions = Vec::new();
    let mut rest = units;
    let mut position = 0;
    while position < rest.len() {
        let unit = &rest[position];
        let ModuleUnitCore::Definition { definition, .. } = &unit.core else {
            rest = substitute_units(
                &shift(-to_index(get_hyp_size(unit)?)),
                &rest[position + 1..],
            )?;
            position = 0;
            continue;
        };
        definitions.push(definition.clone());
        position += 1;
    }
    Ok(definitions)
}

/// `expandInstance` (make_defs): the definitions among the units an INSTANCE inside a LET or
/// DEFINE stands for.
pub fn expand_instance(
    pipeline: &mut Pipeline,
    scope: &ScopeRef,
    definition: &Defn,
) -> Result<Vec<Defn>> {
    let (anonymizer, mut expander) = split(pipeline);
    expand_instance_with(anonymizer, &mut expander, scope, definition)
}

/// Module.Elab.normalize: anonymizes each unit in the context of the ones before it, expands
/// instances, merges repeated definitions, and simplifies the proofs of important modules. The
/// result also joins the modules that later instances can name.
pub fn normalize(
    pipeline: &mut Pipeline,
    modules: &mut HashMap<String, Rc<Mule>>,
    scope: &ScopeRef,
    module: &Mule,
) -> Result<Mule> {
    let mut body: Vec<ModuleUnit> = Vec::new();
    let mut current = scope.clone();
    let emit = |unit: ModuleUnit, body: &mut Vec<ModuleUnit>, current: &mut ScopeRef| {
        *current = adjoin_all(current, &get_unit_hyps(&unit)?);
        body.push(unit);
        Ok::<(), ObligationError>(())
    };
    let is_redundant = |current: &ScopeRef, name: &Option<String>| {
        name.as_deref()
            .is_some_and(|name| find_named(current, name).is_some())
    };
    // Instantiated units arrive anonymized.
    let mut queue: Vec<(ModuleUnit, bool)> = module
        .body
        .iter()
        .map(|unit| (unit.clone(), false))
        .collect();
    let mut index = 0;
    while index < queue.len() {
        let unit = queue[index].0.clone();
        let is_anonymized = queue[index].1;
        index += 1;
        let mut expand = |pipeline: &mut Pipeline,
                          current: &ScopeRef,
                          instance: &InstanceDefinition,
                          is_local: bool,
                          prefix: &str| {
            let (anonymizer, mut expander) = split(pipeline);
            let units = instantiate(
                anonymizer,
                &mut expander,
                modules,
                current,
                instance,
                is_local,
                prefix,
                &unit.location,
            )?;
            queue.splice(index..index, units.into_iter().map(|inner| (inner, true)));
            Ok::<(), ObligationError>(())
        };
        match &unit.core {
            ModuleUnitCore::Anoninst { instance, is_local } => {
                expand(pipeline, &current, instance, *is_local, "")?;
            }
            ModuleUnitCore::Definition {
                definition,
                where_defined,
                visibility,
                is_local,
            } => {
                if let DefnCore::Instance { name, instance } = &definition.core {
                    expand(pipeline, &current, instance, *is_local, name)?;
                    continue;
                }
                let is_recursive = matches!(definition.core, DefnCore::Recursive { .. });
                let anonymized = if is_recursive || is_anonymized {
                    definition.clone()
                } else {
                    let (anonymizer, mut expander) = split(pipeline);
                    anonymizer.defn(&mut expander, &current, definition)?
                };
                let normalized = with_core(
                    &unit,
                    ModuleUnitCore::Definition {
                        definition: anonymized,
                        where_defined: *where_defined,
                        visibility: *visibility,
                        is_local: *is_local,
                    },
                );
                if is_recursive {
                    emit(normalized, &mut body, &mut current)?;
                    continue;
                }
                let hyp = get_unit_hyps(&normalized)?
                    .into_iter()
                    .next()
                    .ok_or_else(ObligationError::assert_failure)?;
                if let Some((depth, found)) = find_named(&current, definition.name())
                    && let HypCore::Defn {
                        definition: found_definition,
                        ..
                    } = &found.core
                {
                    let is_merged = matches!(found_definition.core, DefnCore::Recursive { .. })
                        || is_equal_hyp(
                            &*substitute_hyp(&shift(to_index(depth + 1)), &found)?,
                            &hyp,
                        );
                    if is_merged {
                        let substitution = cons_substitution(
                            at_props(
                                ExprCore::Ix {
                                    index: to_index(depth + 1),
                                },
                                &locate(&unit.location),
                            ),
                            shift(0),
                        );
                        let rest: Vec<ModuleUnit> =
                            queue[index..].iter().map(|entry| entry.0.clone()).collect();
                        let substituted = substitute_units(&substitution, &rest)?;
                        for (entry, inner) in queue[index..].iter_mut().zip(substituted) {
                            entry.0 = inner;
                        }
                        continue;
                    }
                }
                emit(normalized, &mut body, &mut current)?;
            }
            ModuleUnitCore::Recursives { .. }
            | ModuleUnitCore::Constants { .. }
            | ModuleUnitCore::Variables { .. } => emit(unit.clone(), &mut body, &mut current)?,
            ModuleUnitCore::Axiom { name, expression } => {
                if is_redundant(&current, name) {
                    continue;
                }
                pipeline.latest_modules = modules.clone();
                let (anonymizer, mut expander) = split(pipeline);
                let expression = anonymizer.expr(&mut expander, &current, expression)?;
                emit(
                    with_core(
                        &unit,
                        ModuleUnitCore::Axiom {
                            name: name.clone(),
                            expression,
                        },
                    ),
                    &mut body,
                    &mut current,
                )?;
            }
            ModuleUnitCore::Theorem {
                name,
                sequent,
                axiom_count,
                proof,
            } => {
                let is_duplicate = is_redundant(&current, name);
                let name = if is_duplicate {
                    name.as_deref().map(|name| format!("(redundant){name}"))
                } else {
                    name.clone()
                };
                let proof = if is_duplicate {
                    located_proof(ProofCore::Obvious, &proof.props.location)
                } else {
                    proof.clone()
                };
                pipeline.latest_modules = modules.clone();
                let (anonymizer, mut expander) = split(pipeline);
                let sequent = anonymizer.sequent(&mut expander, &current, sequent)?;
                let (hyps, bound) = bind_theorem_name(name.as_deref(), &sequent, &unit.location)?;
                let unset: Vec<Hyp> = hyps
                    .iter()
                    .map(|hyp| match &hyp.core {
                        HypCore::Defn {
                            definition,
                            where_defined,
                            visibility,
                            is_local,
                            ..
                        } => hyp.with_core(HypCore::Defn {
                            definition: definition.clone(),
                            where_defined: *where_defined,
                            visibility: *visibility,
                            is_local: *is_local,
                            is_constness_unset: true,
                        }),
                        _ => hyp.clone(),
                    })
                    .collect();
                let proof_scope = adjoin_all(&adjoin_all(&current, &unset), &bound.context);
                let anonymized = anonymizer.proof(&mut expander, &proof_scope, &proof)?;
                let simplified = if module.is_important {
                    pipeline.simplify.simplify(
                        &get_scope_hyps(&proof_scope),
                        &bound.active,
                        &anonymized,
                        get_scope_time(&bound.context, Time::Always),
                    )?
                } else {
                    anonymized
                };
                emit(
                    with_core(
                        &unit,
                        ModuleUnitCore::Theorem {
                            name,
                            sequent,
                            axiom_count: *axiom_count,
                            proof: simplified,
                        },
                    ),
                    &mut body,
                    &mut current,
                )?;
            }
            ModuleUnitCore::Mutate { mode, usable } => {
                pipeline.latest_modules = modules.clone();
                let (anonymizer, mut expander) = split(pipeline);
                let usable = anonymizer.usable(&mut expander, &current, usable)?;
                emit(
                    with_core(
                        &unit,
                        ModuleUnitCore::Mutate {
                            mode: *mode,
                            usable,
                        },
                    ),
                    &mut body,
                    &mut current,
                )?;
            }
            ModuleUnitCore::Submod { module: submodule } => {
                let normalized = normalize(pipeline, modules, &current, submodule)?;
                emit(
                    with_core(
                        &unit,
                        ModuleUnitCore::Submod {
                            module: Box::new(normalized),
                        },
                    ),
                    &mut body,
                    &mut current,
                )?;
            }
        }
    }
    let normalized = Mule {
        name: module.name.clone(),
        extendees: module.extendees.clone(),
        extendee_locations: module.extendee_locations.clone(),
        body,
        is_important: module.is_important,
        is_standard: module.is_standard,
        depth: Some(get_scope_size(scope)),
        location: module.location.clone(),
    };
    modules.insert(module.name.clone(), Rc::new(normalized.clone()));
    Ok(normalized)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::anonymize::create_anonymizer;
    use crate::expression::{
        Bound, BoundDomain, Bullet, CaseArm, ExceptPoint, ExceptSpec, ExprNode, Fairness, Field,
        HypNode, Modal, ParenForm, Quantifier, Selector, Substitution as Entry, XlabelIndex,
    };
    use crate::module::{Declaration, get_standard_modules};
    use crate::pragma::{OldMethod, PragmaSetting, PragmaValue};
    use crate::proof::{QedStep, Step, StepCore, StepNumber, Usable, UseDef, UseDefCore};
    use crate::simplify::create_simplifier;

    // Each fixture is what `getObligations` handed `normalize.ts` under Bun, for one main module:
    // `(fixture file counter modules calls)`, with the counter when normalization starts, the
    // flattened modules in schedule order (a standard one by name), and what each call to
    // `normalize` gave: `(ok length hash counter salts warnings-length warnings-hash)` for the
    // normalized module as an S-expression, or `(error message failure exception ...)` for the
    // error it threw. The warnings are each `channel: text`, joined by newlines. A location
    // names its file only when it is not the main one.

    #[derive(Debug)]
    enum Sexp {
        Atom(String),
        Text(String),
        List(Vec<Sexp>),
    }

    thread_local! {
        static MAIN: RefCell<Rc<str>> = RefCell::new(Rc::from("M.tla"));
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

    fn parse_text(characters: &[char], position: &mut usize) -> String {
        let mut units: Vec<u16> = Vec::new();
        loop {
            let character = characters[*position];
            *position += 1;
            match character {
                '"' => return String::from_utf16(&units).expect("UTF-16"),
                '\\' => {
                    let escaped = characters[*position];
                    *position += 1;
                    match escaped {
                        'n' => units.push(u16::from(b'\n')),
                        't' => units.push(u16::from(b'\t')),
                        'r' => units.push(u16::from(b'\r')),
                        'b' => units.push(8),
                        'f' => units.push(12),
                        'u' => {
                            let digits: String =
                                characters[*position..*position + 4].iter().collect();
                            *position += 4;
                            units.push(u16::from_str_radix(&digits, 16).expect("hex"));
                        }
                        other => units.extend(other.encode_utf16(&mut [0; 2]).iter()),
                    }
                }
                other => units.extend(other.encode_utf16(&mut [0; 2]).iter()),
            }
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
                Sexp::Text(parse_text(characters, position))
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
        (!is_none(sexp)).then(|| read(sexp))
    }

    fn list<Value>(sexp: &Sexp, read: impl Fn(&Sexp) -> Value) -> Vec<Value> {
        items(sexp).iter().map(read).collect()
    }

    /// `@line:column-line:column`, then `@file` when the file is not the main one.
    fn read_locus(sexp: &Sexp) -> Option<Locus> {
        optional(sexp, |sexp| {
            let mut parts = atom(sexp).trim_start_matches('@').splitn(2, '@');
            let numbers: Vec<u32> = parts
                .next()
                .expect("position")
                .split(['-', ':'])
                .map(|part| part.parse().expect("line or column"))
                .collect();
            Locus {
                file: parts
                    .next()
                    .map_or_else(|| MAIN.with(|main| main.borrow().clone()), Rc::from),
                start_line: numbers[0],
                start_column: numbers[1],
                end_line: numbers[2],
                end_column: numbers[3],
            }
        })
    }

    const BUILTINS: [Builtin; 72] = [
        Builtin::TRUE,
        Builtin::FALSE,
        Builtin::Implies,
        Builtin::Equiv,
        Builtin::Conj,
        Builtin::Disj,
        Builtin::Neg,
        Builtin::Eq,
        Builtin::Neq,
        Builtin::STRING,
        Builtin::BOOLEAN,
        Builtin::SUBSET,
        Builtin::UNION,
        Builtin::DOMAIN,
        Builtin::Subseteq,
        Builtin::Mem,
        Builtin::Notmem,
        Builtin::Setminus,
        Builtin::Cap,
        Builtin::Cup,
        Builtin::Prime,
        Builtin::StrongPrime,
        Builtin::Leadsto,
        Builtin::ENABLED,
        Builtin::UNCHANGED,
        Builtin::Cdot,
        Builtin::Actplus,
        Builtin::BoxTrue,
        Builtin::BoxFalse,
        Builtin::Diamond,
        Builtin::Nat,
        Builtin::Int,
        Builtin::Real,
        Builtin::Plus,
        Builtin::Minus,
        Builtin::Uminus,
        Builtin::Times,
        Builtin::Ratio,
        Builtin::Quotient,
        Builtin::Remainder,
        Builtin::Exp,
        Builtin::Infinity,
        Builtin::Lteq,
        Builtin::Lt,
        Builtin::Gteq,
        Builtin::Gt,
        Builtin::Divides,
        Builtin::Range,
        Builtin::Seq,
        Builtin::Len,
        Builtin::BSeq,
        Builtin::Cat,
        Builtin::Append,
        Builtin::Head,
        Builtin::Tail,
        Builtin::SubSeq,
        Builtin::SelectSeq,
        Builtin::OneArg,
        Builtin::Extend,
        Builtin::Print,
        Builtin::PrintT,
        Builtin::Assert,
        Builtin::JavaTime,
        Builtin::TLCGet,
        Builtin::TLCSet,
        Builtin::Permutations,
        Builtin::SortSeq,
        Builtin::RandomElement,
        Builtin::Any,
        Builtin::ToString,
        Builtin::Unprimable,
        Builtin::Irregular,
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

    fn read_quantifier(sexp: &Sexp) -> Quantifier {
        if atom(sexp) == "Forall" {
            Quantifier::Forall
        } else {
            Quantifier::Exists
        }
    }

    fn read_modal(sexp: &Sexp) -> Modal {
        if atom(sexp) == "Box" {
            Modal::Box
        } else {
            Modal::Dia
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

    fn read_selector(sexp: &Sexp) -> Selector {
        let fields = items(sexp);
        match atom(&fields[0]) {
            "Number" => Selector::Number(number(&fields[1])),
            "Instance" => Selector::Instance(list(&fields[1], read_expr)),
            "Label" => Selector::Label {
                label: text(&fields[1]),
                args: list(&fields[2], read_expr),
            },
            "Down" => Selector::Down,
            "Left" => Selector::Left,
            "Right" => Selector::Right,
            "At" => Selector::At,
            other => panic!("selector {other}"),
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

    fn read_fields(sexp: &Sexp) -> Vec<Field> {
        list(sexp, |sexp| {
            let field = items(sexp);
            Field {
                name: text(&field[0]),
                value: read_expr(&field[1]),
            }
        })
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
            "Bang" => ExprCore::Bang {
                expression: read_expr(&fields[1]),
                selectors: list(&fields[2], read_selector),
            },
            "Apply" => ExprCore::Apply {
                operator: read_expr(&fields[1]),
                args: list(&fields[2], read_expr),
            },
            "With" => ExprCore::With {
                expression: read_expr(&fields[1]),
                method: read_method(&fields[2]),
            },
            "If" => ExprCore::If {
                condition: read_expr(&fields[1]),
                consequent: read_expr(&fields[2]),
                alternative: read_expr(&fields[3]),
            },
            "List" => ExprCore::List {
                bullet: match atom(&fields[1]) {
                    "And" => Bullet::And,
                    "Or" => Bullet::Or,
                    _ => Bullet::Refs,
                },
                items: list(&fields[2], read_expr),
            },
            "Let" => ExprCore::Let {
                definitions: list(&fields[1], read_defn),
                body: read_expr(&fields[2]),
            },
            "Quant" => ExprCore::Quant {
                quantifier: read_quantifier(&fields[1]),
                bounds: list(&fields[2], read_bound),
                body: read_expr(&fields[3]),
            },
            "Tquant" => ExprCore::Tquant {
                quantifier: read_quantifier(&fields[1]),
                names: list(&fields[2], text),
                body: read_expr(&fields[3]),
            },
            "Choose" => ExprCore::Choose {
                name: text(&fields[1]),
                domain: optional(&fields[2], read_expr),
                body: read_expr(&fields[3]),
            },
            "SetSt" => ExprCore::SetSt {
                name: text(&fields[1]),
                domain: read_expr(&fields[2]),
                body: read_expr(&fields[3]),
            },
            "SetOf" => ExprCore::SetOf {
                element: read_expr(&fields[1]),
                bounds: list(&fields[2], read_bound),
            },
            "SetEnum" => ExprCore::SetEnum {
                elements: list(&fields[1], read_expr),
            },
            "Tuple" => ExprCore::Tuple {
                elements: list(&fields[1], read_expr),
            },
            "Product" => ExprCore::Product {
                factors: list(&fields[1], read_expr),
            },
            "Fcn" => ExprCore::Fcn {
                bounds: list(&fields[1], read_bound),
                body: read_expr(&fields[2]),
            },
            "FcnApp" => ExprCore::FcnApp {
                function: read_expr(&fields[1]),
                args: list(&fields[2], read_expr),
            },
            "Arrow" => ExprCore::Arrow {
                domain: read_expr(&fields[1]),
                range: read_expr(&fields[2]),
            },
            "Rect" => ExprCore::Rect {
                fields: read_fields(&fields[1]),
            },
            "Record" => ExprCore::Record {
                fields: read_fields(&fields[1]),
            },
            "Except" => ExprCore::Except {
                function: read_expr(&fields[1]),
                specs: list(&fields[2], |sexp| {
                    let spec = items(sexp);
                    ExceptSpec {
                        trail: list(&spec[0], |sexp| {
                            let point = items(sexp);
                            if atom(&point[0]) == "Dot" {
                                ExceptPoint::Dot(text(&point[1]))
                            } else {
                                ExceptPoint::Apply(read_expr(&point[1]))
                            }
                        }),
                        value: read_expr(&spec[1]),
                    }
                }),
            },
            "Dot" => ExprCore::Dot {
                expression: read_expr(&fields[1]),
                field: text(&fields[2]),
            },
            "Sub" => ExprCore::Sub {
                modal: read_modal(&fields[1]),
                action: read_expr(&fields[2]),
                subscript: read_expr(&fields[3]),
            },
            "Tsub" => ExprCore::Tsub {
                modal: read_modal(&fields[1]),
                action: read_expr(&fields[2]),
                subscript: read_expr(&fields[3]),
            },
            "Fair" => ExprCore::Fair {
                fairness: if atom(&fields[1]) == "Weak" {
                    Fairness::Weak
                } else {
                    Fairness::Strong
                },
                subscript: read_expr(&fields[2]),
                action: read_expr(&fields[3]),
            },
            "Case" => ExprCore::Case {
                arms: list(&fields[1], |sexp| {
                    let arm = items(sexp);
                    CaseArm {
                        condition: read_expr(&arm[0]),
                        body: read_expr(&arm[1]),
                    }
                }),
                other: optional(&fields[2], read_expr),
            },
            "String" => ExprCore::String {
                value: text(&fields[1]),
            },
            "Num" => ExprCore::Num {
                integer: text(&fields[1]),
                fraction: text(&fields[2]),
            },
            "At" => ExprCore::At {
                is_except: boolean(&fields[1]),
            },
            "Parens" => {
                let form = items(&fields[2]);
                ExprCore::Parens {
                    expression: read_expr(&fields[1]),
                    form: match atom(&form[0]) {
                        "Syntax" => ParenForm::Syntax,
                        "Nlabel" => ParenForm::Nlabel {
                            label: text(&form[1]),
                            names: list(&form[2], text),
                        },
                        _ => ParenForm::Xlabel {
                            label: text(&form[1]),
                            indices: list(&form[2], |sexp| {
                                let entry = items(sexp);
                                XlabelIndex {
                                    name: text(&entry[0]),
                                    index: number(&entry[1]),
                                }
                            }),
                        },
                    },
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

    fn read_instance(sexp: &Sexp) -> InstanceDefinition {
        let fields = items(sexp);
        InstanceDefinition {
            args: list(&fields[1], text),
            module: text(&fields[2]),
            substitutions: list(&fields[3], |sexp| {
                let entry = items(sexp);
                Entry {
                    name: text(&entry[0]),
                    expression: read_expr(&entry[1]),
                }
            }),
            location: read_locus(&fields[4]),
        }
    }

    fn read_setting(sexp: &Sexp) -> PragmaSetting {
        let fields = items(sexp);
        PragmaSetting {
            hint: text(&fields[0]),
            value: match &fields[1] {
                Sexp::List(value) => PragmaValue::String(text(&value[1])),
                other if atom(other) == "Default" => PragmaValue::Default,
                other => PragmaValue::Float(number(other)),
            },
        }
    }

    fn read_defn(sexp: &Sexp) -> Defn {
        let fields = items(sexp);
        let core = match atom(&fields[0]) {
            "Recursive" => DefnCore::Recursive {
                name: text(&fields[1]),
                shape: number(&fields[2]),
            },
            "Operator" => DefnCore::Operator {
                name: text(&fields[1]),
                body: read_expr(&fields[2]),
            },
            "Instance" => DefnCore::Instance {
                name: text(&fields[1]),
                instance: read_instance(&fields[2]),
            },
            "Bpragma" => DefnCore::Bpragma {
                name: text(&fields[1]),
                body: read_expr(&fields[2]),
                methods: list(&fields[3], |sexp| list(sexp, read_setting)),
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

    fn read_declarations(sexp: &Sexp) -> Vec<Declaration> {
        list(sexp, |sexp| {
            let declaration = items(sexp);
            Declaration {
                name: text(&declaration[0]),
                shape: number(&declaration[1]),
            }
        })
    }

    fn read_unit(sexp: &Sexp) -> ModuleUnit {
        let fields = items(sexp);
        let core = match atom(&fields[0]) {
            "Constants" => ModuleUnitCore::Constants {
                declarations: read_declarations(&fields[1]),
            },
            "Recursives" => ModuleUnitCore::Recursives {
                declarations: read_declarations(&fields[1]),
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
            "Anoninst" => ModuleUnitCore::Anoninst {
                instance: read_instance(&fields[1]),
                is_local: boolean(&fields[2]),
            },
            other => panic!("unit {other}"),
        };
        ModuleUnit {
            core,
            location: read_locus(&fields[fields.len() - 1]),
        }
    }

    fn read_mule(sexp: &Sexp) -> Mule {
        let fields = items(sexp);
        Mule {
            name: text(&fields[1]),
            is_important: boolean(&fields[2]),
            is_standard: boolean(&fields[3]),
            depth: optional(&fields[4], number),
            body: list(&fields[5], read_unit),
            ..Mule::default()
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
            let is_main = MAIN.with(|main| *main.borrow() == locus.file);
            format!(
                "@{}:{}-{}:{}{}",
                locus.start_line,
                locus.start_column,
                locus.end_line,
                locus.end_column,
                if is_main {
                    String::new()
                } else {
                    format!("@{}", locus.file)
                }
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

    fn emit_selector(selector: &Selector) -> String {
        match selector {
            Selector::Number(value) => node(&["Number".into(), value.to_string()]),
            Selector::Instance(args) => node(&["Instance".into(), emit_list(args, emit_expr)]),
            Selector::Label { label, args } => {
                node(&["Label".into(), str(label), emit_list(args, emit_expr)])
            }
            other => format!("({other:?})"),
        }
    }

    fn emit_method(method: &OldMethod) -> String {
        node(&[
            "method".into(),
            str(&method.name),
            opt(method.tactic.as_deref(), str),
            opt(method.timeout.as_ref(), f64::to_string),
        ])
    }

    fn emit_fields(fields: &[Field]) -> String {
        emit_list(fields, |field| {
            node(&[str(&field.name), emit_expr(&field.value)])
        })
    }

    fn emit_instance(instance: &InstanceDefinition) -> String {
        node(&[
            "instance".into(),
            emit_list(&instance.args, |arg| str(arg)),
            str(&instance.module),
            emit_list(&instance.substitutions, |entry| {
                node(&[str(&entry.name), emit_expr(&entry.expression)])
            }),
            emit_locus(instance.location.as_ref()),
        ])
    }

    fn emit_expr(expression: &Expr) -> String {
        let (kind, mut parts): (&str, Vec<String>) = match &expression.core {
            ExprCore::Ix { index } => ("Ix", vec![index.to_string()]),
            ExprCore::Opaque { name } => ("Opaque", vec![str(name)]),
            ExprCore::Internal { builtin } => ("Internal", vec![builtin.name().into()]),
            ExprCore::Lambda { params, body } => (
                "Lambda",
                vec![
                    emit_list(params, |param| {
                        node(&[
                            str(&param.name),
                            param.shape.to_string(),
                            emit_locus(param.location.as_ref()),
                        ])
                    }),
                    emit_expr(body),
                ],
            ),
            ExprCore::Sequent { sequent } => ("Sequent", vec![emit_sequent(sequent)]),
            ExprCore::Bang {
                expression,
                selectors,
            } => (
                "Bang",
                vec![emit_expr(expression), emit_list(selectors, emit_selector)],
            ),
            ExprCore::Apply { operator, args } => (
                "Apply",
                vec![emit_expr(operator), emit_list(args, emit_expr)],
            ),
            ExprCore::With { expression, method } => {
                ("With", vec![emit_expr(expression), emit_method(method)])
            }
            ExprCore::If {
                condition,
                consequent,
                alternative,
            } => (
                "If",
                vec![
                    emit_expr(condition),
                    emit_expr(consequent),
                    emit_expr(alternative),
                ],
            ),
            ExprCore::List { bullet, items } => (
                "List",
                vec![format!("{bullet:?}"), emit_list(items, emit_expr)],
            ),
            ExprCore::Let { definitions, body } => (
                "Let",
                vec![emit_list(definitions, emit_defn), emit_expr(body)],
            ),
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => (
                "Quant",
                vec![
                    format!("{quantifier:?}"),
                    emit_list(bounds, emit_bound),
                    emit_expr(body),
                ],
            ),
            ExprCore::Tquant {
                quantifier,
                names,
                body,
            } => (
                "Tquant",
                vec![
                    format!("{quantifier:?}"),
                    emit_list(names, |name| str(name)),
                    emit_expr(body),
                ],
            ),
            ExprCore::Choose { name, domain, body } => (
                "Choose",
                vec![str(name), opt(domain.as_ref(), emit_expr), emit_expr(body)],
            ),
            ExprCore::SetSt { name, domain, body } => {
                ("SetSt", vec![str(name), emit_expr(domain), emit_expr(body)])
            }
            ExprCore::SetOf { element, bounds } => (
                "SetOf",
                vec![emit_expr(element), emit_list(bounds, emit_bound)],
            ),
            ExprCore::SetEnum { elements } => ("SetEnum", vec![emit_list(elements, emit_expr)]),
            ExprCore::Tuple { elements } => ("Tuple", vec![emit_list(elements, emit_expr)]),
            ExprCore::Product { factors } => ("Product", vec![emit_list(factors, emit_expr)]),
            ExprCore::Fcn { bounds, body } => {
                ("Fcn", vec![emit_list(bounds, emit_bound), emit_expr(body)])
            }
            ExprCore::FcnApp { function, args } => (
                "FcnApp",
                vec![emit_expr(function), emit_list(args, emit_expr)],
            ),
            ExprCore::Arrow { domain, range } => {
                ("Arrow", vec![emit_expr(domain), emit_expr(range)])
            }
            ExprCore::Rect { fields } => ("Rect", vec![emit_fields(fields)]),
            ExprCore::Record { fields } => ("Record", vec![emit_fields(fields)]),
            ExprCore::Except { function, specs } => (
                "Except",
                vec![
                    emit_expr(function),
                    emit_list(specs, |spec| {
                        node(&[
                            emit_list(&spec.trail, |point| match point {
                                ExceptPoint::Dot(field) => node(&["Dot".into(), str(field)]),
                                ExceptPoint::Apply(expression) => {
                                    node(&["Apply".into(), emit_expr(expression)])
                                }
                            }),
                            emit_expr(&spec.value),
                        ])
                    }),
                ],
            ),
            ExprCore::Dot { expression, field } => ("Dot", vec![emit_expr(expression), str(field)]),
            ExprCore::Sub {
                modal,
                action,
                subscript,
            } => (
                "Sub",
                vec![
                    format!("{modal:?}"),
                    emit_expr(action),
                    emit_expr(subscript),
                ],
            ),
            ExprCore::Tsub {
                modal,
                action,
                subscript,
            } => (
                "Tsub",
                vec![
                    format!("{modal:?}"),
                    emit_expr(action),
                    emit_expr(subscript),
                ],
            ),
            ExprCore::Fair {
                fairness,
                subscript,
                action,
            } => (
                "Fair",
                vec![
                    format!("{fairness:?}"),
                    emit_expr(subscript),
                    emit_expr(action),
                ],
            ),
            ExprCore::Case { arms, other } => (
                "Case",
                vec![
                    emit_list(arms, |arm| {
                        node(&[emit_expr(&arm.condition), emit_expr(&arm.body)])
                    }),
                    opt(other.as_ref(), emit_expr),
                ],
            ),
            ExprCore::String { value } => ("String", vec![str(value)]),
            ExprCore::Num { integer, fraction } => ("Num", vec![str(integer), str(fraction)]),
            ExprCore::At { is_except } => ("At", vec![is_except.to_string()]),
            ExprCore::Parens { expression, form } => (
                "Parens",
                vec![
                    emit_expr(expression),
                    match form {
                        ParenForm::Syntax => "(Syntax)".into(),
                        ParenForm::Nlabel { label, names } => node(&[
                            "Nlabel".into(),
                            str(label),
                            emit_list(names, |name| str(name)),
                        ]),
                        ParenForm::Xlabel { label, indices } => node(&[
                            "Xlabel".into(),
                            str(label),
                            emit_list(indices, |entry| {
                                node(&[str(&entry.name), entry.index.to_string()])
                            }),
                        ]),
                    },
                ],
            ),
        };
        parts.insert(0, kind.into());
        if expression.location.is_some() {
            parts.push(emit_locus(expression.location.as_ref()));
        }
        if expression.is_atomic {
            parts.push("!".into());
        }
        node(&parts)
    }

    fn emit_setting(setting: &PragmaSetting) -> String {
        node(&[
            str(&setting.hint),
            match &setting.value {
                PragmaValue::Default => "Default".into(),
                PragmaValue::String(value) => node(&["String".into(), str(value)]),
                PragmaValue::Float(value) => value.to_string(),
            },
        ])
    }

    fn emit_defn(definition: &Defn) -> String {
        let location = emit_locus(definition.location.as_ref());
        match &definition.core {
            DefnCore::Recursive { name, shape } => {
                node(&["Recursive".into(), str(name), shape.to_string(), location])
            }
            DefnCore::Operator { name, body } => {
                node(&["Operator".into(), str(name), emit_expr(body), location])
            }
            DefnCore::Instance { name, instance } => node(&[
                "Instance".into(),
                str(name),
                emit_instance(instance),
                location,
            ]),
            DefnCore::Bpragma {
                name,
                body,
                methods,
            } => node(&[
                "Bpragma".into(),
                str(name),
                emit_expr(body),
                emit_list(methods, |group| emit_list(group, emit_setting)),
                location,
            ]),
        }
    }

    fn emit_where(where_defined: &WhereDefined) -> String {
        match where_defined {
            WhereDefined::Proof(time) => node(&["Proof".into(), format!("{time:?}")]),
            other => format!("{other:?}"),
        }
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
            HypCore::Flex { name } => node(&["Flex".into(), str(name), location]),
            HypCore::Defn {
                definition,
                where_defined,
                visibility,
                is_local,
                is_constness_unset,
            } => node(&[
                "Defn".into(),
                emit_defn(definition),
                emit_where(where_defined),
                format!("{visibility:?}"),
                is_local.to_string(),
                is_constness_unset.to_string(),
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
            opt(props.method.as_ref(), emit_method),
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
        let (kind, mut parts): (&str, Vec<String>) = match &step.core {
            StepCore::Hide { usable } => ("Hide", vec![emit_usable(usable)]),
            StepCore::Define { definitions } => ("Define", vec![emit_list(definitions, emit_defn)]),
            StepCore::Assert { sequent, proof } => {
                ("Assert", vec![emit_sequent(sequent), emit_proof(proof)])
            }
            StepCore::Suffices { sequent, proof } => {
                ("Suffices", vec![emit_sequent(sequent), emit_proof(proof)])
            }
            StepCore::Pcase { expression, proof } => {
                ("Pcase", vec![emit_expr(expression), emit_proof(proof)])
            }
            StepCore::Pick {
                bounds,
                expression,
                proof,
            } => (
                "Pick",
                vec![
                    emit_list(bounds, emit_bound),
                    emit_expr(expression),
                    emit_proof(proof),
                ],
            ),
            StepCore::Use { usable, is_only } => {
                ("Use", vec![emit_usable(usable), is_only.to_string()])
            }
            StepCore::Have { expression } => ("Have", vec![emit_expr(expression)]),
            StepCore::Take { bounds } => ("Take", vec![emit_list(bounds, emit_bound)]),
            StepCore::Witness { expressions } => {
                ("Witness", vec![emit_list(expressions, emit_expr)])
            }
            StepCore::Forget { count } => ("Forget", vec![count.to_string()]),
        };
        parts.insert(0, kind.into());
        parts.push(emit_props(&step.props));
        node(&parts)
    }

    fn emit_declarations(declarations: &[Declaration]) -> String {
        emit_list(declarations, |declaration| {
            node(&[str(&declaration.name), declaration.shape.to_string()])
        })
    }

    fn emit_unit(unit: &ModuleUnit) -> String {
        let (kind, mut parts): (&str, Vec<String>) = match &unit.core {
            ModuleUnitCore::Constants { declarations } => {
                ("Constants", vec![emit_declarations(declarations)])
            }
            ModuleUnitCore::Recursives { declarations } => {
                ("Recursives", vec![emit_declarations(declarations)])
            }
            ModuleUnitCore::Variables { names } => {
                ("Variables", vec![emit_list(names, |name| str(name))])
            }
            ModuleUnitCore::Definition {
                definition,
                where_defined,
                visibility,
                is_local,
            } => (
                "Definition",
                vec![
                    emit_defn(definition),
                    emit_where(where_defined),
                    format!("{visibility:?}"),
                    is_local.to_string(),
                ],
            ),
            ModuleUnitCore::Axiom { name, expression } => (
                "Axiom",
                vec![opt(name.as_deref(), str), emit_expr(expression)],
            ),
            ModuleUnitCore::Theorem {
                name,
                sequent,
                axiom_count,
                proof,
            } => (
                "Theorem",
                vec![
                    opt(name.as_deref(), str),
                    emit_sequent(sequent),
                    axiom_count.to_string(),
                    emit_proof(proof),
                ],
            ),
            ModuleUnitCore::Submod { module } => ("Submod", vec![emit_mule(module)]),
            ModuleUnitCore::Mutate { mode, usable } => {
                ("Mutate", vec![format!("{mode:?}"), emit_usable(usable)])
            }
            ModuleUnitCore::Anoninst { instance, is_local } => (
                "Anoninst",
                vec![emit_instance(instance), is_local.to_string()],
            ),
        };
        parts.insert(0, kind.into());
        parts.push(emit_locus(unit.location.as_ref()));
        node(&parts)
    }

    fn emit_mule(module: &Mule) -> String {
        node(&[
            "mule".into(),
            str(&module.name),
            module.is_important.to_string(),
            module.is_standard.to_string(),
            opt(module.depth.as_ref(), usize::to_string),
            emit_list(&module.body, emit_unit),
        ])
    }

    fn fnv(text: &str) -> String {
        let hash = text.bytes().fold(0xcbf2_9ce4_8422_2325_u64, |hash, byte| {
            (hash ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3)
        });
        format!("0x{hash:016x}")
    }

    fn digest(text: &str) -> String {
        format!("{} {}", text.len(), fnv(text))
    }

    fn show_channel(channel: Channel) -> &'static str {
        match channel {
            Channel::Toolbox => "toolbox",
            Channel::ToolboxOnly => "toolboxOnly",
            Channel::Stderr => "stderr",
            Channel::Stdout => "stdout",
        }
    }

    /// A call as the fixture records it, with its strings unescaped.
    fn show_call(call: &Sexp) -> String {
        let fields = items(call);
        let show = |sexp: &Sexp| match sexp {
            Sexp::Text(text) => text.clone(),
            other => atom(other).to_owned(),
        };
        fields.iter().map(show).collect::<Vec<_>>().join(" ")
    }

    /// Replays the fixture's calls to `normalize` and gives each one's result, as `show_call`
    /// shows the fixture's, beside the expected one.
    fn replay(fixture: &str) -> Vec<(String, String)> {
        let sexp = parse(fixture);
        let fields = items(&sexp);
        MAIN.with(|main| *main.borrow_mut() = Rc::from(text(&fields[1])));
        let counter = Rc::new(Counter::default());
        counter.value.set(number(&fields[2]));
        let standard = get_standard_modules();
        let order: Vec<Mule> = list(&fields[3], |sexp| {
            let entry = items(sexp);
            if atom(&entry[0]) == "std" {
                let name = text(&entry[1]);
                return standard
                    .iter()
                    .find(|module| module.name == name)
                    .expect("standard module")
                    .clone();
            }
            read_mule(sexp)
        });
        let mut normalized: HashMap<String, Rc<Mule>> = order
            .iter()
            .map(|module| (module.name.clone(), Rc::new(module.clone())))
            .collect();
        let warnings = Rc::new(RefCell::new(Vec::new()));
        let mut sink = |warning: ObligationWarning| {
            warnings.borrow_mut().push(format!(
                "{}: {}",
                show_channel(warning.channel),
                warning.text
            ));
        };
        let mut pipeline = Pipeline {
            anonymizer: create_anonymizer(counter.clone()),
            simplify: create_simplifier(counter.clone()),
            salts: Counter::default(),
            latest_modules: HashMap::new(),
            on_warning: RefCell::new(&mut sink),
        };
        let expected = items(&fields[4]);
        let mut results = Vec::new();
        for module in order.iter().filter(|module| !module.is_standard) {
            let Some(call) = expected.get(results.len()) else {
                break;
            };
            warnings.borrow_mut().clear();
            let result = normalize(&mut pipeline, &mut normalized, &None, module);
            let warned = digest(&warnings.borrow().join("\n"));
            let actual = match result {
                Ok(module) => format!(
                    "ok {} {} {} {warned}",
                    digest(&emit_mule(&module)),
                    counter.value.get(),
                    pipeline.salts.value.get()
                ),
                Err(ObligationError::Proof {
                    message,
                    failure,
                    exception,
                }) => format!(
                    "error {message} {} {exception} {warned}",
                    failure.as_deref().unwrap_or("_")
                ),
                Err(other) => format!("{} {}", other.name(), other.message()),
            };
            results.push((actual, show_call(call)));
        }
        assert_eq!(results.len(), expected.len(), "calls");
        results
    }

    fn check(fixture: &str) {
        for (actual, expected) in replay(fixture) {
            assert_eq!(actual, expected);
        }
    }

    const EXPANDED_MODULE: &str = r#"
        (mule "Inner" false false 0 ((Constants (("S" 0)) @2:1-2:9) (Definition (Operator "Op" (Ix 1
        @3:1-3:9) @3:1-3:9) User Visible false @3:1-3:9) (Theorem "Thm" (sequent () (Ix 2 @4:1-4:9)) 0
        (Obvious (props @5:1-5:9 _ _ _)) @4:1-4:9) (Definition (Operator "Loc" (Apply (Internal Cup) ((Ix
        4) (Ix 3))) @6:1-6:9) User Visible true @6:1-6:9)))
    "#;

    const PARAMETRIC_WARNING: &str = "stderr: File \"M.tla\", line 8, characters 1-8:\nWarning: Instancing produces parametric theorems.\nSuch theorems will be forcibly hidden and cannot be cited.\n(This warning appears at-most once per INSTANCE declaration.)";

    /// `expandInstance` on `N(args) == INSTANCE module WITH S <- T` in a context of `T`, with the
    /// latest modules holding `EXPANDED_MODULE`: the definitions and the salts after, or the error,
    /// and the warnings.
    fn expand(args: &str, module: &str) -> (String, Vec<String>) {
        MAIN.with(|main| *main.borrow_mut() = Rc::from("M.tla"));
        let warnings = Rc::new(RefCell::new(Vec::new()));
        let mut sink = |warning: ObligationWarning| {
            warnings.borrow_mut().push(format!(
                "{}: {}",
                show_channel(warning.channel),
                warning.text
            ));
        };
        let counter = Rc::new(Counter::default());
        let inner = read_mule(&parse(EXPANDED_MODULE));
        let mut pipeline = Pipeline {
            anonymizer: create_anonymizer(counter.clone()),
            simplify: create_simplifier(counter),
            salts: Counter::default(),
            latest_modules: HashMap::from([(inner.name.clone(), Rc::new(inner))]),
            on_warning: RefCell::new(&mut sink),
        };
        let definition = read_defn(&parse(&format!(
            r#"(Instance "N" (instance {args} "{module}" (("S" (Opaque "T" @8:1-8:9))) @8:1-8:9) @8:1-8:9)"#
        )));
        let scope = adjoin_all(&None, &[get_fresh("T", Level::Constant, 0)]);
        let shown = match expand_instance(&mut pipeline, &scope, &definition) {
            Ok(definitions) => format!(
                "{} salts {}",
                definitions
                    .iter()
                    .map(emit_defn)
                    .collect::<Vec<_>>()
                    .join(" "),
                pipeline.salts.value.get()
            ),
            Err(error) => format!("{error:?}"),
        };
        drop(pipeline);
        (shown, warnings.take())
    }

    #[test]
    fn expands_an_instance_into_its_definitions() {
        assert_eq!(
            expand(r#"("a")"#, "Inner"),
            (
                r#"(Operator "N!Op" (Lambda (("a" 0 _)) (Ix 2 @3:1-3:9) @3:1-3:9) @3:1-3:9) (Operator "N!Loc$1" (Lambda (("a" 0 _)) (Apply (Internal Cup) ((Ix 3) (Ix 1)))) @6:1-6:9) salts 1"#
                    .to_owned(),
                vec![PARAMETRIC_WARNING.to_owned()]
            )
        );
        assert_eq!(
            expand("()", "Inner"),
            (
                r#"(Operator "N!Op" (Ix 1 @3:1-3:9) @3:1-3:9) (Operator "N!Loc$1" (Apply (Internal Cup) ((Ix 2) (Ix 1))) @6:1-6:9) salts 1"#
                    .to_owned(),
                Vec::new()
            )
        );
    }

    #[test]
    fn reports_an_unknown_module() {
        let (shown, warnings) = expand("()", "Nope");
        assert_eq!(
            shown,
            format!(
                "{:?}",
                ObligationError::proof_failure("Module \"Nope\" unknown", "Module.Elab.anon#defns")
            )
        );
        assert_eq!(
            warnings,
            ["toolbox: File \"M.tla\", line 8, characters 1-8 :\nModule \"Nope\" unknown\n"]
        );
    }

    #[test]
    fn normalizes_as_the_typescript_does() {
        check(INSTANCES);
        check(PARAMETRIC_THEOREMS);
        check(RECURSIVE_OPERATOR);
        check(UNDECLARED_PARAMETER);
        check(UNKNOWN_LET_INSTANCE);
        check(ENABLED_WITHOUT_TLAPS);
        check(UNINFERRED_PARAMETER);
        check(INSTANCE_MUTATE);
        check(PARAMETRIC_INSTANCE_LEVEL);
        check(PARAMETERIZED_INSTANTIATION);
        check(COOPER_INSTANTIATION);
        check(BACKEND_PRAGMAS);
    }

    const INSTANCES: &str = r#"
        (fixture "M.tla" 3 ((std "Naturals") (mule "Inner" false false _ ((Definition (Operator "Nat"
        (Internal Nat) _) Builtin Visible false _) (Definition (Operator "+" (Lambda (("x1" 0 _) ("x2" 0 _))
        (Apply (Internal Plus) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "-"
        (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Minus) ((Ix 2) (Ix 1)))) _) Builtin Visible false
        _) (Definition (Operator "*" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Times) ((Ix 2) (Ix
        1)))) _) Builtin Visible false _) (Definition (Operator "^" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply
        (Internal Exp) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "<" (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Lt) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Definition (Operator ">" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Gt) ((Ix 2) (Ix 1)))) _)
        Builtin Visible false _) (Definition (Operator "=<" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal
        Lteq) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator ">=" (Lambda (("x1" 0 _)
        ("x2" 0 _)) (Apply (Internal Gteq) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition
        (Operator "%" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Remainder) ((Ix 2) (Ix 1)))) _)
        Builtin Visible false _) (Definition (Operator "\\div" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply
        (Internal Quotient) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator ".." (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Range) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Constants (("S" 0) ("F" 1)) @3:10-3:11@Inner.tla) (Variables ("v") @4:10-4:11@Inner.tla)
        (Definition (Operator "Loc" (Apply (Internal Cup) ((Opaque "S" @5:14-5:15@Inner.tla) (SetEnum ((Num
        "1" "" @5:22-5:23@Inner.tla)) @5:21-5:24@Inner.tla)) @5:14-5:24@Inner.tla) @5:1-5:24@Inner.tla) User
        Hidden true @5:1-5:24@Inner.tla) (Definition (Operator "Op" (Lambda (("a" 0 @6:4-6:5@Inner.tla))
        (Apply (Internal Conj) ((Apply (Internal Mem) ((Opaque "a" @6:10-6:11@Inner.tla) (Opaque "Loc"
        @6:16-6:19@Inner.tla)) @6:10-6:19@Inner.tla) (Apply (Internal Eq) ((Apply (Internal Prime) ((Opaque
        "v" @6:23-6:24@Inner.tla)) @6:23-6:25@Inner.tla) (Opaque "v" @6:28-6:29@Inner.tla))
        @6:23-6:29@Inner.tla)) @6:10-6:29@Inner.tla) @6:1-6:29@Inner.tla) @6:1-6:29@Inner.tla) User Hidden
        false @6:1-6:29@Inner.tla) (Definition (Operator "Act" (Apply (Opaque "+") ((Opaque "v"
        @7:8-7:9@Inner.tla) (Num "1" "" @7:12-7:13@Inner.tla)) @7:8-7:13@Inner.tla) @7:1-7:13@Inner.tla)
        User Hidden false @7:1-7:13@Inner.tla) (Axiom "Ax" (Apply (Internal Neq) ((Opaque "S"
        @8:13-8:14@Inner.tla) (SetEnum () @8:17-8:19@Inner.tla)) @8:13-8:19@Inner.tla) @8:1-8:19@Inner.tla)
        (Axiom _ (Apply (Internal Subseteq) ((Opaque "S" @9:7-9:8@Inner.tla) (Opaque "Nat"
        @9:19-9:22@Inner.tla)) @9:7-9:22@Inner.tla) @9:1-9:22@Inner.tla) (Theorem "Thm" (sequent () (Apply
        (Internal Implies) ((Apply (Opaque "Op" @10:16-10:21@Inner.tla) ((Num "1" ""
        @10:19-10:20@Inner.tla)) @10:16-10:21@Inner.tla) (Internal TRUE @10:25-10:29@Inner.tla))
        @10:16-10:29@Inner.tla)) 0 (Obvious (props @11:3-11:10@Inner.tla _ _ _)) @10:1-11:10@Inner.tla)
        (Theorem _ (sequent () (Apply (Internal Eq) ((Opaque "S" @12:9-12:10@Inner.tla) (Opaque "S"
        @12:13-12:14@Inner.tla)) @12:9-12:14@Inner.tla)) 0 (Omitted Implicit (props @12:14-12:14@Inner.tla _
        _ _)) @12:1-12:14@Inner.tla) (Mutate Use (usable ((Opaque "Ax" @13:5-13:7@Inner.tla)) ())
        @13:1-13:4@Inner.tla) (Mutate Hide (usable () ((Dvar "Op" @14:10-14:12@Inner.tla)))
        @14:1-14:12@Inner.tla) (Definition (Operator "Last" (Apply (Opaque "F" @15:9-15:13@Inner.tla)
        ((Opaque "S" @15:11-15:12@Inner.tla)) @15:9-15:13@Inner.tla) @15:1-15:13@Inner.tla) User Hidden
        false @15:1-15:13@Inner.tla))) (std "Integers") (mule "M" true false _ ((Definition (Operator "Nat"
        (Internal Nat) _) Builtin Visible false _) (Definition (Operator "+" (Lambda (("x1" 0 _) ("x2" 0 _))
        (Apply (Internal Plus) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "-"
        (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Minus) ((Ix 2) (Ix 1)))) _) Builtin Visible false
        _) (Definition (Operator "*" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Times) ((Ix 2) (Ix
        1)))) _) Builtin Visible false _) (Definition (Operator "^" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply
        (Internal Exp) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "<" (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Lt) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Definition (Operator ">" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Gt) ((Ix 2) (Ix 1)))) _)
        Builtin Visible false _) (Definition (Operator "=<" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal
        Lteq) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator ">=" (Lambda (("x1" 0 _)
        ("x2" 0 _)) (Apply (Internal Gteq) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition
        (Operator "%" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Remainder) ((Ix 2) (Ix 1)))) _)
        Builtin Visible false _) (Definition (Operator "\\div" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply
        (Internal Quotient) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator ".." (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Range) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Constants (("T" 0)) @3:10-3:11) (Variables ("w") @4:10-4:11) (Definition (Instance "I" (instance ()
        "Inner" (("S" (Opaque "T" @5:31-5:32)) ("F" (Lambda (("x" 0 _)) (Opaque "x" @5:50-5:51) @5:39-5:51))
        ("v" (Opaque "w" @5:58-5:59))) @5:3-5:59) @5:1-5:59) User Hidden false @5:6-5:59) (Definition
        (Instance "J" (instance ("a") "Inner" (("S" (Opaque "a" @6:34-6:35)) ("F" (Lambda (("x" 0 _))
        (Opaque "x" @6:53-6:54) @6:42-6:54)) ("v" (Opaque "w" @6:61-6:62))) @6:2-6:62) @6:1-6:62) User
        Hidden false @6:9-6:62) (Anoninst (instance () "Inner" (("S" (SetEnum ((Opaque "T" @7:27-7:28))
        @7:26-7:29)) ("F" (Lambda (("x" 0 _)) (Opaque "x" @7:47-7:48) @7:36-7:48)) ("v" (Opaque "w"
        @7:55-7:56))) @7:1-7:56) false @7:1-7:56) (Definition (Instance "K" (instance () "Inner" (("S"
        (Opaque "T" @8:37-8:38)) ("F" (Lambda (("x" 0 _)) (Opaque "x" @8:56-8:57) @8:45-8:57)) ("v" (Opaque
        "w" @8:64-8:65))) @8:9-8:65) @8:1-8:65) User Hidden true @8:12-8:65) (Definition (Operator "Def"
        (Apply (Internal Conj) ((Bang (Opaque "I" @9:8-9:15) ((Label "Op" ((Num "1" "" @9:13-9:14))))
        @9:8-9:15) (Bang (Apply (Opaque "J" @9:19-9:27) ((Opaque "T" @9:21-9:22)) @9:19-9:27) ((Label "Act"
        ())) @9:19-9:27)) @9:8-9:27) @9:1-9:27) User Hidden false @9:1-9:27) (Theorem "T1" (sequent ()
        (Apply (Internal Implies) ((Opaque "Def" @10:15-10:18) (Opaque "Def" @10:22-10:25)) @10:15-10:25)) 0
        (By (usable () ((Dvar "Def" @11:10-11:13))) false (props @11:3-11:5 (Unnamed 0 0) _ _)) @10:1-11:13)
        (Theorem "T1" (sequent () (Internal TRUE @12:15-12:19)) 0 (Obvious (props @13:3-13:10 _ _ _))
        @12:1-13:10) (Definition (Operator "Def2" (Let ((Instance "N" (instance () "Inner" (("S" (Opaque "T"
        @14:43-14:44)) ("F" (Lambda (("x" 0 _)) (Opaque "x" @14:62-14:63) @14:51-14:63)) ("v" (Opaque "w"
        @14:70-14:71))) @14:15-14:71) @14:13-14:71)) (Bang (Opaque "N" @14:75-14:82) ((Label "Op" ((Num "2"
        "" @14:80-14:81)))) @14:75-14:82) @14:9-14:82) @14:1-14:82) User Hidden false @14:1-14:82)
        (Definition (Operator "Dup" (Num "1" "" @15:8-15:9) @15:1-15:9) User Hidden false @15:1-15:9)
        (Definition (Operator "Dup" (Num "1" "" @16:8-16:9) @16:1-16:9) User Hidden false @16:1-16:9) (Axiom
        "Ax1" (Apply (Internal Eq) ((Opaque "T" @17:14-17:15) (Opaque "T" @17:18-17:19)) @17:14-17:19)
        @17:1-17:19) (Axiom "Ax1" (Apply (Internal Eq) ((Opaque "T" @18:14-18:15) (Opaque "T" @18:18-18:19))
        @18:14-18:19) @18:1-18:19) (Theorem _ (sequent ((Fresh "x" 0 Constant (Opaque "T" @19:26-19:27)
        Visible @19:16-19:27)) (Apply (Internal Mem) ((Opaque "x" @19:34-19:35) (Opaque "T" @19:40-19:41))
        @19:34-19:41)) 0 (Steps ((Assert (sequent () (Apply (Internal Mem) ((Opaque "x" @20:9-20:10) (Opaque
        "T" @20:15-20:16)) @20:9-20:16)) (Obvious (props @20:17-20:24 _ _ _)) (props @20:3-20:24 (Named 1
        "1" false) _ _))) (By (usable ((Opaque "<1>1" @21:14-21:18)) ()) false (props @21:11-21:13 (Unnamed
        2 0) _ _)) (props @21:3-21:13 (Unnamed 1 1) _ _) (props @20:3-21:13 (Unnamed 1 1) _ _)) @19:1-21:18)
        (Submod (mule "Sub" true false _ ((Constants (("U" 0)) @23:10-23:11) (Definition (Operator "Sd"
        (Opaque "U" @24:7-24:8) @24:1-24:8) User Hidden false @24:1-24:8) (Theorem _ (sequent () (Apply
        (Internal Eq) ((Opaque "Sd" @25:9-25:11) (Opaque "U" @25:14-25:15)) @25:9-25:15)) 0 (Obvious (props
        @25:16-25:23 _ _ _)) @25:1-25:23))) _) (Definition (Instance "L" (instance () "Sub" (("U" (Opaque
        "T" @27:29-27:30))) @27:3-27:30) @27:1-27:30) User Hidden false @27:6-27:30) (Theorem _ (sequent ()
        (Apply (Internal Eq) ((Opaque "Dup" @28:9-28:12) (Num "1" "" @28:15-28:16)) @28:9-28:16)) 0 (Steps
        ((Define ((Instance "Q" (instance () "Sub" (("U" (Opaque "T" @29:42-29:43))) @29:16-29:43)
        @29:14-29:43)) (props @29:3-29:43 (Unnamed 1 2) _ _))) (By (usable () ((Dvar "Dup" @30:18-30:21)))
        false (props @30:11-30:13 (Unnamed 2 0) _ _)) (props @30:3-30:13 (Unnamed 1 3) _ _) (props
        @29:3-30:13 (Unnamed 1 3) _ _)) @28:1-30:21))) (std "Reals") (std "Sequences") (mule "Sub" true
        false _ ((Constants (("U" 0)) @23:10-23:11) (Definition (Operator "Sd" (Opaque "U" @24:7-24:8)
        @24:1-24:8) User Hidden false @24:1-24:8) (Theorem _ (sequent () (Apply (Internal Eq) ((Opaque "Sd"
        @25:9-25:11) (Opaque "U" @25:14-25:15)) @25:9-25:15)) 0 (Obvious (props @25:16-25:23 _ _ _))
        @25:1-25:23))) (std "TLC")) ((ok 3553 "0xf9a74dcf636610f5" 3 0 0 "0xcbf29ce484222325") (ok 20136
        "0x98a4ed0cef2cea1f" 9 5 205 "0xe94c619f8f4400ae") (ok 300 "0xb926c456d07eb8e3" 9 5 0
        "0xcbf29ce484222325")))
    "#;

    const PARAMETRIC_THEOREMS: &str = r#"
        (fixture "M.tla" 0 ((mule "Inner" false false _ ((Constants (("G" 1)) @2:10-2:14@Inner.tla)
        (Variables ("v") @3:10-3:11@Inner.tla) (Theorem "Named" (sequent () (Apply (Internal ENABLED)
        ((Apply (Internal Eq) ((Apply (Opaque "G" @4:27-4:32@Inner.tla) ((Apply (Internal Prime) ((Opaque
        "v" @4:29-4:30@Inner.tla)) @4:29-4:31@Inner.tla)) @4:27-4:32@Inner.tla) (Num "1" ""
        @4:35-4:36@Inner.tla)) @4:27-4:36@Inner.tla)) @4:18-4:36@Inner.tla)) 0 (Omitted Implicit (props
        @4:37-4:37@Inner.tla _ _ _)) @4:1-4:37@Inner.tla) (Theorem _ (sequent () (Apply (Internal ENABLED)
        ((Apply (Internal Eq) ((Apply (Opaque "G" @5:18-5:23@Inner.tla) ((Apply (Internal Prime) ((Opaque
        "v" @5:20-5:21@Inner.tla)) @5:20-5:22@Inner.tla)) @5:18-5:23@Inner.tla) (Num "2" ""
        @5:26-5:27@Inner.tla)) @5:18-5:27@Inner.tla)) @5:9-5:27@Inner.tla)) 0 (Omitted Implicit (props
        @5:28-5:28@Inner.tla _ _ _)) @5:1-5:28@Inner.tla))) (std "Integers") (mule "M" true false _
        ((Variables ("w") @2:10-2:11) (Definition (Instance "I" (instance () "Inner" (("G" (Lambda (("x" 0
        _)) (Opaque "x" @3:42-3:43) @3:31-3:43)) ("v" (Opaque "w" @3:50-3:51))) @3:3-3:51) @3:1-3:51) User
        Hidden false @3:6-3:51) (Theorem _ (sequent () (Internal TRUE @4:9-4:13)) 0 (Obvious (props
        @4:14-4:21 _ _ _)) @4:1-4:21))) (std "Naturals") (std "Reals") (std "Sequences") (std "TLC")) ((ok
        847 "0x0dc66e3fa5485803" 0 0 0 "0xcbf29ce484222325") (ok 434 "0x531d52cf31347f7f" 0 0 2662
        "0x836756e6748bfcb1")))
    "#;

    const RECURSIVE_OPERATOR: &str = r#"
        (fixture "M.tla" 0 ((std "Integers") (std "Naturals") (mule "M" true false _ ((Definition (Operator
        "Nat" (Internal Nat) _) Builtin Visible false _) (Definition (Operator "+" (Lambda (("x1" 0 _) ("x2"
        0 _)) (Apply (Internal Plus) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "-"
        (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Minus) ((Ix 2) (Ix 1)))) _) Builtin Visible false
        _) (Definition (Operator "*" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Times) ((Ix 2) (Ix
        1)))) _) Builtin Visible false _) (Definition (Operator "^" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply
        (Internal Exp) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "<" (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Lt) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Definition (Operator ">" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Gt) ((Ix 2) (Ix 1)))) _)
        Builtin Visible false _) (Definition (Operator "=<" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal
        Lteq) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator ">=" (Lambda (("x1" 0 _)
        ("x2" 0 _)) (Apply (Internal Gteq) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition
        (Operator "%" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Remainder) ((Ix 2) (Ix 1)))) _)
        Builtin Visible false _) (Definition (Operator "\\div" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply
        (Internal Quotient) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator ".." (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Range) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Recursives (("R" 1)) @3:11-3:15) (Definition (Operator "R" (Lambda (("n" 0 @4:3-4:4)) (If (Apply
        (Internal Eq) ((Opaque "n" @4:12-4:13) (Num "0" "" @4:16-4:17)) @4:12-4:17) (Num "0" "" @4:23-4:24)
        (Apply (Opaque "R" @4:30-4:38) ((Apply (Opaque "-") ((Opaque "n" @4:32-4:33) (Num "1" ""
        @4:36-4:37)) @4:32-4:37)) @4:30-4:38) @4:9-4:38) @4:1-4:38) @4:1-4:38) User Hidden false @4:1-4:38)
        (Theorem _ (sequent () (Apply (Internal Eq) ((Apply (Opaque "R" @5:9-5:13) ((Num "0" "" @5:11-5:12))
        @5:9-5:13) (Num "0" "" @5:16-5:17)) @5:9-5:17)) 0 (By (usable () ((Dvar "R" @6:10-6:11))) false
        (props @6:3-6:5 (Unnamed 0 0) _ _)) @5:1-6:11))) (std "Reals") (std "Sequences") (std "TLC"))
        ((error "Recursive\u0020operators\u0020not\u0020supported\u0020by\u0020TLAPS"
        "Expr.Anon:\u0020Recursive" "Failure(\"Expr.Anon:\u0020Recursive\")" 0 "0xcbf29ce484222325")))
    "#;

    const UNDECLARED_PARAMETER: &str = r#"
        (fixture "M.tla" 0 ((mule "Inner" false false _ ((Constants (("S" 0)) @2:10-2:11@Inner.tla)
        (Definition (Operator "Op" (Opaque "S" @3:7-3:8@Inner.tla) @3:1-3:8@Inner.tla) User Hidden false
        @3:1-3:8@Inner.tla))) (std "Integers") (mule "M" true false _ ((Constants (("T" 0)) @2:10-2:11)
        (Definition (Instance "I" (instance () "Inner" (("Z" (Opaque "T" @3:31-3:32))) @3:3-3:32) @3:1-3:32)
        User Hidden false @3:6-3:32))) (std "Naturals") (std "Reals") (std "Sequences") (std "TLC")) ((ok
        184 "0x0936088965fcd7f0" 0 0 0 "0xcbf29ce484222325") (error
        "Parameter\u0020Z\u0020occurs\u0020in\u0020the\u0020statement\u0020`INSTANCE\u0020Inner\u0020WITH`,\u0020and\u0020is\u0020not\u0020declared\u0020in\u0020the\u0020module\u0020Inner"
        "Parameter\u0020Z\u0020occurs\u0020in\u0020the\u0020statement\u0020`INSTANCE\u0020Inner\u0020WITH`,\u0020and\u0020is\u0020not\u0020declared\u0020in\u0020the\u0020module\u0020Inner"
        "Failure(\"Parameter\u0020Z\u0020occurs\u0020in\u0020the\u0020statement\u0020`INSTANCE\u0020Inner\u0020WITH`,\u0020and\u0020is\u0020not\u0020declared\u0020in\u0020the\u0020module\u0020Inner\")"
        0 "0xcbf29ce484222325")))
    "#;

    const UNKNOWN_LET_INSTANCE: &str = r#"
        (fixture "M.tla" 0 ((mule "Inner" false false _ ((Constants (("S" 0)) @2:10-2:11@Inner.tla)
        (Definition (Operator "Op" (Opaque "S" @3:7-3:8@Inner.tla) @3:1-3:8@Inner.tla) User Hidden false
        @3:1-3:8@Inner.tla))) (std "Integers") (mule "M" true false _ ((Constants (("T" 0)) @2:10-2:11)
        (Definition (Operator "Def" (Let ((Instance "N" (instance () "Inner" (("S" (Opaque "T" @3:42-3:43)))
        @3:14-3:43) @3:12-3:43)) (Bang (Opaque "N" @3:47-3:51) ((Label "Op" ())) @3:47-3:51) @3:8-3:51)
        @3:1-3:51) User Hidden false @3:1-3:51) (Definition (Instance "I" (instance () "Inner" () @4:3-4:20)
        @4:1-4:20) User Hidden false @4:6-4:20))) (std "Naturals") (std "Reals") (std "Sequences") (std
        "TLC")) ((ok 184 "0x0936088965fcd7f0" 0 0 0 "0xcbf29ce484222325") (error
        "Module\u0020\"Inner\"\u0020unknown" "Module.Elab.anon#defns" "Failure(\"Module.Elab.anon#defns\")"
        73 "0xbfc71da8fb71bc0b")))
    "#;

    const ENABLED_WITHOUT_TLAPS: &str = r#"
        (fixture "M.tla" 3 ((std "Naturals") (mule "Inner" false false _ ((Definition (Operator "Nat"
        (Internal Nat) _) Builtin Visible false _) (Definition (Operator "+" (Lambda (("x1" 0 _) ("x2" 0 _))
        (Apply (Internal Plus) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "-"
        (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Minus) ((Ix 2) (Ix 1)))) _) Builtin Visible false
        _) (Definition (Operator "*" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Times) ((Ix 2) (Ix
        1)))) _) Builtin Visible false _) (Definition (Operator "^" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply
        (Internal Exp) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "<" (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Lt) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Definition (Operator ">" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Gt) ((Ix 2) (Ix 1)))) _)
        Builtin Visible false _) (Definition (Operator "=<" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal
        Lteq) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator ">=" (Lambda (("x1" 0 _)
        ("x2" 0 _)) (Apply (Internal Gteq) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition
        (Operator "%" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Remainder) ((Ix 2) (Ix 1)))) _)
        Builtin Visible false _) (Definition (Operator "\\div" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply
        (Internal Quotient) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator ".." (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Range) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Constants (("S" 0) ("F" 1)) @3:10-3:11@Inner.tla) (Variables ("v") @4:10-4:11@Inner.tla)
        (Definition (Operator "Loc" (Apply (Internal Cup) ((Opaque "S" @5:14-5:15@Inner.tla) (SetEnum ((Num
        "1" "" @5:22-5:23@Inner.tla)) @5:21-5:24@Inner.tla)) @5:14-5:24@Inner.tla) @5:1-5:24@Inner.tla) User
        Hidden true @5:1-5:24@Inner.tla) (Definition (Operator "Op" (Lambda (("a" 0 @6:4-6:5@Inner.tla))
        (Apply (Internal Conj) ((Apply (Internal Mem) ((Opaque "a" @6:10-6:11@Inner.tla) (Opaque "Loc"
        @6:16-6:19@Inner.tla)) @6:10-6:19@Inner.tla) (Apply (Internal Eq) ((Apply (Internal Prime) ((Opaque
        "v" @6:23-6:24@Inner.tla)) @6:23-6:25@Inner.tla) (Opaque "v" @6:28-6:29@Inner.tla))
        @6:23-6:29@Inner.tla)) @6:10-6:29@Inner.tla) @6:1-6:29@Inner.tla) @6:1-6:29@Inner.tla) User Hidden
        false @6:1-6:29@Inner.tla) (Definition (Operator "Act" (Apply (Internal ENABLED) ((Apply (Internal
        Eq) ((Apply (Internal Prime) ((Opaque "v" @7:17-7:18@Inner.tla)) @7:17-7:19@Inner.tla) (Apply
        (Opaque "+") ((Opaque "v" @7:22-7:23@Inner.tla) (Num "1" "" @7:26-7:27@Inner.tla))
        @7:22-7:27@Inner.tla)) @7:17-7:27@Inner.tla)) @7:8-7:27@Inner.tla) @7:1-7:28@Inner.tla) User Hidden
        false @7:1-7:28@Inner.tla) (Axiom "Ax" (Apply (Internal Neq) ((Opaque "S" @8:13-8:14@Inner.tla)
        (SetEnum () @8:17-8:19@Inner.tla)) @8:13-8:19@Inner.tla) @8:1-8:19@Inner.tla) (Axiom _ (Apply
        (Internal Subseteq) ((Opaque "S" @9:7-9:8@Inner.tla) (Opaque "Nat" @9:19-9:22@Inner.tla))
        @9:7-9:22@Inner.tla) @9:1-9:22@Inner.tla) (Theorem "Thm" (sequent () (Apply (Internal Implies)
        ((Apply (Opaque "Op" @10:16-10:21@Inner.tla) ((Num "1" "" @10:19-10:20@Inner.tla))
        @10:16-10:21@Inner.tla) (Internal TRUE @10:25-10:29@Inner.tla)) @10:16-10:29@Inner.tla)) 0 (Obvious
        (props @11:3-11:10@Inner.tla _ _ _)) @10:1-11:10@Inner.tla) (Theorem _ (sequent () (Apply (Internal
        Eq) ((Opaque "S" @12:9-12:10@Inner.tla) (Opaque "S" @12:13-12:14@Inner.tla)) @12:9-12:14@Inner.tla))
        0 (Omitted Implicit (props @12:14-12:14@Inner.tla _ _ _)) @12:1-12:14@Inner.tla) (Mutate Use (usable
        ((Opaque "Ax" @13:5-13:7@Inner.tla)) ()) @13:1-13:4@Inner.tla) (Mutate Hide (usable () ((Dvar "Op"
        @14:10-14:12@Inner.tla))) @14:1-14:12@Inner.tla) (Definition (Operator "Last" (Apply (Opaque "F"
        @15:9-15:13@Inner.tla) ((Opaque "S" @15:11-15:12@Inner.tla)) @15:9-15:13@Inner.tla)
        @15:1-15:13@Inner.tla) User Hidden false @15:1-15:13@Inner.tla))) (std "Integers") (mule "M" true
        false _ ((Definition (Operator "Nat" (Internal Nat) _) Builtin Visible false _) (Definition
        (Operator "+" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Plus) ((Ix 2) (Ix 1)))) _) Builtin
        Visible false _) (Definition (Operator "-" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Minus)
        ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "*" (Lambda (("x1" 0 _) ("x2" 0
        _)) (Apply (Internal Times) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "^"
        (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Exp) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Definition (Operator "<" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Lt) ((Ix 2) (Ix 1)))) _)
        Builtin Visible false _) (Definition (Operator ">" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal
        Gt) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "=<" (Lambda (("x1" 0 _)
        ("x2" 0 _)) (Apply (Internal Lteq) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition
        (Operator ">=" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Gteq) ((Ix 2) (Ix 1)))) _) Builtin
        Visible false _) (Definition (Operator "%" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal
        Remainder) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "\\div" (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Quotient) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Definition (Operator ".." (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Range) ((Ix 2) (Ix 1))))
        _) Builtin Visible false _) (Constants (("T" 0)) @3:10-3:11) (Variables ("w") @4:10-4:11)
        (Definition (Instance "I" (instance () "Inner" (("S" (Opaque "T" @5:31-5:32)) ("F" (Lambda (("x" 0
        _)) (Opaque "x" @5:50-5:51) @5:39-5:51)) ("v" (Opaque "w" @5:58-5:59))) @5:3-5:59) @5:1-5:59) User
        Hidden false @5:6-5:59) (Definition (Instance "J" (instance ("a") "Inner" (("S" (Opaque "a"
        @6:34-6:35)) ("F" (Lambda (("x" 0 _)) (Opaque "x" @6:53-6:54) @6:42-6:54)) ("v" (Opaque "w"
        @6:61-6:62))) @6:2-6:62) @6:1-6:62) User Hidden false @6:9-6:62) (Anoninst (instance () "Inner"
        (("S" (SetEnum ((Opaque "T" @7:27-7:28)) @7:26-7:29)) ("F" (Lambda (("x" 0 _)) (Opaque "x"
        @7:47-7:48) @7:36-7:48)) ("v" (Opaque "w" @7:55-7:56))) @7:1-7:56) false @7:1-7:56) (Definition
        (Instance "K" (instance () "Inner" (("S" (Opaque "T" @8:37-8:38)) ("F" (Lambda (("x" 0 _)) (Opaque
        "x" @8:56-8:57) @8:45-8:57)) ("v" (Opaque "w" @8:64-8:65))) @8:9-8:65) @8:1-8:65) User Hidden true
        @8:12-8:65) (Definition (Operator "Def" (Apply (Internal Conj) ((Bang (Opaque "I" @9:8-9:15) ((Label
        "Op" ((Num "1" "" @9:13-9:14)))) @9:8-9:15) (Bang (Apply (Opaque "J" @9:19-9:27) ((Opaque "T"
        @9:21-9:22)) @9:19-9:27) ((Label "Act" ())) @9:19-9:27)) @9:8-9:27) @9:1-9:27) User Hidden false
        @9:1-9:27) (Theorem "T1" (sequent () (Apply (Internal Implies) ((Opaque "Def" @10:15-10:18) (Opaque
        "Def" @10:22-10:25)) @10:15-10:25)) 0 (By (usable () ((Dvar "Def" @11:10-11:13))) false (props
        @11:3-11:5 (Unnamed 0 0) _ _)) @10:1-11:13) (Theorem "T1" (sequent () (Internal TRUE @12:15-12:19))
        0 (Obvious (props @13:3-13:10 _ _ _)) @12:1-13:10) (Definition (Operator "Def2" (Let ((Instance "N"
        (instance () "Inner" (("S" (Opaque "T" @14:43-14:44)) ("F" (Lambda (("x" 0 _)) (Opaque "x"
        @14:62-14:63) @14:51-14:63)) ("v" (Opaque "w" @14:70-14:71))) @14:15-14:71) @14:13-14:71)) (Bang
        (Opaque "N" @14:75-14:82) ((Label "Op" ((Num "2" "" @14:80-14:81)))) @14:75-14:82) @14:9-14:82)
        @14:1-14:82) User Hidden false @14:1-14:82) (Definition (Operator "Dup" (Num "1" "" @15:8-15:9)
        @15:1-15:9) User Hidden false @15:1-15:9) (Definition (Operator "Dup" (Num "1" "" @16:8-16:9)
        @16:1-16:9) User Hidden false @16:1-16:9) (Axiom "Ax1" (Apply (Internal Eq) ((Opaque "T"
        @17:14-17:15) (Opaque "T" @17:18-17:19)) @17:14-17:19) @17:1-17:19) (Axiom "Ax1" (Apply (Internal
        Eq) ((Opaque "T" @18:14-18:15) (Opaque "T" @18:18-18:19)) @18:14-18:19) @18:1-18:19) (Theorem _
        (sequent ((Fresh "x" 0 Constant (Opaque "T" @19:26-19:27) Visible @19:16-19:27)) (Apply (Internal
        Mem) ((Opaque "x" @19:34-19:35) (Opaque "T" @19:40-19:41)) @19:34-19:41)) 0 (Steps ((Assert (sequent
        () (Apply (Internal Mem) ((Opaque "x" @20:9-20:10) (Opaque "T" @20:15-20:16)) @20:9-20:16)) (Obvious
        (props @20:17-20:24 _ _ _)) (props @20:3-20:24 (Named 1 "1" false) _ _))) (By (usable ((Opaque
        "<1>1" @21:14-21:18)) ()) false (props @21:11-21:13 (Unnamed 2 0) _ _)) (props @21:3-21:13 (Unnamed
        1 1) _ _) (props @20:3-21:13 (Unnamed 1 1) _ _)) @19:1-21:18) (Submod (mule "Sub" true false _
        ((Constants (("U" 0)) @23:10-23:11) (Definition (Operator "Sd" (Opaque "U" @24:7-24:8) @24:1-24:8)
        User Hidden false @24:1-24:8) (Theorem _ (sequent () (Apply (Internal Eq) ((Opaque "Sd" @25:9-25:11)
        (Opaque "U" @25:14-25:15)) @25:9-25:15)) 0 (Obvious (props @25:16-25:23 _ _ _)) @25:1-25:23))) _)
        (Definition (Instance "L" (instance () "Sub" (("U" (Opaque "T" @27:29-27:30))) @27:3-27:30)
        @27:1-27:30) User Hidden false @27:6-27:30) (Recursives (("R" 1)) @28:11-28:15) (Definition
        (Operator "R" (Lambda (("n" 0 @29:3-29:4)) (If (Apply (Internal Eq) ((Opaque "n" @29:12-29:13) (Num
        "0" "" @29:16-29:17)) @29:12-29:17) (Num "0" "" @29:23-29:24) (Apply (Opaque "R" @29:30-29:38)
        ((Apply (Opaque "-") ((Opaque "n" @29:32-29:33) (Num "1" "" @29:36-29:37)) @29:32-29:37))
        @29:30-29:38) @29:9-29:38) @29:1-29:38) @29:1-29:38) User Hidden false @29:1-29:38) (Theorem _
        (sequent () (Apply (Internal Eq) ((Apply (Opaque "R" @30:9-30:13) ((Num "0" "" @30:11-30:12))
        @30:9-30:13) (Num "0" "" @30:16-30:17)) @30:9-30:17)) 0 (Steps ((Define ((Instance "Q" (instance ()
        "Sub" (("U" (Opaque "T" @31:42-31:43))) @31:16-31:43) @31:14-31:43)) (props @31:3-31:43 (Unnamed 1
        2) _ _))) (By (usable () ((Dvar "R" @32:18-32:19))) false (props @32:11-32:13 (Unnamed 2 0) _ _))
        (props @32:3-32:13 (Unnamed 1 3) _ _) (props @31:3-32:13 (Unnamed 1 3) _ _)) @30:1-32:19))) (std
        "Reals") (std "Sequences") (mule "Sub" true false _ ((Constants (("U" 0)) @23:10-23:11) (Definition
        (Operator "Sd" (Opaque "U" @24:7-24:8) @24:1-24:8) User Hidden false @24:1-24:8) (Theorem _ (sequent
        () (Apply (Internal Eq) ((Opaque "Sd" @25:9-25:11) (Opaque "U" @25:14-25:15)) @25:9-25:15)) 0
        (Obvious (props @25:16-25:23 _ _ _)) @25:1-25:23))) (std "TLC")) ((ok 3724 "0xe867ba6a5bf3ef1c" 3 0
        0 "0xcbf29ce484222325") (error "Operator\u0020\"EnabledWrapper\"\u0020not\u0020found"
        "Expr.Anon:\u00204" "Failure(\"Expr.Anon:\u00204\")" 276 "0x0db45f2ee5d5ef42")))
    "#;

    const UNINFERRED_PARAMETER: &str = r#"
        (fixture "M.tla" 0 ((mule "Inner" false false _ ((Constants (("S" 0)) @2:10-2:11@Inner.tla)
        (Definition (Operator "Op" (Opaque "S" @3:7-3:8@Inner.tla) @3:1-3:8@Inner.tla) User Hidden false
        @3:1-3:8@Inner.tla))) (std "Integers") (mule "M" true false _ ((Constants (("T" 0)) @2:10-2:11)
        (Definition (Instance "I" (instance () "Inner" () @3:3-3:20) @3:1-3:20) User Hidden false
        @3:6-3:20))) (std "Naturals") (std "Reals") (std "Sequences") (std "TLC")) ((ok 184
        "0x0936088965fcd7f0" 0 0 0 "0xcbf29ce484222325") (error
        "Required\u0020parameter\u0020S\u0020for\u0020module\u0020Inner\u0020could\u0020not\u0020be\u0020inferred."
        "Required\u0020parameter\u0020S\u0020for\u0020module\u0020Inner\u0020could\u0020not\u0020be\u0020inferred."
        "Failure(\"Required\u0020parameter\u0020S\u0020for\u0020module\u0020Inner\u0020could\u0020not\u0020be\u0020inferred.\")"
        0 "0xcbf29ce484222325")))
    "#;

    const INSTANCE_MUTATE: &str = r#"
        (fixture "instance_mutate_test.tla" 0 ((std "Integers") (std "Naturals") (std "Reals") (std
        "Sequences") (std "TLC") (mule "instance_mutate" false false _ ((Definition (Operator "Op" (Lambda
        (("x" 0 @2:4-2:5@instance_mutate.tla)) (Internal TRUE @2:10-2:14@instance_mutate.tla)
        @2:1-2:14@instance_mutate.tla) @2:1-2:14@instance_mutate.tla) User Hidden false
        @2:1-2:14@instance_mutate.tla) (Mutate Use (usable ((Internal TRUE @3:5-3:9@instance_mutate.tla))
        ()) @3:1-3:4@instance_mutate.tla) (Definition (Operator "OpAll" (Quant Forall (("x" Constant
        (NoDomain))) (Apply (Opaque "Op" @4:17-4:22@instance_mutate.tla) ((Opaque "x"
        @4:20-4:21@instance_mutate.tla)) @4:17-4:22@instance_mutate.tla) @4:10-4:22@instance_mutate.tla)
        @4:1-4:22@instance_mutate.tla) User Hidden false @4:1-4:22@instance_mutate.tla))) (mule
        "instance_mutate_test" true false _ ((Anoninst (instance () "instance_mutate" () @6:1-6:25) false
        @6:1-6:25)))) ((ok 674 "0xea5a6b1225388174" 0 0 0 "0xcbf29ce484222325") (ok 577 "0x30a5cc9ad6ad2487"
        0 0 0 "0xcbf29ce484222325")))
    "#;

    const PARAMETRIC_INSTANCE_LEVEL: &str = r#"
        (fixture "Level_of_parametric_INSTANCE_test.tla" 1 ((mule "Inner" true false _ ((Variables ("x")
        @11:10-11:11) (Definition (Operator "Foo" (Opaque "x" @13:8-13:9) @13:1-13:9) User Hidden false
        @13:1-13:9))) (std "Integers") (mule "Level_of_parametric_INSTANCE_test" true false _ ((Submod (mule
        "Inner" true false _ ((Variables ("x") @11:10-11:11) (Definition (Operator "Foo" (Opaque "x"
        @13:8-13:9) @13:1-13:9) User Hidden false @13:1-13:9))) _) (Definition (Instance "M" (instance ("x")
        "Inner" () @22:2-22:23) @22:1-22:23) User Hidden false @22:9-22:23) (Theorem _ (sequent () (Internal
        TRUE @24:9-24:13)) 0 (Steps ((Assert (sequent () (Apply (Internal Implies) ((Bang (Opaque "M"
        @25:7-25:18) ((Label "Foo" ((Internal TRUE @25:13-25:17)))) @25:7-25:18) (Bang (Opaque "M"
        @25:22-25:33) ((Label "Foo" ((Internal TRUE @25:28-25:32)))) @25:22-25:33)) @25:7-25:33)) (Obvious
        (props @26:5-26:12 _ _ _)) (props @25:1-26:12 (Named 1 "1" false) _ _))) (Omitted Implicit (props
        @27:1-27:8 _ _ _)) (props @27:1-27:8 (Unnamed 1 1) _ _) (props @25:1-27:8 (Unnamed 1 1) _ _))
        @24:1-27:8))) (std "Naturals") (std "Reals") (std "Sequences") (std "TLC")) ((ok 148
        "0xb9bd49d6e428dcc2" 1 0 0 "0xcbf29ce484222325") (ok 818 "0x75111ccdd0d18235" 1 0 0
        "0xcbf29ce484222325")))
    "#;

    const PARAMETERIZED_INSTANTIATION: &str = r#"
        (fixture "parameterized_instantiation_test.tla" 0 ((std "Naturals") (std "Sequences") (mule
        "FiniteSets" false false _ ((Anoninst (instance () "Naturals" () @2:7-2:24@FiniteSets.tla) true
        @2:1-2:24@FiniteSets.tla) (Anoninst (instance () "Sequences" () @3:7-3:25@FiniteSets.tla) true
        @3:1-3:25@FiniteSets.tla) (Definition (Operator "IsFiniteSet" (Lambda (("S" 0
        @9:13-9:14@FiniteSets.tla)) (Quant Exists (("seq" Constant (Domain (Apply (Opaque "Seq"
        @14:14-14:20@FiniteSets.tla) ((Opaque "S" @14:18-14:19@FiniteSets.tla))
        @14:14-14:20@FiniteSets.tla)))) (Quant Forall (("s" Constant (Domain (Opaque "S"
        @14:32-14:33@FiniteSets.tla)))) (Quant Exists (("n" Constant (Domain (Apply (Opaque "..") ((Num "1"
        "" @14:45-14:46@FiniteSets.tla) (Apply (Opaque "Len" @14:48-14:56@FiniteSets.tla) ((Opaque "seq"
        @14:52-14:55@FiniteSets.tla)) @14:48-14:56@FiniteSets.tla)) @14:45-14:56@FiniteSets.tla)))) (Apply
        (Internal Eq) ((FcnApp (Opaque "seq" @14:59-14:62@FiniteSets.tla) ((Opaque "n"
        @14:63-14:64@FiniteSets.tla)) @14:59-14:65@FiniteSets.tla) (Opaque "s" @14:68-14:69@FiniteSets.tla))
        @14:59-14:69@FiniteSets.tla) @14:36-14:69@FiniteSets.tla) @14:23-14:69@FiniteSets.tla)
        @14:3-14:69@FiniteSets.tla) @9:1-14:69@FiniteSets.tla) @9:1-14:69@FiniteSets.tla) User Hidden false
        @9:1-14:69@FiniteSets.tla) (Definition (Operator "Cardinality" (Lambda (("S" 0
        @16:13-16:14@FiniteSets.tla)) (Let ((Operator "CS" (Fcn (("T" Constant (Domain (Apply (Internal
        SUBSET) ((Opaque "S" @20:23-20:24@FiniteSets.tla)) @20:16-20:24@FiniteSets.tla)))) (If (Apply
        (Internal Eq) ((Opaque "T" @20:32-20:33@FiniteSets.tla) (SetEnum () @20:36-20:38@FiniteSets.tla))
        @20:32-20:38@FiniteSets.tla) (Num "0" "" @20:44-20:45@FiniteSets.tla) (Apply (Opaque "+") ((Num "1"
        "" @21:44-21:45@FiniteSets.tla) (FcnApp (Opaque "CS" @21:48-21:50@FiniteSets.tla) ((Apply (Internal
        Setminus) ((Opaque "T" @21:51-21:52@FiniteSets.tla) (SetEnum ((Choose "x" _ (Apply (Internal Mem)
        ((Opaque "x" @21:67-21:68@FiniteSets.tla) (Opaque "T" @21:73-21:74@FiniteSets.tla))
        @21:67-21:74@FiniteSets.tla) @21:56-21:74@FiniteSets.tla)) @21:55-21:75@FiniteSets.tla))
        @21:51-21:75@FiniteSets.tla)) @21:48-21:76@FiniteSets.tla)) @21:44-21:76@FiniteSets.tla)
        @20:29-21:76@FiniteSets.tla) @20:7-21:76@FiniteSets.tla) @20:7-21:76@FiniteSets.tla)) (FcnApp
        (Opaque "CS" @22:7-22:9@FiniteSets.tla) ((Opaque "S" @22:10-22:11@FiniteSets.tla))
        @22:7-22:12@FiniteSets.tla) @20:3-22:12@FiniteSets.tla) @16:1-22:12@FiniteSets.tla)
        @16:1-22:12@FiniteSets.tla) User Hidden false @16:1-22:12@FiniteSets.tla))) (std "Integers") (std
        "Reals") (std "TLC") (mule "parameterized_instantiation_aux" false false _ ((Variables ("y")
        @2:10-2:11@parameterized_instantiation_aux.tla) (Definition (Operator "Foo" (Tuple ((Opaque "y"
        @3:10-3:11@parameterized_instantiation_aux.tla) (Opaque "y"
        @3:13-3:14@parameterized_instantiation_aux.tla)) @3:14-3:16@parameterized_instantiation_aux.tla)
        @3:1-3:16@parameterized_instantiation_aux.tla) User Hidden false
        @3:1-3:16@parameterized_instantiation_aux.tla))) (mule "parameterized_instantiation_test" true false
        _ ((Definition (Operator "Nat" (Internal Nat) _) Builtin Visible false _) (Definition (Operator "+"
        (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Plus) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Definition (Operator "-" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Minus) ((Ix 2) (Ix 1))))
        _) Builtin Visible false _) (Definition (Operator "*" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply
        (Internal Times) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "^" (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Exp) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Definition (Operator "<" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Lt) ((Ix 2) (Ix 1)))) _)
        Builtin Visible false _) (Definition (Operator ">" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal
        Gt) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "=<" (Lambda (("x1" 0 _)
        ("x2" 0 _)) (Apply (Internal Lteq) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition
        (Operator ">=" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Gteq) ((Ix 2) (Ix 1)))) _) Builtin
        Visible false _) (Definition (Operator "%" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal
        Remainder) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "\\div" (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Quotient) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Definition (Operator ".." (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Range) ((Ix 2) (Ix 1))))
        _) Builtin Visible false _) (Definition (Operator "Int" (Internal Int) _) Builtin Visible false _)
        (Definition (Operator "-." (Lambda (("x1" 0 _)) (Apply (Internal Uminus) ((Ix 1)))) _) Builtin
        Visible false _) (Anoninst (instance () "Naturals" () @2:7-2:24@FiniteSets.tla) true
        @2:1-2:24@FiniteSets.tla) (Anoninst (instance () "Sequences" () @3:7-3:25@FiniteSets.tla) true
        @3:1-3:25@FiniteSets.tla) (Definition (Operator "IsFiniteSet" (Lambda (("S" 0
        @9:13-9:14@FiniteSets.tla)) (Quant Exists (("seq" Constant (Domain (Apply (Opaque "Seq"
        @14:14-14:20@FiniteSets.tla) ((Opaque "S" @14:18-14:19@FiniteSets.tla))
        @14:14-14:20@FiniteSets.tla)))) (Quant Forall (("s" Constant (Domain (Opaque "S"
        @14:32-14:33@FiniteSets.tla)))) (Quant Exists (("n" Constant (Domain (Apply (Opaque "..") ((Num "1"
        "" @14:45-14:46@FiniteSets.tla) (Apply (Opaque "Len" @14:48-14:56@FiniteSets.tla) ((Opaque "seq"
        @14:52-14:55@FiniteSets.tla)) @14:48-14:56@FiniteSets.tla)) @14:45-14:56@FiniteSets.tla)))) (Apply
        (Internal Eq) ((FcnApp (Opaque "seq" @14:59-14:62@FiniteSets.tla) ((Opaque "n"
        @14:63-14:64@FiniteSets.tla)) @14:59-14:65@FiniteSets.tla) (Opaque "s" @14:68-14:69@FiniteSets.tla))
        @14:59-14:69@FiniteSets.tla) @14:36-14:69@FiniteSets.tla) @14:23-14:69@FiniteSets.tla)
        @14:3-14:69@FiniteSets.tla) @9:1-14:69@FiniteSets.tla) @9:1-14:69@FiniteSets.tla) User Hidden false
        @9:1-14:69@FiniteSets.tla) (Definition (Operator "Cardinality" (Lambda (("S" 0
        @16:13-16:14@FiniteSets.tla)) (Let ((Operator "CS" (Fcn (("T" Constant (Domain (Apply (Internal
        SUBSET) ((Opaque "S" @20:23-20:24@FiniteSets.tla)) @20:16-20:24@FiniteSets.tla)))) (If (Apply
        (Internal Eq) ((Opaque "T" @20:32-20:33@FiniteSets.tla) (SetEnum () @20:36-20:38@FiniteSets.tla))
        @20:32-20:38@FiniteSets.tla) (Num "0" "" @20:44-20:45@FiniteSets.tla) (Apply (Opaque "+") ((Num "1"
        "" @21:44-21:45@FiniteSets.tla) (FcnApp (Opaque "CS" @21:48-21:50@FiniteSets.tla) ((Apply (Internal
        Setminus) ((Opaque "T" @21:51-21:52@FiniteSets.tla) (SetEnum ((Choose "x" _ (Apply (Internal Mem)
        ((Opaque "x" @21:67-21:68@FiniteSets.tla) (Opaque "T" @21:73-21:74@FiniteSets.tla))
        @21:67-21:74@FiniteSets.tla) @21:56-21:74@FiniteSets.tla)) @21:55-21:75@FiniteSets.tla))
        @21:51-21:75@FiniteSets.tla)) @21:48-21:76@FiniteSets.tla)) @21:44-21:76@FiniteSets.tla)
        @20:29-21:76@FiniteSets.tla) @20:7-21:76@FiniteSets.tla) @20:7-21:76@FiniteSets.tla)) (FcnApp
        (Opaque "CS" @22:7-22:9@FiniteSets.tla) ((Opaque "S" @22:10-22:11@FiniteSets.tla))
        @22:7-22:12@FiniteSets.tla) @20:3-22:12@FiniteSets.tla) @16:1-22:12@FiniteSets.tla)
        @16:1-22:12@FiniteSets.tla) User Hidden false @16:1-22:12@FiniteSets.tla) (Variables ("x" "z")
        @4:10-4:11) (Definition (Instance "F" (instance ("y") "parameterized_instantiation_aux" ()
        @5:2-5:49) @5:1-5:49) User Hidden false @5:9-5:49) (Theorem _ (sequent () (Apply (Internal Implies)
        ((Apply (Internal Eq) ((Opaque "x" @7:10-7:11) (Opaque "z" @7:14-7:15)) @7:10-7:15) (Apply (Internal
        Eq) ((Bang (Apply (Opaque "F" @7:21-7:29) ((Opaque "x" @7:23-7:24)) @7:21-7:29) ((Label "Foo" ()))
        @7:21-7:29) (Bang (Apply (Opaque "F" @7:32-7:40) ((Opaque "z" @7:34-7:35)) @7:32-7:40) ((Label "Foo"
        ())) @7:32-7:40)) @7:21-7:40)) @7:10-7:40)) 0 (By (usable () ((Dvar "F!Foo" @8:8-8:13))) false
        (props @8:1-8:3 (Unnamed 0 0) _ _)) @7:1-8:13)))) ((ok 4689 "0x4a8bee87ae87cb97" 0 0 0
        "0xcbf29ce484222325") (ok 426 "0x395a8a251544686e" 0 0 0 "0xcbf29ce484222325") (ok 7304
        "0x8349f223d1f00c8a" 2 0 0 "0xcbf29ce484222325")))
    "#;

    const COOPER_INSTANTIATION: &str = r#"
        (fixture "cooper_instantiation_test.tla" 0 ((std "Integers") (std "Naturals") (std "Reals") (std
        "Sequences") (std "TLC") (mule "cooper_instantiation_test" true false _ ((Definition (Operator "Nat"
        (Internal Nat) _) Builtin Visible false _) (Definition (Operator "+" (Lambda (("x1" 0 _) ("x2" 0 _))
        (Apply (Internal Plus) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "-"
        (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Minus) ((Ix 2) (Ix 1)))) _) Builtin Visible false
        _) (Definition (Operator "*" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Times) ((Ix 2) (Ix
        1)))) _) Builtin Visible false _) (Definition (Operator "^" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply
        (Internal Exp) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator "<" (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Lt) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Definition (Operator ">" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Gt) ((Ix 2) (Ix 1)))) _)
        Builtin Visible false _) (Definition (Operator "=<" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal
        Lteq) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator ">=" (Lambda (("x1" 0 _)
        ("x2" 0 _)) (Apply (Internal Gteq) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition
        (Operator "%" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Remainder) ((Ix 2) (Ix 1)))) _)
        Builtin Visible false _) (Definition (Operator "\\div" (Lambda (("x1" 0 _) ("x2" 0 _)) (Apply
        (Internal Quotient) ((Ix 2) (Ix 1)))) _) Builtin Visible false _) (Definition (Operator ".." (Lambda
        (("x1" 0 _) ("x2" 0 _)) (Apply (Internal Range) ((Ix 2) (Ix 1)))) _) Builtin Visible false _)
        (Definition (Operator "Int" (Internal Int) _) Builtin Visible false _) (Definition (Operator "-."
        (Lambda (("x1" 0 _)) (Apply (Internal Uminus) ((Ix 1)))) _) Builtin Visible false _) (Theorem
        "SimpleArithmetic" (sequent () (With (Internal TRUE @4:29-4:33) (method "cooper" _ _) @4:29-4:33)) 0
        (Omitted Implicit (props @4:53-4:53 _ _ _)) @4:1-4:33) (Theorem _ (sequent ((Fresh "XXX" 0 Constant
        _ Visible @6:16-6:32) (Fresh "i" 0 Constant (Opaque "Int" @7:28-7:31) Visible @7:9-7:31)) (Apply
        (Internal Mem) ((Opaque "XXX" @8:16-8:19) (Opaque "Int" @8:26-8:29)) @8:16-8:29)) 0 (By (usable
        ((Opaque "SimpleArithmetic" @9:4-9:20)) ()) false (props @9:1-9:3 (Unnamed 0 0) _ _)) @6:1-9:20))))
        ((ok 2340 "0x4af71febff659d4a" 2 0 0 "0xcbf29ce484222325")))
    "#;

    const BACKEND_PRAGMAS: &str = r#"
        (fixture "instantiate_backend_pragmas.tla" 0 ((mule "BackendPragmas" true false _ ((Definition
        (Bpragma "SMT" (Internal TRUE @8:8-8:12) ((("prover" (String "smt3")))) @8:1-8:12) User Hidden false
        @8:1-8:12))) (std "Integers") (std "Naturals") (std "Reals") (std "Sequences") (std "TLC") (mule
        "instantiate_backend_pragmas" true false _ ((Submod (mule "BackendPragmas" true false _ ((Definition
        (Bpragma "SMT" (Internal TRUE @8:8-8:12) ((("prover" (String "smt3")))) @8:1-8:12) User Hidden false
        @8:1-8:12))) _) (Definition (Instance "M" (instance () "BackendPragmas" () @11:3-11:29) @11:1-11:29)
        User Hidden false @11:6-11:29) (Theorem _ (sequent () (Internal TRUE @14:9-14:13)) 0 (By (usable
        ((Bang (Opaque "M" @15:4-15:9) ((Label "SMT" ())) @15:4-15:9)) ()) false (props @15:1-15:3 (Unnamed
        0 0) _ _)) @14:1-15:9)))) ((ok 162 "0xa48e033c3cc13c59" 0 0 0 "0xcbf29ce484222325") (ok 659
        "0x33dd169f6c80d85d" 2 0 0 "0xcbf29ce484222325")))
    "#;
}
