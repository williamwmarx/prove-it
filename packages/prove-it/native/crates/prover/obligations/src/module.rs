//! tlapm's module units, with the standard modules, flattening EXTENDS (Module.Flatten), the
//! modules a module depends on (Module.Dep), and substitution in units (Module.Subst).
//! A port of `src/obligations/module.ts`.

use std::cmp::Ordering;
use std::collections::HashSet;
use std::rc::Rc;

use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, BoundDomain, Builtin, Defn, DefnCore, ExceptPoint, Expr, ExprCore, ExprProps, Hyp,
    HypCore, HypNode, InstanceDefinition, Level, Locus, Param, Selector, Sequent, Shape, Time,
    Visibility, WhereDefined, at_expr, expr, exprify_sequent, get_fact, get_fresh, located,
    map_accumulate, to_index,
};
use crate::proof::{Omission, Proof, ProofCore, ProofProps, Usable, UseDef, UseDefCore};
use crate::substitution::{
    Substitution, bump_by, shift, shift_expr, substitute_defn, substitute_expr, substitute_exprs,
    substitute_sequent,
};

#[derive(Clone, Debug)]
pub struct ModuleUnit {
    pub core: ModuleUnitCore,
    pub location: Option<Locus>,
}

#[derive(Clone, Debug)]
pub struct Declaration {
    pub name: String,
    pub shape: Shape,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MutateMode {
    Use,
    Hide,
}

#[derive(Clone, Debug)]
pub enum ModuleUnitCore {
    Constants {
        declarations: Vec<Declaration>,
    },
    Recursives {
        declarations: Vec<Declaration>,
    },
    Variables {
        names: Vec<String>,
    },
    Definition {
        definition: Defn,
        where_defined: WhereDefined,
        visibility: Visibility,
        is_local: bool,
    },
    Axiom {
        name: Option<String>,
        expression: Expr,
    },
    Theorem {
        name: Option<String>,
        sequent: Sequent,
        axiom_count: usize,
        proof: Proof,
    },
    Submod {
        module: Box<Mule>,
    },
    Mutate {
        mode: MutateMode,
        usable: Usable,
    },
    Anoninst {
        instance: InstanceDefinition,
        is_local: bool,
    },
}

impl ModuleUnit {
    /// The same location on another core: `{...unit, ...changes}` in the TypeScript.
    fn with_core(&self, core: ModuleUnitCore) -> Self {
        Self {
            core,
            location: self.location.clone(),
        }
    }
}

/// `depth` is the size of the context the module was normalized in, which instantiation shifts
/// its body by.
#[derive(Clone, Debug, Default)]
pub struct Mule {
    pub name: String,
    pub extendees: Vec<String>,
    pub extendee_locations: Option<Vec<Locus>>,
    pub body: Vec<ModuleUnit>,
    pub is_important: bool,
    pub is_standard: bool,
    pub depth: Option<usize>,
    pub location: Option<Locus>,
}

fn define_builtin(arity: usize, name: &str, builtin: Builtin) -> ModuleUnit {
    let body = if arity == 0 {
        expr(ExprCore::Internal { builtin })
    } else {
        expr(ExprCore::Lambda {
            params: (0..arity)
                .map(|index| Param {
                    name: format!("x{}", index + 1),
                    shape: 0,
                    location: None,
                })
                .collect(),
            body: expr(ExprCore::Apply {
                operator: expr(ExprCore::Internal { builtin }),
                args: (0..arity)
                    .map(|index| {
                        expr(ExprCore::Ix {
                            index: to_index(arity - index),
                        })
                    })
                    .collect(),
            }),
        })
    };
    ModuleUnit {
        core: ModuleUnitCore::Definition {
            definition: Defn {
                core: DefnCore::Operator {
                    name: name.to_owned(),
                    body,
                },
                location: None,
            },
            where_defined: WhereDefined::Builtin,
            visibility: Visibility::Visible,
            is_local: false,
        },
        location: None,
    }
}

fn get_naturals() -> Vec<ModuleUnit> {
    vec![
        define_builtin(0, "Nat", Builtin::Nat),
        define_builtin(2, "+", Builtin::Plus),
        define_builtin(2, "-", Builtin::Minus),
        define_builtin(2, "*", Builtin::Times),
        define_builtin(2, "^", Builtin::Exp),
        define_builtin(2, "<", Builtin::Lt),
        define_builtin(2, ">", Builtin::Gt),
        define_builtin(2, "=<", Builtin::Lteq),
        define_builtin(2, ">=", Builtin::Gteq),
        define_builtin(2, "%", Builtin::Remainder),
        define_builtin(2, "\\div", Builtin::Quotient),
        define_builtin(2, "..", Builtin::Range),
    ]
}

fn get_integers() -> Vec<ModuleUnit> {
    let mut units = get_naturals();
    units.push(define_builtin(0, "Int", Builtin::Int));
    units.push(define_builtin(1, "-.", Builtin::Uminus));
    units
}

fn get_reals() -> Vec<ModuleUnit> {
    let mut units = get_integers();
    units.push(define_builtin(0, "Real", Builtin::Real));
    units.push(define_builtin(2, "/", Builtin::Ratio));
    units.push(define_builtin(0, "Infinity", Builtin::Infinity));
    units
}

fn get_sequences() -> Vec<ModuleUnit> {
    vec![
        define_builtin(1, "Seq", Builtin::Seq),
        define_builtin(1, "Len", Builtin::Len),
        define_builtin(2, "BSeq", Builtin::BSeq),
        define_builtin(2, "\\o", Builtin::Cat),
        define_builtin(2, "Append", Builtin::Append),
        define_builtin(1, "Head", Builtin::Head),
        define_builtin(1, "Tail", Builtin::Tail),
        define_builtin(3, "SubSeq", Builtin::SubSeq),
        define_builtin(2, "SelectSeq", Builtin::SelectSeq),
    ]
}

fn get_tlc() -> Vec<ModuleUnit> {
    vec![
        define_builtin(2, "Print", Builtin::Print),
        define_builtin(1, "PrintT", Builtin::PrintT),
        define_builtin(2, "Assert", Builtin::Assert),
        define_builtin(0, "JavaTime", Builtin::JavaTime),
        define_builtin(1, "TLCGet", Builtin::TLCGet),
        define_builtin(2, "TLCSet", Builtin::TLCSet),
        define_builtin(2, ":>", Builtin::OneArg),
        define_builtin(2, "@@", Builtin::Extend),
        define_builtin(1, "Permutations", Builtin::Permutations),
        define_builtin(2, "SortSeq", Builtin::SortSeq),
        define_builtin(1, "RandomElement", Builtin::RandomElement),
        define_builtin(0, "Any", Builtin::Any),
        define_builtin(1, "ToString", Builtin::ToString),
    ]
}

fn get_standard_module(name: &str, body: Vec<ModuleUnit>) -> Mule {
    Mule {
        name: name.to_owned(),
        body,
        is_standard: true,
        ..Mule::default()
    }
}

/// `STANDARD_MODULES`, in its order: Module.Standard.initctx, apart from $TLAPM, whose
/// Builtins! names no module of the corpora uses.
pub fn get_standard_modules() -> Vec<Mule> {
    vec![
        get_standard_module("Naturals", get_naturals()),
        get_standard_module("Integers", get_integers()),
        get_standard_module("Reals", get_reals()),
        get_standard_module("Sequences", get_sequences()),
        get_standard_module("TLC", get_tlc()),
    ]
}

fn locate_hyp(core: HypCore, location: &Option<Locus>) -> Hyp {
    Rc::new(HypNode {
        core,
        location: location.clone(),
    })
}

pub fn get_unit_hyps(unit: &ModuleUnit) -> Result<Vec<Hyp>> {
    let location = &unit.location;
    Ok(match &unit.core {
        ModuleUnitCore::Constants { declarations } => declarations
            .iter()
            .map(|declaration| {
                let fresh = get_fresh(&declaration.name, Level::Constant, declaration.shape);
                locate_hyp(fresh.core.clone(), location)
            })
            .collect(),
        ModuleUnitCore::Recursives { declarations } => declarations
            .iter()
            .map(|declaration| {
                locate_hyp(
                    HypCore::Defn {
                        definition: Defn {
                            core: DefnCore::Recursive {
                                name: declaration.name.clone(),
                                shape: declaration.shape,
                            },
                            location: location.clone(),
                        },
                        where_defined: WhereDefined::User,
                        visibility: Visibility::Hidden,
                        is_local: false,
                        is_constness_unset: false,
                    },
                    location,
                )
            })
            .collect(),
        ModuleUnitCore::Variables { names } => names
            .iter()
            .map(|name| locate_hyp(HypCore::Flex { name: name.clone() }, location))
            .collect(),
        ModuleUnitCore::Definition {
            definition,
            where_defined,
            visibility,
            is_local,
        } => vec![locate_hyp(
            HypCore::Defn {
                definition: definition.clone(),
                where_defined: *where_defined,
                visibility: *visibility,
                is_local: *is_local,
                is_constness_unset: false,
            },
            location,
        )],
        ModuleUnitCore::Axiom { name, expression } => {
            get_fact_hyps(name.as_deref(), expression.clone(), location)
        }
        ModuleUnitCore::Theorem {
            name,
            sequent,
            axiom_count,
            ..
        } => {
            let shifted = substitute_sequent(
                &shift(
                    -isize::try_from(*axiom_count)
                        .map_err(|_| ObligationError::assert_failure())?,
                ),
                &Sequent {
                    context: sequent.context.get(*axiom_count..).unwrap_or(&[]).to_vec(),
                    active: sequent.active.clone(),
                },
            )?;
            get_fact_hyps(
                name.as_deref(),
                at_expr(
                    &exprify_sequent(&shifted),
                    &ExprProps {
                        location: location.clone(),
                        is_atomic: false,
                    },
                ),
                location,
            )
        }
        ModuleUnitCore::Mutate { mode, usable } => match mode {
            MutateMode::Use => usable
                .facts
                .iter()
                .enumerate()
                .map(|(index, fact)| {
                    let amount =
                        isize::try_from(index).map_err(|_| ObligationError::assert_failure())?;
                    Ok(get_fact(
                        shift_expr(amount, fact)?,
                        Visibility::Visible,
                        Time::Always,
                        location.clone(),
                    ))
                })
                .collect::<Result<_>>()?,
            MutateMode::Hide => Vec::new(),
        },
        ModuleUnitCore::Submod { .. } | ModuleUnitCore::Anoninst { .. } => Vec::new(),
    })
}

fn get_fact_hyps(name: Option<&str>, expression: Expr, location: &Option<Locus>) -> Vec<Hyp> {
    match name {
        None => vec![get_fact(
            expression,
            Visibility::Hidden,
            Time::Always,
            location.clone(),
        )],
        Some(name) => get_named_fact(name, expression, location),
    }
}

pub fn get_hyp_size(unit: &ModuleUnit) -> Result<usize> {
    match &unit.core {
        ModuleUnitCore::Axiom { name, .. } | ModuleUnitCore::Theorem { name, .. } => {
            Ok(if name.is_none() { 1 } else { 2 })
        }
        _ => Ok(get_unit_hyps(unit)?.len()),
    }
}

fn get_named_fact(name: &str, expression: Expr, location: &Option<Locus>) -> Vec<Hyp> {
    vec![
        locate_hyp(
            HypCore::Defn {
                definition: Defn {
                    core: DefnCore::Operator {
                        name: name.to_owned(),
                        body: expression,
                    },
                    location: location.clone(),
                },
                where_defined: WhereDefined::User,
                visibility: Visibility::Visible,
                is_local: false,
                is_constness_unset: false,
            },
            location,
        ),
        get_fact(
            located(ExprCore::Ix { index: 1 }, location.clone()),
            Visibility::Hidden,
            Time::Always,
            location.clone(),
        ),
    ]
}

/// Module.Flatten.exports: what an extending module sees, with local definitions inlined like
/// builtins and proofs omitted.
fn get_exports(module: &Mule) -> Vec<ModuleUnit> {
    module
        .body
        .iter()
        .filter_map(|unit| match &unit.core {
            ModuleUnitCore::Definition {
                definition,
                where_defined,
                visibility,
                is_local,
            } => Some(unit.with_core(ModuleUnitCore::Definition {
                definition: definition.clone(),
                where_defined: if *is_local {
                    WhereDefined::Builtin
                } else {
                    *where_defined
                },
                visibility: *visibility,
                is_local: *is_local,
            })),
            ModuleUnitCore::Mutate { .. } => None,
            ModuleUnitCore::Theorem {
                name,
                sequent,
                axiom_count,
                ..
            } => Some(unit.with_core(ModuleUnitCore::Theorem {
                name: name.clone(),
                sequent: sequent.clone(),
                axiom_count: *axiom_count,
                proof: Proof {
                    core: ProofCore::Omitted(Omission::Elsewhere),
                    props: ProofProps {
                        location: unit.location.clone(),
                        ..ProofProps::default()
                    },
                },
            })),
            ModuleUnitCore::Submod { module } => Some(unit.with_core(ModuleUnitCore::Submod {
                module: Box::new(Mule {
                    body: get_exports(module),
                    ..(**module).clone()
                }),
            })),
            _ => Some(unit.clone()),
        })
        .collect()
}

/// `flatten`, with `modules` the lookup of the TypeScript's map and `extending` the module names
/// being extended, `{module.name}` at the top. tlapm recurses on a module that extends itself
/// until the stack overflows.
pub fn flatten<'a>(
    modules: &dyn Fn(&str) -> Option<&'a Mule>,
    module: &Mule,
    seen: &mut HashSet<String>,
    extending: Option<&HashSet<String>>,
) -> Result<Mule> {
    let extending = extending
        .cloned()
        .unwrap_or_else(|| HashSet::from([module.name.clone()]));
    let mut extension = Vec::new();
    for name in &module.extendees {
        if seen.contains(name) {
            continue;
        }
        if extending.contains(name) {
            return Err(ObligationError::bug("Stack overflow"));
        }
        let extended = modules(name)
            .ok_or_else(|| ObligationError::proof(format!("Module \"{name}\" unknown")))?;
        let mut inner = extending.clone();
        inner.insert(name.clone());
        extension.extend(get_exports(&flatten(
            modules,
            extended,
            seen,
            Some(&inner),
        )?));
        seen.insert(name.clone());
    }
    let body = extension
        .iter()
        .chain(&module.body)
        .map(|unit| match &unit.core {
            ModuleUnitCore::Submod { module: submodule } => {
                Ok(unit.with_core(ModuleUnitCore::Submod {
                    module: Box::new(flatten(modules, submodule, &mut HashSet::new(), None)?),
                }))
            }
            _ => Ok(unit.clone()),
        })
        .collect::<Result<_>>()?;
    Ok(Mule {
        body,
        ..module.clone()
    })
}

/// What `getDependencies` gives. `locations` and `submodules` are the TypeScript's maps, in
/// insertion order.
#[derive(Clone, Debug)]
pub struct Dependencies {
    pub dependencies: Vec<String>,
    pub locations: Vec<(String, Option<Locus>)>,
    pub submodules: Vec<(String, Mule)>,
}

/// Module.Dep.external_deps: the modules a module extends or instantiates, including those of its
/// submodules.
pub fn get_dependencies(module: &Mule) -> Dependencies {
    let mut dependencies = Vec::new();
    let mut locals = Vec::new();
    let mut submodules: Vec<(String, Mule)> = Vec::new();
    // Leaves out the proofs of theorems.
    fn visit(
        unit: &ModuleUnit,
        dependencies: &mut Vec<(String, Option<Locus>)>,
        locals: &mut Vec<String>,
        submodules: &mut Vec<(String, Mule)>,
    ) {
        let ModuleUnitCore::Submod { module } = &unit.core else {
            add_unit_instances(dependencies, unit);
            return;
        };
        if !locals.contains(&module.name) {
            locals.push(module.name.clone());
        }
        match submodules.iter_mut().find(|entry| entry.0 == module.name) {
            Some(entry) => entry.1 = (**module).clone(),
            None => submodules.push((module.name.clone(), (**module).clone())),
        }
        add_extendees(dependencies, module);
        for inner in &module.body {
            visit(inner, dependencies, locals, submodules);
        }
    }
    for unit in &module.body {
        visit(unit, &mut dependencies, &mut locals, &mut submodules);
    }
    dependencies.retain(|entry| !locals.contains(&entry.0));
    add_extendees(&mut dependencies, module);
    let mut names: Vec<String> = dependencies.iter().map(|entry| entry.0.clone()).collect();
    names.sort_by(|left, right| compare_names(left, right));
    Dependencies {
        dependencies: names,
        locations: dependencies,
        submodules,
    }
}

fn add_dependency(
    dependencies: &mut Vec<(String, Option<Locus>)>,
    name: &str,
    location: Option<Locus>,
) {
    if !dependencies.iter().any(|entry| entry.0 == name) {
        dependencies.push((name.to_owned(), location));
    }
}

fn add_extendees(dependencies: &mut Vec<(String, Option<Locus>)>, extending: &Mule) {
    for (index, name) in extending.extendees.iter().enumerate() {
        let location = extending
            .extendee_locations
            .as_ref()
            .and_then(|locations| locations.get(index))
            .cloned();
        add_dependency(dependencies, name, location);
    }
}

// Every INSTANCE definition inside a value, such as one in a LET. The TypeScript walks the
// object's values reflectively; this visits the fields that can hold one in the order the
// TypeScript types declare them.

fn add_unit_instances(dependencies: &mut Vec<(String, Option<Locus>)>, unit: &ModuleUnit) {
    match &unit.core {
        ModuleUnitCore::Definition { definition, .. } => {
            add_defn_instances(dependencies, definition);
        }
        ModuleUnitCore::Axiom { expression, .. } => add_expr_instances(dependencies, expression),
        ModuleUnitCore::Theorem { sequent, .. } => add_sequent_instances(dependencies, sequent),
        ModuleUnitCore::Mutate { usable, .. } => {
            add_exprs_instances(dependencies, &usable.facts);
        }
        ModuleUnitCore::Anoninst { instance, .. } => {
            add_instance_definition(dependencies, instance);
        }
        ModuleUnitCore::Constants { .. }
        | ModuleUnitCore::Recursives { .. }
        | ModuleUnitCore::Variables { .. }
        | ModuleUnitCore::Submod { .. } => {}
    }
}

fn add_instance_definition(
    dependencies: &mut Vec<(String, Option<Locus>)>,
    instance: &InstanceDefinition,
) {
    add_dependency(dependencies, &instance.module, instance.location.clone());
    for entry in &instance.substitutions {
        add_expr_instances(dependencies, &entry.expression);
    }
}

fn add_defn_instances(dependencies: &mut Vec<(String, Option<Locus>)>, definition: &Defn) {
    match &definition.core {
        DefnCore::Recursive { .. } => {}
        DefnCore::Operator { body, .. } | DefnCore::Bpragma { body, .. } => {
            add_expr_instances(dependencies, body);
        }
        DefnCore::Instance { instance, .. } => add_instance_definition(dependencies, instance),
    }
}

fn add_sequent_instances(dependencies: &mut Vec<(String, Option<Locus>)>, sequent: &Sequent) {
    for hyp in &sequent.context {
        match &hyp.core {
            HypCore::Fresh {
                domain: Some(domain),
                ..
            } => add_expr_instances(dependencies, domain),
            HypCore::Fresh { .. } | HypCore::Flex { .. } => {}
            HypCore::Defn { definition, .. } => add_defn_instances(dependencies, definition),
            HypCore::Fact { expression, .. } => add_expr_instances(dependencies, expression),
        }
    }
    add_expr_instances(dependencies, &sequent.active);
}

fn add_exprs_instances(dependencies: &mut Vec<(String, Option<Locus>)>, expressions: &[Expr]) {
    for expression in expressions {
        add_expr_instances(dependencies, expression);
    }
}

fn add_bounds_instances(dependencies: &mut Vec<(String, Option<Locus>)>, bounds: &[Bound]) {
    for bound in bounds {
        if let BoundDomain::Domain(domain) = &bound.domain {
            add_expr_instances(dependencies, domain);
        }
    }
}

fn add_expr_instances(dependencies: &mut Vec<(String, Option<Locus>)>, expression: &Expr) {
    match &expression.core {
        ExprCore::Ix { .. }
        | ExprCore::Opaque { .. }
        | ExprCore::Internal { .. }
        | ExprCore::String { .. }
        | ExprCore::Num { .. }
        | ExprCore::At { .. } => {}
        ExprCore::Lambda { body, .. }
        | ExprCore::Tquant { body, .. }
        | ExprCore::With {
            expression: body, ..
        }
        | ExprCore::Dot {
            expression: body, ..
        }
        | ExprCore::Parens {
            expression: body, ..
        } => add_expr_instances(dependencies, body),
        ExprCore::Sequent { sequent } => add_sequent_instances(dependencies, sequent),
        ExprCore::Bang {
            expression: inner,
            selectors,
        } => {
            add_expr_instances(dependencies, inner);
            for selector in selectors {
                if let Selector::Instance(args) | Selector::Label { args, .. } = selector {
                    add_exprs_instances(dependencies, args);
                }
            }
        }
        ExprCore::Apply { operator, args } => {
            add_expr_instances(dependencies, operator);
            add_exprs_instances(dependencies, args);
        }
        ExprCore::If {
            condition,
            consequent,
            alternative,
        } => {
            add_expr_instances(dependencies, condition);
            add_expr_instances(dependencies, consequent);
            add_expr_instances(dependencies, alternative);
        }
        ExprCore::List {
            items: elements, ..
        }
        | ExprCore::SetEnum { elements }
        | ExprCore::Product { factors: elements }
        | ExprCore::Tuple { elements } => add_exprs_instances(dependencies, elements),
        ExprCore::Let { definitions, body } => {
            for definition in definitions {
                add_defn_instances(dependencies, definition);
            }
            add_expr_instances(dependencies, body);
        }
        ExprCore::Quant { bounds, body, .. } | ExprCore::Fcn { bounds, body } => {
            add_bounds_instances(dependencies, bounds);
            add_expr_instances(dependencies, body);
        }
        ExprCore::Choose { domain, body, .. } => {
            if let Some(domain) = domain {
                add_expr_instances(dependencies, domain);
            }
            add_expr_instances(dependencies, body);
        }
        ExprCore::SetSt { domain, body, .. } => {
            add_expr_instances(dependencies, domain);
            add_expr_instances(dependencies, body);
        }
        ExprCore::SetOf { element, bounds } => {
            add_expr_instances(dependencies, element);
            add_bounds_instances(dependencies, bounds);
        }
        ExprCore::FcnApp { function, args } => {
            add_expr_instances(dependencies, function);
            add_exprs_instances(dependencies, args);
        }
        ExprCore::Arrow { domain, range } => {
            add_expr_instances(dependencies, domain);
            add_expr_instances(dependencies, range);
        }
        ExprCore::Rect { fields } | ExprCore::Record { fields } => {
            for field in fields {
                add_expr_instances(dependencies, &field.value);
            }
        }
        ExprCore::Except { function, specs } => {
            add_expr_instances(dependencies, function);
            for spec in specs {
                for point in &spec.trail {
                    if let ExceptPoint::Apply(inner) = point {
                        add_expr_instances(dependencies, inner);
                    }
                }
                add_expr_instances(dependencies, &spec.value);
            }
        }
        ExprCore::Sub {
            action, subscript, ..
        }
        | ExprCore::Tsub {
            action, subscript, ..
        } => {
            add_expr_instances(dependencies, action);
            add_expr_instances(dependencies, subscript);
        }
        ExprCore::Fair {
            subscript, action, ..
        } => {
            add_expr_instances(dependencies, subscript);
            add_expr_instances(dependencies, action);
        }
        ExprCore::Case { arms, other } => {
            for arm in arms {
                add_expr_instances(dependencies, &arm.condition);
                add_expr_instances(dependencies, &arm.body);
            }
            if let Some(other) = other {
                add_expr_instances(dependencies, other);
            }
        }
    }
}

/// `compareNames`: JavaScript's string order, by UTF-16 code units.
pub fn compare_names(left: &str, right: &str) -> Ordering {
    left.encode_utf16().cmp(right.encode_utf16())
}

fn substitute_usable(substitution: &Substitution, usable: &Usable) -> Result<Usable> {
    Ok(Usable {
        facts: substitute_exprs(substitution, &usable.facts)?,
        defs: usable
            .defs
            .iter()
            .map(|def| match def.core {
                UseDefCore::Dvar { .. } => Ok(def.clone()),
                UseDefCore::Dx { index } => {
                    let substituted = substitute_expr(substitution, &expr(ExprCore::Ix { index }))?;
                    let ExprCore::Ix { index } = substituted.core else {
                        return Err(ObligationError::proof(
                            "substitution produced bad definition",
                        ));
                    };
                    Ok(UseDef {
                        core: UseDefCore::Dx { index },
                        location: def.location.clone(),
                    })
                }
            })
            .collect::<Result<_>>()?,
    })
}

/// Module.Subst.app_modunit. Instantiated theorems carry omitted proofs, which a substitution
/// leaves alone.
fn substitute_unit(
    substitution: &Substitution,
    unit: &ModuleUnit,
) -> Result<(Substitution, ModuleUnit)> {
    Ok(match &unit.core {
        ModuleUnitCore::Constants { declarations }
        | ModuleUnitCore::Recursives { declarations } => {
            (bump_by(declarations.len(), substitution), unit.clone())
        }
        ModuleUnitCore::Variables { names } => (bump_by(names.len(), substitution), unit.clone()),
        ModuleUnitCore::Definition {
            definition,
            where_defined,
            visibility,
            is_local,
        } => (
            bump_by(1, substitution),
            unit.with_core(ModuleUnitCore::Definition {
                definition: substitute_defn(substitution, definition)?,
                where_defined: *where_defined,
                visibility: *visibility,
                is_local: *is_local,
            }),
        ),
        ModuleUnitCore::Axiom { name, expression } => (
            bump_by(get_hyp_size(unit)?, substitution),
            unit.with_core(ModuleUnitCore::Axiom {
                name: name.clone(),
                expression: substitute_expr(substitution, expression)?,
            }),
        ),
        ModuleUnitCore::Theorem {
            name,
            sequent,
            axiom_count,
            proof,
        } => (
            bump_by(get_hyp_size(unit)?, substitution),
            unit.with_core(ModuleUnitCore::Theorem {
                name: name.clone(),
                sequent: substitute_sequent(substitution, sequent)?,
                axiom_count: *axiom_count,
                proof: proof.clone(),
            }),
        ),
        ModuleUnitCore::Submod { module } => (
            substitution.clone(),
            unit.with_core(ModuleUnitCore::Submod {
                module: Box::new(Mule {
                    body: substitute_units(substitution, &module.body)?,
                    ..(**module).clone()
                }),
            }),
        ),
        ModuleUnitCore::Mutate { mode, usable } => (
            match mode {
                MutateMode::Hide => substitution.clone(),
                MutateMode::Use => bump_by(usable.facts.len(), substitution),
            },
            unit.with_core(ModuleUnitCore::Mutate {
                mode: *mode,
                usable: substitute_usable(substitution, usable)?,
            }),
        ),
        ModuleUnitCore::Anoninst { instance, is_local } => (
            substitution.clone(),
            unit.with_core(ModuleUnitCore::Anoninst {
                instance: InstanceDefinition {
                    substitutions: instance
                        .substitutions
                        .iter()
                        .map(|entry| {
                            Ok(crate::expression::Substitution {
                                name: entry.name.clone(),
                                expression: substitute_expr(substitution, &entry.expression)?,
                            })
                        })
                        .collect::<Result<_>>()?,
                    ..instance.clone()
                },
                is_local: *is_local,
            }),
        ),
    })
}

pub fn substitute_units(
    substitution: &Substitution,
    units: &[ModuleUnit],
) -> Result<Vec<ModuleUnit>> {
    Ok(
        map_accumulate(substitution.clone(), units, |current, unit| {
            substitute_unit(&current, unit)
        })?
        .1,
    )
}

/// A named theorem binds its name as a proof definition, which its statement shifts past: the
/// hypotheses it binds and the shifted statement.
pub fn bind_theorem_name(
    name: Option<&str>,
    sequent: &Sequent,
    location: &Option<Locus>,
) -> Result<(Vec<Hyp>, Sequent)> {
    let Some(name) = name else {
        return Ok((Vec::new(), sequent.clone()));
    };
    Ok((
        vec![locate_hyp(
            HypCore::Defn {
                definition: Defn {
                    core: DefnCore::Operator {
                        name: name.to_owned(),
                        body: at_expr(
                            &exprify_sequent(sequent),
                            &ExprProps {
                                location: location.clone(),
                                is_atomic: false,
                            },
                        ),
                    },
                    location: location.clone(),
                },
                where_defined: WhereDefined::Proof(Time::Always),
                visibility: Visibility::Visible,
                is_local: false,
                is_constness_unset: false,
            },
            location,
        )],
        substitute_sequent(&shift(1), sequent)?,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::ExprNode;
    use crate::expression::{Substitution as Entry, hyp};
    use crate::substitution::cons_substitution;

    // The expected text is what `src/obligations/module.ts` gives under Bun for the same inputs,
    // printed by the same printer. `{NAT}` stands for the exported units of Naturals.

    fn locus_at(line: u32) -> Locus {
        Locus {
            file: Rc::from("f.tla"),
            start_line: line,
            start_column: 1,
            end_line: line,
            end_column: 2,
        }
    }

    fn locus(line: u32) -> Option<Locus> {
        Some(locus_at(line))
    }

    fn show_line(location: Option<&Locus>) -> String {
        location.map_or_else(String::new, |locus| format!("@{}", locus.start_line))
    }

    fn show_expr(expression: &Expr) -> String {
        let body = match &expression.core {
            ExprCore::Ix { index } => format!("#{index}"),
            ExprCore::Opaque { name } => name.clone(),
            ExprCore::Internal { builtin } => format!("${}", builtin.name()),
            ExprCore::Lambda { params, body } => format!(
                "(lambda {}. {})",
                params
                    .iter()
                    .map(|param| format!("{}/{}", param.name, param.shape))
                    .collect::<Vec<_>>()
                    .join(" "),
                show_expr(body)
            ),
            ExprCore::Apply { operator, args } => format!(
                "({})",
                std::iter::once(operator)
                    .chain(args)
                    .map(show_expr)
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            ExprCore::Sequent { sequent } => show_sequent(sequent),
            ExprCore::Let { definitions, body } => format!(
                "(let {} in {})",
                definitions
                    .iter()
                    .map(show_defn)
                    .collect::<Vec<_>>()
                    .join("; "),
                show_expr(body)
            ),
            _ => "?".to_owned(),
        };
        format!(
            "{body}{}{}",
            show_line(expression.location.as_ref()),
            if expression.is_atomic { "!" } else { "" }
        )
    }

    fn show_where(where_defined: WhereDefined) -> String {
        match where_defined {
            WhereDefined::Builtin => "Builtin".to_owned(),
            WhereDefined::User => "User".to_owned(),
            WhereDefined::Proof(time) => format!("Proof:{time:?}"),
        }
    }

    fn show_substitutions(instance: &InstanceDefinition) -> String {
        format!(
            "{}[{}]",
            instance.module,
            instance
                .substitutions
                .iter()
                .map(|entry| format!("{}<-{}", entry.name, show_expr(&entry.expression)))
                .collect::<Vec<_>>()
                .join(",")
        )
    }

    fn show_defn(definition: &Defn) -> String {
        let body = match &definition.core {
            DefnCore::Operator { name, body } => format!("{name}=={}", show_expr(body)),
            DefnCore::Recursive { name, shape } => format!("rec {name}/{shape}"),
            DefnCore::Instance { name, instance } => {
                format!("inst {name}={}", show_substitutions(instance))
            }
            DefnCore::Bpragma { .. } => "?".to_owned(),
        };
        format!("{body}{}", show_line(definition.location.as_ref()))
    }

    fn show_hyp(hyp: &Hyp) -> String {
        let body = match &hyp.core {
            HypCore::Fresh {
                name, shape, level, ..
            } => format!("fresh {name}/{shape}/{level:?}"),
            HypCore::Flex { name } => format!("flex {name}"),
            HypCore::Defn {
                definition,
                where_defined,
                visibility,
                is_local,
                ..
            } => format!(
                "defn({},{visibility:?},{is_local}) {}",
                show_where(*where_defined),
                show_defn(definition)
            ),
            HypCore::Fact {
                expression,
                visibility,
                time,
                ..
            } => format!("fact({visibility:?},{time:?}) {}", show_expr(expression)),
        };
        format!("{body}{}", show_line(hyp.location.as_ref()))
    }

    fn show_hyps(hyps: &[Hyp]) -> String {
        hyps.iter().map(show_hyp).collect::<Vec<_>>().join(", ")
    }

    fn show_sequent(sequent: &Sequent) -> String {
        format!(
            "[{} |- {}]",
            show_hyps(&sequent.context),
            show_expr(&sequent.active)
        )
    }

    fn show_declarations(declarations: &[Declaration]) -> String {
        declarations
            .iter()
            .map(|declaration| format!("{}/{}", declaration.name, declaration.shape))
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn show_unit(unit: &ModuleUnit) -> String {
        let body = match &unit.core {
            ModuleUnitCore::Constants { declarations } => {
                format!("Constants {}", show_declarations(declarations))
            }
            ModuleUnitCore::Recursives { declarations } => {
                format!("Recursives {}", show_declarations(declarations))
            }
            ModuleUnitCore::Variables { names } => format!("Variables {}", names.join(" ")),
            ModuleUnitCore::Definition {
                definition,
                where_defined,
                visibility,
                is_local,
            } => format!(
                "Definition({},{visibility:?},{is_local}) {}",
                show_where(*where_defined),
                show_defn(definition)
            ),
            ModuleUnitCore::Axiom { name, expression } => format!(
                "Axiom {} {}",
                name.as_deref().unwrap_or("_"),
                show_expr(expression)
            ),
            ModuleUnitCore::Theorem {
                name,
                sequent,
                axiom_count,
                proof,
            } => {
                let kind = match &proof.core {
                    ProofCore::Obvious => "Obvious".to_owned(),
                    ProofCore::Omitted(omission) => format!("Omitted:{omission:?}"),
                    _ => "?".to_owned(),
                };
                format!(
                    "Theorem {} {axiom_count} {} proof={kind}{}",
                    name.as_deref().unwrap_or("_"),
                    show_sequent(sequent),
                    show_line(proof.props.location.as_ref())
                )
            }
            ModuleUnitCore::Submod { module } => format!("Submod {}", show_mule(module)),
            ModuleUnitCore::Mutate { mode, usable } => format!(
                "Mutate {mode:?} {} defs {}",
                usable
                    .facts
                    .iter()
                    .map(show_expr)
                    .collect::<Vec<_>>()
                    .join(" "),
                usable
                    .defs
                    .iter()
                    .map(|def| {
                        let name = match &def.core {
                            UseDefCore::Dvar { name } => name.clone(),
                            UseDefCore::Dx { index } => format!("D{index}"),
                        };
                        format!("{name}{}", show_line(def.location.as_ref()))
                    })
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            ModuleUnitCore::Anoninst { instance, is_local } => {
                format!("Anoninst {is_local} {}", show_substitutions(instance))
            }
        };
        format!("{body}{}", show_line(unit.location.as_ref()))
    }

    fn show_mule(module: &Mule) -> String {
        format!(
            "{{{} ext={} std={} | {}}}",
            module.name,
            module.extendees.join(","),
            module.is_standard,
            module
                .body
                .iter()
                .map(show_unit)
                .collect::<Vec<_>>()
                .join("; ")
        )
    }

    fn show_result(result: Result<String>) -> String {
        result.unwrap_or_else(|error| match &error {
            ObligationError::Proof { exception, .. } => {
                format!("ERR {}: {} / {exception}", error.name(), error.message())
            }
            _ => format!("ERR {}: {} / ", error.name(), error.message()),
        })
    }

    fn ix(index: isize) -> Expr {
        expr(ExprCore::Ix { index })
    }

    fn ix_at(index: isize, line: u32) -> Expr {
        located(ExprCore::Ix { index }, locus(line))
    }

    fn atomic(expression: &Expr) -> Expr {
        Rc::new(ExprNode {
            is_atomic: true,
            ..(**expression).clone()
        })
    }

    fn opaque(name: &str) -> Expr {
        expr(ExprCore::Opaque {
            name: name.to_owned(),
        })
    }

    fn apply(operator: Expr, args: Vec<Expr>) -> Expr {
        expr(ExprCore::Apply { operator, args })
    }

    fn let_in(definitions: Vec<Defn>, body: Expr) -> Expr {
        expr(ExprCore::Let { definitions, body })
    }

    fn fact(expression: Expr) -> Hyp {
        get_fact(expression, Visibility::Visible, Time::Always, None)
    }

    fn operator_defn(name: &str, body: Expr) -> Defn {
        Defn {
            core: DefnCore::Operator {
                name: name.to_owned(),
                body,
            },
            location: None,
        }
    }

    fn instance(module: &str, line: u32, substitutions: Vec<Entry>) -> InstanceDefinition {
        InstanceDefinition {
            args: Vec::new(),
            module: module.to_owned(),
            substitutions,
            location: locus(line),
        }
    }

    fn instance_defn(name: &str, module: &str, line: u32, substitutions: Vec<Entry>) -> Defn {
        Defn {
            core: DefnCore::Instance {
                name: name.to_owned(),
                instance: instance(module, line, substitutions),
            },
            location: None,
        }
    }

    fn entry(name: &str, expression: Expr) -> Entry {
        Entry {
            name: name.to_owned(),
            expression,
        }
    }

    fn unit(core: ModuleUnitCore, location: Option<Locus>) -> ModuleUnit {
        ModuleUnit { core, location }
    }

    fn definition(definition: Defn) -> ModuleUnitCore {
        ModuleUnitCore::Definition {
            definition,
            where_defined: WhereDefined::User,
            visibility: Visibility::Visible,
            is_local: false,
        }
    }

    fn obvious() -> Proof {
        Proof {
            core: ProofCore::Obvious,
            props: ProofProps::default(),
        }
    }

    fn theorem(
        name: Option<&str>,
        context: Vec<Hyp>,
        active: Expr,
        axiom_count: usize,
    ) -> ModuleUnitCore {
        ModuleUnitCore::Theorem {
            name: name.map(str::to_owned),
            sequent: Sequent { context, active },
            axiom_count,
            proof: obvious(),
        }
    }

    fn declarations(entries: &[(&str, Shape)]) -> Vec<Declaration> {
        entries
            .iter()
            .map(|(name, shape)| Declaration {
                name: (*name).to_owned(),
                shape: *shape,
            })
            .collect()
    }

    fn names(entries: &[&str]) -> Vec<String> {
        entries.iter().map(|name| (*name).to_owned()).collect()
    }

    fn variables(entries: &[&str]) -> ModuleUnitCore {
        ModuleUnitCore::Variables {
            names: names(entries),
        }
    }

    fn mutate(mode: MutateMode, facts: Vec<Expr>, defs: Vec<UseDef>) -> ModuleUnitCore {
        ModuleUnitCore::Mutate {
            mode,
            usable: Usable { facts, defs },
        }
    }

    fn mule(name: &str, extendees: &[&str], body: Vec<ModuleUnitCore>) -> Mule {
        Mule {
            name: name.to_owned(),
            extendees: names(extendees),
            body: body.into_iter().map(|core| unit(core, None)).collect(),
            ..Mule::default()
        }
    }

    fn submod(module: Mule) -> ModuleUnitCore {
        ModuleUnitCore::Submod {
            module: Box::new(module),
        }
    }

    fn expected(label: &str) -> String {
        EXPECTED.iter().find(|entry| entry.0 == label).map_or_else(
            || format!("no expectation for {label}"),
            |entry| entry.1.replace("{NAT}", NATURALS),
        )
    }

    #[test]
    fn builds_the_standard_modules() {
        let modules = get_standard_modules();
        assert_eq!(
            modules
                .iter()
                .map(|module| module.name.as_str())
                .collect::<Vec<_>>(),
            ["Naturals", "Integers", "Reals", "Sequences", "TLC"]
        );
        let hyps = |name: &str| {
            let module = modules.iter().find(|module| module.name == name);
            show_result(module.map_or_else(
                || Ok(String::new()),
                |module| {
                    Ok(module
                        .body
                        .iter()
                        .map(|unit| Ok(show_hyps(&get_unit_hyps(unit)?)))
                        .collect::<Result<Vec<_>>>()?
                        .join(" ; "))
                },
            ))
        };
        assert_eq!(hyps("Reals"), expected("std Reals"));
        assert_eq!(hyps("TLC"), expected("std TLC"));
        assert_eq!(show_mule(&modules[3]), expected("std mule"));
    }

    #[test]
    fn gives_unit_hyps_and_sizes() {
        let units = [
            (
                "constants",
                unit(
                    ModuleUnitCore::Constants {
                        declarations: declarations(&[("N", 0), ("F", 2)]),
                    },
                    locus(3),
                ),
            ),
            (
                "recursives",
                unit(
                    ModuleUnitCore::Recursives {
                        declarations: declarations(&[("R", 1)]),
                    },
                    locus(4),
                ),
            ),
            ("variables", unit(variables(&["x", "y"]), None)),
            (
                "definition",
                unit(
                    ModuleUnitCore::Definition {
                        definition: operator_defn("Op", apply(opaque("f"), vec![ix(1)])),
                        where_defined: WhereDefined::Builtin,
                        visibility: Visibility::Hidden,
                        is_local: true,
                    },
                    locus(5),
                ),
            ),
            (
                "axiom unnamed",
                unit(
                    ModuleUnitCore::Axiom {
                        name: None,
                        expression: ix_at(2, 9),
                    },
                    locus(6),
                ),
            ),
            (
                "axiom named",
                unit(
                    ModuleUnitCore::Axiom {
                        name: Some("Ax".to_owned()),
                        expression: ix(2),
                    },
                    locus(7),
                ),
            ),
            (
                "theorem ctx",
                unit(
                    theorem(
                        Some("Thm"),
                        vec![fact(ix(1)), fact(ix(3)), fact(ix(5))],
                        apply(ix(1), vec![ix(4)]),
                        1,
                    ),
                    locus(8),
                ),
            ),
            (
                "theorem empty noloc",
                unit(theorem(None, Vec::new(), atomic(&ix_at(3, 12)), 0), None),
            ),
            (
                "theorem empty loc",
                unit(
                    theorem(None, vec![fact(ix(1))], atomic(&ix_at(3, 12)), 1),
                    locus(13),
                ),
            ),
            (
                "theorem big count",
                unit(theorem(Some("T"), vec![fact(ix(1))], ix(4), 3), None),
            ),
            (
                "mutate use",
                unit(
                    mutate(
                        MutateMode::Use,
                        vec![ix(1), apply(ix(2), vec![ix(3)])],
                        Vec::new(),
                    ),
                    locus(14),
                ),
            ),
            (
                "mutate hide",
                unit(mutate(MutateMode::Hide, vec![ix(1)], Vec::new()), None),
            ),
            ("submod", unit(submod(mule("Sub", &[], Vec::new())), None)),
            (
                "anoninst",
                unit(
                    ModuleUnitCore::Anoninst {
                        instance: InstanceDefinition {
                            args: Vec::new(),
                            module: "Naturals".to_owned(),
                            substitutions: Vec::new(),
                            location: None,
                        },
                        is_local: false,
                    },
                    None,
                ),
            ),
        ];
        for (label, unit) in &units {
            assert_eq!(
                show_result(get_unit_hyps(unit).map(|hyps| show_hyps(&hyps))),
                expected(&format!("hyps {label}")),
                "{label}"
            );
            assert_eq!(
                show_result(get_hyp_size(unit).map(|size| size.to_string())),
                expected(&format!("size {label}")),
                "{label}"
            );
        }
    }

    fn get_flatten_modules() -> Vec<Mule> {
        let mut modules = get_standard_modules();
        let body = vec![
            unit(variables(&["c"]), None),
            unit(
                ModuleUnitCore::Definition {
                    definition: operator_defn("L", opaque("l")),
                    where_defined: WhereDefined::User,
                    visibility: Visibility::Visible,
                    is_local: true,
                },
                locus(20),
            ),
            unit(mutate(MutateMode::Use, vec![ix(1)], Vec::new()), None),
            unit(theorem(Some("CT"), Vec::new(), ix(1), 0), locus(21)),
            unit(
                submod(mule(
                    "CS",
                    &[],
                    vec![
                        mutate(MutateMode::Hide, Vec::new(), Vec::new()),
                        definition(operator_defn("Q", opaque("q"))),
                    ],
                )),
                None,
            ),
        ];
        modules.push(Mule {
            body,
            ..mule("C", &["Naturals"], Vec::new())
        });
        modules.push(mule(
            "B",
            &["C", "Naturals"],
            vec![ModuleUnitCore::Constants {
                declarations: declarations(&[("b", 0)]),
            }],
        ));
        modules.push(mule("Self", &["Self"], Vec::new()));
        modules.push(mule("Loop1", &["Loop2"], Vec::new()));
        modules.push(mule("Loop2", &["Loop1"], Vec::new()));
        modules
    }

    #[test]
    fn flattens_extends() {
        let modules = get_flatten_modules();
        let lookup = |name: &str| modules.iter().find(|module| module.name == name);
        let top = mule(
            "A",
            &["B", "C", "Integers"],
            vec![
                variables(&["a"]),
                submod(mule("Inner", &["C"], vec![variables(&["i"])])),
            ],
        );
        let run = |label: &str, module: &Mule, seen: &[&str]| {
            let mut seen = seen.iter().map(|name| (*name).to_owned()).collect();
            assert_eq!(
                show_result(flatten(&lookup, module, &mut seen, None).map(|flat| show_mule(&flat))),
                expected(label),
                "{label}"
            );
        };
        run("flatten A", &top, &[]);
        run("flatten A seen", &top, &["C"]);
        if let Some(module) = lookup("Self") {
            run("flatten self", module, &[]);
        }
        if let Some(module) = lookup("Loop1") {
            run("flatten loop", module, &[]);
        }
        run(
            "flatten unknown",
            &mule("U", &["Naturals", "Nope"], Vec::new()),
            &[],
        );
        run(
            "flatten sub unknown",
            &mule("U", &[], vec![submod(mule("S", &["Gone"], Vec::new()))]),
            &[],
        );
        let mut seen = HashSet::new();
        assert!(flatten(&lookup, &top, &mut seen, None).is_ok());
        let mut grown: Vec<_> = seen.into_iter().collect();
        grown.sort();
        assert_eq!(grown.join(","), expected("flatten seen grows"));
    }

    fn show_dependencies(result: &Dependencies) -> String {
        format!(
            "deps={} locs={} subs={}/{}",
            result.dependencies.join(","),
            result
                .locations
                .iter()
                .map(|(name, location)| format!("{name}{}", show_line(location.as_ref())))
                .collect::<Vec<_>>()
                .join(","),
            result
                .submodules
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>()
                .join(","),
            result
                .submodules
                .iter()
                .map(|(_, module)| module.body.len().to_string())
                .collect::<Vec<_>>()
                .join(",")
        )
    }

    #[test]
    fn gives_dependencies() {
        let mut first_submodule = mule(
            "Sub1",
            &["Ext1", "Zeta"],
            vec![
                definition(instance_defn("S", "SubInst", 41, Vec::new())),
                submod(mule("Sub2", &["Sub1"], Vec::new())),
            ],
        );
        first_submodule.extendee_locations = Some(vec![locus_at(42)]);
        let mut module = mule(
            "D",
            &["Zeta", "Alpha", "Sub1"],
            vec![
                definition(operator_defn(
                    "X",
                    let_in(
                        vec![instance_defn(
                            "I",
                            "Let1",
                            30,
                            vec![entry(
                                "p",
                                let_in(vec![instance_defn("J", "Nested", 31, Vec::new())], ix(1)),
                            )],
                        )],
                        ix(1),
                    ),
                )),
                ModuleUnitCore::Anoninst {
                    instance: instance(
                        "Anon",
                        33,
                        vec![entry(
                            "q",
                            let_in(vec![instance_defn("K", "InSub", 32, Vec::new())], ix(1)),
                        )],
                    ),
                    is_local: false,
                },
                definition(instance_defn("N", "Named", 34, Vec::new())),
                definition(instance_defn("N2", "Alpha", 35, Vec::new())),
                ModuleUnitCore::Theorem {
                    name: Some("T".to_owned()),
                    sequent: Sequent {
                        context: vec![hyp(HypCore::Defn {
                            definition: instance_defn("H", "Hyp", 36, Vec::new()),
                            where_defined: WhereDefined::User,
                            visibility: Visibility::Visible,
                            is_local: false,
                            is_constness_unset: false,
                        })],
                        active: let_in(vec![instance_defn("A", "Active", 37, Vec::new())], ix(1)),
                    },
                    axiom_count: 0,
                    proof: Proof {
                        core: ProofCore::By {
                            usable: Usable {
                                facts: vec![let_in(
                                    vec![instance_defn("P", "ProofOnly", 38, Vec::new())],
                                    ix(1),
                                )],
                                defs: Vec::new(),
                            },
                            is_only: false,
                        },
                        props: ProofProps::default(),
                    },
                },
                ModuleUnitCore::Axiom {
                    name: None,
                    expression: apply(
                        opaque("f"),
                        vec![let_in(
                            vec![instance_defn("Z", "Axy", 39, Vec::new())],
                            ix(1),
                        )],
                    ),
                },
                mutate(
                    MutateMode::Use,
                    vec![let_in(
                        vec![instance_defn("U", "Used", 40, Vec::new())],
                        ix(1),
                    )],
                    Vec::new(),
                ),
                submod(first_submodule),
                submod(mule(
                    "Sub1",
                    &["Late"],
                    vec![variables(&["v"]), variables(&["w"])],
                )),
                definition(instance_defn("Lo", "Sub2", 43, Vec::new())),
                definition(instance_defn("U1", "\u{1F600}", 44, Vec::new())),
                definition(instance_defn("U2", "\u{FF5E}", 45, Vec::new())),
                definition(instance_defn("U3", "é", 46, Vec::new())),
            ],
        );
        module.extendee_locations = Some(vec![locus_at(1), locus_at(2)]);
        assert_eq!(
            show_dependencies(&get_dependencies(&module)),
            expected("deps D")
        );
        assert_eq!(
            show_dependencies(&get_dependencies(&mule("E", &[], Vec::new()))),
            expected("deps empty")
        );
    }

    #[test]
    fn compares_names_by_utf16() {
        for (left, right) in [
            ("a", "b"),
            ("b", "a"),
            ("a", "a"),
            ("", "a"),
            ("Z", "a"),
            ("\u{1F600}", "\u{FF5E}"),
            ("ab", "a"),
        ] {
            let order = match compare_names(left, right) {
                Ordering::Less => "-1",
                Ordering::Equal => "0",
                Ordering::Greater => "1",
            };
            assert_eq!(order, expected(&format!("compare {left}|{right}")));
        }
    }

    #[test]
    fn substitutes_units() {
        let units = vec![
            unit(
                ModuleUnitCore::Constants {
                    declarations: declarations(&[("N", 0)]),
                },
                None,
            ),
            unit(variables(&["x", "y"]), None),
            unit(
                definition(operator_defn("Op", apply(ix(1), vec![ix(2), ix(5)]))),
                locus(50),
            ),
            unit(
                ModuleUnitCore::Axiom {
                    name: Some("Ax".to_owned()),
                    expression: apply(ix(1), vec![ix(4)]),
                },
                locus(51),
            ),
            unit(
                theorem(None, vec![fact(ix(1))], apply(ix(1), vec![ix(2), ix(9)]), 0),
                locus(52),
            ),
            unit(
                mutate(
                    MutateMode::Use,
                    vec![ix(1), ix(7)],
                    vec![
                        UseDef {
                            core: UseDefCore::Dvar {
                                name: "dv".to_owned(),
                            },
                            location: locus(53),
                        },
                        UseDef {
                            core: UseDefCore::Dx { index: 8 },
                            location: locus(54),
                        },
                    ],
                ),
                None,
            ),
            unit(
                mutate(
                    MutateMode::Hide,
                    vec![ix(8)],
                    vec![UseDef {
                        core: UseDefCore::Dx { index: 9 },
                        location: None,
                    }],
                ),
                None,
            ),
            unit(
                submod(mule(
                    "SM",
                    &[],
                    vec![
                        ModuleUnitCore::Axiom {
                            name: None,
                            expression: ix(10),
                        },
                        ModuleUnitCore::Axiom {
                            name: None,
                            expression: ix(10),
                        },
                    ],
                )),
                None,
            ),
            unit(
                ModuleUnitCore::Anoninst {
                    instance: InstanceDefinition {
                        args: names(&["z"]),
                        module: "Inst".to_owned(),
                        substitutions: vec![entry("c", ix(10))],
                        location: None,
                    },
                    is_local: true,
                },
                locus(55),
            ),
            unit(
                ModuleUnitCore::Recursives {
                    declarations: declarations(&[("R", 1), ("Q", 0)]),
                },
                None,
            ),
            unit(
                ModuleUnitCore::Axiom {
                    name: None,
                    expression: ix(11),
                },
                None,
            ),
        ];
        let show_units = |result: Result<Vec<ModuleUnit>>| {
            show_result(
                result.map(|units| units.iter().map(show_unit).collect::<Vec<_>>().join("; ")),
            )
        };
        assert_eq!(
            show_units(substitute_units(&shift(3), &units)),
            expected("subst shift 3")
        );
        let cons = cons_substitution(opaque("e"), shift(0));
        let axiom = |index| {
            unit(
                ModuleUnitCore::Axiom {
                    name: None,
                    expression: ix(index),
                },
                None,
            )
        };
        assert_eq!(
            show_units(substitute_units(
                &cons,
                &[axiom(1), unit(variables(&["v"]), None), axiom(2)]
            )),
            expected("subst cons")
        );
        assert_eq!(
            show_units(substitute_units(
                &cons,
                &[
                    unit(variables(&["v"]), None),
                    unit(
                        mutate(
                            MutateMode::Hide,
                            Vec::new(),
                            vec![UseDef {
                                core: UseDefCore::Dx { index: 2 },
                                location: None,
                            }],
                        ),
                        None,
                    ),
                ]
            )),
            expected("subst bad def")
        );
        assert_eq!(
            show_result(substitute_units(&shift(1), &[]).map(|units| units.len().to_string())),
            expected("subst empty")
        );
    }

    #[test]
    fn binds_theorem_names() {
        let run = |label: &str, name: Option<&str>, sequent: Sequent, location: Option<Locus>| {
            assert_eq!(
                show_result(bind_theorem_name(name, &sequent, &location).map(
                    |(hyps, sequent)| format!("{} || {}", show_hyps(&hyps), show_sequent(&sequent))
                )),
                expected(label),
                "{label}"
            );
        };
        run(
            "bind none",
            None,
            Sequent {
                context: vec![fact(ix(1))],
                active: ix(2),
            },
            locus(60),
        );
        run(
            "bind ctx",
            Some("T"),
            Sequent {
                context: vec![fact(ix(1))],
                active: apply(ix(2), vec![ix(1)]),
            },
            locus(61),
        );
        run(
            "bind empty noloc",
            Some("T"),
            Sequent {
                context: Vec::new(),
                active: atomic(&ix_at(2, 62)),
            },
            None,
        );
        run(
            "bind empty loc",
            Some("T"),
            Sequent {
                context: Vec::new(),
                active: atomic(&ix_at(2, 62)),
            },
            locus(63),
        );
    }

    const NATURALS: &str = r#"Definition(Builtin,Visible,false) Nat==$Nat; Definition(Builtin,Visible,false) +==(lambda x1/0 x2/0. ($Plus #2 #1)); Definition(Builtin,Visible,false) -==(lambda x1/0 x2/0. ($Minus #2 #1)); Definition(Builtin,Visible,false) *==(lambda x1/0 x2/0. ($Times #2 #1)); Definition(Builtin,Visible,false) ^==(lambda x1/0 x2/0. ($Exp #2 #1)); Definition(Builtin,Visible,false) <==(lambda x1/0 x2/0. ($Lt #2 #1)); Definition(Builtin,Visible,false) >==(lambda x1/0 x2/0. ($Gt #2 #1)); Definition(Builtin,Visible,false) =<==(lambda x1/0 x2/0. ($Lteq #2 #1)); Definition(Builtin,Visible,false) >===(lambda x1/0 x2/0. ($Gteq #2 #1)); Definition(Builtin,Visible,false) %==(lambda x1/0 x2/0. ($Remainder #2 #1)); Definition(Builtin,Visible,false) \div==(lambda x1/0 x2/0. ($Quotient #2 #1)); Definition(Builtin,Visible,false) ..==(lambda x1/0 x2/0. ($Range #2 #1))"#;

    const EXPECTED: &[(&str, &str)] = &[
        (
            "std Reals",
            r#"defn(Builtin,Visible,false) Nat==$Nat ; defn(Builtin,Visible,false) +==(lambda x1/0 x2/0. ($Plus #2 #1)) ; defn(Builtin,Visible,false) -==(lambda x1/0 x2/0. ($Minus #2 #1)) ; defn(Builtin,Visible,false) *==(lambda x1/0 x2/0. ($Times #2 #1)) ; defn(Builtin,Visible,false) ^==(lambda x1/0 x2/0. ($Exp #2 #1)) ; defn(Builtin,Visible,false) <==(lambda x1/0 x2/0. ($Lt #2 #1)) ; defn(Builtin,Visible,false) >==(lambda x1/0 x2/0. ($Gt #2 #1)) ; defn(Builtin,Visible,false) =<==(lambda x1/0 x2/0. ($Lteq #2 #1)) ; defn(Builtin,Visible,false) >===(lambda x1/0 x2/0. ($Gteq #2 #1)) ; defn(Builtin,Visible,false) %==(lambda x1/0 x2/0. ($Remainder #2 #1)) ; defn(Builtin,Visible,false) \div==(lambda x1/0 x2/0. ($Quotient #2 #1)) ; defn(Builtin,Visible,false) ..==(lambda x1/0 x2/0. ($Range #2 #1)) ; defn(Builtin,Visible,false) Int==$Int ; defn(Builtin,Visible,false) -.==(lambda x1/0. ($Uminus #1)) ; defn(Builtin,Visible,false) Real==$Real ; defn(Builtin,Visible,false) /==(lambda x1/0 x2/0. ($Ratio #2 #1)) ; defn(Builtin,Visible,false) Infinity==$Infinity"#,
        ),
        (
            "std TLC",
            r#"defn(Builtin,Visible,false) Print==(lambda x1/0 x2/0. ($Print #2 #1)) ; defn(Builtin,Visible,false) PrintT==(lambda x1/0. ($PrintT #1)) ; defn(Builtin,Visible,false) Assert==(lambda x1/0 x2/0. ($Assert #2 #1)) ; defn(Builtin,Visible,false) JavaTime==$JavaTime ; defn(Builtin,Visible,false) TLCGet==(lambda x1/0. ($TLCGet #1)) ; defn(Builtin,Visible,false) TLCSet==(lambda x1/0 x2/0. ($TLCSet #2 #1)) ; defn(Builtin,Visible,false) :>==(lambda x1/0 x2/0. ($OneArg #2 #1)) ; defn(Builtin,Visible,false) @@==(lambda x1/0 x2/0. ($Extend #2 #1)) ; defn(Builtin,Visible,false) Permutations==(lambda x1/0. ($Permutations #1)) ; defn(Builtin,Visible,false) SortSeq==(lambda x1/0 x2/0. ($SortSeq #2 #1)) ; defn(Builtin,Visible,false) RandomElement==(lambda x1/0. ($RandomElement #1)) ; defn(Builtin,Visible,false) Any==$Any ; defn(Builtin,Visible,false) ToString==(lambda x1/0. ($ToString #1))"#,
        ),
        (
            "std mule",
            r#"{Sequences ext= std=true | Definition(Builtin,Visible,false) Seq==(lambda x1/0. ($Seq #1)); Definition(Builtin,Visible,false) Len==(lambda x1/0. ($Len #1)); Definition(Builtin,Visible,false) BSeq==(lambda x1/0 x2/0. ($BSeq #2 #1)); Definition(Builtin,Visible,false) \o==(lambda x1/0 x2/0. ($Cat #2 #1)); Definition(Builtin,Visible,false) Append==(lambda x1/0 x2/0. ($Append #2 #1)); Definition(Builtin,Visible,false) Head==(lambda x1/0. ($Head #1)); Definition(Builtin,Visible,false) Tail==(lambda x1/0. ($Tail #1)); Definition(Builtin,Visible,false) SubSeq==(lambda x1/0 x2/0 x3/0. ($SubSeq #3 #2 #1)); Definition(Builtin,Visible,false) SelectSeq==(lambda x1/0 x2/0. ($SelectSeq #2 #1))}"#,
        ),
        (
            "hyps constants",
            r#"fresh N/0/Constant@3, fresh F/2/Constant@3"#,
        ),
        ("size constants", r#"2"#),
        ("hyps recursives", r#"defn(User,Hidden,false) rec R/1@4@4"#),
        ("size recursives", r#"1"#),
        ("hyps variables", r#"flex x, flex y"#),
        ("size variables", r#"2"#),
        (
            "hyps definition",
            r#"defn(Builtin,Hidden,true) Op==(f #1)@5"#,
        ),
        ("size definition", r#"1"#),
        ("hyps axiom unnamed", r#"fact(Hidden,Always) #2@9@6"#),
        ("size axiom unnamed", r#"1"#),
        (
            "hyps axiom named",
            r#"defn(User,Visible,false) Ax==#2@7@7, fact(Hidden,Always) #1@7@7"#,
        ),
        ("size axiom named", r#"2"#),
        (
            "hyps theorem ctx",
            r#"defn(User,Visible,false) Thm==[fact(Visible,Always) #2, fact(Visible,Always) #4 |- (#1 #3)]@8@8@8, fact(Hidden,Always) #1@8@8"#,
        ),
        ("size theorem ctx", r#"2"#),
        ("hyps theorem empty noloc", r#"fact(Hidden,Always) #3@12!"#),
        ("size theorem empty noloc", r#"1"#),
        ("hyps theorem empty loc", r#"fact(Hidden,Always) #2@13!@13"#),
        ("size theorem empty loc", r#"1"#),
        (
            "hyps theorem big count",
            r#"defn(User,Visible,false) T==#1, fact(Hidden,Always) #1"#,
        ),
        ("size theorem big count", r#"2"#),
        (
            "hyps mutate use",
            r#"fact(Visible,Always) #1@14, fact(Visible,Always) (#3 #4)@14"#,
        ),
        ("size mutate use", r#"2"#),
        ("hyps mutate hide", r#""#),
        ("size mutate hide", r#"0"#),
        ("hyps submod", r#""#),
        ("size submod", r#"0"#),
        ("hyps anoninst", r#""#),
        ("size anoninst", r#"0"#),
        (
            "flatten A",
            r#"{A ext=B,C,Integers std=false | {NAT}; Variables c; Definition(Builtin,Visible,true) L==l@20; Theorem CT 0 [ |- #1] proof=Omitted:Elsewhere@21@21; Submod {CS ext= std=false | Definition(User,Visible,false) Q==q}; Constants b/0; {NAT}; Definition(Builtin,Visible,false) Int==$Int; Definition(Builtin,Visible,false) -.==(lambda x1/0. ($Uminus #1)); Variables a; Submod {Inner ext=C std=false | {NAT}; Variables c; Definition(Builtin,Visible,true) L==l@20; Theorem CT 0 [ |- #1] proof=Omitted:Elsewhere@21@21; Submod {CS ext= std=false | Definition(User,Visible,false) Q==q}; Variables i}}"#,
        ),
        (
            "flatten A seen",
            r#"{A ext=B,C,Integers std=false | {NAT}; Constants b/0; {NAT}; Definition(Builtin,Visible,false) Int==$Int; Definition(Builtin,Visible,false) -.==(lambda x1/0. ($Uminus #1)); Variables a; Submod {Inner ext=C std=false | {NAT}; Variables c; Definition(Builtin,Visible,true) L==l@20; Theorem CT 0 [ |- #1] proof=Omitted:Elsewhere@21@21; Submod {CS ext= std=false | Definition(User,Visible,false) Q==q}; Variables i}}"#,
        ),
        (
            "flatten self",
            r#"ERR TlaProofError: Oops, this seems to be a bug in TLAPM. / Stack overflow"#,
        ),
        (
            "flatten loop",
            r#"ERR TlaProofError: Oops, this seems to be a bug in TLAPM. / Stack overflow"#,
        ),
        (
            "flatten unknown",
            r#"ERR TlaProofError: Module "Nope" unknown / Failure("Module \"Nope\" unknown")"#,
        ),
        (
            "flatten sub unknown",
            r#"ERR TlaProofError: Module "Gone" unknown / Failure("Module \"Gone\" unknown")"#,
        ),
        ("flatten seen grows", r#"B,C,Integers,Naturals"#),
        (
            "deps D",
            r#"deps=Active,Alpha,Anon,Axy,Ext1,Hyp,InSub,Late,Let1,Named,Nested,Sub1,SubInst,Used,Zeta,é,😀,～ locs=Let1@30,Nested@31,Anon@33,InSub@32,Named@34,Alpha@35,Hyp@36,Active@37,Axy@39,Used@40,Ext1@42,Zeta,SubInst@41,Late,😀@44,～@45,é@46,Sub1 subs=Sub1,Sub2/2,0"#,
        ),
        ("deps empty", r#"deps= locs= subs=/"#),
        ("compare a|b", r#"-1"#),
        ("compare b|a", r#"1"#),
        ("compare a|a", r#"0"#),
        ("compare |a", r#"-1"#),
        ("compare Z|a", r#"-1"#),
        ("compare 😀|～", r#"-1"#),
        ("compare ab|a", r#"1"#),
        (
            "subst shift 3",
            r#"Constants N/0; Variables x y; Definition(User,Visible,false) Op==(#1 #2 #8)@50; Axiom Ax (#1 #4)@51; Theorem _ 0 [fact(Visible,Always) #1 |- (#1 #2 #12)] proof=Obvious@52; Mutate Use #1 #7 defs dv@53 D11@54; Mutate Hide #8 defs D9; Submod {SM ext= std=false | Axiom _ #13; Axiom _ #10}; Anoninst true Inst[c<-#13]@55; Recursives R/1 Q/0; Axiom _ #11"#,
        ),
        ("subst cons", r#"Axiom _ e; Variables v; Axiom _ #2"#),
        (
            "subst bad def",
            r#"ERR TlaProofError: substitution produced bad definition / Failure("substitution produced bad definition")"#,
        ),
        ("subst empty", r#"0"#),
        ("bind none", r#" || [fact(Visible,Always) #1 |- #2]"#),
        (
            "bind ctx",
            r#"defn(Proof:Always,Visible,false) T==[fact(Visible,Always) #1 |- (#2 #1)]@61@61@61 || [fact(Visible,Always) #2 |- (#3 #1)]"#,
        ),
        (
            "bind empty noloc",
            r#"defn(Proof:Always,Visible,false) T==#2@62! || [ |- #3@62!]"#,
        ),
        (
            "bind empty loc",
            r#"defn(Proof:Always,Visible,false) T==#2@63!@63@63 || [ |- #3@62!]"#,
        ),
    ];
}
