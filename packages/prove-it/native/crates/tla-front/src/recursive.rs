//! The RECURSIVE declarations whose SANY report the front end writes, and nothing else.
//!
//! `Generator.processRecursive` binds each declared operator at the current LET/IN level,
//! `processOperator` and `processFunction` define it, `checkForUndefinedRecursiveOps` reports it if
//! nothing does by the end of its LET or module, and `SymbolTable.addSymbol` decides what any other
//! binding of its name means. The front end follows these only for the shapes below, and declines
//! any other module with a RECURSIVE declaration (native/design/front.md, and the grid in
//! crates/tla-front/tests/recursive-shapes).
//!
//! A declaration of N with k arguments, at module level or in a LET, is analyzed only if:
//!
//! - N is no built-in, and nothing before it in its module or LET names N or binds it;
//! - nothing after it in its scope binds N other than one definition of N in the same module or LET,
//!   or, for a LET's declaration, one LET definition of N within a later definition of that LET;
//! - its definition, if any, is an operator definition with k parameters that take no arguments,
//!   or a function definition when k is 0; at module level it may instead be an operator
//!   definition with another number of such parameters, or a function definition when k isn't 0;
//! - nothing in its scope names N if that definition isn't of the first shape, or if N is left
//!   undefined or defined at a deeper LET;
//! - a LET with RECURSIVE declarations has no INSTANCE and no other LET with RECURSIVE declarations
//!   within it;
//! - a module nested in another declares nothing RECURSIVE at its own level;
//! - after a module-level declaration, no INSTANCE without a name adds names to the module.
//!
//! The resolver checks the rest: that N isn't bound where the declaration appears.

use std::rc::Rc;

use crate::ast::{
    Assumed, Declaration, Definition, DefinitionKind, DefinitionUnit, Expr, Expression,
    ExpressionKind, Fact, Instance, Module, ModuleUnit, Name, Proof, ProofKind, Selector,
    Statement, StepBody,
};
use crate::errors::FrontError;
use crate::resolve::{CORE_SYMBOLS, is_before};
use crate::standard_builtins::CORE_OPERATORS;

type Result<T> = std::result::Result<T, FrontError>;

/// How a part of a module mentions a name: as a reference, as a binding other than a definition,
/// and in how many LET definitions.
#[derive(Clone, Copy, Default)]
struct Mentions {
    is_referenced: bool,
    is_bound: bool,
    definitions: usize,
}

impl Mentions {
    fn add(self, other: Mentions) -> Mentions {
        Mentions {
            is_referenced: self.is_referenced || other.is_referenced,
            is_bound: self.is_bound || other.is_bound,
            definitions: self.definitions + other.definitions,
        }
    }

    fn bound(is_bound: bool) -> Mentions {
        Mentions {
            is_bound,
            ..Mentions::default()
        }
    }

    fn is_any(self) -> bool {
        self.is_referenced || self.is_bound || self.definitions != 0
    }
}

/// A name SANY's symbol table holds from the start, whose RECURSIVE declaration `addSymbol`
/// rejects before the generator's exception could count it.
fn is_builtin(name: &str) -> bool {
    CORE_SYMBOLS.contains(&name) || CORE_OPERATORS.iter().any(|operator| operator.0 == name)
}

fn not_yet(reason: &str, name: &str) -> FrontError {
    FrontError::NotYet(format!("{reason} {name}"))
}

fn sum(mentions: impl IntoIterator<Item = Mentions>) -> Mentions {
    mentions
        .into_iter()
        .fold(Mentions::default(), Mentions::add)
}

fn get_expressions_mentions(expressions: &[Expr], name: &str) -> Mentions {
    sum(expressions
        .iter()
        .map(|expression| get_mentions(expression, name)))
}

fn is_named(names: &[impl AsRef<str>], name: &str) -> bool {
    names.iter().any(|bound| bound.as_ref() == name)
}

fn get_mentions(expression: &Expression, name: &str) -> Mentions {
    let is_referenced = match &expression.kind {
        ExpressionKind::Subexpression { selectors, .. } => {
            matches!(selectors.first(), Some(Selector::Name { name: written, .. }) if &**written == name)
        }
        _ => expression.reference().is_some_and(|written| {
            &*written == name
                || written
                    .strip_prefix(name)
                    .is_some_and(|rest| rest.starts_with('!'))
        }),
    };
    let own = match &expression.kind {
        ExpressionKind::Quantified { bounds, .. }
        | ExpressionKind::FunctionConstruction { bounds, .. }
        | ExpressionKind::SetMap { bounds, .. } => Mentions::bound(
            bounds
                .iter()
                .any(|bound| is_named(bound.pattern.names(), name)),
        ),
        ExpressionKind::SetFilter { bound, .. } => {
            Mentions::bound(is_named(bound.pattern.names(), name))
        }
        ExpressionKind::UnboundedQuantifier { names, .. }
        | ExpressionKind::Lambda { params: names, .. } => Mentions::bound(is_named(names, name)),
        ExpressionKind::Choose { pattern, .. } => Mentions::bound(is_named(pattern.names(), name)),
        ExpressionKind::Let {
            definitions,
            instances,
            recursive,
            ..
        } => {
            let mut parts = Parts::default();
            for instance in instances.iter().flatten() {
                parts.add_instance(instance);
            }
            Mentions {
                definitions: definitions
                    .iter()
                    .filter(|definition| &*definition.name == name)
                    .count(),
                ..Mentions::bound(
                    is_named(&parts.names, name)
                        || definitions
                            .iter()
                            .any(|definition| is_named(&get_bound_names(definition), name))
                        || recursive
                            .iter()
                            .any(|declaration| &*declaration.name == name),
                )
            }
            .add(get_expressions_mentions(&parts.expressions, name))
        }
        _ => Mentions::default(),
    };
    Mentions {
        is_referenced,
        ..own
    }
    .add(get_expressions_mentions(&expression.children(), name))
}

/// The parameters of an operator definition, or the bound names of a function definition.
fn get_bound_names(definition: &Definition) -> Vec<Name> {
    match &definition.kind {
        DefinitionKind::Operator { params, .. } => {
            params.iter().map(|param| param.name.clone()).collect()
        }
        DefinitionKind::Function { bounds } => bounds
            .iter()
            .flat_map(|bound| bound.pattern.names().to_vec())
            .collect(),
    }
}

/// The names a part of a module binds, and the expressions it holds, those of its proofs included.
#[derive(Default)]
struct Parts {
    names: Vec<Name>,
    expressions: Vec<Expr>,
}

impl Parts {
    fn of_unit(unit: &ModuleUnit) -> Parts {
        let mut parts = Parts::default();
        match unit {
            ModuleUnit::Constants { declarations, .. }
            | ModuleUnit::Variables { declarations, .. }
            | ModuleUnit::Recursive(declarations) => parts.names.extend(
                declarations
                    .iter()
                    .map(|declaration| declaration.name.clone()),
            ),
            ModuleUnit::Definition(definition) => {
                parts.names.push(definition.name.clone());
                parts.add_definition(definition);
            }
            ModuleUnit::Instance(instance) => parts.add_instance(instance),
            ModuleUnit::Assumption(assumption) => {
                parts.names.extend(assumption.name.clone());
                parts.expressions.push(assumption.expression.clone());
            }
            ModuleUnit::Theorem(theorem) => {
                parts.names.extend(theorem.name.clone());
                parts.add_statement(&theorem.statement);
                if let Some(proof) = &theorem.proof {
                    parts.add_proof(proof);
                }
            }
            ModuleUnit::Use(use_or_hide) => {
                parts.add_facts(&use_or_hide.facts);
                parts.add_facts(&use_or_hide.defs);
            }
            ModuleUnit::Module(inner) => {
                parts.names.push(inner.name.clone());
                for unit in &inner.units {
                    let inner_parts = Parts::of_unit(unit);
                    parts.names.extend(inner_parts.names);
                    parts.expressions.extend(inner_parts.expressions);
                }
            }
        }
        parts
    }

    /// A definition's parameters or bound names, its body and its bounds, without its name.
    fn add_definition(&mut self, definition: &Definition) {
        self.names.extend(get_bound_names(definition));
        if let DefinitionKind::Function { bounds } = &definition.kind {
            self.expressions
                .extend(bounds.iter().map(|bound| bound.set.clone()));
        }
        self.expressions.push(definition.body.clone());
    }

    fn add_instance(&mut self, instance: &Instance) {
        self.names.extend(instance.name.clone());
        self.names
            .extend(instance.params.iter().map(|param| param.name.clone()));
        self.expressions.extend(
            instance
                .substitutions
                .iter()
                .map(|substitution| substitution.expression.clone()),
        );
    }

    fn add_facts(&mut self, facts: &[Fact]) {
        self.expressions
            .extend(facts.iter().filter_map(|fact| match fact {
                Fact::Expression(expression) => Some(expression.clone()),
                Fact::Module { .. } => None,
            }));
    }

    fn add_assumed(&mut self, assumed: &Assumed) {
        match assumed {
            Assumed::Expression(expression) => self.expressions.push(expression.clone()),
            Assumed::NewSymbol(symbol) => {
                self.names.push(symbol.name.clone());
                self.expressions.extend(symbol.set.clone());
            }
            Assumed::AssumeProve(assume_prove)
            | Assumed::Label {
                body: assume_prove, ..
            } => {
                for assumed in &assume_prove.assumptions {
                    self.add_assumed(assumed);
                }
                self.expressions.push(assume_prove.conclusion.clone());
            }
        }
    }

    fn add_statement(&mut self, statement: &Statement) {
        match statement {
            Statement::Expression(expression) => self.expressions.push(expression.clone()),
            Statement::AssumeProve(assume_prove) => {
                self.add_assumed(&Assumed::AssumeProve(assume_prove.clone()));
            }
        }
    }

    fn add_proof(&mut self, proof: &Proof) {
        match &proof.kind {
            ProofKind::Obvious { .. } | ProofKind::Omitted { .. } => {}
            ProofKind::By { facts, defs, .. } => {
                self.add_facts(facts);
                self.add_facts(defs);
            }
            ProofKind::Steps { steps, .. } => {
                for step in steps {
                    self.add_step(&step.body);
                    if let Some(proof) = &step.proof {
                        self.add_proof(proof);
                    }
                }
            }
        }
    }

    fn add_step(&mut self, body: &StepBody) {
        match body {
            StepBody::UseOrHide(use_or_hide) => {
                self.add_facts(&use_or_hide.facts);
                self.add_facts(&use_or_hide.defs);
            }
            StepBody::Instance(instance) => self.add_instance(instance),
            StepBody::Define { definitions, .. } => {
                for definition in definitions {
                    match definition {
                        DefinitionUnit::Definition(definition) => {
                            self.names.push(definition.name.clone());
                            self.add_definition(definition);
                        }
                        DefinitionUnit::Instance(instance) => self.add_instance(instance),
                    }
                }
            }
            StepBody::Have(expression) | StepBody::Case(expression) => {
                self.expressions.push(expression.clone());
            }
            StepBody::Witness(expressions) => self.expressions.extend(expressions.iter().cloned()),
            StepBody::Take { names, bounds, .. } => {
                self.names.extend(names.iter().cloned());
                self.expressions
                    .extend(bounds.iter().map(|bound| bound.set.clone()));
            }
            StepBody::Pick {
                names,
                bounds,
                body,
                ..
            } => {
                self.names.extend(names.iter().cloned());
                self.expressions
                    .extend(bounds.iter().map(|bound| bound.set.clone()));
                self.expressions.push(body.clone());
            }
            StepBody::Assert { statement, .. } => self.add_statement(statement),
            StepBody::Qed => {}
        }
    }

    fn get_mentions(&self, name: &str) -> Mentions {
        Mentions::bound(is_named(&self.names, name))
            .add(get_expressions_mentions(&self.expressions, name))
    }
}

/// What a definition mentions apart from the name it defines.
fn get_definition_mentions(definition: &Definition, name: &str) -> Mentions {
    let mut parts = Parts::default();
    parts.add_definition(definition);
    parts.get_mentions(name)
}

/// Whether the definition is of the shape `processOperator` or `processFunction` completes a
/// declaration with `arity` arguments with: SANY gives the declared operator's parameters the
/// arities of the definition's only when it reaches the definition.
fn is_completing(definition: &Definition, arity: usize) -> bool {
    match &definition.kind {
        DefinitionKind::Operator { params, .. } => params.len() == arity,
        DefinitionKind::Function { .. } => arity == 0,
    }
}

fn has_higher_order_params(definition: &Definition) -> bool {
    matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.iter().any(|param| param.arity != 0))
}

/// Checks each RECURSIVE declaration of the module, of the modules within it, and of their LETs.
pub fn check_recursive(module: &Module) -> Result<()> {
    for (index, unit) in module.units.iter().enumerate() {
        match unit {
            ModuleUnit::Recursive(declarations) => {
                if let Some(declaration) = declarations
                    .iter()
                    .find(|declaration| is_builtin(&declaration.name))
                {
                    return Err(not_yet(
                        "a RECURSIVE declaration of the built-in",
                        &declaration.name,
                    ));
                }
                for declaration in declarations {
                    check_module_declaration(module, index, &declaration.name, declaration.arity)?;
                }
            }
            ModuleUnit::Module(inner) => {
                if let Some(ModuleUnit::Recursive(declarations)) = inner
                    .units
                    .iter()
                    .find(|unit| matches!(unit, ModuleUnit::Recursive(_)))
                {
                    return Err(not_yet(
                        "a module nested in another that declares RECURSIVE",
                        &declarations[0].name,
                    ));
                }
                check_recursive(inner)?;
            }
            _ => {}
        }
    }
    module
        .units
        .iter()
        .filter(|unit| !matches!(unit, ModuleUnit::Module(_)))
        .flat_map(|unit| Parts::of_unit(unit).expressions)
        .try_for_each(|expression| check_lets(&expression, false))
}

fn check_module_declaration(module: &Module, index: usize, name: &str, arity: usize) -> Result<()> {
    let units = &module.units;
    let ModuleUnit::Recursive(declarations) = &units[index] else {
        return Ok(());
    };
    let is_redeclared = declarations
        .iter()
        .filter(|declaration| &*declaration.name == name)
        .count()
        > 1;
    if is_redeclared
        || units[..index]
            .iter()
            .any(|unit| Parts::of_unit(unit).get_mentions(name).is_any())
    {
        return Err(not_yet(
            "a RECURSIVE declaration of a name a module binds or names before it:",
            name,
        ));
    }
    let after = &units[index + 1..];
    let definitions: Vec<&Definition> = after
        .iter()
        .filter_map(|unit| match unit {
            ModuleUnit::Definition(definition) if &*definition.name == name => Some(&**definition),
            _ => None,
        })
        .collect();
    let mentions = sum(after.iter().map(|unit| match unit {
        ModuleUnit::Definition(definition) if &*definition.name == name => {
            get_definition_mentions(definition, name)
        }
        _ => Parts::of_unit(unit).get_mentions(name),
    }));
    let is_instanced = after
        .iter()
        .any(|unit| matches!(unit, ModuleUnit::Instance(instance) if instance.name.is_none()));
    if definitions.len() > 1
        || mentions.is_bound
        || mentions.definitions != 0
        || is_instanced
        || definitions
            .first()
            .is_some_and(|definition| has_higher_order_params(definition))
    {
        return Err(not_yet(
            "a module-level RECURSIVE declaration that something else binds, or an INSTANCE may:",
            name,
        ));
    }
    let is_complete = definitions
        .first()
        .is_some_and(|definition| is_completing(definition, arity));
    if !is_complete && mentions.is_referenced {
        return Err(not_yet(
            "a reference to an operator declared RECURSIVE and left undefined or defined otherwise:",
            name,
        ));
    }
    Ok(())
}

fn check_definition_lets(definition: &Definition, is_in_recursive: bool) -> Result<()> {
    if let DefinitionKind::Function { bounds } = &definition.kind {
        for bound in bounds {
            check_lets(&bound.set, is_in_recursive)?;
        }
    }
    check_lets(&definition.body, is_in_recursive)
}

fn check_lets(expression: &Expression, is_in_recursive: bool) -> Result<()> {
    let ExpressionKind::Let {
        definitions,
        instances,
        recursive,
        body,
    } = &expression.kind
    else {
        return expression
            .children()
            .iter()
            .try_for_each(|child| check_lets(child, is_in_recursive));
    };
    if !recursive.is_empty() {
        let name = &recursive[0].name;
        if let Some(declaration) = recursive
            .iter()
            .find(|declaration| is_builtin(&declaration.name))
        {
            return Err(not_yet(
                "a RECURSIVE declaration of the built-in",
                &declaration.name,
            ));
        }
        if instances.is_some() {
            return Err(not_yet(
                "a LET with an INSTANCE and RECURSIVE declarations:",
                name,
            ));
        }
        if is_in_recursive {
            return Err(not_yet(
                "a LET with RECURSIVE declarations within another such LET:",
                name,
            ));
        }
        for declaration in recursive {
            check_let_declaration(definitions, recursive, body, declaration)?;
        }
    }
    let is_in_recursive = is_in_recursive || !recursive.is_empty();
    for definition in definitions {
        check_definition_lets(definition, is_in_recursive)?;
    }
    check_lets(body, is_in_recursive)
}

fn check_let_declaration(
    definitions: &[Rc<Definition>],
    recursive: &[Rc<Declaration>],
    body: &Expression,
    declaration: &Declaration,
) -> Result<()> {
    let name = &*declaration.name;
    let position = declaration.location.position();
    let (before, after): (Vec<&Definition>, Vec<&Definition>) = definitions
        .iter()
        .map(|definition| &**definition)
        .partition(|definition| is_before(definition.location.position(), position));
    let is_named_before = before.iter().any(|definition| {
        &*definition.name == name || get_definition_mentions(definition, name).is_any()
    });
    let is_redeclared = recursive
        .iter()
        .filter(|other| &*other.name == name)
        .count()
        > 1;
    if is_named_before || is_redeclared {
        return Err(not_yet(
            "a LET's RECURSIVE declaration of a name it binds or names before it:",
            name,
        ));
    }
    let own: Vec<&Definition> = after
        .iter()
        .copied()
        .filter(|definition| &*definition.name == name)
        .collect();
    let mentions = sum(after
        .iter()
        .map(|definition| get_definition_mentions(definition, name)))
    .add(get_mentions(body, name));
    let body_mentions = get_mentions(body, name);
    let is_shaped = match own.as_slice() {
        [] => true,
        [definition] => {
            is_completing(definition, declaration.arity) && !has_higher_order_params(definition)
        }
        _ => false,
    };
    // `processOperator` reports a LET definition of the name within a later definition as at the
    // wrong LET/IN level, which leaves the declaration undefined.
    let is_wrong_level = own.is_empty()
        && mentions.definitions == 1
        && body_mentions.definitions == 0
        && !mentions.is_referenced;
    if !is_shaped
        || mentions.is_bound
        || (mentions.definitions != 0 && !is_wrong_level)
        || (own.is_empty() && mentions.is_referenced)
    {
        return Err(not_yet(
            "a LET's RECURSIVE declaration that something else binds or defines, or that is defined otherwise:",
            name,
        ));
    }
    Ok(())
}
