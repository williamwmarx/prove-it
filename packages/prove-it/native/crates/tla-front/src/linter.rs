//! SANY's linter, `tla2sany.linter.Linter` as `src/sany/linter.ts` ports it, on the modules the
//! front end parses: it warns about a record field named like a definition or declaration of the
//! module, unless a field of a record with the same fields is built from declarations.

use std::rc::Rc;

use crate::ast::*;
use crate::errors::{FrontError, SanyError, format_range};
use crate::hash::{FastMap, FastSet};
use crate::instances::map_children;
use crate::resolve::{Tables, get_bound_names};
use crate::tlc_data::SANY_OPERATOR_SYNONYMS;

type Result<T> = std::result::Result<T, FrontError>;

fn not_yet(reason: &str) -> FrontError {
    FrontError::NotYet(format!("{reason}, which SANY's linter reads"))
}

/// Operators whose values are sets of values that a record field may range over, by the module
/// that defines them. SANY compares the name of the definition with the module's, so no definition
/// of Reals counts.
const SET_OPERATORS: &[(&str, &str)] =
    &[("Integers", "Int"), ("Naturals", "Nat"), ("Reals", "Reals")];

/// The names an operator is written by, as SANY's synonyms give them.
fn get_spellings(name: &str) -> Vec<&str> {
    SANY_OPERATOR_SYNONYMS
        .iter()
        .find(|synonyms| synonyms.contains(&name))
        .map_or_else(|| vec![name], |synonyms| synonyms.to_vec())
}

/// What a module name means where an expression names it.
#[derive(Clone)]
enum Meaning {
    /// A CONSTANT or VARIABLE, or a NEW symbol, which SANY's linter takes as a declaration.
    Declared,
    /// A definition, the module that defines it, and the INSTANCE that brought it, if any.
    Defined {
        definition: Rc<Definition>,
        owner: Rc<Module>,
        instance: Option<(Rc<Instance>, Rc<Module>)>,
    },
}

/// The modules a spec loads, by name, with their inner modules.
pub struct Linter<'a> {
    modules: &'a FastMap<Rc<str>, Rc<Module>>,
    inner: FastMap<Rc<str>, Rc<Module>>,
    tables: Tables,
}

/// A name bound around an expression: a formal parameter or bound name, which SANY's linter takes
/// as built from declarations, or a LET definition, with the names around the LET.
#[derive(Clone)]
enum Binding {
    Formal,
    Let {
        definition: Rc<Definition>,
        outer: Rc<Locals>,
        siblings: Rc<[Rc<Definition>]>,
    },
}

type Locals = Vec<(Name, Binding)>;

fn bind_formals<'n>(locals: &Locals, names: impl IntoIterator<Item = &'n Name>) -> Locals {
    let mut inner = locals.clone();
    inner.extend(
        names
            .into_iter()
            .map(|name| (name.clone(), Binding::Formal)),
    );
    inner
}

/// The names in a LET's definitions and body: the names around it and its definitions.
fn bind_lets(locals: &Locals, definitions: &[Rc<Definition>]) -> Locals {
    let outer = Rc::new(locals.clone());
    let siblings: Rc<[Rc<Definition>]> = Rc::from(definitions);
    let mut inner = locals.clone();
    inner.extend(definitions.iter().map(|definition| {
        (
            definition.name.clone(),
            Binding::Let {
                definition: definition.clone(),
                outer: outer.clone(),
                siblings: siblings.clone(),
            },
        )
    }));
    inner
}

impl<'a> Linter<'a> {
    pub fn new(modules: &'a FastMap<Rc<str>, Rc<Module>>) -> Linter<'a> {
        fn add_inner(module: &Rc<Module>, inner: &mut FastMap<Rc<str>, Rc<Module>>) {
            for nested in &module.modules {
                inner
                    .entry(nested.name.clone())
                    .or_insert_with(|| nested.clone());
                add_inner(nested, inner);
            }
        }
        let mut inner = FastMap::default();
        for module in modules.values() {
            add_inner(module, &mut inner);
        }
        Linter {
            modules,
            inner,
            tables: Tables::default(),
        }
    }

    fn get_module(&self, name: &str) -> Result<Rc<Module>> {
        self.inner
            .get(name)
            .or_else(|| self.modules.get(name))
            .cloned()
            .ok_or_else(|| not_yet("a module the report doesn't load"))
    }

    /// `ModuleNode.getExtendedModuleSet(true)`: the modules a module extends, directly or not.
    fn get_extended(&self, module: &Rc<Module>, found: &mut Vec<Rc<Module>>) -> Result<()> {
        for name in &module.extends {
            let extended = self.get_module(name)?;
            if found.iter().any(|item| Rc::ptr_eq(item, &extended)) {
                continue;
            }
            found.push(extended.clone());
            self.get_extended(&extended, found)?;
        }
        Ok(())
    }

    /// What a module exports by `name` to a module that extends or instantiates it, or, when
    /// `is_own`, what the module itself sees by it.
    fn lookup(&self, module: &Rc<Module>, name: &str, is_own: bool) -> Result<Option<Meaning>> {
        let spellings = get_spellings(name);
        let is_named = |candidate: &str| spellings.contains(&candidate);
        if module
            .constants
            .iter()
            .chain(&module.variables)
            .any(|declaration| is_named(&declaration.name))
        {
            return Ok(Some(Meaning::Declared));
        }
        if let Some(definition) = module
            .definitions
            .iter()
            .find(|definition| is_named(&definition.name) && (is_own || !definition.is_hidden()))
        {
            return Ok(Some(Meaning::Defined {
                definition: definition.clone(),
                owner: module.clone(),
                instance: None,
            }));
        }
        for extended in &module.extends {
            if let Some(meaning) = self.lookup(&self.get_module(extended)?, name, false)? {
                return Ok(Some(meaning));
            }
        }
        for instance in &module.instances {
            if instance.is_local && !is_own {
                continue;
            }
            let (selected, rest) = match &instance.name {
                None => (true, name),
                Some(instance_name) => match name.strip_prefix(&format!("{instance_name}!")) {
                    Some(rest) => (true, rest),
                    None => (false, name),
                },
            };
            if !selected {
                continue;
            }
            let instancee = self.get_module(&instance.module)?;
            match self.lookup(&instancee, rest, false)? {
                // SANY substitutes for the declarations of the module an INSTANCE names.
                None | Some(Meaning::Declared) => {}
                Some(Meaning::Defined {
                    definition, owner, ..
                }) => {
                    return Ok(Some(Meaning::Defined {
                        definition,
                        owner,
                        instance: Some((instance.clone(), module.clone())),
                    }));
                }
            }
        }
        Ok(None)
    }

    /// Whether the declarations of a module, or of the modules it extends, include any.
    fn has_declarations(&self, module: &Rc<Module>) -> Result<bool> {
        let mut extended = Vec::new();
        self.get_extended(module, &mut extended)?;
        Ok(std::iter::once(module)
            .chain(&extended)
            .any(|item| !item.constants.is_empty() || !item.variables.is_empty()))
    }

    /// The declarations an INSTANCE of `instancee` substitutes for, with its own and those of the
    /// modules `instancee` extends.
    fn get_declarations(&self, instancee: &Rc<Module>) -> Result<Vec<Rc<Declaration>>> {
        let mut extended = Vec::new();
        self.get_extended(instancee, &mut extended)?;
        Ok(std::iter::once(instancee)
            .chain(&extended)
            .flat_map(|item| item.constants.iter().chain(&item.variables).cloned())
            .collect())
    }
}

/// `Linter.isBuiltFromDeclarations`: whether an expression applies a declared or bound symbol,
/// BOOLEAN or a standard set of numbers, directly or through the definitions it applies.
struct Visit<'b, 'a> {
    linter: &'b Linter<'a>,
    visited: FastSet<usize>,
}

impl Visit<'_, '_> {
    fn name(&mut self, name: &str, module: &Rc<Module>, locals: &Locals) -> Result<bool> {
        if let Some((_, binding)) = locals.iter().rev().find(|(bound, _)| &**bound == name) {
            return match binding {
                Binding::Formal => Ok(true),
                Binding::Let {
                    definition,
                    outer,
                    siblings,
                } => self.definition(definition, module, &bind_lets(outer, siblings)),
            };
        }
        if name == "BOOLEAN" {
            return Ok(true);
        }
        let Some(meaning) = self.linter.lookup(module, name, true)? else {
            return Ok(false);
        };
        let Meaning::Defined {
            definition,
            owner,
            instance,
        } = meaning
        else {
            return Ok(true);
        };
        if SET_OPERATORS
            .iter()
            .any(|(module_name, set)| *owner.name == **module_name && *definition.name == **set)
        {
            return Ok(true);
        }
        if let Some((instance, instancer)) = instance
            && self.visited.insert(Rc::as_ptr(&instance) as usize)
            && self.substitutions(&instance, &instancer)?
        {
            return Ok(true);
        }
        self.definition(&definition, &owner, &Vec::new())
    }

    /// `SubstInNode.getChildren`: the substitutions an INSTANCE makes, explicit or not, for the
    /// declarations of a module that has any.
    fn substitutions(&mut self, instance: &Rc<Instance>, instancer: &Rc<Module>) -> Result<bool> {
        let instancee = self.linter.get_module(&instance.module)?;
        if !self.linter.has_declarations(&instancee)? {
            return Ok(false);
        }
        let params = bind_formals(&Vec::new(), instance.params.iter().map(|param| &param.name));
        for declaration in self.linter.get_declarations(&instancee)? {
            let explicit = instance
                .substitutions
                .iter()
                .find(|substitution| substitution.name == declaration.name);
            let is_built = match explicit {
                Some(substitution) => {
                    self.expression(&substitution.expression, instancer, &params)?
                }
                None => self.name(&declaration.name, instancer, &params)?,
            };
            if is_built {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn definition(
        &mut self,
        definition: &Rc<Definition>,
        module: &Rc<Module>,
        locals: &Locals,
    ) -> Result<bool> {
        if !self.visited.insert(Rc::as_ptr(definition) as usize) {
            return Ok(false);
        }
        let inner = match &definition.kind {
            DefinitionKind::Operator { params, .. } => {
                bind_formals(locals, params.iter().map(|param| &param.name))
            }
            DefinitionKind::Function { bounds } => {
                for bound in bounds {
                    if self.expression(&bound.set, module, locals)? {
                        return Ok(true);
                    }
                }
                bind_formals(locals, &get_bound_names(bounds))
            }
        };
        self.expression(&definition.body, module, &inner)
    }

    fn expression(
        &mut self,
        expression: &Expr,
        module: &Rc<Module>,
        locals: &Locals,
    ) -> Result<bool> {
        match &expression.kind {
            ExpressionKind::Identifier { name, .. }
            | ExpressionKind::OperatorReference { operator: name, .. } => {
                self.name(name, module, locals)
            }
            ExpressionKind::Apply { operator, args, .. } => {
                if self.name(operator, module, locals)? {
                    return Ok(true);
                }
                for arg in args {
                    if self.expression(arg, module, locals)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            ExpressionKind::Let {
                definitions, body, ..
            } => {
                let inner = bind_lets(locals, definitions);
                for definition in definitions {
                    if self.definition(definition, module, &inner)? {
                        return Ok(true);
                    }
                }
                self.expression(body, module, &inner)
            }
            ExpressionKind::Subexpression { .. } => Err(not_yet("a subexpression")),
            _ => {
                let mut result = Ok(false);
                map_children(expression, &self.linter.tables, &mut |child, bound| {
                    if matches!(result, Ok(false)) {
                        result = self.expression(child, module, &bind_formals(locals, bound));
                    }
                    Ok(child.clone())
                })?;
                result
            }
        }
    }
}

/// A record or set of records SANY generates for a module, with its fields in order and the
/// names bound around it.
struct RecordNode {
    expression: Expr,
    fields: Vec<RecordField>,
    locals: Locals,
}

/// Collects the records of the module's units, in the order SANY generates them.
struct Collector<'t> {
    tables: &'t Tables,
    records: Vec<RecordNode>,
}

impl Collector<'_> {
    /// A record joins after the records in its fields.
    fn expression(&mut self, expression: &Expr, locals: &Locals) -> Result<()> {
        if let ExpressionKind::Let {
            definitions, body, ..
        } = &expression.kind
        {
            let inner = bind_lets(locals, definitions);
            for definition in definitions {
                self.definition(definition, &inner)?;
            }
            return self.expression(body, &inner);
        }
        let mut result = Ok(());
        map_children(expression, self.tables, &mut |child, bound| {
            if result.is_ok() {
                result = self.expression(child, &bind_formals(locals, bound));
            }
            Ok(child.clone())
        })?;
        result?;
        if let ExpressionKind::Record { fields, .. } = &expression.kind {
            self.records.push(RecordNode {
                expression: expression.clone(),
                fields: fields.clone(),
                locals: locals.clone(),
            });
        }
        Ok(())
    }

    fn definition(&mut self, definition: &Definition, locals: &Locals) -> Result<()> {
        let inner = match &definition.kind {
            DefinitionKind::Operator { params, .. } => {
                bind_formals(locals, params.iter().map(|param| &param.name))
            }
            DefinitionKind::Function { bounds } => {
                for bound in bounds {
                    self.expression(&bound.set, locals)?;
                }
                bind_formals(locals, &get_bound_names(bounds))
            }
        };
        self.expression(&definition.body, &inner)
    }

    fn instance(&mut self, instance: &Instance, locals: &Locals) -> Result<()> {
        let inner = bind_formals(locals, instance.params.iter().map(|param| &param.name));
        for substitution in &instance.substitutions {
            self.expression(&substitution.expression, &inner)?;
        }
        Ok(())
    }

    fn facts(&mut self, facts: &[Fact], locals: &Locals) -> Result<()> {
        for fact in facts {
            if let Fact::Expression(expression) = fact {
                self.expression(expression, locals)?;
            }
        }
        Ok(())
    }

    /// The records of a statement, and the names its NEW symbols bind.
    fn assumed(&mut self, assumed: &Assumed, locals: &mut Locals) -> Result<()> {
        match assumed {
            Assumed::Expression(expression) => self.expression(expression, locals),
            Assumed::NewSymbol(symbol) => {
                if let Some(set) = &symbol.set {
                    self.expression(set, locals)?;
                }
                // SANY's linter takes a NEW symbol, an OpDeclNode, as a declaration.
                locals.push((symbol.name.clone(), Binding::Formal));
                Ok(())
            }
            Assumed::AssumeProve(assume_prove) => {
                let mut inner = locals.clone();
                for assumption in &assume_prove.assumptions {
                    self.assumed(assumption, &mut inner)?;
                }
                self.expression(&assume_prove.conclusion, &inner)
            }
        }
    }

    fn statement(&mut self, statement: &Statement, locals: &mut Locals) -> Result<()> {
        match statement {
            Statement::Expression(expression) => self.expression(expression, locals),
            Statement::AssumeProve(assume_prove) => {
                for assumption in &assume_prove.assumptions {
                    self.assumed(assumption, locals)?;
                }
                self.expression(&assume_prove.conclusion, locals)
            }
        }
    }

    fn proof(&mut self, proof: &Proof, locals: &Locals) -> Result<()> {
        match &proof.kind {
            ProofKind::By { facts, defs, .. } => {
                self.facts(facts, locals)?;
                self.facts(defs, locals)
            }
            ProofKind::Steps { steps, .. } => {
                let mut scope = locals.clone();
                for step in steps {
                    let mut inner = scope.clone();
                    match &step.body {
                        StepBody::UseOrHide(use_or_hide) => {
                            self.facts(&use_or_hide.facts, &inner)?;
                            self.facts(&use_or_hide.defs, &inner)?;
                        }
                        StepBody::Instance(instance) => self.instance(instance, &inner)?,
                        // A DEFINE step's definitions are in scope for the steps after it.
                        StepBody::Define { definitions, .. } => {
                            let defined: Vec<Rc<Definition>> = definitions
                                .iter()
                                .filter_map(|unit| match unit {
                                    DefinitionUnit::Definition(definition) => {
                                        Some(definition.clone())
                                    }
                                    DefinitionUnit::Instance(_) => None,
                                })
                                .collect();
                            scope = bind_lets(&scope, &defined);
                            inner = scope.clone();
                            for unit in definitions {
                                match unit {
                                    DefinitionUnit::Definition(definition) => {
                                        self.definition(definition, &inner)?
                                    }
                                    DefinitionUnit::Instance(instance) => {
                                        self.instance(instance, &inner)?
                                    }
                                }
                            }
                        }
                        StepBody::Have(expression) | StepBody::Case(expression) => {
                            self.expression(expression, &inner)?
                        }
                        StepBody::Witness(expressions) => {
                            for expression in expressions {
                                self.expression(expression, &inner)?;
                            }
                        }
                        StepBody::Take { bounds, names, .. } => {
                            for bound in bounds {
                                self.expression(&bound.set, &inner)?;
                            }
                            scope = bind_formals(&scope, names);
                            scope = bind_formals(&scope, &get_bound_names(bounds));
                        }
                        StepBody::Pick {
                            bounds,
                            names,
                            body,
                            ..
                        } => {
                            for bound in bounds {
                                self.expression(&bound.set, &inner)?;
                            }
                            inner = bind_formals(&inner, names);
                            inner = bind_formals(&inner, &get_bound_names(bounds));
                            self.expression(body, &inner)?;
                            scope = inner.clone();
                        }
                        StepBody::Assert { statement, .. } => {
                            self.statement(statement, &mut inner)?;
                        }
                        StepBody::Qed => {}
                    }
                    if let Some(proof) = &step.proof {
                        self.proof(proof, &inner)?;
                    }
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }
}

/// `ModuleNode.getRecords`: the records SANY generates for a module, without its inner modules',
/// in the order of the units, a record after the records in its fields.
fn get_records(module: &Module, tables: &Tables) -> Result<Vec<RecordNode>> {
    let mut collector = Collector {
        tables,
        records: Vec::new(),
    };
    for unit in &module.units {
        match unit {
            ModuleUnit::Definition(definition) => collector.definition(definition, &Vec::new())?,
            ModuleUnit::Instance(instance) => collector.instance(instance, &Vec::new())?,
            ModuleUnit::Assumption(assumption) => {
                collector.expression(&assumption.expression, &Vec::new())?
            }
            ModuleUnit::Theorem(theorem) => {
                let mut locals = Vec::new();
                collector.statement(&theorem.statement, &mut locals)?;
                if let Some(proof) = &theorem.proof {
                    collector.proof(proof, &locals)?;
                }
            }
            ModuleUnit::Use(use_or_hide) => {
                collector.facts(&use_or_hide.facts, &Vec::new())?;
                collector.facts(&use_or_hide.defs, &Vec::new())?;
            }
            ModuleUnit::Constants { .. }
            | ModuleUnit::Variables { .. }
            | ModuleUnit::Recursive(_)
            | ModuleUnit::Module(_) => {}
        }
    }
    Ok(collector.records)
}

/// `Records.sameDomain`.
fn is_same_domain(record: &RecordNode, other: &RecordNode) -> bool {
    Rc::ptr_eq(&record.expression, &other.expression)
        || (record.fields.len() == other.fields.len()
            && record.fields.iter().all(|field| {
                other
                    .fields
                    .iter()
                    .any(|other_field| other_field.name == field.name)
            }))
}

impl Linter<'_> {
    /// Where SANY's context of a top-level module has a symbol of a name, as the linter prints
    /// it, or none.
    fn get_symbol_location(&self, module: &Rc<Module>, name: &str) -> Result<Option<String>> {
        let found = module
            .constants
            .iter()
            .chain(&module.variables)
            .find(|declaration| *declaration.name == *name)
            .map(|declaration| declaration.location.range.clone());
        if let Some(range) = found {
            return range
                .map(|range| Some(format_range(&range)))
                .ok_or_else(|| not_yet("a declaration without a range"));
        }
        if let Some(definition) = module
            .definitions
            .iter()
            .find(|definition| *definition.name == *name)
        {
            return definition
                .location
                .range
                .as_ref()
                .map(|range| Some(format_range(range)))
                .ok_or_else(|| not_yet("a definition without a range"));
        }
        for extended in &module.extends {
            let extended = self.get_module(extended)?;
            if let Some(Meaning::Declared) | Some(Meaning::Defined { instance: None, .. }) =
                self.lookup(&extended, name, false)?
            {
                return self.get_symbol_location(&extended, name);
            }
        }
        let is_elsewhere = module
            .instances
            .iter()
            .any(|instance| instance.name.as_deref() == Some(name))
            || module
                .theorems
                .iter()
                .filter_map(|theorem| theorem.name.as_deref())
                .chain(
                    module
                        .assumptions
                        .iter()
                        .filter_map(|assumption| assumption.name.as_deref()),
                )
                .any(|fact| fact == name)
            || self.lookup(module, name, true)?.is_some();
        if is_elsewhere {
            return Err(not_yet(
                "a field named like an instance's definition or a fact",
            ));
        }
        Ok(None)
    }

    /// `Linter.lintRecords`: the warnings for the records of a top-level module.
    pub fn lint_module(&self, name: &str) -> Result<Vec<SanyError>> {
        let module = self.get_module(name)?;
        let records = get_records(&module, &self.tables)?;
        if records.is_empty() {
            return Ok(Vec::new());
        }
        let mut extended = Vec::new();
        self.get_extended(&module, &mut extended)?;
        let mut all_records: Vec<(RecordNode, Rc<Module>)> = Vec::new();
        for item in &extended {
            for record in get_records(item, &self.tables)? {
                all_records.push((record, item.clone()));
            }
        }
        for record in get_records(&module, &self.tables)? {
            all_records.push((record, module.clone()));
        }
        let mut warnings = Vec::new();
        for record in &records {
            // The linter checks the fields of every record with the same domain, which includes
            // the record itself.
            let mut is_exempt = false;
            for (other, owner) in &all_records {
                if !is_same_domain(other, record) {
                    continue;
                }
                for field in &other.fields {
                    let mut visit = Visit {
                        linter: self,
                        visited: FastSet::default(),
                    };
                    if visit.expression(&field.value, owner, &other.locals)? {
                        is_exempt = true;
                        break;
                    }
                }
                if is_exempt {
                    break;
                }
            }
            if is_exempt {
                continue;
            }
            for field in &record.fields {
                let Some(located) = self.get_symbol_location(&module, &field.name)? else {
                    continue;
                };
                let Some(range) = &field.location.range else {
                    return Err(not_yet("a field without a range"));
                };
                let name = &field.name;
                warnings.push(SanyError {
                    location: format_range(range),
                    message: format!(
                        "The field name \"{name}\" in the record constructor is identical to the existing definition or declaration\nnamed {name}, located at {located}.\nThe field in the record will not take the value of the {name} definition or declaration.\nIn TLA+, field names in records are strings, regardless of any similarly named declarations or definitions.\nTherefore, DOMAIN [{name} |-> ...] = {{\"{name}\"}} holds true."
                    ),
                });
            }
        }
        Ok(warnings)
    }
}
