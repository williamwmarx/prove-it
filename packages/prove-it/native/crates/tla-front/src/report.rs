//! What SANY prints while TLC runs it on a spec, as `getSanyReport` in `src/sany/report.ts` does:
//! the file it parses each module from, each module it analyzes and each module it lints.

use std::path::Path;
use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::{Assumed, Expr, ExpressionKind, Module, ModuleUnit, Statement};
use crate::config::parse_config;
use crate::environment::{EnvironmentOptions, create_environment};
use crate::errors::FrontError;
use crate::get_standard_module;
use crate::hash::{FastMap, FastSet};
use crate::parser::{extract_module, parse_sany_module};

type Result<T> = std::result::Result<T, Stop>;

/// Why SANY stops: a fatal error of its parsing phase, which it prints, or what the front end
/// doesn't cover yet.
enum Stop {
    Fatal {
        location: Option<Rc<str>>,
        message: String,
    },
    Front(FrontError),
}

impl From<FrontError> for Stop {
    fn from(error: FrontError) -> Stop {
        Stop::Front(error)
    }
}

fn not_yet(reason: &str) -> Stop {
    Stop::Front(FrontError::NotYet(reason.to_owned()))
}

/// Where SANY reads a module from, as `SanyModuleOrigin`: a file of its own, the file of the root
/// module, or the files of its standard modules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleOrigin {
    File,
    RootFile,
    Standard,
}

/// How the run reads and names the spec's modules.
pub struct ReportOptions<'a> {
    pub version: TlcVersion,
    /// The file name TLC gives SANY, which SANY prints in its fatal errors, or else the root
    /// module's name.
    pub file_name: Option<&'a str>,
    /// A module's text from a file of its own, beside the spec or in the library.
    pub load_module: &'a dyn Fn(&str) -> Option<String>,
    /// The file TLC prints that it parses a module from, as `createFileDescriber` names it.
    pub describe_file: &'a dyn Fn(&str, ModuleOrigin) -> String,
}

/// tla2sany.semantic.StandardModules: SANY lints the modules other than these.
const UNLINTED_MODULES: &[&str] = &[
    "FiniteSets",
    "Sequences",
    "Bags",
    "Naturals",
    "Integers",
    "Reals",
    "RealTime",
    "Randomization",
    "TLC",
];

/// The modules a file extends and instantiates, as SANY's ParseUnit collects them, and the module
/// of that file which first names each.
#[derive(Default)]
struct Dependencies {
    extendees: Vec<Rc<str>>,
    instancees: Vec<Rc<str>>,
    importers: FastMap<Rc<str>, Rc<str>>,
}

fn get_let_instances(expression: &Expr, found: &mut Vec<Rc<str>>) {
    if let ExpressionKind::Let {
        instances: Some(instances),
        ..
    } = &expression.kind
    {
        found.extend(instances.iter().map(|instance| instance.module.clone()));
    }
    expression
        .children()
        .iter()
        .for_each(|child| get_let_instances(child, found));
}

fn get_assumed_instances(assumed: &Assumed, found: &mut Vec<Rc<str>>) {
    match assumed {
        Assumed::Expression(expression) => get_let_instances(expression, found),
        Assumed::NewSymbol(_) => {}
        Assumed::AssumeProve(assume_prove) => {
            assume_prove
                .assumptions
                .iter()
                .for_each(|assumption| get_assumed_instances(assumption, found));
            get_let_instances(&assume_prove.conclusion, found);
        }
    }
}

/// SpecObj.instanceResolvesToInternalModule: SANY finds a module that the root module
/// instantiates among its inner modules only when its first top-level INSTANCE of the module
/// follows the inner module.
fn is_internal_instance(module: &Module, name: &str) -> bool {
    let mut seen: FastSet<&str> = FastSet::default();
    for unit in &module.units {
        match unit {
            ModuleUnit::Module(inner) => {
                seen.insert(&inner.name);
            }
            ModuleUnit::Instance(instance) if &*instance.module == name => {
                return seen.contains(name);
            }
            _ => {}
        }
    }
    false
}

/// `getDependencies`: ParseUnit.calculateContextWithinParseUnit lets a module know the inner
/// modules defined before it in the modules enclosing it and the inner modules of the modules it
/// extends, but not itself.
fn get_dependencies(module: &Rc<Module>) -> Dependencies {
    fn visit(
        current: &Rc<Module>,
        is_root: bool,
        context: &FastMap<Rc<str>, Rc<Module>>,
        dependencies: &mut Dependencies,
    ) {
        let is_external = |name: &Rc<str>| !context.contains_key(name);
        let mut add_imports = |names: Vec<Rc<str>>, is_extension: bool| {
            for name in names {
                dependencies
                    .importers
                    .entry(name.clone())
                    .or_insert_with(|| current.name.clone());
                if is_extension {
                    dependencies.extendees.push(name);
                } else {
                    dependencies.instancees.push(name);
                }
            }
        };
        add_imports(
            current
                .extends
                .iter()
                .filter(|name| is_external(name))
                .cloned()
                .collect(),
            true,
        );
        let mut instances = Vec::new();
        for unit in &current.units {
            match unit {
                ModuleUnit::Instance(instance) => instances.push(instance.module.clone()),
                ModuleUnit::Definition(definition) => {
                    get_let_instances(&definition.body, &mut instances)
                }
                ModuleUnit::Theorem(theorem) if is_root => match &theorem.statement {
                    Statement::Expression(expression) => {
                        get_let_instances(expression, &mut instances)
                    }
                    Statement::AssumeProve(assume_prove) => get_assumed_instances(
                        &Assumed::AssumeProve(assume_prove.clone()),
                        &mut instances,
                    ),
                },
                ModuleUnit::Assumption(assumption) if is_root => {
                    get_let_instances(&assumption.expression, &mut instances)
                }
                _ => {}
            }
        }
        add_imports(
            instances
                .into_iter()
                .filter(|name| is_external(name) && !is_internal_instance(current, name))
                .collect(),
            false,
        );
        let mut peers = context.clone();
        for inner in &current.modules {
            let mut inner_context = peers.clone();
            // ParseUnit.handleExtensions.
            let mut extenders: Vec<*const Module> = Vec::new();
            fn add_extended_inner_modules(
                extender: &Rc<Module>,
                extenders: &mut Vec<*const Module>,
                inner_context: &mut FastMap<Rc<str>, Rc<Module>>,
            ) {
                if extenders.contains(&Rc::as_ptr(extender)) {
                    return;
                }
                extenders.push(Rc::as_ptr(extender));
                for name in &extender.extends {
                    let Some(extendee) = inner_context.get(name).cloned() else {
                        continue;
                    };
                    for extendee_inner in &extendee.modules {
                        inner_context
                            .entry(extendee_inner.name.clone())
                            .or_insert_with(|| extendee_inner.clone());
                    }
                    add_extended_inner_modules(&extendee, extenders, inner_context);
                }
            }
            add_extended_inner_modules(inner, &mut extenders, &mut inner_context);
            visit(inner, false, &inner_context, dependencies);
            peers.insert(inner.name.clone(), inner.clone());
        }
    }
    let mut dependencies = Dependencies::default();
    visit(module, true, &FastMap::default(), &mut dependencies);
    dependencies
}

struct Loaded {
    module: Rc<Module>,
    dependencies: Rc<Dependencies>,
}

struct Loader<'a> {
    options: &'a ReportOptions<'a>,
    source: &'a str,
    modules: FastMap<Rc<str>, Loaded>,
    lines: Vec<String>,
}

impl Loader<'_> {
    fn get_dependencies(&self, name: &str) -> Rc<Dependencies> {
        self.modules[name].dependencies.clone()
    }

    /// `loadSource` in `getSanyReport` and in the generator: TLC prints the file of a module
    /// before SANY parses it.
    fn load(
        &mut self,
        name: &Rc<str>,
        text: Option<String>,
        origin: ModuleOrigin,
        importer: &Rc<str>,
    ) -> Result<()> {
        if self.modules.contains_key(name) {
            return Ok(());
        }
        let Some(text) = text else {
            return Err(Stop::Fatal {
                location: Some(importer.clone()),
                message: format!(
                    "Cannot find source file for module {name} imported in module {importer}."
                ),
            });
        };
        self.lines.push(format!(
            "Parsing file {}\n",
            (self.options.describe_file)(name, origin)
        ));
        // SANY validates the PlusCal of each module it loads.
        if text.contains("--algorithm") || text.contains("--fair") {
            return Err(not_yet("PlusCal"));
        }
        let module = parse_sany_module(&text, None, self.options.version)
            .map_err(|_| not_yet("SANY's parse errors"))?;
        if module.name != *name {
            return Err(Stop::Fatal {
                location: None,
                message: format!(
                    "File name '{name}' does not match the name '{}' of the top level module it contains.",
                    module.name
                ),
            });
        }
        let module = Rc::new(module);
        let dependencies = Rc::new(get_dependencies(&module));
        self.modules.insert(
            name.clone(),
            Loaded {
                module,
                dependencies,
            },
        );
        Ok(())
    }

    /// The text of a module other than the root module and where SANY reads it from.
    fn read(&self, name: &str) -> (Option<String>, ModuleOrigin) {
        if let Some(file) = (self.options.load_module)(name) {
            return (Some(file), ModuleOrigin::File);
        }
        // TLC 1.7.4's SANY reads a module only from a file of its own.
        let extracted = (self.options.version != TlcVersion::V1_7_4)
            .then(|| extract_module(self.source, name))
            .flatten();
        match extracted {
            Some(text) => (Some(text), ModuleOrigin::RootFile),
            None => (
                get_standard_module(name, self.options.version).map(str::to_owned),
                ModuleOrigin::Standard,
            ),
        }
    }

    /// SpecObj.loadSpec: SANY resolves the first unresolved name it finds from the root, every
    /// extended module before any instantiated one, each in the context of the module that names
    /// it.
    fn find_unresolved(
        &self,
        name: &Rc<str>,
        is_extension: bool,
        visited: &mut FastSet<Rc<str>>,
        resolutions: &FastSet<(Rc<str>, Rc<str>)>,
    ) -> Option<(Rc<str>, Rc<str>, Rc<str>)> {
        if !self.modules.contains_key(name) || !visited.insert(name.clone()) {
            return None;
        }
        let dependencies = self.get_dependencies(name);
        let is_resolved =
            |dependency: &Rc<str>| resolutions.contains(&(name.clone(), dependency.clone()));
        let names = if is_extension {
            &dependencies.extendees
        } else {
            &dependencies.instancees
        };
        if let Some(unresolved) = names.iter().find(|dependency| !is_resolved(dependency)) {
            let naming_module = dependencies
                .importers
                .get(unresolved)
                .cloned()
                .unwrap_or_else(|| name.clone());
            return Some((unresolved.clone(), name.clone(), naming_module));
        }
        dependencies
            .extendees
            .iter()
            .chain(&dependencies.instancees)
            .filter(|dependency| is_resolved(dependency))
            .find_map(|dependency| {
                self.find_unresolved(dependency, is_extension, visited, resolutions)
            })
    }

    /// `calculateDependencies`: SANY analyzes each module after the modules it extends and
    /// instantiates.
    fn get_analysis_order(
        &self,
        name: &Rc<str>,
        path: &mut Vec<Rc<str>>,
        visiting: &mut FastSet<Rc<str>>,
        order: &mut Vec<Rc<str>>,
    ) -> Result<()> {
        if let Some(start) = path.iter().position(|item| item == name) {
            let cycle: Vec<String> = path[start..]
                .iter()
                .chain([name])
                .map(|item| format!("{item}.tla"))
                .collect();
            return Err(Stop::Fatal {
                location: None,
                message: format!(
                    "Circular dependency among .tla files; dependency cycle is:\n\n  {}",
                    cycle.join(" --> ")
                ),
            });
        }
        if !visiting.insert(name.clone()) {
            return Ok(());
        }
        path.push(name.clone());
        let dependencies = self.get_dependencies(name);
        for dependency in dependencies
            .extendees
            .iter()
            .chain(&dependencies.instancees)
        {
            self.get_analysis_order(dependency, path, visiting, order)?;
        }
        path.pop();
        order.push(name.clone());
        Ok(())
    }
}

fn collect_field_names(expression: &Expr, names: &mut FastSet<Rc<str>>) {
    if let ExpressionKind::Record {
        is_set: false,
        fields,
    } = &expression.kind
    {
        names.extend(fields.iter().map(|field| field.name.clone()));
    }
    expression
        .children()
        .iter()
        .for_each(|child| collect_field_names(child, names));
}

fn collect_module_names(
    module: &Module,
    names: &mut FastSet<Rc<str>>,
    fields: &mut FastSet<Rc<str>>,
) {
    names.insert(module.name.clone());
    names.extend(
        module
            .constants
            .iter()
            .map(|declaration| declaration.name.clone()),
    );
    names.extend(
        module
            .variables
            .iter()
            .map(|declaration| declaration.name.clone()),
    );
    names.extend(
        module
            .definitions
            .iter()
            .map(|definition| definition.name.clone()),
    );
    names.extend(
        module
            .instances
            .iter()
            .filter_map(|instance| instance.name.clone()),
    );
    names.extend(
        module
            .assumptions
            .iter()
            .filter_map(|assumption| assumption.name.clone()),
    );
    names.extend(
        module
            .theorems
            .iter()
            .filter_map(|theorem| theorem.name.clone()),
    );
    for definition in &module.definitions {
        collect_field_names(&definition.body, fields);
    }
    for assumption in &module.assumptions {
        collect_field_names(&assumption.expression, fields);
    }
    for instance in &module.instances {
        for substitution in &instance.substitutions {
            collect_field_names(&substitution.expression, fields);
        }
    }
    for inner in &module.modules {
        collect_module_names(inner, names, fields);
    }
}

/// What SANY prints for the spec at `spec_path` while TLC runs it: when SANY accepts the spec
/// without a message, or stops at a fatal error other than a parse error. `NotYet` for SANY's
/// other messages, PlusCal and what SANY's linter could warn about.
pub fn get_sany_text(
    spec_path: &Path,
    options: &ReportOptions,
) -> std::result::Result<String, FrontError> {
    let root: Rc<str> = Rc::from(
        spec_path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .unwrap_or_default(),
    );
    let source = std::fs::read_to_string(spec_path)
        .map_err(|_| FrontError::NotYet("a spec without a file".to_owned()))?;
    let mut loader = Loader {
        options,
        source: &source,
        modules: FastMap::default(),
        lines: Vec::new(),
    };
    match write_sany_text(&mut loader, &root) {
        Ok(()) => Ok(loader.lines.concat()),
        Err(Stop::Front(error)) => Err(error),
        // TLC 1.7.4's SANY aborts with an AbortException instead.
        Err(Stop::Fatal { .. }) if options.version == TlcVersion::V1_7_4 => {
            Err(FrontError::NotYet("TLC 1.7.4's fatal errors".to_owned()))
        }
        Err(Stop::Fatal { location, message }) => {
            let fatal = format!(
                "{}\n\n{message}",
                location.map_or_else(
                    || "Unknown location".to_owned(),
                    |module| format!("In module {module}")
                )
            );
            let name = options.file_name.unwrap_or(&root);
            Ok(format!(
                "{}\nFatal errors while parsing TLA+ spec in file {name}\n\n{fatal}\n*** Errors: 1\n\n{fatal}\n\n\n\n",
                loader.lines.concat()
            ))
        }
    }
}

fn write_sany_text(loader: &mut Loader, root: &Rc<str>) -> Result<()> {
    let options = loader.options;
    let source = loader.source;
    let root = root.clone();
    loader.load(&root, Some(source.to_owned()), ModuleOrigin::File, &root)?;
    let mut resolutions: FastSet<(Rc<str>, Rc<str>)> = FastSet::default();
    loop {
        let next = [true, false].into_iter().find_map(|is_extension| {
            loader.find_unresolved(&root, is_extension, &mut FastSet::default(), &resolutions)
        });
        let Some((name, importer, naming_module)) = next else {
            break;
        };
        if !loader.modules.contains_key(&name) {
            let (text, origin) = loader.read(&name);
            loader.load(&name, text, origin, &naming_module)?;
        }
        resolutions.insert((importer, name));
    }
    let mut order = Vec::new();
    loader.get_analysis_order(&root, &mut Vec::new(), &mut FastSet::default(), &mut order)?;
    // SANY's messages come from linking, which reports what SANY's semantic analysis does.
    let config =
        parse_config("", options.version).map_err(|error| FrontError::Config(error.message))?;
    let environment = create_environment(&EnvironmentOptions {
        source,
        load_module: &|name| loader.read(name).0,
        config: &config,
        is_unconfigured: true,
        version: options.version,
        is_level_checked: true,
    })
    .map_err(|_| not_yet("SANY's semantic errors"))?;
    if !environment.printed.is_empty() {
        return Err(not_yet("SANY's warnings"));
    }
    for name in &order {
        loader
            .lines
            .push(format!("Semantic processing of module {name}\n"));
    }
    // SANY.frontEndLinting: TLC 1.7.4's SANY has no linter.
    if options.version != TlcVersion::V1_7_4 {
        let linted: Vec<&Rc<str>> = order
            .iter()
            .filter(|name| !UNLINTED_MODULES.contains(&&***name))
            .collect();
        let mut names: FastSet<Rc<str>> = FastSet::default();
        let mut fields: FastSet<Rc<str>> = FastSet::default();
        for loaded in loader.modules.values() {
            let mut ignored = FastSet::default();
            collect_module_names(&loaded.module, &mut names, &mut ignored);
        }
        for name in &linted {
            collect_module_names(
                &loader.modules[&***name].module,
                &mut FastSet::default(),
                &mut fields,
            );
        }
        if fields.iter().any(|field| names.contains(field)) {
            return Err(not_yet(
                "a record field named like a definition, which SANY's linter checks",
            ));
        }
        for name in linted {
            loader.lines.push(format!("Linting of module {name}\n"));
        }
    }
    Ok(())
}
