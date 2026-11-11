//! A model's IR from its spec and configuration, as the native binary reads it in place of the
//! TypeScript front end's.

use std::path::Path;
use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::SourceRange;
use crate::config::parse_config;
use crate::dependencies::create_definition_facts;
use crate::describe::{Description, Part, UNNAMED_ACTION, describe};
use crate::environment::{EnvironmentOptions, create_environment};
use crate::errors::{FrontError, format_range};
use crate::eval::Evaluator;
use crate::hash::{FastMap, FastSet};
use crate::lower::{Lowering, RankedTexts};
use crate::order::{TlcOrder, get_checker_strings, get_unique};
use crate::spec::{
    Properties, Specification, check_invariants, check_search_config, create_identifier,
    get_properties, get_specification,
};
use crate::values::ValueOrder;

/// The module TLC adds to the root module's EXTENDS where it records the trace for its trace
/// exploration spec, for the post condition that writes it.
pub const TRACE_MODULE: &str = "_TLCTrace";

/// What the model is checked with besides its files.
pub struct ModelOptions<'a> {
    /// The directories of the modules a spec reads that aren't beside it, such as the community
    /// modules, in the order TLC searches them (`-DTLA-Library`).
    pub libraries: &'a [&'a Path],
    /// The TLC version the run asks for, or none for the default, master's.
    pub version: Option<TlcVersion>,
    /// Whether TLC prints its warnings, which `-nowarning` turns off.
    pub is_warning_enabled: bool,
    /// Whether the IR holds TLCGet("spec") where an expression reads it, which the native
    /// binary checks the model with, as it holds TLC's actions; the TypeScript front end's model
    /// lowers neither.
    pub is_spec_described: bool,
    /// The seed TLC seeds its generator with, which `-seed` gives.
    pub random_seed: u64,
    /// The modules of the post conditions TLC adds to the root module's EXTENDS, in its order
    /// (`ParameterizedSpecObj`): `-dumpTrace`'s, and `_TLCTrace` where TLC records the trace for
    /// its trace exploration spec, its default. SANY loads them with the spec, which interns their
    /// strings, and each loads Integers, whose Java methods TLC then loads over Naturals'.
    pub root_extendees: &'a [&'a str],
}

/// A module's text from the spec's directory, or else the first library's that has it.
pub fn load_module(spec_path: &Path, libraries: &[&Path], name: &str) -> Option<String> {
    let directory = spec_path.parent().unwrap_or(Path::new("."));
    let file = format!("{name}.tla");
    std::iter::once(directory)
        .chain(libraries.iter().copied())
        .find_map(|directory| std::fs::read_to_string(directory.join(&file)).ok())
}

/// A message TLC prints itself as it starts, once it has computed the constant definitions and
/// before it checks the assumptions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StartupMessage {
    pub code: u32,
    pub is_warning: bool,
    pub text: String,
    /// The position among the IR's startup predicates of the invariant TLC warns about only where
    /// the value the engine computes for it at startup is TRUE; none for a message TLC prints
    /// whatever the startup computes.
    pub predicate: Option<usize>,
}

/// A model's IR, and what TLC prints as it starts the model besides SANY's report and what the
/// startup's Print and PrintT print.
pub struct LoweredModel {
    pub ir: Vec<u8>,
    /// The messages, or why the front end doesn't know them yet.
    pub startup_messages: Result<Vec<StartupMessage>, String>,
    /// What TLC prints of the Java overrides it loads, right after `Starting...`, before it
    /// computes the constant definitions.
    pub override_messages: Vec<StartupMessage>,
    /// How a simulation labels an initial state, as `TLCStateInfo` labels the last of TLC's
    /// initial predicates (`initPredVec`): `Init line 4, col 9 to line 4, col 13 of module M`, or
    /// `Initial predicate` and where an unnamed one is written. None where the front end can't
    /// tell.
    pub initial_label: Option<String>,
}

/// The encoded IR of the model the configuration describes, without TLC's actions, which the
/// engine splits, or `NotYet` for what the front end doesn't lower yet.
pub fn lower_model(
    spec_path: &Path,
    config_text: &str,
    options: &ModelOptions,
) -> Result<Vec<u8>, FrontError> {
    lower_front(spec_path, config_text, options).map(|lowered| lowered.ir)
}

/// The model's IR, with what TLC prints itself as it starts: `createSearch`'s warnings about the
/// invariants and properties, then `createLivenessChecker`'s, in `printCheckProgress`'s words.
pub fn lower_front(
    spec_path: &Path,
    config_text: &str,
    options: &ModelOptions,
) -> Result<LoweredModel, FrontError> {
    with_files(spec_path, options, |sources| {
        lower_ranked(sources, config_text, options, &[]).map(|(lowered, ..)| lowered)
    })
}

/// What a model is lowered from: the root module's text, the text of each other module by its
/// name, and the Java override TLC loads for a module, by its name (`loadClass`), from the spec's
/// directory, which TLC names the override by.
pub struct ModelSources<'a> {
    pub source: &'a str,
    pub directory: &'a Path,
    pub load_module: &'a dyn Fn(&str) -> Option<String>,
    pub load_class: &'a dyn Fn(&str) -> Option<Vec<u8>>,
}

/// The model's sources from the file system: the spec's file, the modules beside it or in the
/// libraries, and the classes beside it.
fn with_files<T>(
    spec_path: &Path,
    options: &ModelOptions,
    lower: impl FnOnce(&ModelSources) -> Result<T, FrontError>,
) -> Result<T, FrontError> {
    let source = std::fs::read_to_string(spec_path)
        .map_err(|error| FrontError::Config(format!("{}: {error}", spec_path.display())))?;
    let directory = spec_path.parent().unwrap_or(Path::new("."));
    lower(&ModelSources {
        source: &source,
        directory,
        load_module: &|name| load_module(spec_path, options.libraries, name),
        load_class: &|name| std::fs::read(directory.join(format!("{name}.class"))).ok(),
    })
}

/// What finds the texts TLC interns as it computes the constant definitions an IR holds, given
/// their indexes in TLC's order and how many of the IR's ranked texts TLC interned before.
pub type StartupTexts = dyn Fn(&tla_ir::Ir, &[tla_ir::Index], usize) -> Vec<Box<[u16]>>;

/// The model as `lower_front` lowers it, with the strings TLC makes as it computes the constant
/// definitions ranked after the spec's, as `check.ts` lowers its IR once it has computed them.
/// `get_startup_texts` finds them in the IR, given the indexes of the definitions TLC computes
/// as it starts, in its order; where it finds some, the model is lowered again with them ranked.
pub fn lower_front_ranking(
    spec_path: &Path,
    config_text: &str,
    options: &ModelOptions,
    get_startup_texts: &StartupTexts,
) -> Result<LoweredModel, FrontError> {
    with_files(spec_path, options, |sources| {
        lower_front_ranking_of(sources, config_text, options, get_startup_texts)
    })
}

/// `lower_front_ranking` of the model's sources as the caller holds them.
pub fn lower_front_ranking_of(
    sources: &ModelSources,
    config_text: &str,
    options: &ModelOptions,
    get_startup_texts: &StartupTexts,
) -> Result<LoweredModel, FrontError> {
    let (lowered, startup, interned) = lower_ranked(sources, config_text, options, &[])?;
    let Ok(ir) = tla_ir::decode(&lowered.ir) else {
        return Ok(lowered);
    };
    let startup_texts = get_startup_texts(&ir, &startup, interned);
    if startup_texts.is_empty() {
        return Ok(lowered);
    }
    lower_ranked(sources, config_text, options, &startup_texts).map(|(lowered, ..)| lowered)
}

fn lower_ranked(
    sources: &ModelSources,
    config_text: &str,
    options: &ModelOptions,
    startup_texts: &[Box<[u16]>],
) -> Result<(LoweredModel, Vec<tla_ir::Index>, usize), FrontError> {
    let version = options.version.unwrap_or(TlcVersion::Master);
    let source = sources.source;
    let load = sources.load_module;
    let load_class = sources.load_class;
    let config = parse_config(config_text, version).map_err(|error| match error.unworded {
        Some(reason) => FrontError::NotYet(reason.to_owned()),
        None => FrontError::Config(error.message),
    })?;
    // SANY's errors come from linking, before TLC's orders parse the modules again.
    let mut environment = create_environment(&EnvironmentOptions {
        source,
        load_module: load,
        config: &config,
        is_unconfigured: false,
        version,
        is_level_checked: false,
        load_class: Some(load_class),
    })?;
    // TLC loads Integers' methods over Naturals' once Integers is anywhere in the parsed closure.
    // Every module a root extendee can be today (`_TLCTrace` and the -dumpTrace modules) reaches
    // it through TLCExt, so any root extendee loads them; one that doesn't would need its closure.
    if !options.root_extendees.is_empty() {
        for builtin in environment.builtins.values_mut() {
            builtin.flags &=
                !(tla_ir::Builtin::NATURALS_GEQ | tla_ir::Builtin::NATURALS_METHOD) as u32;
        }
    }
    let order = TlcOrder::new(source, load, version)?.with_root_extendees(options.root_extendees);
    // TLC computes the constant definitions after SANY and before it builds its checker.
    let sany = order.get_sany_string_order(&config)?;
    let decoded: Vec<Option<String>> = startup_texts
        .iter()
        .map(|units| String::from_utf16(units).ok())
        .collect();
    // A text with a lone surrogate, which a `str` can't hold, as `Tail("😀a")` makes, ranks by a
    // name of its own and keeps its units for the IR's wide texts. The name is U+FFFF, as many
    // times as it takes to be no text the front ranks, then the units in hex.
    let taken: FastSet<&str> = sany
        .iter()
        .chain(decoded.iter().flatten())
        .map(String::as_str)
        .chain(get_checker_strings(&config))
        .collect();
    let mut wide: FastMap<Rc<str>, Box<[u16]>> = FastMap::default();
    let startup: Vec<String> = decoded
        .iter()
        .zip(startup_texts)
        .map(|(text, units)| {
            text.clone().unwrap_or_else(|| {
                let hex: String = units.iter().map(|unit| format!("{unit:04x}")).collect();
                let name = (1..)
                    .map(|count| format!("{}{hex}", "\u{FFFF}".repeat(count)))
                    .find(|name| !taken.contains(name.as_str()))
                    .expect("a name no text takes");
                wide.insert(Rc::from(name.as_str()), units.clone());
                name
            })
        })
        .collect();
    let texts: Vec<Rc<str>> = get_unique(
        sany.iter()
            .map(String::as_str)
            .chain(startup.iter().map(String::as_str))
            .chain(get_checker_strings(&config)),
    )
    .into_iter()
    .map(Rc::from)
    .collect();
    let variable_order = order.get_declaration_order(true)?;
    let facts = create_definition_facts(&environment);
    let ranks: FastMap<Rc<str>, u32> = texts
        .iter()
        .enumerate()
        .map(|(rank, text)| (text.clone(), rank as u32))
        .collect();
    let evaluator = Evaluator::new(&environment, ValueOrder { ranks: &ranks }, version, true);
    let lowered = (|| {
        let constant_invariants = check_invariants(
            &config,
            &environment,
            &facts,
            &evaluator,
            options.is_warning_enabled,
        )?;
        // TLC reads the specification after it warns about the invariants.
        let specification =
            get_specification(&config, &environment, &facts, version, Some(&evaluator)).map_err(
                |error| match (error, &constant_invariants) {
                    (error @ FrontError::Config(_), Some(names))
                        if options.is_warning_enabled && !names.is_empty() =>
                    {
                        FrontError::Warned(get_constant_invariant_warnings(names), Box::new(error))
                    }
                    (error, _) => error,
                },
            )?;
        let properties = get_properties(&config, &environment, &facts, version, Some(&evaluator))?;
        // `getTlcOrder`: the variables in TLC's order of declarations.
        let position = |index: &i32| {
            let variable = &environment.variables[*index as usize];
            variable_order
                .iter()
                .position(|name| name == variable)
                .unwrap_or(environment.variables.len())
        };
        let mut tlc_order: Vec<i32> = (0..environment.variables.len() as i32).collect();
        tlc_order.sort_by_key(position);
        let mut lowering = Lowering::new(
            &environment,
            RankedTexts {
                texts: &texts,
                ranks: ranks.clone(),
                wide: &wide,
            },
        );
        lowering.evaluator = Some(&evaluator);
        lowering.random_seed = options.random_seed;
        let version_text = options.version.map(|version| match version {
            TlcVersion::V1_7_4 => "1.7.4",
            TlcVersion::Master => "master",
        });
        // `processSpec`'s checks of the configuration, which count the invariants it keeps: not
        // those that are TRUE constants.
        let is_invariant_kept = match &constant_invariants {
            Some(constant_true) => config
                .invariants
                .iter()
                .any(|name| !constant_true.iter().any(|constant| **constant == **name)),
            None => !config.invariants.is_empty(),
        };
        let is_checking_behaviors = is_invariant_kept
            || !properties.invariants.is_empty()
            || !properties.action_properties.is_empty()
            || !properties.liveness.is_empty();
        if specification.init.is_none()
            && (is_checking_behaviors
                || !properties.initial_predicates.is_empty()
                || !environment.variables.is_empty())
        {
            return Err(match version {
                TlcVersion::V1_7_4 => FrontError::NotYet("TLC 1.7.4's missing Init".to_owned()),
                TlcVersion::Master => FrontError::Config(
                    "The configuration file did not specify the initial state predicate."
                        .to_owned(),
                ),
            });
        }
        if specification.next.is_none() && is_checking_behaviors {
            return Err(FrontError::Config(
                "The configuration file did not specify the next state predicate.".to_owned(),
            ));
        }
        check_search_config(&config, &environment, &facts, &evaluator)?;
        // TLC searches no states of a spec without variables, which `check.ts` lowers with FALSE for
        // Init and Next.
        let model = if environment.variables.is_empty() {
            let no_behavior = Some(create_identifier("FALSE"));
            let constant = Specification {
                init: no_behavior.clone(),
                next: no_behavior,
                scope: None,
                temporals: Vec::new(),
            };
            lowering.write_model(
                &config,
                &constant,
                &Properties::default(),
                options.is_warning_enabled,
                version_text,
                Vec::new(),
            )?
        } else {
            lowering
                .write_model(
                    &config,
                    &specification,
                    &properties,
                    options.is_warning_enabled,
                    version_text,
                    tlc_order,
                )
                // TLC warns about the invariants and the properties as it processes the spec,
                // before it starts the liveness checker.
                .map_err(|error| match error {
                    FrontError::Warned(warnings, error) if options.is_warning_enabled => {
                        FrontError::Warned(
                            get_search_warnings(
                                &constant_invariants
                                    .iter()
                                    .flatten()
                                    .map(|name| (name.clone(), None))
                                    .collect::<Vec<_>>(),
                                &properties.state_level,
                            )
                            .into_iter()
                            .chain(warnings)
                            .collect(),
                            error,
                        )
                    }
                    error => error,
                })?
        };
        let branches = lowering.branches;
        let (ir, startup) = lowering.finish_indexing(model)?;
        // TLCGet("spec"), where an expression reads it; where the front end can't describe the
        // specification, the engine stops where TLC would read it.
        let description = describe(&config, &environment, &facts, &evaluator).ok();
        // TLC places a definition an INSTANCE with substitutions copies at the INSTANCE.
        let initial_label = description.as_ref().and_then(|description| {
            let init = description.inits.last()?;
            let location = environment
                .instance_actions
                .values()
                .find(|action| action.name == init.name)
                .map_or(&init.location, |action| &action.location);
            let range = format_range(location.range.as_ref()?);
            Some(if &*init.name == UNNAMED_ACTION {
                format!("Initial predicate {range}")
            } else {
                format!("{} {range}", init.name)
            })
        });
        let ir = match description {
            Some(description) if options.is_spec_described && reads_spec(&ir) => {
                tla_trace::add_spec(&ir, &to_spec_description(&ir, description)).unwrap_or(ir)
            }
            _ => ir,
        };
        // Under -nowarning TLC prints none of its warnings.
        let (constant_invariants, state_level) = if options.is_warning_enabled {
            (
                get_constant_invariants(&config, &environment, &facts),
                &properties.state_level[..],
            )
        } else {
            (Vec::new(), &[][..])
        };
        let startup_messages = get_startup_messages(
            &config,
            &constant_invariants,
            state_level,
            branches,
            version,
            options.is_warning_enabled,
        );
        let override_messages = get_override_messages(&environment, sources.directory)
            .map(|messages| {
                // -nowarning drops a method that matches no operator.
                messages
                    .into_iter()
                    .filter(|message| options.is_warning_enabled || !message.is_warning)
                    .collect::<Vec<_>>()
            })
            .and_then(|messages| {
                // TLC lists the methods in an order that depends on the JVM.
                if messages.len() > 1 {
                    return Err("the Java overrides TLC lists in the JVM's order".to_owned());
                }
                Ok(messages)
            });
        let (startup_messages, override_messages) = match override_messages {
            Ok(messages) => (startup_messages, messages),
            Err(reason) => (Err(reason), Vec::new()),
        };
        Ok((
            LoweredModel {
                override_messages,
                ir: tla_ir::encode(&ir),
                startup_messages,
                initial_label,
            },
            startup,
        ))
    })();
    // TLC stops on a constant predicate the engine checks at startup before what follows it, so
    // the front end can't report what follows.
    match lowered {
        Err(error) if evaluator.is_deferring() && !matches!(error, FrontError::NotYet(_)) => Err(
            FrontError::NotYet("an error after a constant predicate the engine checks".to_owned()),
        ),
        lowered => lowered.map(|(lowered, startup)| (lowered, startup, sany.len())),
    }
}

// `printCheckProgress`'s report of each method of a Java class that overrides a module, which
// names the class file by its URL (`Class#getResource`).
fn get_override_messages(
    environment: &crate::environment::Environment,
    directory: &Path,
) -> Result<Vec<StartupMessage>, String> {
    environment
        .java_overrides
        .iter()
        .map(|java_override| {
            let class = directory.join(format!("{}.class", java_override.module));
            // WebAssembly has no working directory, and `is_absolute` is false there for any path,
            // so a path from the root stays as it is.
            let is_absolute =
                class.is_absolute() || cfg!(target_arch = "wasm32") && class.has_root();
            let path = if is_absolute {
                class
            } else {
                std::path::absolute(class).map_err(|error| error.to_string())?
            };
            let path = path.to_str().unwrap_or_default();
            // `pathToFileURL` escapes what a URL can't hold, which the front end doesn't follow.
            let is_plain = !path.is_empty()
                && path.chars().all(|character| {
                    character.is_ascii_alphanumeric() || "/._-".contains(character)
                });
            if !is_plain {
                return Err("the URL of a Java class whose path a URL escapes".to_owned());
            }
            Ok(StartupMessage {
                code: if java_override.is_matched { 2168 } else { 2400 },
                is_warning: !java_override.is_matched,
                predicate: None,
                text: format!(
                    "{} {} operator override from file:{path} with signature: <Java Method: {}>.",
                    if java_override.is_matched {
                        "Loading"
                    } else {
                        "Failed to match"
                    },
                    java_override.operator,
                    java_override.signature
                ),
            })
        })
        .collect()
}

// What TLC prints as it starts after the constant definitions: `createSearch`'s warnings, in the
// order it makes them, then `createLivenessChecker`'s (`printCheckProgress`). The printer adds
// the hint after TLC's first warning, drops a warning it printed already, and, under -nowarning,
// every warning (`createMessagePrinter`); the front end gives no warnings under -nowarning.
fn get_startup_messages(
    config: &crate::config::ModelConfig,
    constant_invariants: &[(Rc<str>, Option<usize>)],
    state_level_properties: &[Rc<str>],
    branches: Option<usize>,
    version: TlcVersion,
    is_warning_enabled: bool,
) -> Result<Vec<StartupMessage>, String> {
    if version == TlcVersion::V1_7_4 {
        return Err("what TLC 1.7.4 prints as it starts".to_owned());
    }
    let mut messages = get_search_warnings(constant_invariants, state_level_properties);
    // TLC warns about a symmetry set too small as it computes the symmetry, which the engine does
    // between the constant definitions and these warnings' place in TLC's order: unchecked yet.
    if config.symmetry.is_some() && !messages.is_empty() {
        return Err("warnings about the invariants or properties with a symmetry".to_owned());
    }
    if let Some(branches) = branches {
        if config.symmetry.is_some() && is_warning_enabled {
            messages.push(get_liveness_symmetry_warning());
        }
        messages.push(StartupMessage {
            code: 2212,
            is_warning: false,
            predicate: None,
            text: format!(
                "Implied-temporal checking--satisfiability problem has {branches} branches."
            ),
        });
    }
    Ok(messages)
}

// The invariants TLC may warn are constants that are TRUE (`processConfigInvariants`), in the
// configuration's order: each the configuration gives TRUE, and each the engine's startup
// computes, with its position among the IR's startup predicates.
fn get_constant_invariants(
    config: &crate::config::ModelConfig,
    environment: &crate::environment::Environment,
    facts: &crate::dependencies::DefinitionFacts,
) -> Vec<(Rc<str>, Option<usize>)> {
    // The invariants come first among the startup predicates, before the conjuncts of the
    // specification.
    let predicates = crate::spec::get_constant_predicates(config, environment, facts, &[]);
    config
        .invariants
        .iter()
        .filter_map(|name| {
            let predicate = predicates
                .iter()
                .position(|(_, kind, predicate, _)| *kind == "invariant" && predicate == name);
            let is_given = environment.constants.contains_key(name.as_str());
            // TLC holds an invariant the configuration substitutes for as the definition it names,
            // and doesn't warn of it.
            let is_substituted = environment.substitutions.contains_key(name.as_str());
            ((is_given || predicate.is_some()) && !is_substituted)
                .then(|| (Rc::from(name.as_str()), predicate))
        })
        .collect()
}

/// TLC's warnings about invariants that are TRUE constants, by name.
pub(crate) fn get_constant_invariant_warnings(names: &[Rc<str>]) -> Vec<StartupMessage> {
    let names: Vec<_> = names.iter().map(|name| (name.clone(), None)).collect();
    get_search_warnings(&names, &[])
}

// `createSearch`'s warnings about the invariants and the properties.
fn get_search_warnings(
    constant_invariants: &[(Rc<str>, Option<usize>)],
    state_level_properties: &[Rc<str>],
) -> Vec<StartupMessage> {
    let warning = |code: u32, text: String| StartupMessage {
        code,
        is_warning: true,
        text,
        predicate: None,
    };
    constant_invariants
        .iter()
        .map(|(name, predicate)| StartupMessage { predicate: *predicate, ..warning(2149, format!("The invariant {name} is a constant-level formula (i.e., it contains no variables, primes, or temporal operators) and evaluates to TRUE. To assert constant-level formulas in your spec, use ASSUME ConstInv. If you optionally want to give the assumption a name, write ASSUME YourAssumption == ConstInv instead. See https://explain.tlapl.us/assumptions-and-invariants for additional details.")) })
        .chain(state_level_properties.iter().map(|name| warning(2255, format!("The formula {name} is a state-level formula, but it was used as a PROPERTY (or PROPERTIES), where a temporal formula is typically expected. State-level formulas used as PROPERTY or PROPERTIES are only checked in the initial state. To verify that the formula {name} holds in all states of every behavior, use INVARIANT {name} instead. Alternatively, applying the \"always\" temporal operator ([]) to the state-level formula {name} changes it into a temporal formula, asserting that {name} holds in all states of every behavior. See https://explain.tlapl.us/invariants-and-properties for additional details."))))
        .collect()
}

/// The warning TLC prints as it starts the liveness checker of a model with a symmetry
/// (`createLivenessChecker`).
pub fn get_liveness_symmetry_warning() -> StartupMessage {
    StartupMessage {
        code: 2279,
        is_warning: true,
        predicate: None,
        text: "Declaring symmetry during liveness checking is dangerous. It might cause TLC to miss violations of the stated liveness properties. Please check liveness without symmetry defined.".to_owned(),
    }
}

// Whether an expression of the IR applies TLC's TLCGet to "spec".
fn reads_spec(ir: &tla_ir::Ir) -> bool {
    ir.nodes.arena.iter().any(|node| match &node.kind {
        tla_ir::NodeKind::Apply { name, args } => {
            !name.is_local
                && matches!(name.resolution, tla_ir::Resolution::Builtin(index)
                    if &*ir.texts[ir.builtins[index as usize].name as usize] == "TLCGet")
                && args.first().is_some_and(|&arg| {
                    matches!(&ir.nodes.arena[arg as usize].kind,
                        tla_ir::NodeKind::String(text) if &*ir.texts[*text as usize] == "spec")
                })
        }
        _ => false,
    })
}

// The description with each part's range in the IR's texts.
fn to_spec_description(ir: &tla_ir::Ir, description: Description) -> tla_trace::SpecDescription {
    let range = |range: Option<&SourceRange>| {
        let range = range?;
        let module = ir.texts.iter().position(|text| **text == *range.module)?;
        Some(tla_ir::SourceRange {
            module: module as tla_ir::TextId,
            start_line: range.start.line as i32,
            start_column: range.start.column as i32,
            end_line: range.end.line as i32,
            end_column: range.end.column as i32,
        })
    };
    let parts = |parts: Vec<Part>| {
        parts
            .into_iter()
            .map(|part| tla_trace::Described {
                name: part.name.to_string(),
                range: range(part.location.range.as_ref()),
            })
            .collect()
    };
    tla_trace::SpecDescription {
        inits: parts(description.inits),
        temporals: parts(description.temporals),
        invariants: parts(description.invariants),
        implied_inits: parts(description.implied_inits),
        implied_actions: parts(description.implied_actions),
        implied_temporals: parts(description.implied_temporals),
        variables: parts(description.variables),
        action_constraints: parts(description.action_constraints),
        constraints: parts(description.constraints),
    }
}
