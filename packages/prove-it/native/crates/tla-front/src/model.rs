//! A model's IR from its spec and configuration, as the native binary reads it in place of the
//! TypeScript front end's.

use std::path::Path;
use std::rc::Rc;

use crate::TlcVersion;
use crate::config::parse_config;
use crate::dependencies::create_definition_facts;
use crate::environment::{EnvironmentOptions, create_environment};
use crate::errors::FrontError;
use crate::eval::Evaluator;
use crate::hash::FastMap;
use crate::lower::{Lowering, RankedTexts};
use crate::order::TlcOrder;
use crate::spec::{
    Properties, Specification, check_invariants, check_search_config, create_identifier,
    get_properties, get_specification,
};
use crate::values::ValueOrder;

/// What the model is checked with besides its files.
pub struct ModelOptions<'a> {
    /// The directories of the modules a spec reads that aren't beside it, such as the community
    /// modules, in the order TLC searches them (`-DTLA-Library`).
    pub libraries: &'a [&'a Path],
    /// The TLC version the run asks for, or none for the default, master's.
    pub version: Option<TlcVersion>,
    /// Whether TLC prints its warnings, which `-nowarning` turns off.
    pub is_warning_enabled: bool,
}

/// A module's text from the spec's directory, or else the first library's that has it.
pub fn load_module(spec_path: &Path, libraries: &[&Path], name: &str) -> Option<String> {
    let directory = spec_path.parent().unwrap_or(Path::new("."));
    let file = format!("{name}.tla");
    std::iter::once(directory)
        .chain(libraries.iter().copied())
        .find_map(|directory| std::fs::read_to_string(directory.join(&file)).ok())
}

/// The encoded IR of the model the configuration describes, without TLC's actions, which the
/// engine splits, or `NotYet` for what the front end doesn't lower yet.
pub fn lower_model(
    spec_path: &Path,
    config_text: &str,
    options: &ModelOptions,
) -> Result<Vec<u8>, FrontError> {
    let version = options.version.unwrap_or(TlcVersion::Master);
    let source = std::fs::read_to_string(spec_path)
        .map_err(|error| FrontError::Config(format!("{}: {error}", spec_path.display())))?;
    let load = |name: &str| load_module(spec_path, options.libraries, name);
    let config =
        parse_config(config_text, version).map_err(|error| FrontError::Config(error.message))?;
    // SANY's errors come from linking, before TLC's orders parse the modules again.
    let environment = create_environment(&EnvironmentOptions {
        source: &source,
        load_module: &load,
        config: &config,
        is_unconfigured: false,
        version,
        is_level_checked: false,
    })?;
    let order = TlcOrder::new(&source, &load, version)?;
    let texts: Vec<Rc<str>> = order
        .get_string_order(&config)?
        .iter()
        .map(|text| Rc::from(text.as_str()))
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
        check_invariants(&config, &environment, &facts, &evaluator)?;
        let specification =
            get_specification(&config, &environment, &facts, version, Some(&evaluator))?;
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
            },
        );
        lowering.evaluator = Some(&evaluator);
        let version_text = options.version.map(|version| match version {
            TlcVersion::V1_7_4 => "1.7.4",
            TlcVersion::Master => "master",
        });
        // `createSearch`'s checks of the configuration.
        let is_checking_behaviors = !config.invariants.is_empty()
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
            lowering.write_model(
                &config,
                &specification,
                &properties,
                options.is_warning_enabled,
                version_text,
                tlc_order,
            )?
        };
        Ok(tla_ir::encode(&lowering.finish(model)?))
    })();
    // TLC stops on a constant predicate the engine checks at startup before what follows it, so
    // the front end can't report what follows.
    match lowered {
        Err(error) if evaluator.is_deferring() && !matches!(error, FrontError::NotYet(_)) => Err(
            FrontError::NotYet("an error after a constant predicate the engine checks".to_owned()),
        ),
        lowered => lowered,
    }
}
