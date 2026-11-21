//! Configuration table objects and the global `Defns` entries which substitutions copy.
//! A receiver's attached value is distinct from the global entry after Java overrides.

use std::rc::Rc;

use crate::ast::{Declaration, Definition, Name};
use crate::config::ConfigValue;
use crate::environment::{Builtin, OperatorTable};
use crate::errors::FrontError;
use crate::hash::FastMap;
use crate::ordered_map::OrderedMap;
use crate::resolve::{Result, SymbolKind, Symbols};
use crate::values::ValueOrder;

/// Created when the linker installs a method from the packaged class's method registry under
/// a closed resolver namespace. Neither a builtin name nor its flags creates this object.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CallableClass {
    Method,
    Evaluating,
}

#[derive(Clone, Debug)]
pub(crate) struct PackagedMethod {
    pub module: Name,
    pub class: CallableClass,
    pub minimum_level: u8,
    pub provider: Name,
    pub method: Name,
    pub installation: Name,
    pub builtin: Builtin,
}

impl PackagedMethod {
    pub fn operators(module: &str) -> impl Iterator<Item = &str> {
        include_str!("tlc_callable_classes.tsv")
            .lines()
            .filter(|line| !line.starts_with('#'))
            .filter_map(move |line| {
                let mut fields = line.split('\t');
                (fields.next()? == module).then(|| fields.next()).flatten()
            })
    }

    pub fn registered(module: &str, builtin: Builtin) -> Option<Self> {
        let row = include_str!("tlc_callable_classes.tsv")
            .lines()
            .filter(|line| !line.starts_with('#'))
            .find_map(|line| {
                let fields: Vec<_> = line.split('\t').collect();
                (fields.len() == 8 && fields[0] == module && fields[1] == &*builtin.name)
                    .then_some(fields)
            })?;
        let class = match row[2] {
            "Method" => CallableClass::Method,
            "Evaluating" => CallableClass::Evaluating,
            _ => return None,
        };
        if row[7] == "Annotated" && row[6].parse::<usize>().ok()? != builtin.arity {
            return None;
        }
        Some(Self {
            module: Rc::from(module),
            class,
            minimum_level: row[3].parse().ok()?,
            provider: Rc::from(row[4]),
            method: Rc::from(row[5]),
            installation: Rc::from(row[7]),
            builtin,
        })
    }
}

/// The actual object a configuration phase puts in `Defns` or on a declared receiver.
#[derive(Clone, Debug)]
pub(crate) enum Object {
    Value(ConfigValue),
    Table(Rc<OperatorTable>),
    Method(PackagedMethod),
    OpDef {
        _header: Rc<Definition>,
        semantic_arity: usize,
    },
    Unknown,
}

/// Only explicit constructor and write events populate this model. Missing information is
/// unknown; it does not establish an empty ToolObject cell or a successfully initialized value.
#[derive(Default)]
pub(crate) struct TableObjects {
    pub defns: OrderedMap<Name, Object>,
    receivers: FastMap<usize, Object>,
    attachments: OrderedMap<Name, Rc<OperatorTable>>,
    initializers: Vec<Object>,
    pub method_aliases: OrderedMap<Name, PackagedMethod>,
    pub unknown_installations: Vec<(Name, Name)>,
    pub is_complete: bool,
    pub is_admitted: bool,
}

impl TableObjects {
    pub fn new(root_symbols: &Symbols, definitions: &OrderedMap<Name, Rc<Definition>>) -> Self {
        Self {
            // These are the root semantic OpDef names used by SpecProcessor's Defns dictionary.
            // A native resolution key only joins that binding to its modeled original header.
            defns: root_symbols
                .iter()
                .filter(|(_, symbol)| symbol.kind == SymbolKind::Definition)
                .map(|(name, symbol)| {
                    let object = definitions
                        .get(&symbol.key)
                        .map(|definition| Object::OpDef {
                            _header: definition.clone(),
                            semantic_arity: symbol.arity,
                        })
                        .unwrap_or(Object::Unknown);
                    (name.clone(), object)
                })
                .collect(),
            is_complete: true,
            ..Self::default()
        }
    }

    pub fn assign_value(&mut self, name: &Name, value: &ConfigValue) {
        self.defns
            .insert(name.clone(), Object::Value(value.clone()));
    }

    pub fn attach_table(&mut self, key: &Name, rows: &Rc<OperatorTable>, global: Option<&Name>) {
        self.attachments.insert(key.clone(), rows.clone());
        if let Some(name) = global {
            self.defns.insert(name.clone(), Object::Table(rows.clone()));
        }
    }

    pub fn install_method(&mut self, key: &Name, method: &PackagedMethod) {
        self.defns
            .insert(key.clone(), Object::Method(method.clone()));
    }

    pub fn unknown_global(&mut self, name: Name) {
        self.defns.insert(name, Object::Unknown);
    }

    pub fn register_declaration(&mut self, declaration: &Rc<Declaration>) {
        let object = self
            .defns
            .get(&declaration.name)
            .cloned()
            .unwrap_or(Object::Unknown);
        self.receivers
            .insert(Rc::as_ptr(declaration) as usize, object);
    }

    /// `processSpec` copies the current global entry, not a lookup through the target header.
    pub fn substitute(
        &mut self,
        receiver_key: &Name,
        global_name: &Name,
        target: &str,
        declaration: Option<&Rc<Declaration>>,
    ) {
        let object = self.defns.get(target).cloned().unwrap_or(Object::Unknown);
        if let Some(declaration) = declaration {
            self.receivers
                .insert(Rc::as_ptr(declaration) as usize, object.clone());
        }
        if let Object::Method(method) = &object
            && self.attachments.contains_key(target)
        {
            self.method_aliases
                .insert(receiver_key.clone(), method.clone());
        }
        if let Object::Table(rows) = &object {
            self.attachments.insert(receiver_key.clone(), rows.clone());
        }
        self.defns.insert(global_name.clone(), object);
    }

    /// The module participation decision is made from the actual linked modules, before an
    /// initializer event is recorded for a declared semantic receiver.
    pub fn initialize_declaration(&mut self, declaration: &Rc<Declaration>) {
        match self.receivers.get(&(Rc::as_ptr(declaration) as usize)) {
            Some(Object::Table(rows)) => {
                if !self
                    .initializers
                    .iter()
                    .any(|other| matches!(other, Object::Table(other) if Rc::ptr_eq(rows, other)))
                {
                    self.initializers.push(Object::Table(rows.clone()));
                }
            }
            Some(Object::Value(value)) => self.initializers.push(Object::Value(value.clone())),
            Some(Object::Method(method)) => {
                let _ = (
                    &method.module,
                    method.class,
                    method.minimum_level,
                    &method.provider,
                    &method.method,
                    &method.installation,
                );
            }
            Some(Object::OpDef { semantic_arity, .. }) => {
                // A nullary replacement evaluates its original semantic body and can change
                // subsequent startup objects. Native code-view parameter lists are not its arity.
                if *semantic_arity == 0 {
                    self.is_complete = false;
                }
            }
            Some(Object::Unknown) | None => self.is_complete = false,
        }
    }

    /// Before any startup effects, prove that every value of every initialized table can be
    /// normalized. An unsupported initializer is a global decline, including an unused table.
    pub fn admit(&mut self, order: &ValueOrder<'_>, closed: bool) -> Result<()> {
        if !closed || !self.is_complete || self.attachments.is_empty() {
            return Ok(());
        }
        fn normalized(value: &ConfigValue, order: &ValueOrder<'_>) -> Result<ConfigValue> {
            let value = match value {
                ConfigValue::Set(values) => ConfigValue::Set(
                    values
                        .iter()
                        .map(|value| normalized(value, order))
                        .collect::<Result<Vec<_>>>()?,
                ),
                ConfigValue::Record(fields) => ConfigValue::Record(
                    fields
                        .iter()
                        .map(|(name, value)| Ok((name.clone(), normalized(value, order)?)))
                        .collect::<Result<Vec<_>>>()?,
                ),
                value => value.clone(),
            };
            order.normalize(&value)
        }
        let check = |value| {
            normalized(value, order).map(|_| ()).map_err(|_| FrontError::NotYet(
            "an unsupported value initialized before a configuration operator table is evaluated".into()))
        };
        for object in &self.initializers {
            match object {
                Object::Table(rows) => {
                    for (arguments, result) in rows.iter() {
                        for value in arguments.iter().chain([result]) {
                            check(value)?;
                        }
                    }
                }
                Object::Value(value) => check(value)?,
                _ => unreachable!("only actual value constructor events initialize here"),
            }
        }
        self.is_admitted = self.is_complete;
        Ok(())
    }

    pub fn knows_table(&self, rows: &Rc<OperatorTable>) -> bool {
        self.is_admitted
            && self
                .attachments
                .values()
                .any(|other| Rc::ptr_eq(rows, other))
    }
}

#[cfg(test)]
mod table_tests {
    use crate::java_parent::tests::sha256;

    /// The value the table's header gives a key, which it names once.
    fn get_recorded(table: &'static str, key: &str) -> &'static str {
        let prefix = format!("# {key}: ");
        let mut values = table
            .lines()
            .filter_map(|line| line.strip_prefix(prefix.as_str()));
        let value = values.next().expect(key);
        assert!(values.next().is_none(), "{key}");
        value
    }

    /// `tlc_callable_classes.tsv` is the output of `scripts/tlc-overrides/TlcCallableClasses.java`
    /// run on the pinned jar (its header says how), and records the SHA-256 of that generator and
    /// of its rows: a change to either that isn't the other regenerated fails here.
    #[test]
    fn callable_classes_record_the_hashes_of_their_generator_and_rows() {
        let table = include_str!("tlc_callable_classes.tsv");
        let generator = include_bytes!("../../../../scripts/tlc-overrides/TlcCallableClasses.java");
        let rows: String = table
            .split_inclusive('\n')
            .filter(|line| !line.starts_with('#'))
            .collect();
        assert_eq!(
            sha256(generator),
            get_recorded(table, "generator_sha256"),
            "generator_sha256"
        );
        assert_eq!(
            sha256(rows.as_bytes()),
            get_recorded(table, "rows_sha256"),
            "rows_sha256"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TlcVersion;
    use crate::config::parse_config;
    use crate::environment::{EnvironmentOptions, link_environment};
    use crate::model::{ClassOrigin, JavaProfile, ModelOrigin};

    #[test]
    fn callable_class_and_minimum_level_come_from_actual_provider_descriptors() {
        let builtin = |name: &str, arity| Builtin {
            name: Rc::from(name),
            intrinsic: None,
            arity,
            flags: 1,
            table: None,
        };
        let method = PackagedMethod::registered("TLCExt", builtin("TLCGetOrDefault", 2)).unwrap();
        assert_eq!(
            (method.class, method.minimum_level),
            (CallableClass::Method, 0)
        );
        assert_eq!(&*method.provider, "tlc2.module.TLCExt");
        let evaluating = PackagedMethod::registered("TLC", builtin("TLCGet", 1)).unwrap();
        assert_eq!(
            (evaluating.class, evaluating.minimum_level),
            (CallableClass::Evaluating, 1)
        );
        assert_eq!(&*evaluating.provider, "tlc2.module.TLCGetSet");
        assert!(PackagedMethod::registered("Unknown", builtin("TLCGet", 1)).is_none());
    }

    #[test]
    fn closed_packaged_json_installs_known_global_lookup_objects() {
        let source =
            "---- MODULE M ----\nEXTENDS Integers,TLC,Json\nASSUME ToJson(1) = \"1\"\n====\n";
        let config = parse_config(
            "CONSTANT ToJson(2) = {1,\"a\"} ToJson(1) = \"1\"",
            TlcVersion::Master,
        )
        .unwrap();
        let origin = ModelOrigin::new(JavaProfile::Default, &|_| ClassOrigin::Absent);
        let environment = link_environment(&EnvironmentOptions {
            linked_extendees: &[],
            origin: Some(&origin),
            source,
            load_module: &|_| None,
            config: &config,
            is_unconfigured: false,
            version: TlcVersion::Master,
            is_level_checked: false,
            load_class: Some(&|_| None),
        })
        .unwrap();
        assert!(
            environment.operator_objects.is_complete,
            "{:?}",
            environment.operator_objects.unknown_installations
        );
        assert!(matches!(
            environment.operator_objects.defns.get("ToJson"),
            Some(Object::Method(PackagedMethod {
                class: CallableClass::Method,
                minimum_level: 0,
                ..
            }))
        ));
    }
}

#[cfg(test)]
mod global_dictionary_key_tests {
    use super::*;
    use crate::TlcVersion;
    use crate::config::parse_config;
    use crate::environment::{EnvironmentOptions, link_environment};
    use crate::model::{ClassOrigin, JavaProfile, ModelOrigin, ParentRuntime};

    #[test]
    fn imported_json_aliases_copy_global_methods_not_native_attachment_keys() {
        let pinned = crate::get_standard_module("Json", TlcVersion::Master).unwrap();
        let at = pinned.rfind("\n====").unwrap();
        let custom = format!(
            "{}\nFoo == PrintT(\"hidden-json\"){}",
            &pinned[..at],
            &pinned[at..]
        );
        for opcode in ["ToJson", "ToJsonArray", "ToJsonObject"] {
            let config = parse_config(
                &format!("CONSTANT {opcode}(1)={{1,\"a\"}} F <- {opcode}"),
                TlcVersion::Master,
            )
            .unwrap();
            let mut origin = ModelOrigin::new(JavaProfile::Default, &|_| ClassOrigin::Absent);
            origin.parent_runtime = ParentRuntime::ModeledTlcMasterJdk21;
            let environment = link_environment(&EnvironmentOptions {
                linked_extendees: &[],
                origin: Some(&origin),
                source: "---- MODULE M ----\nEXTENDS Integers,TLC,Json\nCONSTANT F(_)\nASSUME TRUE\n====\n",
                load_module: &|name| (name == "Json").then(|| custom.clone()),
                config: &config,
                is_unconfigured: false,
                version: TlcVersion::Master,
                is_level_checked: false,
                load_class: None,
            }).unwrap();
            assert!(matches!(
                environment.operator_objects.defns.get(opcode),
                Some(Object::Method(_))
            ));
            assert!(matches!(
                environment.operator_objects.defns.get("F"),
                Some(Object::Method(_))
            ));
            assert!(
                environment
                    .operator_objects
                    .initializers
                    .iter()
                    .all(|object| matches!(object, Object::Method(_)))
            );
            let native_key = environment
                .builtins
                .iter()
                .find(|(key, builtin)| {
                    key.as_ref() != opcode
                        && builtin.name.as_ref() == opcode
                        && builtin.table.is_some()
                })
                .map(|(key, _)| key)
                .unwrap();
            assert!(
                environment
                    .operator_objects
                    .attachments
                    .contains_key(native_key)
            );
            assert!(environment.operator_objects.defns.get(native_key).is_none());
        }
    }

    #[test]
    fn scoped_body_table_keeps_the_global_original_opdef() {
        let config =
            parse_config("CONSTANT F(1)=[N]{1,\"bad\"} C <- F", TlcVersion::Master).unwrap();
        let mut origin = ModelOrigin::new(JavaProfile::Default, &|_| ClassOrigin::Absent);
        origin.parent_runtime = ParentRuntime::ModeledTlcMasterJdk21;
        let environment = link_environment(&EnvironmentOptions {
            linked_extendees: &[],
            origin: Some(&origin),
            source: "---- MODULE M ----\nEXTENDS N\nCONSTANT C(_)\nASSUME TRUE\n====\n",
            load_module: &|name| {
                (name == "N").then(|| "---- MODULE N ----\nF(x)==FALSE\n====\n".to_owned())
            },
            config: &config,
            is_unconfigured: false,
            version: TlcVersion::Master,
            is_level_checked: false,
            load_class: None,
        })
        .unwrap();
        let (Some(Object::OpDef { _header: f, .. }), Some(Object::OpDef { _header: c, .. })) = (
            environment.operator_objects.defns.get("F"),
            environment.operator_objects.defns.get("C"),
        ) else {
            panic!("scoped body replacement changed the global lookup object");
        };
        assert!(Rc::ptr_eq(f, c));
        assert!(
            environment
                .operator_objects
                .initializers
                .iter()
                .all(|object| !matches!(object, Object::Table(_)))
        );
    }

    #[test]
    fn unproved_receiver_phase_uses_legacy_before_row_initialization() {
        let rows = Rc::new(vec![(
            vec![ConfigValue::Number(1.0)],
            ConfigValue::Set(vec![
                ConfigValue::Number(1.0),
                ConfigValue::String("a".into()),
            ]),
        )]);
        let mut objects = TableObjects::default();
        objects.attachments.insert(Rc::from("F"), rows.clone());
        objects.initializers.push(Object::Table(rows));
        objects.is_complete = false;
        objects
            .admit(
                &ValueOrder {
                    ranks: &FastMap::default(),
                },
                true,
            )
            .unwrap();
        assert!(!objects.is_admitted);
    }
}

#[cfg(test)]
mod unknown_global_prefix_json_tests {
    use crate::TlcVersion;
    use crate::model::{
        ClassOrigin, JavaProfile, ModelOptions, ModelOrigin, ModelSources, ParentRuntime,
        lower_front_ranking_with_origin,
    };
    use crate::report::{ReportOptions, get_sany_text_of};
    use crate::source_reads::ModuleSourceReads;

    #[test]
    fn a_theorem_rhs_is_not_an_opdef_global_and_cannot_certify_new_json() {
        let source = "---- MODULE M ----\nEXTENDS Json\nCONSTANT F\nTHEOREM T == TRUE\nASSUME ToJsonArray({})=\"[]\"\n====\n";
        let reads = ModuleSourceReads::default();
        let modules = |name: &str| {
            reads.record(name, Ok(None));
            None
        };
        let report = get_sany_text_of(
            "M",
            source,
            &ReportOptions {
                version: TlcVersion::Master,
                file_name: None,
                load_module: &modules,
                describe_file: &|name, _| Ok(name.to_owned()),
                root_extendees: &[],
                is_xml_export: false,
                lint_codes: Default::default(),
            },
        )
        .unwrap();
        assert!(!report.is_failed);
        let classes = |_: &str| None;
        let sources = ModelSources {
            source,
            load_module: &modules,
            load_class: &classes,
        };
        let mut origin = ModelOrigin::new(JavaProfile::Default, &|_| ClassOrigin::Absent);
        origin.parent_runtime = ParentRuntime::ModeledTlcMasterJdk21;
        origin.module_source_reads = Some(&reads);
        let lowered = lower_front_ranking_with_origin(
            &sources,
            "CONSTANT F <- T",
            &ModelOptions {
                libraries: &[],
                version: Some(TlcVersion::Master),
                is_warning_enabled: false,
                is_spec_described: false,
                random_seed: 0,
                root_extendees: &[],
            },
            &|_, _, _| vec![],
            Some(&origin),
        );
        // `defns` holds no ThmOrAssumpDefNode, so TLC rejects the substitution before it reads
        // the assumption (`scripts/tlc-json-global-defns/theorem-target-array`), and no IR
        // certifies the Json sources.
        assert!(matches!(
            lowered,
            Err(crate::errors::FrontError::Config(message))
                if message == "The configuration file substitutes for F with the undefined identifier T."
        ));
    }
}
