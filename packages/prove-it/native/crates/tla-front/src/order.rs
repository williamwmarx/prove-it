//! TLC's orders, as `src/tlc/order.ts` reproduces them: TLC orders strings and model values by
//! when it first interned their text, compares a state's variables in the order of SANY's symbol
//! table, and computes the constant definitions in the order of each module's table.

use std::cell::RefCell;
use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::{Module, Name, Position};
use crate::config::{ConfigValue, ModelConfig};
use crate::errors::{FrontError, SanyError, SanyReport, SyntaxError};
use crate::hash::{FastMap, FastSet};
use crate::lexer::{Token, TokenKind, tokenize};
use crate::ordered_map::OrderedMap;
use crate::parser::{extract_module, parse_module, parse_module_tokens};
use crate::resolve::{Result, is_before};
use crate::standard_builtins::USER_STANDARD_MODULES;
use crate::standard_modules::TLC_SOURCES;
use crate::tlc_data::{
    SANY_BUILTINS, SANY_NODE_NAMES, SANY_OPERATOR_SYNONYMS, TLC_RUNTIME_STRINGS,
    TLC_STARTUP_STRINGS,
};
use tla_trace::RECORD_VALUE_FIELDS;

#[derive(Clone, Copy, PartialEq, Eq)]
enum SymbolKind {
    Builtin,
    Constant,
    Variable,
    Definition,
    Theorem,
    Module,
}

#[derive(Clone)]
struct SymbolEntry {
    key: Rc<str>,
    name: Rc<str>,
    hash: u32,
    kind: SymbolKind,
    is_local: bool,
}

/// `java.util.Hashtable` as SANY's Context uses it: default capacity 11, load factor 0.75, new
/// entries at the head of their bucket, and enumeration from the last bucket to the first.
struct SymbolTable {
    buckets: Vec<Vec<SymbolEntry>>,
    threshold: usize,
    keys: FastSet<Rc<str>>,
    inserted: Vec<SymbolEntry>,
    /// Where the entries the module adds itself start, after those of the modules it extends.
    own_start: usize,
}

impl SymbolTable {
    fn new() -> SymbolTable {
        SymbolTable {
            buckets: vec![Vec::new(); 11],
            threshold: 8,
            keys: FastSet::default(),
            inserted: Vec::new(),
            own_start: 0,
        }
    }

    fn enumerate(&self) -> Vec<SymbolEntry> {
        self.buckets
            .iter()
            .rev()
            .flat_map(|bucket| bucket.iter().rev().cloned())
            .collect()
    }

    fn put(&mut self, entry: SymbolEntry) {
        if self.keys.contains(&entry.key) {
            return;
        }
        if self.inserted.len() >= self.threshold {
            let capacity = self.buckets.len() * 2 + 1;
            let mut rehashed = vec![Vec::new(); capacity];
            for existing in self.enumerate() {
                rehashed[existing.hash as usize % capacity].push(existing);
            }
            self.buckets = rehashed;
            self.threshold = capacity * 3 / 4;
        }
        let bucket = entry.hash as usize % self.buckets.len();
        self.buckets[bucket].push(entry.clone());
        self.keys.insert(entry.key.clone());
        self.inserted.push(entry);
    }
}

/// The name tla2sany.st.Location gives an unknown module, which it interns as it initializes.
const UNKNOWN_LOCATION: &str = "--unknown--";

/// The strings TLC interns as it builds its checker, after it computes the constant definitions:
/// tlc2.tool.Action's name for an unnamed action as `processConfig` builds the first action, the
/// names TLCGetSet interns as `AbstractChecker.createConfig` initializes it, the mode createConfig
/// makes, and RecordValue's field names as createConfig builds its record, unless a constant
/// definition built a record before.
pub fn get_checker_strings<'a>(config: &ModelConfig) -> impl Iterator<Item = &'a str> {
    let has_actions = config.init.is_some()
        || config.next.is_some()
        || config.specification.is_some()
        || !config.invariants.is_empty()
        || !config.properties.is_empty();
    has_actions
        .then_some("UnnamedAction")
        .into_iter()
        .chain(TLC_RUNTIME_STRINGS.iter().copied())
        .chain(["bfs"])
        .chain(RECORD_VALUE_FIELDS)
}

/// Texts in the order of their first occurrences, as TLC interns them.
pub fn get_unique<'a>(texts: impl Iterator<Item = &'a str>) -> Vec<String> {
    let mut seen: FastSet<&str> = FastSet::default();
    texts
        .filter(|text| seen.insert(text))
        .map(str::to_owned)
        .collect()
}

const SEMANTIC_PRELUDE: [&str; 5] = [
    "LAMBDA",
    "$$InAssume",
    "nullODN",
    "nullOpArg",
    "nullLabelNode",
];

const THEOREM_KEYWORDS: [&str; 4] = ["THEOREM", "LEMMA", "COROLLARY", "PROPOSITION"];

/// SANY's NewSymb declares a CONSTANT or VARIABLE local to an ASSUME ... PROVE, after the ASSUME, a
/// comma or NEW, where a module's own declaration never starts. A field may be named ASSUME or NEW.
fn is_proof_declaration(tokens: &[Token], index: usize) -> bool {
    let Some(previous) = index.checked_sub(1).map(|at| &tokens[at]) else {
        return false;
    };
    match previous.kind {
        TokenKind::Keyword => {
            matches!(&*previous.text, "ASSUME" | "NEW")
                && (index < 2 || &*tokens[index - 2].text != ".")
        }
        TokenKind::Operator => &*previous.text == ",",
        _ => false,
    }
}

fn get_canonical_name(name: &str) -> &str {
    SANY_OPERATOR_SYNONYMS
        .iter()
        .find(|synonyms| synonyms.contains(&name))
        .map_or(name, |synonyms| synonyms[0])
}

fn get_java_hash(text: &str) -> i32 {
    text.encode_utf16().fold(0i32, |hash, unit| {
        hash.wrapping_mul(31).wrapping_add(i32::from(unit))
    })
}

fn create_entry(name: &str, kind: SymbolKind, is_local: bool) -> SymbolEntry {
    SymbolEntry {
        key: if kind == SymbolKind::Module {
            Rc::from(format!("module {name}"))
        } else {
            Rc::from(name)
        },
        name: Rc::from(name),
        hash: (get_java_hash(name) & 0x7fff_ffff) as u32,
        kind,
        is_local,
    }
}

fn text_at(tokens: &[Token], index: usize) -> Option<&str> {
    tokens.get(index).map(|token| &*token.text)
}

fn get_declared_name(tokens: &[Token], start: usize) -> (String, usize) {
    let first = &tokens[start];
    let second = tokens.get(start + 1);
    if &*first.text == "_" && second.is_some_and(|second| second.kind == TokenKind::Operator) {
        let operator = &second.expect("an operator").text;
        return if text_at(tokens, start + 2) == Some("_") {
            (get_canonical_name(operator).to_owned(), start + 3)
        } else {
            (operator.to_string(), start + 2)
        };
    }
    if first.kind == TokenKind::Operator {
        let name = if &*first.text == "-" {
            "-.".to_owned()
        } else {
            get_canonical_name(&first.text).to_owned()
        };
        return (name, start + 2);
    }
    if second.map(|second| &*second.text) != Some("(") {
        return (first.text.to_string(), start + 1);
    }
    let mut close = start + 2;
    while close < tokens.len() && &*tokens[close].text != ")" {
        close += 1;
    }
    (first.text.to_string(), close + 1)
}

fn get_declarations(tokens: &[Token], start: usize) -> Vec<String> {
    let mut names = Vec::new();
    let mut index = start;
    loop {
        let (name, end) = get_declared_name(tokens, index);
        names.push(name);
        if text_at(tokens, end) != Some(",") {
            return names;
        }
        index = end + 1;
    }
}

fn get_location(token: &Token) -> Position {
    Position {
        line: token.line,
        column: token.column,
    }
}

/// The modules a module extends and instantiates, with its inner modules, as SANY's SpecObj
/// walks them to decide which module to parse next.
#[derive(Clone)]
struct ModuleReferences {
    key: String,
    unit: Option<Name>,
    extends: Vec<String>,
    instances: Vec<String>,
    inner: Vec<Rc<ModuleReferences>>,
    all_extends: Rc<RefCell<FastSet<String>>>,
}

fn get_module_references(
    tokens: &[Token],
    unit: Option<&Name>,
    inner_modules: &mut FastMap<String, Rc<ModuleReferences>>,
) -> Rc<ModuleReferences> {
    let all_extends: Rc<RefCell<FastSet<String>>> = Rc::default();
    fn read(
        tokens: &[Token],
        start: usize,
        key: String,
        unit: Option<&Name>,
        all_extends: &Rc<RefCell<FastSet<String>>>,
        inner_modules: &mut FastMap<String, Rc<ModuleReferences>>,
    ) -> (Rc<ModuleReferences>, usize) {
        let mut references = ModuleReferences {
            key: key.clone(),
            unit: unit.cloned(),
            extends: Vec::new(),
            instances: Vec::new(),
            inner: Vec::new(),
            all_extends: all_extends.clone(),
        };
        let mut index = start + 1;
        while index < tokens.len() {
            let token = &tokens[index];
            if token.kind == TokenKind::ModuleEnd {
                return (Rc::new(references), index);
            }
            if token.kind == TokenKind::Separator && text_at(tokens, index + 1) == Some("MODULE") {
                let name = text_at(tokens, index + 2).unwrap_or("").to_owned();
                let (inner, end) = read(
                    tokens,
                    index,
                    format!("{key}/{name}"),
                    unit,
                    all_extends,
                    inner_modules,
                );
                inner_modules.insert(name, inner.clone());
                references.inner.push(inner);
                index = end;
            } else if index > 0 && text_at(tokens, index - 1) == Some(".") {
                // A record field named EXTENDS or INSTANCE, as in r.EXTENDS.
            } else if &*token.text == "EXTENDS" {
                let names = get_declarations(tokens, index + 1);
                all_extends.borrow_mut().extend(names.iter().cloned());
                references.extends.extend(names);
            } else if &*token.text == "INSTANCE"
                && tokens
                    .get(index + 1)
                    .is_some_and(|next| next.kind == TokenKind::Identifier)
            {
                references
                    .instances
                    .push(tokens[index + 1].text.to_string());
            }
            index += 1;
        }
        (Rc::new(references), tokens.len())
    }
    read(
        tokens,
        0,
        unit.map_or_else(String::new, |unit| unit.to_string()),
        unit,
        &all_extends,
        inner_modules,
    )
    .0
}

fn utf16_length(text: &str) -> u32 {
    text.encode_utf16().count() as u32
}

fn is_adjacent(left: &Token, right: Option<&Token>) -> bool {
    right.is_some_and(|right| {
        right.line == left.line && right.column == left.column + utf16_length(&left.text)
    })
}

fn escape_string(text: &str) -> String {
    let mut escaped = String::from("\"");
    for character in text.chars() {
        match character {
            '\\' => escaped.push_str("\\\\"),
            '"' => escaped.push_str("\\\""),
            '\n' => escaped.push_str("\\n"),
            '\t' => escaped.push_str("\\t"),
            '\r' => escaped.push_str("\\r"),
            '\u{c}' => escaped.push_str("\\f"),
            other => escaped.push(other),
        }
    }
    escaped.push('"');
    escaped
}

/// The texts SANY interns while parsing, in order. SANY reads a proof step label such as `<1>2`
/// and a module header such as `---- MODULE` as one token. It interns a string literal as
/// written, quotes included, and interns the literal's contents only during semantic analysis.
fn get_parsed_texts(tokens: &[Token]) -> Vec<String> {
    let mut texts = Vec::new();
    let mut index = 0;
    while index < tokens.len() {
        let token = &tokens[index];
        let is_number_label = |text: &str| {
            !text.is_empty()
                && (text.bytes().all(|byte| byte.is_ascii_digit()) || text == "*" || text == "+")
        };
        let is_step_label = &*token.text == "<"
            && is_adjacent(token, tokens.get(index + 1))
            && is_number_label(&tokens[index + 1].text)
            && text_at(tokens, index + 2) == Some(">")
            && is_adjacent(&tokens[index + 1], tokens.get(index + 2));
        if is_step_label {
            index += if is_adjacent(&tokens[index + 2], tokens.get(index + 3)) {
                4
            } else {
                3
            };
            continue;
        }
        let is_header =
            &*token.text == "MODULE" && index > 0 && tokens[index - 1].kind == TokenKind::Separator;
        if !is_header {
            texts.push(if token.kind == TokenKind::String {
                escape_string(&token.text)
            } else {
                token.text.to_string()
            });
        }
        index += 1;
    }
    texts
}

/// A module starts with `---- MODULE Name`, so its third token is its name.
fn get_module_name(tokens: &[Token]) -> Option<&str> {
    text_at(tokens, 2)
}

fn get_ranges(tokens: &[Token]) -> OrderedMap<String, (usize, usize)> {
    let mut ranges = OrderedMap::new();
    let mut open: Vec<(String, usize)> = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        if token.kind == TokenKind::Separator && text_at(tokens, index + 1) == Some("MODULE") {
            open.push((text_at(tokens, index + 2).unwrap_or("").to_owned(), index));
        }
        if token.kind == TokenKind::ModuleEnd
            && let Some((name, start)) = open.pop()
            && !ranges.contains_key(&name)
        {
            ranges.insert(name, (start, index + 1));
        }
    }
    ranges
}

fn find_module(modules: &[Rc<Module>], name: &str) -> Option<Rc<Module>> {
    modules
        .iter()
        .find(|module| &*module.name == name)
        .cloned()
        .or_else(|| {
            modules
                .iter()
                .find_map(|module| find_module(&module.modules, name))
        })
}

/// The references of a module, read once, which may read inner modules too.
type GetUnitReferences<'a> = dyn FnMut(Option<&Name>, &mut FastMap<String, Rc<ModuleReferences>>) -> Result<Rc<ModuleReferences>>
    + 'a;

/// A module's source read into tokens once, and parsed from them once.
struct ModuleText {
    text: Option<String>,
    tokens: Rc<Vec<Token>>,
    ranges: OrderedMap<String, (usize, usize)>,
    module: RefCell<Option<Rc<Module>>>,
}

impl ModuleText {
    fn get_module(&self, version: TlcVersion) -> Result<Rc<Module>> {
        if let Some(module) = self.module.borrow().clone() {
            return Ok(module);
        }
        let module = Rc::new(match &self.text {
            None => parse_module("")?,
            Some(text) => parse_module_tokens(text, &self.tokens, version)?,
        });
        *self.module.borrow_mut() = Some(module.clone());
        Ok(module)
    }
}

/// The tokens of a module TLC reads: a file's, or a module nested in one, in `start..end`.
#[derive(Clone)]
struct ParsedModule {
    text: Rc<ModuleText>,
    nested: Option<String>,
    start: usize,
    end: usize,
}

impl ParsedModule {
    fn tokens(&self) -> &[Token] {
        &self.text.tokens[self.start..self.end]
    }

    fn get_module(&self, version: TlcVersion) -> Result<Rc<Module>> {
        let file = self.text.get_module(version)?;
        Ok(match &self.nested {
            Some(name) => find_module(&file.modules, name).unwrap_or(file),
            None => file,
        })
    }
}

/// The modules TLC reads for a spec: the root module, TLC's standard modules, the files the
/// loader returns, the modules that follow the root module, and the modules nested in any of
/// these. A module without a source has no tokens.
pub struct TlcOrder<'a> {
    source: &'a str,
    load_module: &'a dyn Fn(&str) -> Option<String>,
    version: TlcVersion,
    files: RefCell<FastMap<String, ParsedModule>>,
    nested_modules: RefCell<FastMap<String, ParsedModule>>,
    texts: RefCell<FastMap<String, Rc<ModuleText>>>,
    contexts: RefCell<FastMap<String, Rc<RefCell<SymbolTable>>>>,
    /// The modules TLC adds to the root module's EXTENDS for its post conditions.
    root_extendees: &'a [&'a str],
}

fn missing_module_error(name: &str, importer: &str) -> FrontError {
    let mut error = SyntaxError::sany(vec![SanyError {
        location: format!("In module {importer}"),
        message: format!(
            "Cannot find source file for module {name} imported in module {importer}."
        ),
    }]);
    if let Some(report) = &mut error.sany {
        **report = SanyReport {
            is_fatal: true,
            ..(**report).clone()
        };
    }
    FrontError::Syntax(error)
}

/// A module's context, which a module that names its own module while the front end builds its
/// context, such as a file instantiating its inner module of the file's name, finds unbuilt: the
/// front end keys contexts by name where SANY scopes the inner module's.
fn get_built(table: &RefCell<SymbolTable>) -> Result<std::cell::Ref<'_, SymbolTable>> {
    table
        .try_borrow()
        .map_err(|_| FrontError::NotYet("a module that names a module of its own name".to_owned()))
}

impl<'a> TlcOrder<'a> {
    pub fn new(
        source: &'a str,
        load_module: &'a dyn Fn(&str) -> Option<String>,
        version: TlcVersion,
    ) -> Result<TlcOrder<'a>> {
        let order = TlcOrder {
            source,
            load_module,
            version,
            files: RefCell::default(),
            nested_modules: RefCell::default(),
            texts: RefCell::default(),
            contexts: RefCell::default(),
            root_extendees: &[],
        };
        order.get_file(None)?;
        Ok(order)
    }

    /// The order where TLC adds these modules to the root module's EXTENDS for its post
    /// conditions, as `_TLCTrace` where it records the trace for its trace exploration spec.
    /// SANY parses and analyzes them as the root's other extendees, after its own.
    pub fn with_root_extendees(mut self, root_extendees: &'a [&'a str]) -> TlcOrder<'a> {
        self.root_extendees = root_extendees;
        self
    }

    fn read_text(&self, text: Option<String>) -> Result<Rc<ModuleText>> {
        if let Some(text) = &text
            && let Some(known) = self.texts.borrow().get(text)
        {
            return Ok(known.clone());
        }
        let tokens = match &text {
            None => Vec::new(),
            Some(text) => tokenize(text)?,
        };
        let read = Rc::new(ModuleText {
            ranges: get_ranges(&tokens),
            tokens: Rc::new(tokens),
            module: RefCell::new(None),
            text: text.clone(),
        });
        if let Some(text) = text {
            self.texts.borrow_mut().insert(text, read.clone());
        }
        Ok(read)
    }

    fn get_file(&self, name: Option<&str>) -> Result<ParsedModule> {
        let key = name.unwrap_or("").to_owned();
        if let Some(cached) = self.files.borrow().get(&key) {
            return Ok(cached.clone());
        }
        let text = match name {
            None => Some(self.source.to_owned()),
            Some(name) => USER_STANDARD_MODULES
                .contains(&name)
                .then(|| (self.load_module)(name))
                .flatten()
                .or_else(|| {
                    TLC_SOURCES
                        .iter()
                        .find(|module| module.0 == name)
                        .map(|module| module.1.to_owned())
                })
                .or_else(|| (self.load_module)(name))
                // The post conditions' modules, as `_TLCTrace`, are SANY's own standard modules.
                .or_else(|| crate::get_standard_module(name, self.version).map(str::to_owned))
                .or_else(|| extract_module(self.source, name)),
        };
        let read = self.read_text(text)?;
        let (start, end) = get_module_name(&read.tokens)
            .and_then(|module_name| read.ranges.get(module_name).copied())
            .unwrap_or((0, 0));
        let file = ParsedModule {
            text: read.clone(),
            nested: None,
            start,
            end,
        };
        self.files.borrow_mut().insert(key, file.clone());
        for (nested_name, (nested_start, nested_end)) in read.ranges.iter() {
            if *nested_start == start || self.nested_modules.borrow().contains_key(nested_name) {
                continue;
            }
            self.nested_modules.borrow_mut().insert(
                nested_name.clone(),
                ParsedModule {
                    text: read.clone(),
                    nested: Some(nested_name.clone()),
                    start: *nested_start,
                    end: *nested_end,
                },
            );
        }
        Ok(file)
    }

    fn get_parsed(&self, name: Option<&str>) -> Result<ParsedModule> {
        if let Some(name) = name
            && let Some(nested) = self.nested_modules.borrow().get(name)
        {
            return Ok(nested.clone());
        }
        self.get_file(name)
    }

    /// Every string TLC interns before model checking starts but those it makes computing the
    /// constant definitions: the strings SANY interns, then those TLC interns as it builds its
    /// checker.
    pub fn get_string_order(&self, config: &ModelConfig) -> Result<Vec<String>> {
        let sany = self.get_sany_string_order(config)?;
        Ok(get_unique(
            sany.iter()
                .map(String::as_str)
                .chain(get_checker_strings(config)),
        ))
    }

    /// The strings TLC interns before it computes the constant definitions, in order: values in
    /// the config, TLC's startup strings, each module's tokens in the order `SpecObj.loadSpec`
    /// parses the modules, with Location's after the root's, and string literals in semantic
    /// analysis order.
    pub fn get_sany_string_order(&self, config: &ModelConfig) -> Result<Vec<String>> {
        let mut order: OrderedMap<String, ()> = OrderedMap::new();
        let mut intern = |text: &str| {
            if !order.contains_key(text) {
                order.insert(text.to_owned(), ());
            }
        };
        fn intern_config_value(value: &ConfigValue, intern: &mut dyn FnMut(&str)) {
            match value {
                ConfigValue::ModelValue(name) => intern(name),
                ConfigValue::String(text) => intern(text),
                ConfigValue::Set(elements) => {
                    for element in elements {
                        intern_config_value(element, intern);
                    }
                }
                _ => {}
            }
        }
        for constant in &config.constants {
            for arg in constant.args.iter().flatten() {
                intern_config_value(arg, &mut intern);
            }
            intern_config_value(&constant.value, &mut intern);
        }
        TLC_STARTUP_STRINGS.iter().for_each(|text| intern(text));
        let mut inner_modules: FastMap<String, Rc<ModuleReferences>> = FastMap::default();
        let mut unit_references: FastMap<String, Rc<ModuleReferences>> = FastMap::default();
        let unit_key =
            |name: Option<&Name>| name.map_or_else(|| "\u{0}".to_owned(), |name| name.to_string());
        let mut get_unit_references =
            |name: Option<&Name>,
             inner_modules: &mut FastMap<String, Rc<ModuleReferences>>|
             -> Result<Rc<ModuleReferences>> {
                if let Some(cached) = unit_references.get(&unit_key(name)) {
                    return Ok(cached.clone());
                }
                let parsed = self.get_parsed(name.map(|name| &**name))?;
                let mut references = get_module_references(parsed.tokens(), name, inner_modules);
                if name.is_none() && !self.root_extendees.is_empty() {
                    let mut root = Rc::unwrap_or_clone(references);
                    for &extendee in self.root_extendees {
                        root.extends.push(extendee.to_owned());
                        root.all_extends.borrow_mut().insert(extendee.to_owned());
                    }
                    references = Rc::new(root);
                }
                unit_references.insert(unit_key(name), references.clone());
                Ok(references)
            };
        let mut relations: FastSet<String> = FastSet::default();
        let mut dependencies: FastMap<String, Vec<String>> = FastMap::default();
        let root_tokens = self.get_parsed(None)?.tokens().to_vec();
        for (index, text) in get_parsed_texts(&root_tokens).iter().enumerate() {
            if index == 3 {
                SANY_NODE_NAMES.iter().for_each(|name| intern(name));
            }
            intern(text);
        }
        // pcal.Validator reads the root module's location once SANY has parsed it, which
        // initializes tla2sany.st.Location before SANY parses the modules the root uses.
        intern(UNKNOWN_LOCATION);
        let root_references = get_unit_references(None, &mut inner_modules)?;
        let mut parsed_units: FastSet<String> = FastSet::default();
        loop {
            // The first reference not yet resolved, searching the extensions before the
            // instantiations, as SpecObj does.
            let mut found = None;
            for is_extension in [true, false] {
                let mut visited: FastSet<String> = FastSet::default();
                found = self.search(
                    &root_references,
                    &mut visited,
                    is_extension,
                    &relations,
                    &mut inner_modules,
                    &mut get_unit_references,
                )?;
                if found.is_some() {
                    break;
                }
            }
            let Some((module, name)) = found else {
                break;
            };
            relations.insert(format!("{}>{name}", module.key));
            dependencies
                .entry(unit_key(module.unit.as_ref()))
                .or_default()
                .push(name.clone());
            if !parsed_units.insert(name.clone()) {
                continue;
            }
            // SANY stops at the first module it can't find, in the order it reads them.
            let parsed = self.get_parsed(Some(&name))?;
            if parsed.text.tokens.is_empty() {
                let root = self.get_parsed(None)?;
                let importer = module
                    .unit
                    .as_ref()
                    .map(|unit| unit.to_string())
                    .or_else(|| get_module_name(&root.text.tokens).map(str::to_owned))
                    .unwrap_or_else(|| "undefined".to_owned());
                return Err(missing_module_error(&name, &importer));
            }
            for text in get_parsed_texts(parsed.tokens()) {
                intern(&text);
            }
        }
        SEMANTIC_PRELUDE.iter().for_each(|text| intern(text));
        let mut analyzed: FastSet<String> = FastSet::default();
        self.analyze(
            None,
            &mut analyzed,
            &dependencies,
            &mut inner_modules,
            &mut get_unit_references,
            &mut intern,
        )?;
        Ok(order.keys().cloned().collect())
    }

    #[allow(clippy::too_many_arguments)]
    fn analyze(
        &self,
        name: Option<&Name>,
        analyzed: &mut FastSet<String>,
        dependencies: &FastMap<String, Vec<String>>,
        inner_modules: &mut FastMap<String, Rc<ModuleReferences>>,
        get_unit_references: &mut GetUnitReferences,
        intern: &mut dyn FnMut(&str),
    ) -> Result<()> {
        let key = name.map_or_else(|| "\u{0}".to_owned(), |name| name.to_string());
        if !analyzed.insert(key.clone()) {
            return Ok(());
        }
        let unit_dependencies = dependencies.get(&key).cloned().unwrap_or_default();
        let extendees = get_unit_references(name, inner_modules)?
            .all_extends
            .clone();
        let (extended, others): (Vec<String>, Vec<String>) = unit_dependencies
            .into_iter()
            .partition(|item| extendees.borrow().contains(item));
        for item in extended.iter().chain(&others) {
            let item: Name = Rc::from(item.as_str());
            self.analyze(
                Some(&item),
                analyzed,
                dependencies,
                inner_modules,
                get_unit_references,
                intern,
            )?;
        }
        let parsed = self.get_parsed(name.map(|name| &**name))?;
        for token in parsed.tokens() {
            if token.kind == TokenKind::String {
                intern(&token.text);
            }
        }
        Ok(())
    }

    fn search(
        &self,
        module: &Rc<ModuleReferences>,
        visited: &mut FastSet<String>,
        is_extension: bool,
        relations: &FastSet<String>,
        inner_modules: &mut FastMap<String, Rc<ModuleReferences>>,
        get_unit_references: &mut GetUnitReferences,
    ) -> Result<Option<(Rc<ModuleReferences>, String)>> {
        if !visited.insert(module.key.clone()) {
            return Ok(None);
        }
        let is_resolved =
            |module: &ModuleReferences,
             name: &str,
             inner: &FastMap<String, Rc<ModuleReferences>>| {
                inner.contains_key(name) || relations.contains(&format!("{}>{name}", module.key))
            };
        let names = if is_extension {
            &module.extends
        } else {
            &module.instances
        };
        if let Some(name) = names
            .iter()
            .find(|referenced| !is_resolved(module, referenced, inner_modules))
        {
            return Ok(Some((module.clone(), name.clone())));
        }
        let mut nested: Vec<Rc<ModuleReferences>> = Vec::new();
        let get_referenced = |name: &str,
                              inner_modules: &mut FastMap<String, Rc<ModuleReferences>>,
                              get_unit_references: &mut GetUnitReferences|
         -> Result<Rc<ModuleReferences>> {
            if let Some(inner) = inner_modules.get(name) {
                return Ok(inner.clone());
            }
            get_unit_references(Some(&Rc::from(name)), inner_modules)
        };
        for name in &module.extends {
            nested.push(get_referenced(name, inner_modules, get_unit_references)?);
        }
        for name in &module.instances {
            if is_resolved(module, name, inner_modules) {
                nested.push(get_referenced(name, inner_modules, get_unit_references)?);
            }
        }
        nested.extend(module.inner.iter().cloned());
        for item in &nested {
            if let Some(found) = self.search(
                item,
                visited,
                is_extension,
                relations,
                inner_modules,
                get_unit_references,
            )? {
                return Ok(Some(found));
            }
        }
        Ok(None)
    }

    /// SANY's Context of a module, which the root module has under `None`.
    fn get_context(&self, name: Option<&str>) -> Result<Rc<RefCell<SymbolTable>>> {
        let key = name.unwrap_or("").to_owned();
        if let Some(cached) = self.contexts.borrow().get(&key) {
            return Ok(cached.clone());
        }
        let table = Rc::new(RefCell::new(SymbolTable::new()));
        self.contexts.borrow_mut().insert(key, table.clone());
        for builtin in SANY_BUILTINS.iter().rev() {
            table
                .borrow_mut()
                .put(create_entry(builtin, SymbolKind::Builtin, false));
        }
        let unit = self.get_parsed(name)?;
        let module = unit.get_module(self.version)?;
        for extended in &module.extends {
            let extended = self.get_context(Some(extended))?;
            let entries = get_built(&extended)?.inserted.clone();
            for entry in entries {
                if !entry.is_local {
                    table.borrow_mut().put(entry);
                }
            }
        }
        let own_start = table.borrow().inserted.len();
        table.borrow_mut().own_start = own_start;
        for (_, apply) in self.get_units(&unit, &module)? {
            apply(self, &mut table.borrow_mut())?;
        }
        Ok(table)
    }

    #[allow(clippy::type_complexity)]
    fn get_units(
        &self,
        unit: &ParsedModule,
        module: &Module,
    ) -> Result<Vec<(Position, Box<dyn Fn(&Self, &mut SymbolTable) -> Result<()>>)>> {
        let tokens = &unit.text.tokens;
        let mut units: Vec<(Position, Box<dyn Fn(&Self, &mut SymbolTable) -> Result<()>>)> =
            Vec::new();
        let mut statement_locations: Vec<Position> = Vec::new();
        let declare =
            |units: &mut Vec<(Position, Box<dyn Fn(&Self, &mut SymbolTable) -> Result<()>>)>,
             index: usize,
             kind: SymbolKind| {
                let names = get_declarations(tokens, index + 1);
                units.push((
                    get_location(&tokens[index]),
                    Box::new(move |_, table| {
                        for name in &names {
                            table.put(create_entry(name, kind, false));
                        }
                        Ok(())
                    }),
                ));
            };
        let recursive_names: FastSet<Name> = module
            .definitions
            .iter()
            .filter(|definition| definition.is_recursive)
            .map(|definition| definition.name.clone())
            .collect();
        let mut depth = 0;
        for index in unit.start..unit.end {
            let token = &tokens[index];
            if token.kind == TokenKind::Separator && text_at(tokens, index + 1) == Some("MODULE") {
                depth += 1;
                if depth == 2 {
                    let name = text_at(tokens, index + 2).unwrap_or("").to_owned();
                    units.push((
                        get_location(token),
                        Box::new(move |_, table| {
                            table.put(create_entry(&name, SymbolKind::Module, false));
                            Ok(())
                        }),
                    ));
                }
                continue;
            }
            if token.kind == TokenKind::ModuleEnd {
                depth -= 1;
            }
            if depth != 1 || token.kind != TokenKind::Keyword {
                continue;
            }
            if is_proof_declaration(tokens, index) {
                continue;
            }
            match &*token.text {
                "CONSTANT" | "CONSTANTS" => declare(&mut units, index, SymbolKind::Constant),
                "VARIABLE" | "VARIABLES" => declare(&mut units, index, SymbolKind::Variable),
                "RECURSIVE" => {
                    let names = get_declarations(tokens, index + 1);
                    if names
                        .iter()
                        .all(|name| recursive_names.contains(name.as_str()))
                    {
                        declare(&mut units, index, SymbolKind::Definition);
                    }
                }
                _ => {}
            }
            let is_named_theorem = THEOREM_KEYWORDS.contains(&&*token.text)
                && tokens
                    .get(index + 1)
                    .is_some_and(|next| next.kind == TokenKind::Identifier)
                && text_at(tokens, index + 2) == Some("==");
            if is_named_theorem {
                statement_locations.push(get_location(token));
                let name = tokens[index + 1].text.to_string();
                units.push((
                    get_location(token),
                    Box::new(move |_, table| {
                        table.put(create_entry(&name, SymbolKind::Theorem, false));
                        Ok(())
                    }),
                ));
            }
        }
        for assumption in &module.assumptions {
            statement_locations.push(assumption.location.position());
            let Some(name) = assumption.name.clone() else {
                continue;
            };
            units.push((
                assumption.location.position(),
                Box::new(move |_, table| {
                    table.put(create_entry(&name, SymbolKind::Theorem, false));
                    Ok(())
                }),
            ));
        }
        for definition in &module.definitions {
            let location = definition.location.position();
            if statement_locations.contains(&location) {
                continue;
            }
            let name = get_canonical_name(&definition.name).to_owned();
            let is_local = definition.is_local;
            units.push((
                location,
                Box::new(move |_, table| {
                    table.put(create_entry(&name, SymbolKind::Definition, is_local));
                    Ok(())
                }),
            ));
        }
        for instance in &module.instances {
            let instance = instance.clone();
            units.push((
                instance.location.position(),
                Box::new(move |order, table| {
                    let context = order.get_context(Some(&instance.module))?;
                    let instancee = get_built(&context)?.enumerate();
                    let prefix = instance
                        .name
                        .as_ref()
                        .map_or_else(String::new, |name| format!("{name}!"));
                    for kind in [SymbolKind::Definition, SymbolKind::Theorem] {
                        for entry in instancee.iter().filter(|entry| entry.kind == kind) {
                            if entry.is_local {
                                continue;
                            }
                            table.put(create_entry(
                                &format!("{prefix}{}", entry.name),
                                entry.kind,
                                instance.is_local,
                            ));
                        }
                    }
                    if let Some(name) = &instance.name {
                        table.put(create_entry(
                            name,
                            SymbolKind::Definition,
                            instance.is_local,
                        ));
                    }
                    Ok(())
                }),
            ));
        }
        units.sort_by(|left, right| {
            if is_before(left.0, right.0) {
                std::cmp::Ordering::Less
            } else if is_before(right.0, left.0) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        });
        Ok(units)
    }

    /// The variables or constants of the root module in the reverse of its context
    /// enumeration, as `ModuleNode.getVariableDecls` and `getConstantDecls` return them.
    pub fn get_declaration_order(&self, is_variable: bool) -> Result<Vec<Name>> {
        let kind = if is_variable {
            SymbolKind::Variable
        } else {
            SymbolKind::Constant
        };
        let mut names: Vec<Name> = self
            .get_context(None)?
            .borrow()
            .enumerate()
            .into_iter()
            .filter(|entry| entry.kind == kind)
            .map(|entry| entry.name)
            .collect();
        names.reverse();
        Ok(names)
    }

    /// The names of the definitions a module adds to its context, in the order of
    /// `ModuleNode.getOpDefs`, in which TLC computes the constant definitions as it starts.
    pub fn get_definition_order(&self, name: Option<&str>) -> Result<Vec<Name>> {
        // The root module's context reads every file of the spec, and so finds the modules
        // nested in the files it extends or instantiates.
        self.get_context(None)?;
        let table = self.get_context(name)?;
        let table = table.borrow();
        Ok(table.inserted[table.own_start..]
            .iter()
            .filter(|entry| entry.kind == SymbolKind::Definition)
            .map(|entry| entry.name.clone())
            .collect())
    }
}
