//! Reads the blob `src/engine/ir.ts` writes, checking every count, index and offset as it goes.

use std::fmt;

use crate::{
    Action, ActionProperty, Atom, AtomKind, Bound, Builtin, ConfigName, Constant, Definition,
    DefinitionForm, EnabledActions, IR_VERSION, Index, Ir, Junction, LiveProperty, LiveTerm, MAGIC,
    Model, Name, Node, NodeId, NodeKind, Nodes, Param, PathStep, Pattern, Possible, Printed,
    Resolution, Scope, ScopeBinding, Selector, SourceRange, Startup, TextId, Update, Value, Values,
    code, tag,
};

/// Why a blob isn't an IR this decoder reads: where it stopped, in words, and what it found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodeError {
    pub word: usize,
    pub message: String,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "at word {}: {}", self.word, self.message)
    }
}

impl std::error::Error for DecodeError {}

type Decoded<T> = Result<T, DecodeError>;

/// The deepest nesting of nodes the decoder follows, so a blob can't overflow its stack.
const MAXIMUM_DEPTH: usize = 10_000;

/// Decodes an IR.
pub fn decode(bytes: &[u8]) -> Decoded<Ir> {
    crate::on_nesting_stack(|| decode_here(bytes))
}

fn decode_here(bytes: &[u8]) -> Decoded<Ir> {
    let fail = |message: String| DecodeError { word: 0, message };
    if bytes.len() < 16 || !bytes.len().is_multiple_of(4) {
        return Err(fail(format!("{} bytes are no IR", bytes.len())));
    }
    let word = |index: usize| {
        u32::from_le_bytes(
            bytes[index * 4..index * 4 + 4]
                .try_into()
                .expect("four bytes"),
        )
    };
    if word(0) != MAGIC {
        return Err(fail("not an engine IR".into()));
    }
    if word(1) != IR_VERSION {
        return Err(fail(format!("IR version {}, not {IR_VERSION}", word(1))));
    }
    let (word_count, text_length) = (word(2) as usize, word(3) as usize);
    if word_count < 4 || word_count * 4 + text_length.next_multiple_of(4) != bytes.len() {
        return Err(fail(format!(
            "{word_count} words and {text_length} bytes of text don't make {} bytes",
            bytes.len()
        )));
    }
    let text = &bytes[word_count * 4..word_count * 4 + text_length];
    if bytes[word_count * 4 + text_length..]
        .iter()
        .any(|&byte| byte != 0)
    {
        return Err(fail("the text's padding isn't zero".into()));
    }
    let words: Vec<i32> = (0..word_count).map(|index| word(index) as i32).collect();
    Decoder {
        words: &words,
        at: 4,
        text_count: 0,
        node_count: 0,
        depth: 0,
        offsets: Vec::new(),
    }
    .read(text)
}

struct Decoder<'a> {
    words: &'a [i32],
    at: usize,
    text_count: u32,
    node_count: u32,
    depth: usize,
    // The node at each word offset of the nodes section, or u32::MAX where none starts.
    offsets: Vec<NodeId>,
}

// A section that refers to nodes before they are read keeps their offsets, then the node ids.
struct Pending {
    word: usize,
    offset: i32,
}

impl Decoder<'_> {
    fn error<T>(&self, message: impl Into<String>) -> Decoded<T> {
        Err(DecodeError {
            word: self.at,
            message: message.into(),
        })
    }

    fn next(&mut self) -> Decoded<i32> {
        match self.words.get(self.at) {
            Some(&word) => {
                self.at += 1;
                Ok(word)
            }
            None => self.error("the words end early"),
        }
    }

    fn live_terms(&mut self) -> Decoded<Vec<LiveTerm>> {
        let words = self.count()?;
        let end = self.at + words;
        let mut terms = Vec::new();
        while self.at < end {
            let position = |decoder: &mut Self| -> Decoded<Index> {
                match decoder.next()? {
                    word if word >= 0 => Ok(word as Index),
                    word => decoder.error(format!("an atom at {word}")),
                }
            };
            terms.push(match self.next()? {
                code::LIVE_FALSE => LiveTerm::Boolean(false),
                code::LIVE_TRUE => LiveTerm::Boolean(true),
                code::LIVE_STATE => LiveTerm::State(position(self)?),
                code::LIVE_ENABLED => LiveTerm::Enabled(position(self)?),
                code::LIVE_ACTION => LiveTerm::Action {
                    atom: position(self)?,
                    enabled: if self.words.get(self.at) == Some(&-1) {
                        self.at += 1;
                        None
                    } else {
                        Some(position(self)?)
                    },
                },
                code::LIVE_NOT => LiveTerm::Not,
                code::LIVE_ALWAYS => LiveTerm::Always,
                code::LIVE_EVENTUALLY => LiveTerm::Eventually,
                code::LIVE_NEXT => LiveTerm::Next,
                code::LIVE_AND => LiveTerm::And(self.count()? as u32),
                code::LIVE_OR => LiveTerm::Or(self.count()? as u32),
                other => return self.error(format!("a liveness term {other}")),
            });
        }
        if self.at != end {
            return self.error("a liveness formula past its words");
        }
        Ok(terms)
    }

    fn count(&mut self) -> Decoded<usize> {
        let count = self.next()?;
        let remaining = self.words.len() - self.at;
        if count < 0 || count as usize > remaining {
            return self.error(format!("a count of {count} with {remaining} words left"));
        }
        Ok(count as usize)
    }

    // A 64-bit number as two words, the low first.
    fn long(&mut self) -> Decoded<u64> {
        let low = self.next()? as u32;
        let high = self.next()? as u32;
        Ok(u64::from(low) | (u64::from(high) << 32))
    }

    fn flag(&mut self) -> Decoded<bool> {
        match self.next()? {
            0 => Ok(false),
            1 => Ok(true),
            other => self.error(format!("{other} isn't 0 or 1")),
        }
    }

    fn below(&mut self, limit: usize, what: &str) -> Decoded<u32> {
        let word = self.next()?;
        if word < 0 || word as usize >= limit {
            return self.error(format!("{what} {word} isn't below {limit}"));
        }
        Ok(word as u32)
    }

    fn optional_below(&mut self, limit: usize, what: &str) -> Decoded<Option<u32>> {
        if self.words.get(self.at) == Some(&-1) {
            self.at += 1;
            return Ok(None);
        }
        self.below(limit, what).map(Some)
    }

    fn text(&mut self) -> Decoded<TextId> {
        self.below(self.text_count as usize, "text")
    }

    // A node's source range: its module's text, or -1 and zeros for none.
    fn range(&mut self) -> Decoded<Option<SourceRange>> {
        let module = self.next()?;
        if module == -1 {
            for _ in 0..4 {
                if self.next()? != 0 {
                    return self.error("a range without a module that has a position");
                }
            }
            return Ok(None);
        }
        if module < 0 || module as usize >= self.text_count as usize {
            return self.error(format!("the module text {module}"));
        }
        Ok(Some(SourceRange {
            module: module as TextId,
            start_line: self.next()?,
            start_column: self.next()?,
            end_line: self.next()?,
            end_column: self.next()?,
        }))
    }

    fn texts(&mut self) -> Decoded<Vec<TextId>> {
        let count = self.count()?;
        (0..count).map(|_| self.text()).collect()
    }

    fn params(&mut self) -> Decoded<Vec<Param>> {
        let count = self.count()?;
        (0..count)
            .map(|_| {
                Ok(Param {
                    name: self.text()?,
                    arity: self.next()?,
                })
            })
            .collect()
    }

    fn pending(&mut self) -> Decoded<Pending> {
        let word = self.at;
        let offset = self.next()?;
        Ok(Pending { word, offset })
    }

    fn resolve(&self, pending: &Pending) -> Decoded<NodeId> {
        match usize::try_from(pending.offset)
            .ok()
            .and_then(|offset| self.offsets.get(offset))
        {
            Some(&id) if id != u32::MAX => Ok(id),
            _ => Err(DecodeError {
                word: pending.word,
                message: format!("no node starts at offset {}", pending.offset),
            }),
        }
    }

    fn read(mut self, text: &[u8]) -> Decoded<Ir> {
        let ranked_count = self.next()?;
        let text_count = self.count()?;
        if ranked_count < 0 || ranked_count as usize > text_count {
            return self.error(format!("{ranked_count} ranked of {text_count} texts"));
        }
        let text = match std::str::from_utf8(text) {
            Ok(text) => text,
            Err(error) => return self.error(format!("text that isn't UTF-8: {error}")),
        };
        // Each text ends at a count of UTF-16 code units, as JavaScript measures it.
        let mut texts = Vec::with_capacity(text_count);
        let mut characters = text.char_indices().peekable();
        let (mut start, mut units) = (0, 0);
        for _ in 0..text_count {
            let end = self.next()?;
            while units < end {
                let Some((_, character)) = characters.next() else {
                    return self.error(format!("a text ending at {end}, past the text"));
                };
                units += character.len_utf16() as i32;
            }
            if units != end {
                return self.error(format!("a text ending at {end}, within a character"));
            }
            let byte = characters.peek().map_or(text.len(), |&(byte, _)| byte);
            texts.push(Box::from(&text[start..byte]));
            start = byte;
        }
        if start != text.len() {
            return self.error(format!(
                "{} bytes of text after the last",
                text.len() - start
            ));
        }
        self.text_count = text_count as u32;

        let variables = self.texts()?;
        let order_count = self.count()?;
        let tlc_order = (0..order_count)
            .map(|_| {
                self.below(variables.len(), "variable")
                    .map(|index| index as i32)
            })
            .collect::<Decoded<_>>()?;

        let builtin_count = self.count()?;
        let builtins = (0..builtin_count)
            .map(|_| {
                Ok(Builtin {
                    name: self.text()?,
                    arity: self.next()?,
                    flags: self.next()?,
                })
            })
            .collect::<Decoded<Vec<_>>>()?;

        // The values come after the constants and scopes that name them, so their ordinals are
        // checked once the values are read.
        let mut value_refs = Vec::new();
        let constant_count = self.count()?;
        let mut constants = Vec::with_capacity(constant_count);
        for _ in 0..constant_count {
            let name = self.text()?;
            value_refs.push(self.at);
            let value = self.value_ordinal()?;
            constants.push(Constant { name, value });
        }

        let scope_count = self.count()?;
        let mut scopes = Vec::with_capacity(scope_count);
        let mut scope_nodes = Vec::new();
        for _ in 0..scope_count {
            let parent = self.optional_below(scope_count, "scope")?;
            let name = self.text()?;
            let binding = match self.next()? {
                code::SCOPE_VALUE => {
                    value_refs.push(self.at);
                    ScopeBinding::Value(self.value_ordinal()?)
                }
                code::SCOPE_THUNK => {
                    scope_nodes.push(self.pending()?);
                    ScopeBinding::Thunk {
                        expression: 0,
                        scope: self.optional_below(scope_count, "scope")?,
                    }
                }
                code::SCOPE_CLOSURE => {
                    let name = self.text()?;
                    let params = self.params()?;
                    scope_nodes.push(self.pending()?);
                    ScopeBinding::Closure {
                        name,
                        params,
                        body: 0,
                        scope: self.optional_below(scope_count, "scope")?,
                    }
                }
                code::SCOPE_OPAQUE => ScopeBinding::Opaque,
                other => return self.error(format!("a scope binding of kind {other}")),
            };
            scopes.push(Scope {
                parent,
                name,
                binding,
            });
        }

        let values = self.values()?;
        if let Some(&word) = value_refs
            .iter()
            .find(|&&word| self.words[word] >= 0 && self.words[word] as usize >= values.list.len())
        {
            return Err(DecodeError {
                word,
                message: format!("value {} of {}", self.words[word], values.list.len()),
            });
        }

        let mut model_nodes = Vec::new();
        let mut model = self.model(scope_count, &mut model_nodes)?;

        let definition_count = self.count()?;
        let definition_offsets = (0..definition_count)
            .map(|_| self.pending())
            .collect::<Decoded<Vec<_>>>()?;
        let node_words = self.count()?;
        let nodes_start = self.at;
        if nodes_start + node_words != self.words.len() {
            return self.error(format!(
                "{node_words} words of nodes with {} left",
                self.words.len() - nodes_start
            ));
        }
        let limits = Limits {
            constants: constant_count,
            definitions: definition_count,
            builtins: builtin_count,
            values: values.list.len(),
        };
        let nodes = self.nodes(nodes_start, &limits)?;

        for (scope, pending) in scopes
            .iter_mut()
            .filter(|scope| {
                matches!(
                    scope.binding,
                    ScopeBinding::Thunk { .. } | ScopeBinding::Closure { .. }
                )
            })
            .zip(&scope_nodes)
        {
            let id = self.resolve(pending)?;
            match &mut scope.binding {
                ScopeBinding::Thunk { expression, .. } => *expression = id,
                ScopeBinding::Closure { body, .. } => *body = id,
                _ => unreachable!("only thunks and closures have nodes"),
            }
        }
        let mut resolved = model_nodes.iter().map(|pending| self.resolve(pending));
        model.visit_nodes(&mut |slot| {
            *slot = resolved.next().expect("a node for each slot")?;
            Ok(())
        })?;
        let definitions = definition_offsets
            .iter()
            .map(|pending| {
                let id = self.resolve(pending)?;
                match nodes.arena[id as usize].kind {
                    NodeKind::Definition(_) => Ok(id),
                    _ => Err(DecodeError {
                        word: pending.word,
                        message: format!("the node at {} isn't a definition", pending.offset),
                    }),
                }
            })
            .collect::<Decoded<_>>()?;

        Ok(Ir {
            ranked_count: ranked_count as u32,
            texts,
            variables,
            tlc_order,
            builtins,
            constants,
            scopes,
            values,
            model,
            definitions,
            nodes,
        })
    }

    fn value_ordinal(&mut self) -> Decoded<Option<u32>> {
        match self.next()? {
            -1 => Ok(None),
            ordinal if ordinal >= 0 => Ok(Some(ordinal as u32)),
            other => self.error(format!("value {other}")),
        }
    }

    fn values(&mut self) -> Decoded<Values> {
        let count = self.count()?;
        let strings = self.texts()?;
        let word_count = self.count()?;
        let end = self.at + word_count;
        let list = (0..count)
            .map(|_| self.value(strings.len(), 0))
            .collect::<Decoded<_>>()?;
        if self.at != end {
            return self.error(format!("the values end at {}, not {end}", self.at));
        }
        Ok(Values { strings, list })
    }

    fn value(&mut self, string_count: usize, depth: usize) -> Decoded<Value> {
        if depth > MAXIMUM_DEPTH {
            return self.error("values nested too deep");
        }
        let elements = |decoder: &mut Self, count: usize| {
            (0..count)
                .map(|_| decoder.value(string_count, depth + 1))
                .collect::<Decoded<Vec<_>>>()
        };
        Ok(match self.next()? {
            code::FALSE => Value::Bool(false),
            code::TRUE => Value::Bool(true),
            code::INTEGER => Value::Int(self.next()?),
            code::STRING => Value::String(self.below(string_count, "string")?),
            code::MODEL_VALUE => Value::ModelValue(self.below(string_count, "string")?),
            code::SET => {
                let count = self.count()?;
                Value::Set(elements(self, count)?)
            }
            code::FUNCTION => {
                let class = self.next()?;
                let count = self.count()?;
                Value::Function {
                    class,
                    domain: elements(self, count)?,
                    range: elements(self, count)?,
                }
            }
            code::INTERVAL_FUNCTION => {
                let class = self.next()?;
                let low = self.next()?;
                let count = self.count()?;
                Value::IntervalFunction {
                    class,
                    low,
                    range: elements(self, count)?,
                }
            }
            other => return self.error(format!("a value of tag {other}")),
        })
    }

    fn config_names(&mut self, is_printed: bool) -> Decoded<Vec<Printed<ConfigName>>> {
        let count = self.count()?;
        (0..count)
            .map(|_| {
                let name = self.text()?;
                // Definitions are checked against their count once it is read.
                let definition = match self.next()? {
                    -1 => None,
                    index if index >= 0 => Some(index as u32),
                    other => return self.error(format!("definition {other}")),
                };
                let has_repeated_effect = if is_printed { self.flag()? } else { false };
                Ok(Printed {
                    root: ConfigName { name, definition },
                    has_repeated_effect,
                })
            })
            .collect()
    }

    fn unprinted(&mut self) -> Decoded<Vec<ConfigName>> {
        Ok(self
            .config_names(false)?
            .into_iter()
            .map(|printed| printed.root)
            .collect())
    }

    fn model(&mut self, scope_count: usize, pending: &mut Vec<Pending>) -> Decoded<Model> {
        let mut node = |decoder: &mut Self| -> Decoded<NodeId> {
            pending.push(decoder.pending()?);
            Ok(0)
        };
        let init = node(self)?;
        let next = node(self)?;
        let scope = self.optional_below(scope_count, "scope")?;
        let count = self.count()?;
        let actions = (0..count)
            .map(|_| {
                Ok(Action {
                    expression: node(self)?,
                    scope: self.optional_below(scope_count, "scope")?,
                    label: self.text()?,
                })
            })
            .collect::<Decoded<_>>()?;
        let is_labelled = self.flag()?;
        let invariants = self.config_names(true)?;
        let count = self.count()?;
        let (property_invariants, property_invariant_names) = (0..count)
            .map(|_| {
                Ok((
                    Printed {
                        root: node(self)?,
                        has_repeated_effect: self.flag()?,
                    },
                    self.text()?,
                ))
            })
            .collect::<Decoded<Vec<_>>>()?
            .into_iter()
            .unzip();
        let constraints = self.unprinted()?;
        let action_constraints = self.unprinted()?;
        let possible = self
            .config_names(true)?
            .into_iter()
            .map(|named| Possible {
                name: named.root,
                is_action: named.has_repeated_effect,
            })
            .collect();
        let count = self.count()?;
        let action_properties = (0..count)
            .map(|_| {
                Ok(ActionProperty {
                    action: node(self)?,
                    subscript: node(self)?,
                })
            })
            .collect::<Decoded<_>>()?;
        let count = self.count()?;
        let initial_predicates = (0..count).map(|_| node(self)).collect::<Decoded<_>>()?;
        let mut views = self.unprinted()?;
        if views.len() > 1 {
            return self.error(format!("{} views", views.len()));
        }
        let view = views.pop();
        let mut aliases = self.unprinted()?;
        if aliases.len() > 1 {
            return self.error(format!("{} aliases", aliases.len()));
        }
        let alias = aliases.pop();
        let symmetry = match self.next()? {
            -1 => None,
            count if count >= 0 => Some(
                (0..count)
                    .map(|_| {
                        let pairs = self.count()?;
                        (0..pairs)
                            .map(|_| Ok((self.text()?, self.text()?)))
                            .collect::<Decoded<Vec<_>>>()
                    })
                    .collect::<Decoded<_>>()?,
            ),
            other => return self.error(format!("{other} permutations")),
        };
        let check_deadlock = self.flag()?;
        let is_warning_enabled = self.flag()?;
        let is_recording_graph = self.flag()?;
        let version = self.optional_below(self.text_count as usize, "text")?;
        let random_seed = self.long()?;
        let startup_random = self.long()?;
        let count = self.count()?;
        let mut atoms = Vec::with_capacity(count);
        for _ in 0..count {
            let kind = self.next()?;
            let expression = node(self)?;
            let unchanged = if self.words.get(self.at) == Some(&-1) {
                self.at += 1;
                None
            } else {
                Some(node(self)?)
            };
            let scope = self.optional_below(scope_count, "scope")?;
            let actions = match self.words.get(self.at) {
                Some(&code::ENABLED_UNKNOWN) => {
                    self.at += 1;
                    EnabledActions::Unknown
                }
                Some(&code::ENABLED_ALL) => {
                    self.at += 1;
                    EnabledActions::All
                }
                _ => {
                    let count = self.count()?;
                    EnabledActions::Some((0..count).map(|_| self.next()).collect::<Decoded<_>>()?)
                }
            };
            let kind = match (kind, unchanged, actions) {
                (code::ATOM_STATE, None, EnabledActions::Unknown) => AtomKind::State,
                (code::ATOM_ACTION, unchanged, EnabledActions::Unknown) => AtomKind::Action {
                    unchanged,
                    enabled: self.optional_below(count, "atom")?,
                },
                (code::ATOM_ENABLED, None, actions) => AtomKind::Enabled { actions },
                (kind, ..) => return self.error(format!("an atom of kind {kind}")),
            };
            atoms.push(Atom {
                kind,
                expression,
                scope,
            });
        }
        let live_formula = self.live_terms()?;
        let count = self.count()?;
        let live_properties = (0..count)
            .map(|_| {
                Ok(LiveProperty {
                    name: self.text()?,
                    formula: self.live_terms()?,
                })
            })
            .collect::<Decoded<_>>()?;
        Ok(Model {
            init,
            next,
            scope,
            actions,
            is_labelled,
            invariants,
            property_invariants,
            property_invariant_names,
            constraints,
            action_constraints,
            possible,
            action_properties,
            initial_predicates,
            view,
            alias,
            symmetry,
            check_deadlock,
            is_warning_enabled,
            is_recording_graph,
            version,
            random_seed,
            startup_random,
            atoms,
            live_formula,
            live_properties,
        })
    }

    fn nodes(&mut self, start: usize, limits: &Limits) -> Decoded<Nodes> {
        self.offsets = vec![u32::MAX; self.words.len() - start];
        let mut nodes = Nodes::default();
        while self.at < self.words.len() {
            let id = self.node(start, limits, &mut nodes)?;
            nodes.top.push(id);
        }
        Ok(nodes)
    }

    fn node(&mut self, start: usize, limits: &Limits, nodes: &mut Nodes) -> Decoded<NodeId> {
        self.depth += 1;
        if self.depth > MAXIMUM_DEPTH {
            return self.error("nodes nested too deep");
        }
        let offset = self.at - start;
        let word = self.next()?;
        let (tag, flags) = (word & 0xff, word >> 8);
        if tag == tag::REFERENCE {
            let target = self.pending()?;
            if target.offset < 0 || target.offset as usize >= offset {
                return self.error(format!("a reference forward to {}", target.offset));
            }
            let id = self.resolve(&target)?;
            self.depth -= 1;
            return Ok(self.push(nodes, offset, (0, 0, None), NodeKind::Reference(id)));
        }
        let line = self.next()?;
        let column = self.next()?;
        let range = self.range()?;
        let is_flagged = match (tag, flags) {
            (tag::DEFINITION, _) | (_, 0) => false,
            (_, 1) => true,
            _ => return self.error(format!("tag {tag} with flags {flags}")),
        };
        if is_flagged
            && !matches!(
                tag,
                tag::NUMBER
                    | tag::IDENTIFIER
                    | tag::APPLY
                    | tag::AND
                    | tag::OR
                    | tag::CASE
                    | tag::UNBOUNDED_QUANTIFIER
                    | tag::FUNCTION_CONSTRUCTION
            )
        {
            return self.error(format!("tag {tag} with a flag"));
        }
        // The node's id is taken before its children's, as its offset comes before theirs.
        let id = self.push(nodes, offset, (line, column, range), NodeKind::ExceptAt);
        let mut junction = None;
        let mut child = |decoder: &mut Self| decoder.node(start, limits, nodes);
        let kind = match tag {
            tag::NUMBER if is_flagged => NodeKind::WideNumber(self.text()?),
            tag::NUMBER => NodeKind::Number(self.next()?),
            tag::DECIMAL => NodeKind::Decimal(self.text()?),
            tag::STRING => NodeKind::String(self.text()?),
            tag::IDENTIFIER => NodeKind::Identifier(self.name(is_flagged, limits)?),
            tag::APPLY => {
                let name = self.name(is_flagged, limits)?;
                let args = self.children(&mut child)?;
                NodeKind::Apply { name, args }
            }
            tag::OPERATOR_REFERENCE => NodeKind::OperatorReference(self.name(false, limits)?),
            tag::LAMBDA => NodeKind::Lambda {
                params: self.texts()?,
                body: child(self)?,
            },
            tag::AND | tag::OR => {
                let count = self.count()?;
                let prefix_ends = (0..count)
                    .map(|_| Ok((self.next()?, self.next()?)))
                    .collect::<Decoded<Vec<_>>>()?;
                if is_flagged || !prefix_ends.is_empty() {
                    junction = Some(Junction {
                        is_bulleted: is_flagged,
                        prefix_ends,
                    });
                }
                let operands = self.children(&mut child)?;
                if tag == tag::AND {
                    NodeKind::And(operands)
                } else {
                    NodeKind::Or(operands)
                }
            }
            tag::PRIME => NodeKind::Prime(child(self)?),
            tag::UNCHANGED => NodeKind::Unchanged(child(self)?),
            tag::ENABLED => NodeKind::Enabled(child(self)?),
            tag::ALWAYS => NodeKind::Always(child(self)?),
            tag::EVENTUALLY => NodeKind::Eventually(child(self)?),
            tag::IF => NodeKind::If {
                condition: child(self)?,
                consequent: child(self)?,
                alternative: child(self)?,
            },
            tag::CASE => {
                let count = self.count()?;
                let arms = (0..count)
                    .map(|_| Ok((child(self)?, child(self)?)))
                    .collect::<Decoded<_>>()?;
                let other = if is_flagged { Some(child(self)?) } else { None };
                NodeKind::Case { arms, other }
            }
            tag::LET => {
                let instances = self.count()? as u32;
                let definitions = self.children(&mut child)?;
                NodeKind::Let {
                    instances,
                    definitions,
                    body: child(self)?,
                }
            }
            tag::FORALL => NodeKind::Forall {
                bounds: self.bounds(&mut child)?,
                body: child(self)?,
            },
            tag::EXISTS => NodeKind::Exists {
                bounds: self.bounds(&mut child)?,
                body: child(self)?,
            },
            tag::UNBOUNDED_QUANTIFIER => NodeKind::UnboundedQuantifier {
                is_forall: is_flagged,
                names: self.texts()?,
                body: child(self)?,
            },
            tag::CHOOSE => {
                let pattern = self.pattern()?;
                let set = if self.flag()? {
                    Some(child(self)?)
                } else {
                    None
                };
                NodeKind::Choose {
                    pattern,
                    set,
                    body: child(self)?,
                }
            }
            tag::SET_ENUMERATION => NodeKind::SetEnumeration(self.children(&mut child)?),
            tag::TUPLE => NodeKind::Tuple(self.children(&mut child)?),
            tag::SET_FILTER => {
                let mut bounds = self.bounds(&mut child)?;
                if bounds.len() != 1 {
                    return self.error(format!("a set filter with {} bounds", bounds.len()));
                }
                NodeKind::SetFilter {
                    bound: bounds.pop().expect("one bound"),
                    predicate: child(self)?,
                }
            }
            tag::SET_MAP => NodeKind::SetMap {
                expression: child(self)?,
                bounds: self.bounds(&mut child)?,
            },
            tag::FUNCTION_CONSTRUCTION => NodeKind::FunctionConstruction {
                is_recursive: is_flagged,
                bounds: self.bounds(&mut child)?,
                body: child(self)?,
            },
            tag::FUNCTION_SET => NodeKind::FunctionSet {
                domain: child(self)?,
                range: child(self)?,
            },
            tag::RECORD => NodeKind::Record(self.fields(&mut child)?),
            tag::RECORD_SET => NodeKind::RecordSet(self.fields(&mut child)?),
            tag::EXCEPT => {
                let function = child(self)?;
                let count = self.count()?;
                let mut updates = Vec::with_capacity(count);
                for _ in 0..count {
                    let steps = self.count()?;
                    let mut path = Vec::with_capacity(steps);
                    for _ in 0..steps {
                        path.push(match self.next()? {
                            0 => PathStep::Field(self.text()?),
                            1 => PathStep::Index(self.children(&mut child)?),
                            other => return self.error(format!("an EXCEPT step of kind {other}")),
                        });
                    }
                    updates.push(Update {
                        path,
                        value: child(self)?,
                    });
                }
                NodeKind::Except { function, updates }
            }
            tag::EXCEPT_AT => NodeKind::ExceptAt,
            tag::FUNCTION_APPLICATION => NodeKind::FunctionApplication {
                function: child(self)?,
                args: self.children(&mut child)?,
            },
            tag::BRACKET => NodeKind::Bracket(self.children(&mut child)?),
            tag::FIELD_ACCESS => NodeKind::FieldAccess {
                record: child(self)?,
                field: self.text()?,
            },
            tag::PRODUCT => NodeKind::Product(self.children(&mut child)?),
            tag::BOX_ACTION => NodeKind::BoxAction {
                action: child(self)?,
                subscript: child(self)?,
            },
            tag::ANGLE_ACTION => NodeKind::AngleAction {
                action: child(self)?,
                subscript: child(self)?,
            },
            tag::WEAK_FAIRNESS | tag::STRONG_FAIRNESS => {
                let subscript = child(self)?;
                let action = child(self)?;
                let enabled = if self.flag()? {
                    Some(child(self)?)
                } else {
                    None
                };
                if tag == tag::WEAK_FAIRNESS {
                    NodeKind::WeakFairness {
                        subscript,
                        action,
                        enabled,
                    }
                } else {
                    NodeKind::StrongFairness {
                        subscript,
                        action,
                        enabled,
                    }
                }
            }
            tag::LABEL => NodeKind::Label {
                name: self.text()?,
                params: self.texts()?,
                body: child(self)?,
            },
            tag::SUBEXPRESSION => {
                let count = self.count()?;
                let mut selectors = Vec::with_capacity(count);
                for _ in 0..count {
                    selectors.push(match self.next()? {
                        0 => Selector::Name {
                            name: self.text()?,
                            args: self.children(&mut child)?,
                        },
                        1 => Selector::Operand(self.next()?),
                        2 => Selector::Bound(self.children(&mut child)?),
                        3 => Selector::At,
                        4 => Selector::Colon,
                        other => return self.error(format!("a selector of kind {other}")),
                    });
                }
                NodeKind::Subexpression(selectors)
            }
            tag::DEFINITION => {
                if flags & !0x1f != 0 {
                    return self.error(format!("definition flags {flags}"));
                }
                let name = self.text()?;
                let startup = match self.next()? {
                    code::NO_STARTUP_VALUE => Startup::None,
                    code::OBJECT_STARTUP_VALUE => Startup::Object,
                    ordinal if (ordinal as usize) < limits.values => {
                        Startup::Value(Some(ordinal as u32))
                    }
                    other => return self.error(format!("startup value {other}")),
                };
                let form = match self.next()? {
                    0 => DefinitionForm::Operator(self.params()?),
                    1 => DefinitionForm::Function(self.bounds(&mut child)?),
                    other => return self.error(format!("a definition of kind {other}")),
                };
                NodeKind::Definition(Definition {
                    name,
                    flags,
                    startup,
                    form,
                    body: child(self)?,
                })
            }
            other => return self.error(format!("tag {other}")),
        };
        if let NodeKind::Let { definitions, .. } = &kind
            && let Some(&definition) = definitions
                .iter()
                .find(|&&id| !matches!(nodes.arena[id as usize].kind, NodeKind::Definition(_)))
        {
            return self.error(format!("a LET defines node {definition}"));
        }
        nodes.arena[id as usize].kind = kind;
        if let Some(junction) = junction {
            nodes.junctions.insert(id, junction);
        }
        self.depth -= 1;
        Ok(id)
    }

    fn push(
        &mut self,
        nodes: &mut Nodes,
        offset: usize,
        (line, column, range): (i32, i32, Option<SourceRange>),
        kind: NodeKind,
    ) -> NodeId {
        let id = self.node_count;
        self.node_count += 1;
        self.offsets[offset] = id;
        nodes.arena.push(Node {
            line,
            column,
            range,
            kind,
        });
        id
    }

    fn children(
        &mut self,
        child: &mut impl FnMut(&mut Self) -> Decoded<NodeId>,
    ) -> Decoded<Vec<NodeId>> {
        let count = self.count()?;
        (0..count).map(|_| child(self)).collect()
    }

    fn pattern(&mut self) -> Decoded<Pattern> {
        match self.next()? {
            0 => Ok(Pattern::Name(self.text()?)),
            1 => Ok(Pattern::Tuple(self.texts()?)),
            other => self.error(format!("a pattern of kind {other}")),
        }
    }

    fn bounds(
        &mut self,
        child: &mut impl FnMut(&mut Self) -> Decoded<NodeId>,
    ) -> Decoded<Vec<Bound>> {
        let count = self.count()?;
        (0..count)
            .map(|_| {
                Ok(Bound {
                    pattern: self.pattern()?,
                    set: child(self)?,
                })
            })
            .collect()
    }

    fn fields(
        &mut self,
        child: &mut impl FnMut(&mut Self) -> Decoded<NodeId>,
    ) -> Decoded<Vec<(TextId, NodeId)>> {
        let count = self.count()?;
        (0..count)
            .map(|_| Ok((self.text()?, child(self)?)))
            .collect()
    }

    fn name(&mut self, is_local: bool, limits: &Limits) -> Decoded<Name> {
        let text = self.text()?;
        let kind = self.next()?;
        let payload = self.next()?;
        let within = |limit: usize| payload >= 0 && (payload as usize) < limit;
        let resolution = match kind {
            code::RESOLUTION_NONE if payload == 0 => Resolution::None,
            // The variable of an instance that ENABLED's rewrite names, such as x@ENABLED, may
            // have a slot past the state's, as in the TypeScript environment.
            code::RESOLUTION_VARIABLE if payload >= 0 => Resolution::Variable(payload as u32),
            code::RESOLUTION_CONSTANT if within(limits.constants) => {
                Resolution::Constant(payload as Index)
            }
            code::RESOLUTION_DEFINITION if within(limits.definitions) => {
                Resolution::Definition(payload as Index)
            }
            code::RESOLUTION_BUILTIN if within(limits.builtins) => {
                Resolution::Builtin(payload as Index)
            }
            _ => return self.error(format!("a resolution of kind {kind} to {payload}")),
        };
        Ok(Name {
            text,
            resolution,
            is_local,
        })
    }
}

struct Limits {
    constants: usize,
    definitions: usize,
    builtins: usize,
    values: usize,
}

impl Model {
    /// Calls `visit` on every node the model refers to, in the order of the blob.
    pub fn visit_nodes(
        &mut self,
        visit: &mut impl FnMut(&mut NodeId) -> Decoded<()>,
    ) -> Decoded<()> {
        visit(&mut self.init)?;
        visit(&mut self.next)?;
        for action in &mut self.actions {
            visit(&mut action.expression)?;
        }
        for invariant in &mut self.property_invariants {
            visit(&mut invariant.root)?;
        }
        for property in &mut self.action_properties {
            visit(&mut property.action)?;
            visit(&mut property.subscript)?;
        }
        for predicate in &mut self.initial_predicates {
            visit(predicate)?;
        }
        for atom in &mut self.atoms {
            visit(&mut atom.expression)?;
            if let AtomKind::Action {
                unchanged: Some(unchanged),
                ..
            } = &mut atom.kind
            {
                visit(unchanged)?;
            }
        }
        Ok(())
    }
}
