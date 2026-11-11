//! Writes an [`Ir`] as `src/engine/ir.ts` does, so that decoding a blob and encoding it again gives
//! the same bytes.

use crate::{
    AtomKind, Bound, Builtin, ConfigName, DefinitionForm, EnabledActions, IR_VERSION, Ir, Junction,
    LiveTerm, MAGIC, Name, NodeId, NodeKind, Param, PathStep, Pattern, Resolution, ScopeBinding,
    Selector, SourceRange, Value, code, tag,
};

/// Encodes an IR.
pub fn encode(ir: &Ir) -> Vec<u8> {
    crate::on_nesting_stack(|| encode_here(ir))
}

fn encode_here(ir: &Ir) -> Vec<u8> {
    let mut nodes = NodeWriter {
        ir,
        words: Vec::new(),
        offsets: vec![-1; ir.nodes.arena.len()],
    };
    for &id in &ir.nodes.top {
        nodes.node(id);
    }
    let offset = |id: NodeId| nodes.offsets[id as usize];
    let optional = |index: Option<u32>| index.map_or(-1, |index| index as i32);

    let mut words = vec![
        MAGIC as i32,
        IR_VERSION as i32,
        0,
        0,
        ir.ranked_count as i32,
    ];
    words.push(ir.texts.len() as i32);
    // The texts' units are encoded together, as JavaScript encodes them joined, so a lone surrogate
    // that ends a text and one that starts the next are one code point.
    let mut units = Vec::new();
    for id in 0..ir.texts.len() as crate::TextId {
        units.extend(ir.get_text_units(id));
        words.push(units.len() as i32);
    }
    let mut text = Vec::new();
    crate::wtf8::encode(&units, &mut text);
    words.push(ir.variables.len() as i32);
    words.extend(ir.variables.iter().map(|&variable| variable as i32));
    words.push(ir.tlc_order.len() as i32);
    words.extend(&ir.tlc_order);
    words.push(ir.builtins.len() as i32);
    for builtin in &ir.builtins {
        words.extend([builtin.name as i32, builtin.arity, builtin.flags]);
        if builtin.flags & Builtin::TABLE != 0 {
            words.push(builtin.table.len() as i32);
            for &(arguments, value) in &builtin.table {
                words.extend([optional(arguments), optional(value)]);
            }
        }
    }
    words.push(ir.constants.len() as i32);
    for constant in &ir.constants {
        words.extend([constant.name as i32, optional(constant.value)]);
    }
    words.push(ir.scopes.len() as i32);
    for scope in &ir.scopes {
        words.extend([optional(scope.parent), scope.name as i32]);
        match &scope.binding {
            ScopeBinding::Value(value) => words.extend([code::SCOPE_VALUE, optional(*value)]),
            ScopeBinding::Thunk { expression, scope } => {
                words.extend([code::SCOPE_THUNK, offset(*expression), optional(*scope)]);
            }
            ScopeBinding::Closure {
                name,
                params,
                body,
                scope,
            } => {
                words.extend([code::SCOPE_CLOSURE, *name as i32]);
                write_params(&mut words, params);
                words.extend([offset(*body), optional(*scope)]);
            }
            ScopeBinding::Opaque => words.push(code::SCOPE_OPAQUE),
        }
    }
    words.push(ir.values.list.len() as i32);
    words.push(ir.values.strings.len() as i32);
    words.extend(ir.values.strings.iter().map(|&text| text as i32));
    let mut values = Vec::new();
    for value in &ir.values.list {
        write_value(&mut values, value);
    }
    words.push(values.len() as i32);
    words.extend(values);

    let model = &ir.model;
    words.extend([
        offset(model.init),
        model.next.map_or(-1, offset),
        optional(model.scope),
    ]);
    words.push(model.actions.len() as i32);
    for action in &model.actions {
        words.extend([
            offset(action.expression),
            optional(action.scope),
            action.label as i32,
            action.name as i32,
        ]);
        words.extend(range_words(action.location));
        words.push(optional(action.definition));
    }
    words.push(model.is_labelled as i32);
    let config_name = |name: &ConfigName| [name.name as i32, optional(name.definition)].into_iter();
    words.push(model.invariants.len() as i32);
    for invariant in &model.invariants {
        words.extend(config_name(&invariant.root));
        words.push(invariant.has_repeated_effect as i32);
    }
    words.push(model.property_invariants.len() as i32);
    for ((invariant, &name), &scope) in model
        .property_invariants
        .iter()
        .zip(&model.property_invariant_names)
        .zip(&model.property_invariant_scopes)
    {
        words.extend([
            offset(invariant.root),
            optional(scope),
            invariant.has_repeated_effect as i32,
            name as i32,
        ]);
    }
    for names in [&model.constraints, &model.action_constraints] {
        words.push(names.len() as i32);
        words.extend(names.iter().flat_map(config_name));
    }
    words.push(model.possible.len() as i32);
    for possible in &model.possible {
        words.extend(config_name(&possible.name));
        words.push(possible.is_action as i32);
    }
    words.push(model.action_properties.len() as i32);
    for property in &model.action_properties {
        words.extend([
            offset(property.action),
            offset(property.subscript),
            optional(property.scope),
            property.name as i32,
        ]);
    }
    words.push(model.initial_predicates.len() as i32);
    for ((&predicate, &scope), &name) in model
        .initial_predicates
        .iter()
        .zip(&model.initial_predicate_scopes)
        .zip(&model.initial_predicate_names)
    {
        words.extend([offset(predicate), name as i32, optional(scope)]);
    }
    words.push(model.view.is_some() as i32);
    words.extend(model.view.iter().flat_map(config_name));
    words.push(model.alias.is_some() as i32);
    words.extend(model.alias.iter().flat_map(config_name));
    words.push(model.postconditions.len() as i32);
    words.extend(model.postconditions.iter().flat_map(config_name));
    words.extend([
        model.check_deadlock as i32,
        model.is_warning_enabled as i32,
        model.is_recording_graph as i32,
        optional(model.version),
    ]);
    let long = model.random_seed;
    words.extend([long as u32 as i32, (long >> 32) as u32 as i32]);
    words.push(model.atoms.len() as i32);
    for atom in &model.atoms {
        let (kind, unchanged, actions) = match &atom.kind {
            AtomKind::State => (code::ATOM_STATE, None, &EnabledActions::Unknown),
            AtomKind::Action { unchanged, .. } => {
                (code::ATOM_ACTION, *unchanged, &EnabledActions::Unknown)
            }
            AtomKind::Enabled { actions } => (code::ATOM_ENABLED, None, actions),
        };
        words.extend([
            kind,
            offset(atom.expression),
            unchanged.map_or(-1, offset),
            optional(atom.scope),
        ]);
        match actions {
            EnabledActions::Unknown => words.push(code::ENABLED_UNKNOWN),
            EnabledActions::All => words.push(code::ENABLED_ALL),
            EnabledActions::Some(positions) => {
                words.push(positions.len() as i32);
                words.extend(positions);
            }
        }
        if let AtomKind::Action { enabled, .. } = &atom.kind {
            words.push(optional(*enabled));
        }
    }
    push_live(&mut words, &model.live_formula);
    words.push(model.live_properties.len() as i32);
    for property in &model.live_properties {
        words.push(property.name as i32);
        push_live(&mut words, &property.formula);
    }
    words.extend(range_words(model.specification));
    let startup = &model.startup;
    words.push(startup.substitutes.len() as i32);
    for &(name, definition) in &startup.substitutes {
        words.extend([name as i32, definition as i32]);
    }
    words.push(startup.definitions.len() as i32);
    words.extend(
        startup
            .definitions
            .iter()
            .map(|&definition| definition as i32),
    );
    words.push(startup.predicates.len() as i32);
    for predicate in &startup.predicates {
        words.extend([
            predicate.form as i32,
            predicate.kind as i32,
            predicate.name as i32,
            predicate.definition as i32,
        ]);
    }
    match &startup.symmetry {
        None => words.push(-1),
        Some(symmetry) => {
            words.extend([
                symmetry.definition as i32,
                symmetry.permuted_sets.len() as i32,
            ]);
            for set in &symmetry.permuted_sets {
                words.extend([set.name as i32, set.operand.map_or(-1, offset)]);
            }
        }
    }
    words.push(startup.assumptions.len() as i32);
    for &(assumption, name) in &startup.assumptions {
        words.extend([offset(assumption), name as i32]);
    }
    words.extend(range_words(model.next_substitution));
    words.push(model.instance_actions.len() as i32);
    for action in &model.instance_actions {
        words.extend([action.definition as i32, action.name as i32]);
        words.extend(range_words(action.location));
    }
    words.push(model.instance_names.len() as i32);
    for &(definition, name) in &model.instance_names {
        words.extend([definition as i32, name as i32]);
    }
    words.push(model.tlc_spec.map_or(-1, |value| value as i32));
    words.push(model.periodic.is_some() as i32);
    words.extend(model.periodic.iter().flat_map(config_name));
    words.push(ir.definitions.len() as i32);
    words.extend(ir.definitions.iter().map(|&id| offset(id)));
    words.push(nodes.words.len() as i32);
    words.extend(&nodes.words);
    words[2] = words.len() as i32;
    words[3] = text.len() as i32;

    let mut bytes = Vec::with_capacity(words.len() * 4 + text.len() + 3);
    for word in words {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    bytes.extend_from_slice(&text);
    bytes.resize(bytes.len().next_multiple_of(4), 0);
    bytes
}

// A source range: its module's text and its positions, or -1 and zeros for none.
fn range_words(range: Option<SourceRange>) -> [i32; 5] {
    match range {
        Some(range) => [
            range.module as i32,
            range.start_line,
            range.start_column,
            range.end_line,
            range.end_column,
        ],
        None => [-1, 0, 0, 0, 0],
    }
}

fn write_params(words: &mut Vec<i32>, params: &[Param]) {
    words.push(params.len() as i32);
    for param in params {
        words.extend([param.name as i32, param.arity]);
    }
}

fn write_value(words: &mut Vec<i32>, value: &Value) {
    match value {
        Value::Bool(false) => words.push(code::FALSE),
        Value::Bool(true) => words.push(code::TRUE),
        Value::Int(value) => words.extend([code::INTEGER, *value]),
        Value::String(index) => words.extend([code::STRING, *index as i32]),
        Value::ModelValue(index) => words.extend([code::MODEL_VALUE, *index as i32]),
        Value::Set(elements) => {
            words.extend([code::SET, elements.len() as i32]);
            elements
                .iter()
                .for_each(|element| write_value(words, element));
        }
        Value::Function {
            class,
            domain,
            range,
        } => {
            words.extend([code::FUNCTION, *class, domain.len() as i32]);
            domain
                .iter()
                .chain(range)
                .for_each(|element| write_value(words, element));
        }
        Value::IntervalFunction { class, low, range } => {
            words.extend([code::INTERVAL_FUNCTION, *class, *low, range.len() as i32]);
            range.iter().for_each(|element| write_value(words, element));
        }
    }
}

struct NodeWriter<'a> {
    ir: &'a Ir,
    words: Vec<i32>,
    // The offset each node was written at, or -1 until it is.
    offsets: Vec<i32>,
}

impl<'a> NodeWriter<'a> {
    fn node(&mut self, id: NodeId) {
        let node = &self.ir.nodes.arena[id as usize];
        self.offsets[id as usize] = self.words.len() as i32;
        if let NodeKind::Reference(target) = node.kind {
            let target = self.offsets[target as usize];
            self.words.extend([tag::REFERENCE, target]);
            return;
        }
        let flag = |is_set: bool| if is_set { tag::FLAG } else { 0 };
        let tag_word = match &node.kind {
            NodeKind::Number(_) => tag::NUMBER,
            NodeKind::WideNumber(_) => tag::NUMBER | tag::FLAG,
            NodeKind::Decimal(_) => tag::DECIMAL,
            NodeKind::String(_) => tag::STRING,
            NodeKind::Identifier(name) => tag::IDENTIFIER | flag(name.is_local),
            NodeKind::Apply { name, .. } => tag::APPLY | flag(name.is_local),
            NodeKind::OperatorReference(_) => tag::OPERATOR_REFERENCE,
            NodeKind::Lambda { .. } => tag::LAMBDA,
            NodeKind::And(_) => tag::AND | flag(self.junction(id).is_bulleted),
            NodeKind::Or(_) => tag::OR | flag(self.junction(id).is_bulleted),
            NodeKind::Prime(_) => tag::PRIME,
            NodeKind::Unchanged(_) => tag::UNCHANGED,
            NodeKind::Enabled(_) => tag::ENABLED,
            NodeKind::If { .. } => tag::IF,
            NodeKind::Case { other, .. } => tag::CASE | flag(other.is_some()),
            NodeKind::Let { .. } => tag::LET,
            NodeKind::Forall { .. } => tag::FORALL,
            NodeKind::Exists { .. } => tag::EXISTS,
            NodeKind::UnboundedQuantifier { is_forall, .. } => {
                tag::UNBOUNDED_QUANTIFIER | flag(*is_forall)
            }
            NodeKind::Choose { .. } => tag::CHOOSE,
            NodeKind::SetEnumeration(_) => tag::SET_ENUMERATION,
            NodeKind::SetFilter { .. } => tag::SET_FILTER,
            NodeKind::SetMap { .. } => tag::SET_MAP,
            NodeKind::Tuple(_) => tag::TUPLE,
            NodeKind::FunctionConstruction { is_recursive, .. } => {
                tag::FUNCTION_CONSTRUCTION | flag(*is_recursive)
            }
            NodeKind::FunctionSet { .. } => tag::FUNCTION_SET,
            NodeKind::Record(_) => tag::RECORD,
            NodeKind::RecordSet(_) => tag::RECORD_SET,
            NodeKind::Except { .. } => tag::EXCEPT,
            NodeKind::ExceptAt => tag::EXCEPT_AT,
            NodeKind::FunctionApplication { .. } => tag::FUNCTION_APPLICATION,
            NodeKind::Bracket(_) => tag::BRACKET,
            NodeKind::FieldAccess { .. } => tag::FIELD_ACCESS,
            NodeKind::Product(_) => tag::PRODUCT,
            NodeKind::Always(_) => tag::ALWAYS,
            NodeKind::Eventually(_) => tag::EVENTUALLY,
            NodeKind::BoxAction { .. } => tag::BOX_ACTION,
            NodeKind::AngleAction { .. } => tag::ANGLE_ACTION,
            NodeKind::WeakFairness { .. } => tag::WEAK_FAIRNESS,
            NodeKind::StrongFairness { .. } => tag::STRONG_FAIRNESS,
            NodeKind::Label { .. } => tag::LABEL,
            NodeKind::Subexpression(_) => tag::SUBEXPRESSION,
            NodeKind::Definition(definition) => {
                tag::DEFINITION | definition.flags << tag::DEFINITION_FLAGS
            }
            NodeKind::Reference(_) => unreachable!("written above"),
        };
        self.words.extend([tag_word, node.line, node.column]);
        self.words.extend(range_words(node.range));
        match &node.kind {
            NodeKind::Number(value) => self.words.push(*value),
            NodeKind::WideNumber(text) | NodeKind::Decimal(text) | NodeKind::String(text) => {
                self.words.push(*text as i32)
            }
            NodeKind::Identifier(name) | NodeKind::OperatorReference(name) => self.name(name),
            NodeKind::Apply { name, args } => {
                self.name(name);
                self.children(args);
            }
            NodeKind::Lambda { params, body } => {
                self.texts(params);
                self.node(*body);
            }
            NodeKind::And(children) | NodeKind::Or(children) => {
                let prefix_ends = &self.junction(id).prefix_ends;
                self.words.push(prefix_ends.len() as i32);
                for &(line, column) in prefix_ends {
                    self.words.extend([line, column]);
                }
                self.children(children);
            }
            NodeKind::SetEnumeration(children)
            | NodeKind::Tuple(children)
            | NodeKind::Bracket(children)
            | NodeKind::Product(children) => self.children(children),
            NodeKind::Prime(child)
            | NodeKind::Unchanged(child)
            | NodeKind::Enabled(child)
            | NodeKind::Always(child)
            | NodeKind::Eventually(child) => self.node(*child),
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } => {
                self.node(*condition);
                self.node(*consequent);
                self.node(*alternative);
            }
            NodeKind::Case { arms, other } => {
                self.words.push(arms.len() as i32);
                for &(condition, body) in arms {
                    self.node(condition);
                    self.node(body);
                }
                if let Some(other) = other {
                    self.node(*other);
                }
            }
            NodeKind::Let {
                instances,
                definitions,
                body,
            } => {
                self.words.push(*instances as i32);
                self.children(definitions);
                self.node(*body);
            }
            NodeKind::Forall { bounds, body } | NodeKind::Exists { bounds, body } => {
                self.bounds(bounds);
                self.node(*body);
            }
            NodeKind::UnboundedQuantifier { names, body, .. } => {
                self.texts(names);
                self.node(*body);
            }
            NodeKind::Choose { pattern, set, body } => {
                self.pattern(pattern);
                self.words.push(set.is_some() as i32);
                if let Some(set) = set {
                    self.node(*set);
                }
                self.node(*body);
            }
            NodeKind::SetFilter { bound, predicate } => {
                self.bounds(std::slice::from_ref(bound));
                self.node(*predicate);
            }
            NodeKind::SetMap { expression, bounds } => {
                self.node(*expression);
                self.bounds(bounds);
            }
            NodeKind::FunctionConstruction { bounds, body, .. } => {
                self.bounds(bounds);
                self.node(*body);
            }
            NodeKind::FunctionSet { domain, range } => {
                self.node(*domain);
                self.node(*range);
            }
            NodeKind::Record(fields) | NodeKind::RecordSet(fields) => {
                self.words.push(fields.len() as i32);
                for &(name, value) in fields {
                    self.words.push(name as i32);
                    self.node(value);
                }
            }
            NodeKind::Except { function, updates } => {
                self.node(*function);
                self.words.push(updates.len() as i32);
                for update in updates {
                    self.words.push(update.path.len() as i32);
                    for step in &update.path {
                        match step {
                            PathStep::Field(name) => self.words.extend([0, *name as i32]),
                            PathStep::Index(args) => {
                                self.words.push(1);
                                self.children(args);
                            }
                        }
                    }
                    self.node(update.value);
                }
            }
            NodeKind::ExceptAt => {}
            NodeKind::FunctionApplication { function, args } => {
                self.node(*function);
                self.children(args);
            }
            NodeKind::FieldAccess { record, field } => {
                self.node(*record);
                self.words.push(*field as i32);
            }
            NodeKind::BoxAction { action, subscript }
            | NodeKind::AngleAction { action, subscript } => {
                self.node(*action);
                self.node(*subscript);
            }
            NodeKind::WeakFairness {
                subscript,
                action,
                enabled,
            }
            | NodeKind::StrongFairness {
                subscript,
                action,
                enabled,
            } => {
                self.node(*subscript);
                self.node(*action);
                self.words.push(enabled.is_some() as i32);
                if let Some(enabled) = enabled {
                    self.node(*enabled);
                }
            }
            NodeKind::Label { name, params, body } => {
                self.words.push(*name as i32);
                self.texts(params);
                self.node(*body);
            }
            NodeKind::Subexpression(selectors) => {
                self.words.push(selectors.len() as i32);
                for selector in selectors {
                    match selector {
                        Selector::Name { name, args } => {
                            self.words.extend([0, *name as i32]);
                            self.children(args);
                        }
                        Selector::Operand(operand) => self.words.extend([1, *operand]),
                        Selector::Bound(args) => {
                            self.words.push(2);
                            self.children(args);
                        }
                        Selector::At => self.words.push(3),
                        Selector::Colon => self.words.push(4),
                    }
                }
            }
            NodeKind::Definition(definition) => {
                self.words.push(definition.name as i32);
                match &definition.form {
                    DefinitionForm::Operator(params) => {
                        self.words.push(0);
                        write_params(&mut self.words, params);
                    }
                    DefinitionForm::Function(bounds) => {
                        self.words.push(1);
                        self.bounds(bounds);
                    }
                }
                self.node(definition.body);
            }
            NodeKind::Reference(_) => unreachable!("written above"),
        }
    }

    fn name(&mut self, name: &Name) {
        let (kind, payload) = match name.resolution {
            Resolution::None => (code::RESOLUTION_NONE, 0),
            Resolution::Variable(index) => (code::RESOLUTION_VARIABLE, index),
            Resolution::Constant(index) => (code::RESOLUTION_CONSTANT, index),
            Resolution::Definition(index) => (code::RESOLUTION_DEFINITION, index),
            Resolution::Builtin(index) => (code::RESOLUTION_BUILTIN, index),
        };
        self.words.extend([name.text as i32, kind, payload as i32]);
    }

    fn texts(&mut self, texts: &[u32]) {
        self.words.push(texts.len() as i32);
        self.words.extend(texts.iter().map(|&text| text as i32));
    }

    fn junction(&self, id: NodeId) -> &'a Junction {
        static PLAIN: Junction = Junction {
            is_bulleted: false,
            prefix_ends: Vec::new(),
        };
        self.ir.nodes.junctions.get(&id).unwrap_or(&PLAIN)
    }

    fn children(&mut self, children: &[NodeId]) {
        self.words.push(children.len() as i32);
        for &child in children {
            self.node(child);
        }
    }

    fn pattern(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::Name(name) => self.words.extend([0, *name as i32]),
            Pattern::Tuple(names) => {
                self.words.push(1);
                self.texts(names);
            }
        }
    }

    fn bounds(&mut self, bounds: &[Bound]) {
        self.words.push(bounds.len() as i32);
        for bound in bounds {
            self.pattern(&bound.pattern);
            self.node(bound.set);
        }
    }
}

fn push_live(words: &mut Vec<i32>, terms: &[LiveTerm]) {
    let mut live = Vec::new();
    for term in terms {
        match *term {
            LiveTerm::Boolean(false) => live.push(code::LIVE_FALSE),
            LiveTerm::Boolean(true) => live.push(code::LIVE_TRUE),
            LiveTerm::State(atom) => live.extend([code::LIVE_STATE, atom as i32]),
            LiveTerm::Enabled(atom) => live.extend([code::LIVE_ENABLED, atom as i32]),
            LiveTerm::Action { atom, enabled } => {
                live.extend([
                    code::LIVE_ACTION,
                    atom as i32,
                    enabled.map_or(-1, |index| index as i32),
                ]);
            }
            LiveTerm::Not => live.push(code::LIVE_NOT),
            LiveTerm::Always => live.push(code::LIVE_ALWAYS),
            LiveTerm::Eventually => live.push(code::LIVE_EVENTUALLY),
            LiveTerm::Next => live.push(code::LIVE_NEXT),
            LiveTerm::And(count) => live.extend([code::LIVE_AND, count as i32]),
            LiveTerm::Or(count) => live.extend([code::LIVE_OR, count as i32]),
        }
    }
    words.push(live.len() as i32);
    words.extend(live);
}
