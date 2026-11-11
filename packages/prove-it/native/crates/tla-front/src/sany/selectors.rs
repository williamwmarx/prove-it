//! A port of `src/sany/selectors.ts`: SANY's `Generator.selectorToNode`, which turns a name such
//! as `Op(a)!lab(b)!:!2` into the semantic node it names, following the Subexpression algorithm of
//! SANY's Subexpression.tla.

use crate::ast::{Expr, ExpressionKind, Operand, Selector};
use crate::sany::Result;
use crate::sany::nodes::{
    CONSTANT_DECL_KIND, DefKind, Graph, Name, NodeId, NodeKind, OpAppl, SanyLocation,
};

/// What `createSelectorResolver` takes from the generator (`SelectorGenerator` in
/// `selectors.ts`), which `generator.rs` implements. TLC 1.7.4 is retired, so there is no
/// `version`: the port follows TLC master.
pub trait SelectorGenerator {
    fn graph(&self) -> &Graph;
    fn graph_mut(&mut self) -> &mut Graph;
    fn resolve_symbol(&self, name: &str) -> Option<NodeId>;
    fn resolve_synonym(&self, name: &str) -> Name;
    fn generate_expression(&mut self, expression: &Expr) -> Result<NodeId>;
    fn generate_argument(
        &mut self,
        operator: NodeId,
        index: usize,
        argument: &Expr,
        location: &SanyLocation,
    ) -> Result<NodeId>;
    /// `createOpAppl`, followed by `matchArguments` as the generator's resolver does.
    fn create_op_appl(
        &mut self,
        operator: NodeId,
        operands: Vec<NodeId>,
        location: &SanyLocation,
    ) -> Result<NodeId>;
    fn create_op_arg(&mut self, operator: NodeId, location: &SanyLocation) -> NodeId;
    fn create_formal_param(
        &mut self,
        name: Name,
        arity: usize,
        location: Option<SanyLocation>,
    ) -> NodeId;
    fn create_lambda(
        &mut self,
        params: Vec<NodeId>,
        body: NodeId,
        location: &SanyLocation,
    ) -> NodeId;
    fn copy_subst_in(&mut self, prefix: NodeId, body: NodeId) -> NodeId;
    fn get_builtin(&self, name: &str) -> NodeId;
    /// `Errors.addMessage` for an error SANY recovers from, and the null node SANY returns after
    /// one.
    fn add_error(&mut self, location: &SanyLocation, text: String) -> NodeId;
    /// `Generator.illegalLabelRef`: whether the node being generated lies outside the scope of a
    /// declaration that the label lies in.
    fn is_out_of_label_scope(&self, label: NodeId) -> bool;
    /// `Generator.illegalAPPosRef`, for the clause at `position` of an ASSUME/PROVE.
    fn is_out_of_clause_scope(&self, assume_prove: NodeId, position: usize) -> bool;
}

/// `PROOF_STEP_OPERATORS`: the proof steps a theorem's body may be, with SANY's names for them.
const PROOF_STEP_OPERATORS: [(&str, &str); 7] = [
    ("$Qed", "QED step"),
    ("$Pfcase", "CASE"),
    ("$Have", "HAVE"),
    ("$Take", "TAKE"),
    ("$Pick", "PICK"),
    ("$Witness", "WITNESS"),
    ("$Suffices", "SUFFICES"),
];

/// `SelectorOp`: an operand selector `!i` is `Operand(i)`, and the other selectors are named
/// after SANY's NameSel, NullSel, GGSel (`>>`), LLSel (`<<`), ColonSel and AtSel.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum SelectorOp {
    Operand(f64),
    Name,
    Null,
    Last,
    First,
    Colon,
    At,
}

/// `SelectorItem`, with where SANY locates the selector and its parenthesized arguments, when
/// known.
#[derive(Clone, Debug)]
pub struct SelectorItem {
    pub op: SelectorOp,
    pub name: Name,
    pub args: Option<Vec<Expr>>,
    pub location: Option<SanyLocation>,
    pub args_location: Option<SanyLocation>,
}

impl SelectorItem {
    fn new(op: SelectorOp, name: Name, args: Option<Vec<Expr>>) -> SelectorItem {
        SelectorItem {
            op,
            name,
            args,
            location: None,
            args_location: None,
        }
    }

    /// `getArgs`.
    fn get_args(&self) -> &[Expr] {
        self.args.as_deref().unwrap_or(&[])
    }

    /// `getSelectorItemName`: SANY's selectorItemToString, which names an operand selector after
    /// the argument it selects.
    fn get_display_name(&self) -> String {
        match self.op {
            SelectorOp::Operand(_) => format!("argument selector {}", self.name),
            _ => self.name.to_string(),
        }
    }
}

/// `getNameParts`: the parts of a name like `I!Op` or `Op!lab`, except for an operator such as
/// `!!` that contains a `!`.
fn get_name_parts(name: &Name) -> Vec<Name> {
    if !name.contains('!') || name.split('!').any(str::is_empty) {
        return vec![name.clone()];
    }
    name.split('!').map(Name::from).collect()
}

/// `getSelectorItems`.
pub fn get_selector_items(expression: &Expr) -> Option<Vec<SelectorItem>> {
    match &expression.kind {
        ExpressionKind::Identifier { name, .. } => Some(
            get_name_parts(name)
                .into_iter()
                .map(|part| SelectorItem::new(SelectorOp::Name, part, None))
                .collect(),
        ),
        ExpressionKind::Apply {
            operator,
            args,
            argument_counts,
            ..
        } => {
            let parts = get_name_parts(operator);
            let last = parts.len() - 1;
            let mut cursor = 0;
            Some(
                parts
                    .into_iter()
                    .enumerate()
                    .map(|(index, part)| {
                        let count = argument_counts
                            .as_ref()
                            .map_or(if index == last { args.len() } else { 0 }, |counts| {
                                counts.get(index).copied().unwrap_or(0)
                            });
                        let part_args =
                            &args[cursor.min(args.len())..(cursor + count).min(args.len())];
                        cursor += count;
                        SelectorItem::new(
                            SelectorOp::Name,
                            part,
                            (!part_args.is_empty()).then(|| part_args.to_vec()),
                        )
                    })
                    .collect(),
            )
        }
        ExpressionKind::Subexpression { selectors, .. } => Some(
            selectors
                .iter()
                .map(|selector| match selector {
                    Selector::Name { name, args } => SelectorItem::new(
                        SelectorOp::Name,
                        name.clone(),
                        (!args.is_empty()).then(|| args.clone()),
                    ),
                    Selector::Operand(Operand::Index(index)) => SelectorItem::new(
                        SelectorOp::Operand(*index),
                        Name::from(index.to_string()),
                        None,
                    ),
                    Selector::Operand(Operand::First) => {
                        SelectorItem::new(SelectorOp::First, Name::from("<<"), None)
                    }
                    Selector::Operand(Operand::Last) => {
                        SelectorItem::new(SelectorOp::Last, Name::from(">>"), None)
                    }
                    Selector::Bound(args) => SelectorItem::new(
                        SelectorOp::Null,
                        Name::from("!(...)"),
                        Some(args.clone()),
                    ),
                    Selector::At => SelectorItem::new(SelectorOp::At, Name::from("@"), None),
                    Selector::Colon => SelectorItem::new(SelectorOp::Colon, Name::from(":"), None),
                })
                .collect(),
        ),
        _ => None,
    }
}

/// `isGeneralId`: whether SANY parses a selector as a GeneralId rather than an OpApplication,
/// which it does unless its last part is a name with arguments.
pub fn is_general_id(items: &[SelectorItem]) -> bool {
    let last = items.last().expect("a selector has an item");
    last.op != SelectorOp::Name || last.args.is_none()
}

/// `getArgNumber`: Subexpression.tla's ArgNum, the human number of the operand that a selector
/// picks out of an expression with `arity` operands, if there is one.
fn get_arg_number(op: SelectorOp, arity: usize) -> Option<usize> {
    match op {
        SelectorOp::Operand(number) if number > 0.0 && number <= arity as f64 => {
            Some(number as usize)
        }
        SelectorOp::First if arity > 0 => Some(1),
        SelectorOp::Last if arity == 2 => Some(2),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    FindingOpName,
    FollowingLabels,
    FindingSubExpr,
}

/// `SelectorWalk`: the state of Generator.selectorToNode as it walks the items. `let_in` is the
/// LET/IN whose context names are looked up in (`letInContext`).
struct SelectorWalk {
    name: Option<Name>,
    name_location: Option<SanyLocation>,
    node: Option<NodeId>,
    index: usize,
    mode: Mode,
    previous_mode: Option<Mode>,
    let_in: Option<NodeId>,
    definition_arity_found: usize,
    definition_args: Vec<NodeId>,
    is_in_suffices: bool,
}

/// `isDeclarationLike`.
fn is_declaration_like(graph: &Graph, symbol: NodeId) -> bool {
    match graph.kind(symbol) {
        NodeKind::OpDecl(_) | NodeKind::FormalParam(_) => true,
        NodeKind::OpDef(node) => {
            matches!(node.def_kind, DefKind::BuiltIn | DefKind::NumberedProofStep)
        }
        _ => false,
    }
}

fn is_op_def(graph: &Graph, id: NodeId, def_kind: DefKind) -> bool {
    graph
        .op_def(id)
        .is_some_and(|node| node.def_kind == def_kind)
}

fn is_named(graph: &Graph, id: NodeId, name: &str) -> bool {
    graph
        .node(id)
        .symbol_name()
        .is_some_and(|symbol| &**symbol == name)
}

/// `getQuantifierSymbols`.
fn get_quantifier_symbols(node: &OpAppl) -> Vec<NodeId> {
    match &node.bounded {
        Some(bounded) if !bounded.is_empty() => bounded.concat(),
        _ => node.unbounded.clone().unwrap_or_default(),
    }
}

/// `extendLocation`: Generator.extendedBy, a name's location grown to the end of its next part.
fn extend_location(name: Option<SanyLocation>, part: &SanyLocation) -> SanyLocation {
    match name {
        None => part.clone(),
        Some(name) => SanyLocation {
            end_line: part.end_line,
            end_column: part.end_column,
            ..name
        },
    }
}

/// The parameters of a definition: an OpDef's or a ThmOrAssumpDef's.
fn get_definition_params(graph: &Graph, definition: NodeId) -> Vec<NodeId> {
    match graph.kind(definition) {
        NodeKind::OpDef(node) => node.params.clone().unwrap_or_default(),
        NodeKind::ThmOrAssumpDef(node) => node.params.clone(),
        _ => Vec::new(),
    }
}

/// The resolver `createSelectorResolver` returns, SANY's `Generator.selectorToNode`: with
/// `expected_arity` 0 the expression a selector names, with a positive one the operator argument,
/// and with -1 the definition a DEF clause names. A fact can also be an ASSUME/PROVE, a NEW clause
/// or a module instance.
pub fn selector_to_node<G: SelectorGenerator>(
    generator: &mut G,
    items: &[SelectorItem],
    expected_arity: i32,
    is_fact: bool,
    is_def: bool,
    location: &SanyLocation,
) -> Result<NodeId> {
    let mut subst_in_prefix: Vec<NodeId> = Vec::new();
    let mut params: Vec<NodeId> = Vec::new();
    let mut all_args: Vec<NodeId> = Vec::new();
    let item_location = |index: usize| items[index].location.as_ref().unwrap_or(location);
    let mut walk = SelectorWalk {
        name: None,
        name_location: None,
        node: None,
        index: 0,
        mode: Mode::FindingOpName,
        previous_mode: None,
        let_in: None,
        definition_arity_found: 0,
        definition_args: Vec::new(),
        is_in_suffices: false,
    };
    let last_index = items.len() - 1;

    while walk.index < items.len() {
        let item = &items[walk.index];
        if (!matches!(item.op, SelectorOp::Name | SelectorOp::Null) || expected_arity != 0)
            && item.args.is_some()
        {
            return Ok(generator.add_error(
                item_location(walk.index),
                format!("Selector `{}' should not have argument(s).", item.name),
            ));
        }
        match walk.mode {
            Mode::FindingOpName => {
                let mut symbol = None;
                let mut new_name = None;
                let mut collected_args: Vec<Expr> = Vec::new();
                while symbol.is_none() && walk.index < items.len() {
                    let current = &items[walk.index];
                    new_name = (current.op == SelectorOp::Name).then(|| {
                        let synonym = generator.resolve_synonym(&current.name);
                        match &walk.name {
                            None => synonym,
                            Some(name) => Name::from(format!("{name}!{synonym}")),
                        }
                    });
                    if walk.name.is_none() && current.op != SelectorOp::Name {
                        return Ok(generator.add_error(
                            item_location(walk.index),
                            format!("Need name or step number here, not `{}'.", current.name),
                        ));
                    }
                    if let Some(new_name) = &new_name {
                        symbol = match walk.let_in {
                            None => generator.resolve_symbol(new_name),
                            Some(let_in) => match generator.graph().kind(let_in) {
                                NodeKind::LetIn(node) => node.context.get_symbol(new_name),
                                _ => None,
                            },
                        };
                    }
                    if symbol.is_none() {
                        if new_name.is_some() {
                            walk.name = new_name.clone();
                            walk.name_location = Some(extend_location(
                                walk.name_location.take(),
                                item_location(walk.index),
                            ));
                        }
                        collected_args.extend_from_slice(current.get_args());
                        walk.index += 1;
                    }
                }
                let Some(symbol) = symbol else {
                    let name = walk.name.as_deref().unwrap_or_default();
                    return Ok(generator.add_error(
                        walk.name_location.as_ref().unwrap_or(location),
                        format!("Unknown operator: `{name}'."),
                    ));
                };
                if matches!(generator.graph().kind(symbol), NodeKind::Module(_)) {
                    return Ok(generator.add_error(
                        item_location(walk.index),
                        format!("Module name ({}) not allowed here.", items[walk.index].name),
                    ));
                }
                walk.node = Some(symbol);
                walk.name_location = Some(extend_location(
                    walk.name_location.take(),
                    item_location(walk.index),
                ));
                walk.name = new_name;
                let name = walk.name.clone().unwrap_or_default();
                if is_declaration_like(generator.graph(), symbol) && items.len() != 1 {
                    return Ok(generator.add_error(
                        item_location(walk.index),
                        format!("Cannot take subexpression of `{name}'."),
                    ));
                }
                let node_arity = generator.graph().node(symbol).symbol_arity();
                if expected_arity == 0 {
                    collected_args.extend_from_slice(items[walk.index].get_args());
                    if walk.definition_arity_found + collected_args.len() != node_arity {
                        return Ok(generator.add_error(
                            items[walk.index].args_location.as_ref().unwrap_or(location),
                            format!(
                                "The operator {name} requires {} arguments.",
                                node_arity as i64 - walk.definition_arity_found as i64
                            ),
                        ));
                    }
                    for (argument_index, argument) in collected_args.iter().enumerate() {
                        let argument = generator.generate_argument(
                            symbol,
                            argument_index + walk.definition_arity_found,
                            argument,
                            item_location(walk.index),
                        )?;
                        walk.definition_args.push(argument);
                    }
                }
                walk.definition_arity_found = node_arity;
                if is_op_def(generator.graph(), symbol, DefKind::ModuleInstance) {
                    if walk.index == last_index && !(is_def || is_fact) {
                        return Ok(generator.add_error(
                            item_location(walk.index),
                            format!("Operator name {name} is incomplete."),
                        ));
                    }
                } else {
                    let graph = generator.graph();
                    let (is_definition, body) = match graph.kind(symbol) {
                        NodeKind::OpDef(node) if node.def_kind == DefKind::UserDefined => {
                            (true, node.body)
                        }
                        NodeKind::ThmOrAssumpDef(node) => (true, Some(node.body)),
                        _ => (false, None),
                    };
                    if graph.op_def(symbol).is_some_and(|node| {
                        node.def_kind == DefKind::UserDefined && !node.is_defined
                    }) && items.len() != 1
                    {
                        return Ok(generator.add_error(
                            item_location(walk.index),
                            format!(
                                "Subexpression of  `{name}' used inside the operator's definition."
                            ),
                        ));
                    }
                    if walk.index != last_index && is_definition {
                        params.extend(get_definition_params(graph, symbol));
                        walk.name = None;
                        walk.name_location = None;
                        walk.mode = if items[walk.index + 1].op == SelectorOp::Name {
                            Mode::FollowingLabels
                        } else {
                            Mode::FindingSubExpr
                        };
                        all_args.append(&mut walk.definition_args);
                        walk.definition_arity_found = 0;
                        let mut body = body;
                        while let Some(id) = body
                            && let NodeKind::SubstIn(node) = graph.kind(id)
                            && !node.is_assume_prove
                        {
                            subst_in_prefix.push(id);
                            body = Some(node.body);
                        }
                        while let Some(id) = body
                            && let NodeKind::SubstIn(node) = graph.kind(id)
                            && node.is_assume_prove
                        {
                            subst_in_prefix.push(id);
                            body = Some(node.body);
                        }
                        if walk.mode == Mode::FindingSubExpr {
                            walk.node = body;
                        }
                    }
                }
                walk.previous_mode = Some(Mode::FindingOpName);
            }
            Mode::FollowingLabels => {
                let graph = generator.graph();
                let labels = walk.node.and_then(|owner| match graph.kind(owner) {
                    NodeKind::OpDef(node) => Some(&node.labels),
                    NodeKind::ThmOrAssumpDef(node) => Some(&node.labels),
                    NodeKind::Label(node) => Some(&node.labels),
                    _ => None,
                });
                let Some(label) = labels.and_then(|labels| labels.get(&*item.name).copied()) else {
                    return Ok(generator.add_error(
                        item_location(walk.index),
                        format!("Cannot find label `{}'.", item.name),
                    ));
                };
                walk.node = Some(label);
                if generator.is_out_of_label_scope(label) {
                    return Ok(generator.add_error(
                        item_location(walk.index),
                        format!(
                            "Accessing subexpression labeled `{}' of ASSUME/PROVE clause within the scope of a declaration\n from outside that declaration's scope.",
                            item.name
                        ),
                    ));
                }
                let NodeKind::Label(label_node) = generator.graph().kind(label) else {
                    return crate::sany::not_yet("a label that is not a Label node");
                };
                let label_params = label_node.params.clone();
                let label_body = label_node.body;
                if expected_arity == 0 {
                    if label_params.len() != item.get_args().len() {
                        return Ok(generator.add_error(
                            item_location(walk.index),
                            format!("Label `{}' used with wrong number of arguments.", item.name),
                        ));
                    }
                    for argument in item.get_args() {
                        let argument = generator.generate_expression(argument)?;
                        all_args.push(argument);
                    }
                }
                params.extend(label_params);
                if walk.index < last_index && items[walk.index + 1].op != SelectorOp::Name {
                    walk.mode = Mode::FindingSubExpr;
                }
                if walk.mode == Mode::FindingSubExpr {
                    walk.node = Some(label_body);
                }
                walk.previous_mode = Some(Mode::FollowingLabels);
            }
            Mode::FindingSubExpr => {
                let nonexistent_error = format!(
                    "Nonexistent operand specified by `{}'.",
                    item.get_display_name()
                );
                if item.op == SelectorOp::Colon {
                    let is_allowed = walk.previous_mode != Some(Mode::FindingSubExpr)
                        && ((walk.index == last_index
                            && walk.previous_mode == Some(Mode::FindingOpName))
                            || (walk.index < last_index
                                && items[walk.index + 1].op == SelectorOp::Name));
                    if !is_allowed {
                        return Ok(generator.add_error(
                            item_location(walk.index),
                            "`!:' can be used only after a name and either at the end after an\noperator name or before an operator name.".to_owned(),
                        ));
                    }
                } else {
                    // An absent node is the null SANY's generator returns for an expression it
                    // reported an error in.
                    let Some(node) = walk
                        .node
                        .filter(|&node| !generator.graph().node(node).is_absent())
                    else {
                        return Ok(generator.add_error(
                            item_location(walk.index),
                            "Subexpression selection failed, probably due to an error in the selected expression.".to_owned(),
                        ));
                    };
                    let graph = generator.graph();
                    match graph.kind(node) {
                        NodeKind::LetIn(let_in) => {
                            if get_arg_number(item.op, 1) != Some(1) {
                                return Ok(generator.add_error(
                                    item_location(walk.index),
                                    "A LET/IN expression has only one operand.".to_owned(),
                                ));
                            }
                            walk.node = Some(let_in.body);
                        }
                        NodeKind::OpAppl(appl) => {
                            let operator = appl.operator;
                            let operands = &appl.operands;
                            let is_user_operator = match graph.kind(operator) {
                                NodeKind::FormalParam(_) => true,
                                NodeKind::OpDecl(declaration) => {
                                    declaration.decl_kind == CONSTANT_DECL_KIND
                                }
                                NodeKind::OpDef(definition) => {
                                    definition.def_kind == DefKind::UserDefined
                                }
                                _ => false,
                            };
                            let get_pair = |pair: Option<NodeId>| {
                                pair.and_then(|pair| match graph.kind(pair) {
                                    NodeKind::OpAppl(pair_appl)
                                        if is_named(graph, pair_appl.operator, "$Pair") =>
                                    {
                                        Some(pair_appl)
                                    }
                                    _ => None,
                                })
                            };
                            let get_operand =
                                |number: usize| operands.get(number - 1).copied().flatten();
                            let not_pair_error =
                                "Internal error: Expecting $Pair and didn't find it.";
                            let operand_number = get_arg_number(item.op, operands.len());
                            let operator_name = graph
                                .node(operator)
                                .symbol_name()
                                .map(|name| name.to_string())
                                .unwrap_or_default();
                            if is_user_operator {
                                let arity = graph.node(operator).symbol_arity();
                                let Some(number) = get_arg_number(item.op, arity) else {
                                    return Ok(generator
                                        .add_error(item_location(walk.index), nonexistent_error));
                                };
                                walk.node = get_operand(number);
                            } else if is_op_def(graph, operator, DefKind::BuiltIn) {
                                if operator_name == "$RcdConstructor"
                                    || operator_name == "$SetOfRcds"
                                {
                                    let Some(number) = operand_number else {
                                        return Ok(generator.add_error(
                                            item_location(walk.index),
                                            nonexistent_error,
                                        ));
                                    };
                                    let Some(pair) = get_pair(get_operand(number)) else {
                                        return Ok(generator.add_error(
                                            item_location(walk.index),
                                            not_pair_error.to_owned(),
                                        ));
                                    };
                                    walk.node = pair.operands.get(1).copied().flatten();
                                } else if operator_name == "$Case" {
                                    if walk.index == last_index {
                                        return Ok(generator.add_error(
                                            item_location(walk.index),
                                            "Subexpression of CASE must have form !i!j.".to_owned(),
                                        ));
                                    }
                                    let Some(number) = operand_number else {
                                        return Ok(generator.add_error(
                                            item_location(walk.index),
                                            nonexistent_error,
                                        ));
                                    };
                                    let Some(pair) = get_pair(get_operand(number)) else {
                                        return Ok(generator.add_error(
                                            item_location(walk.index),
                                            not_pair_error.to_owned(),
                                        ));
                                    };
                                    walk.index += 1;
                                    let Some(number) = get_arg_number(items[walk.index].op, 2)
                                    else {
                                        return Ok(generator.add_error(
                                            item_location(walk.index),
                                            "Second selector for CASE subexpression must specify  one of two operands.".to_owned(),
                                        ));
                                    };
                                    walk.node = pair.operands.get(number - 1).copied().flatten();
                                    if walk.node.is_none() {
                                        return Ok(generator.add_error(
                                            item_location(walk.index),
                                            "Selecting OTHER in a CASE statement.".to_owned(),
                                        ));
                                    }
                                } else if operator_name == "$Except" {
                                    if operand_number.is_some_and(|number| number > 1) {
                                        return Ok(generator.add_error(
                                            item_location(walk.index),
                                            "Selecting subexpression of an EXCEPT not yet implemented.".to_owned(),
                                        ));
                                    }
                                    let Some(number) = operand_number else {
                                        return Ok(generator.add_error(
                                            item_location(walk.index),
                                            nonexistent_error,
                                        ));
                                    };
                                    walk.node = get_operand(number);
                                } else if appl.bounded.as_ref().is_none_or(Vec::is_empty)
                                    && appl.unbounded.as_ref().is_none_or(Vec::is_empty)
                                {
                                    let Some(number) = operand_number else {
                                        return Ok(generator.add_error(
                                            item_location(walk.index),
                                            nonexistent_error,
                                        ));
                                    };
                                    walk.node = get_operand(number);
                                } else if matches!(item.op, SelectorOp::Null | SelectorOp::At) {
                                    let symbols = get_quantifier_symbols(appl);
                                    let body = operands.first().copied().flatten();
                                    let symbol_count = symbols.len();
                                    params.extend(symbols);
                                    if item.op == SelectorOp::Null {
                                        if item.get_args().len() != symbol_count {
                                            return Ok(generator.add_error(
                                                item_location(walk.index),
                                                format!(
                                                    "Selector with {} argument(s) used for quantifier with {symbol_count} bound identifier(s).",
                                                    item.get_args().len()
                                                ),
                                            ));
                                        }
                                        for argument in item.get_args() {
                                            let argument =
                                                generator.generate_expression(argument)?;
                                            all_args.push(argument);
                                        }
                                    }
                                    walk.node = body;
                                } else {
                                    let Some(number) = get_arg_number(item.op, appl.ranges.len())
                                    else {
                                        return Ok(generator.add_error(
                                            item_location(walk.index),
                                            nonexistent_error,
                                        ));
                                    };
                                    walk.node = Some(appl.ranges[number - 1]);
                                }
                            } else {
                                return Ok(generator.add_error(
                                    item_location(walk.index),
                                    format!(
                                        "Choosing operand `{}' of subexpression with no operands.",
                                        item.name
                                    ),
                                ));
                            }
                        }
                        NodeKind::AssumeProve(assume_prove) => {
                            if assume_prove.is_suffices && !walk.is_in_suffices {
                                if get_arg_number(item.op, 1) != Some(1) {
                                    return Ok(generator.add_error(
                                        item_location(walk.index),
                                        "Accessing non-existent subexpression of a SUFFICES"
                                            .to_owned(),
                                    ));
                                }
                                walk.is_in_suffices = true;
                            } else {
                                walk.is_in_suffices = false;
                                let assumptions = assume_prove.assumptions.clone();
                                let goal = assume_prove.goal;
                                let Some(number) = get_arg_number(item.op, 1 + assumptions.len())
                                else {
                                    return Ok(generator
                                        .add_error(item_location(walk.index), nonexistent_error));
                                };
                                if generator.is_out_of_clause_scope(node, number) {
                                    return Ok(generator.add_error(
                                        item_location(walk.index),
                                        "Accessing ASSUME/PROVE clause within the scope of a declaration\n from outside that declaration's scope.".to_owned(),
                                    ));
                                }
                                if number <= assumptions.len() {
                                    let assumption = assumptions[number - 1];
                                    walk.node = Some(assumption);
                                    if matches!(
                                        generator.graph().kind(assumption),
                                        NodeKind::NewSymb { .. }
                                    ) && walk.index != last_index
                                    {
                                        return Ok(generator.add_error(
                                            item_location(walk.index),
                                            "Selected a subexpression of a NEW clause of an ASSUME."
                                                .to_owned(),
                                        ));
                                    }
                                } else {
                                    walk.node = Some(goal);
                                }
                            }
                        }
                        NodeKind::OpArg { op, .. } => {
                            let lambda = match graph.kind(*op) {
                                NodeKind::OpDef(lambda) if &*lambda.name == "LAMBDA" => lambda,
                                _ => {
                                    return Ok(generator.add_error(
                                        item_location(walk.index),
                                        "Trying to select subexpression of an operator argument."
                                            .to_owned(),
                                    ));
                                }
                            };
                            if !matches!(item.op, SelectorOp::Null | SelectorOp::At) {
                                return Ok(generator.add_error(
                                    item_location(walk.index),
                                    format!(
                                        "Cannot use !{} to select subexpression of a LAMBDA.",
                                        item.name
                                    ),
                                ));
                            }
                            let lambda_arity = lambda.arity;
                            let lambda_params = lambda.params.clone().unwrap_or_default();
                            let lambda_body = lambda.body;
                            if item.op == SelectorOp::Null {
                                if lambda_arity != item.get_args().len() {
                                    return Ok(generator.add_error(
                                        item_location(walk.index),
                                        format!(
                                            "Selector with {} arguments used for LAMBDA expression taking {lambda_arity} arguments.",
                                            item.get_args().len()
                                        ),
                                    ));
                                }
                                for argument in item.get_args() {
                                    let argument = generator.generate_expression(argument)?;
                                    all_args.push(argument);
                                }
                            }
                            params.extend(lambda_params);
                            walk.node = lambda_body;
                        }
                        NodeKind::Label(label) => {
                            walk.node = Some(label.body);
                            walk.index -= 1;
                        }
                        _ => {
                            return Ok(generator.add_error(
                                item_location(walk.index),
                                "Selecting subexpression of expression that has none.".to_owned(),
                            ));
                        }
                    }
                }
                let Some(mut node) = walk.node else {
                    return Ok(generator.add_error(
                        item_location(walk.index),
                        format!(
                            "An unexpected null node specified by '{}'.\nThis is probably due to a previous error.",
                            item.name
                        ),
                    ));
                };
                if walk.index != last_index {
                    let next = &items[walk.index + 1];
                    if next.op == SelectorOp::Name {
                        let graph = generator.graph();
                        while let NodeKind::Label(label) = graph.kind(node) {
                            node = label.body;
                        }
                        walk.node = Some(node);
                        if !matches!(graph.kind(node), NodeKind::LetIn(_)) {
                            return Ok(generator.add_error(
                                item_location(walk.index),
                                "A name selector here must be from a LET clause.".to_owned(),
                            ));
                        }
                        walk.let_in = Some(node);
                        walk.mode = Mode::FindingOpName;
                    } else if next.op == SelectorOp::Colon {
                        return Ok(generator.add_error(
                            item_location(walk.index),
                            "!: should not follow an operand selector.".to_owned(),
                        ));
                    }
                }
                walk.previous_mode = Some(Mode::FindingSubExpr);
            }
        }
        walk.index += 1;
    }

    let Some(node) = walk.node else {
        return Ok(generator.add_error(
            location,
            "Subexpression selection failed, probably due to an error in the selected expression."
                .to_owned(),
        ));
    };
    let graph = generator.graph();
    match graph.kind(node) {
        NodeKind::AssumeProve(_) | NodeKind::NewSymb { .. } if is_fact => return Ok(node),
        NodeKind::AssumeProve(_) => {
            return Ok(generator.add_error(
                location,
                "Selected ASSUME/PROVE instead of expression.".to_owned(),
            ));
        }
        NodeKind::NewSymb { .. } => {
            return Ok(generator.add_error(
                location,
                "Selected a NEW declaration as an expression or operator.".to_owned(),
            ));
        }
        _ => {}
    }
    if expected_arity < 0 {
        let is_definition = match graph.kind(node) {
            NodeKind::OpDef(definition) => match definition.def_kind {
                DefKind::UserDefined | DefKind::NumberedProofStep => true,
                DefKind::ModuleInstance => is_def,
                DefKind::BuiltIn => false,
            },
            NodeKind::ThmOrAssumpDef(_) => true,
            _ => false,
        };
        if walk.previous_mode != Some(Mode::FindingOpName) || !is_definition {
            return Ok(generator.add_error(
                location,
                "DEF clause entry should describe a defined operator.".to_owned(),
            ));
        }
        if graph
            .op_def(node)
            .and_then(|definition| definition.step)
            .is_some_and(|step| !matches!(graph.kind(step), NodeKind::DefStep { .. }))
        {
            return Ok(generator.add_error(
                location,
                "DEF clause entry refers to a non-definition step.".to_owned(),
            ));
        }
        return Ok(node);
    }
    if is_op_def(graph, node, DefKind::NumberedProofStep) {
        return Ok(generator.add_error(
            location,
            if is_fact {
                "Step number of non-fact used as a fact".to_owned()
            } else {
                "Step number of non-expression step used as an expression.".to_owned()
            },
        ));
    }
    if expected_arity > 0 {
        let found = params.len()
            + match graph.kind(node) {
                NodeKind::OpArg { op, .. } => graph.node(*op).symbol_arity(),
                _ if walk.previous_mode == Some(Mode::FindingOpName)
                    && graph.node(node).is_symbol() =>
                {
                    graph.node(node).symbol_arity()
                }
                _ => 0,
            };
        if expected_arity as usize != found {
            return Ok(generator.add_error(
                location,
                format!("Expected arity {expected_arity} but found operator of arity {found}."),
            ));
        }
    }
    let mut current = node;
    if walk.previous_mode == Some(Mode::FindingOpName) && params.len() + subst_in_prefix.len() > 0 {
        if !matches!(
            graph.kind(current),
            NodeKind::OpDef(_) | NodeKind::ThmOrAssumpDef(_)
        ) {
            return Ok(generator.add_error(
                items[last_index].location.as_ref().unwrap_or(location),
                "Internal Error: Found unexpected node kind after FindingOpName".to_owned(),
            ));
        }
        all_args.extend_from_slice(&walk.definition_args);
        let mut operands = Vec::new();
        for param in get_definition_params(graph, current) {
            let NodeKind::FormalParam(param) = generator.graph().kind(param) else {
                return crate::sany::not_yet("a definition's parameter that is not a FormalParam");
            };
            let param = param.clone();
            let copy = generator.create_formal_param(param.name, param.arity, param.location);
            params.push(copy);
            operands.push(if param.arity == 0 {
                generator.create_op_appl(copy, Vec::new(), location)?
            } else {
                generator.create_op_arg(copy, location)
            });
        }
        current = generator.create_op_appl(current, operands, location)?;
    }
    if let NodeKind::OpArg { op, .. } = generator.graph().kind(current) {
        let operator = *op;
        if expected_arity == 0 {
            return Ok(generator.add_error(
                location,
                "Selected operator argument when expression expected.".to_owned(),
            ));
        }
        if params.len() + subst_in_prefix.len() > 0 {
            for param_index in 0..generator.graph().node(operator).symbol_arity() {
                let param = generator.create_formal_param(
                    Name::from(format!("NewParam{param_index}")),
                    0,
                    None,
                );
                params.push(param);
            }
            current = generator.create_op_appl(operator, walk.definition_args.clone(), location)?;
        }
    }
    let graph = generator.graph();
    if !is_fact {
        let is_assume_prove = match graph.kind(current) {
            NodeKind::ThmOrAssumpDef(definition) => {
                matches!(graph.kind(definition.body), NodeKind::AssumeProve(_))
            }
            NodeKind::Label(label) => label.is_assume_prove,
            _ => false,
        };
        if is_assume_prove {
            return Ok(generator.add_error(
                location,
                "ASSUME/PROVE used where an expression is required.".to_owned(),
            ));
        }
        if let NodeKind::ThmOrAssumpDef(definition) = graph.kind(current)
            && let NodeKind::OpAppl(body) = graph.kind(definition.body)
            && let Some((_, step)) = PROOF_STEP_OPERATORS
                .iter()
                .find(|(operator, _)| is_named(graph, body.operator, operator))
        {
            return Ok(generator.add_error(
                location,
                format!("{step} proof step selected instead of expression."),
            ));
        }
    }
    let is_operator = match graph.kind(current) {
        NodeKind::FormalParam(_) | NodeKind::OpDecl(_) | NodeKind::ThmOrAssumpDef(_) => true,
        NodeKind::OpDef(definition) => {
            matches!(definition.def_kind, DefKind::UserDefined | DefKind::BuiltIn)
        }
        _ => false,
    };
    if is_operator {
        return if expected_arity > 0 {
            Ok(generator.create_op_arg(current, location))
        } else {
            generator.create_op_appl(current, walk.definition_args, location)
        };
    }
    match graph.kind(current) {
        NodeKind::OpArg { .. } => return Ok(current),
        NodeKind::OpDef(_) if is_fact || is_def => return Ok(current),
        NodeKind::OpDef(_) | NodeKind::Module(_) => {
            return Ok(generator.add_error(
                location,
                "Module instantiation selected instead of expression.".to_owned(),
            ));
        }
        _ => {}
    }
    let expression = subst_in_prefix.iter().rev().fold(current, |body, &prefix| {
        generator.copy_subst_in(prefix, body)
    });
    let lambda =
        (!params.is_empty()).then(|| generator.create_lambda(params.clone(), expression, location));
    if expected_arity > 0 {
        return match lambda {
            Some(lambda) if params.len() == expected_arity as usize => {
                Ok(generator.create_op_arg(lambda, location))
            }
            _ => Ok(generator.add_error(
                location,
                format!(
                    "Expected operator argument with arity {expected_arity} but found one of arity {}.",
                    params.len()
                ),
            )),
        };
    }
    if params.len() != all_args.len() {
        return Ok(generator.add_error(
            location,
            format!(
                "Expected {} arguments but found {}.",
                params.len(),
                all_args.len()
            ),
        ));
    }
    match lambda {
        None => {
            let nop = generator.get_builtin("$Nop");
            generator.create_op_appl(nop, vec![expression], location)
        }
        Some(lambda) => generator.create_op_appl(lambda, all_args, location),
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Name, SelectorItem, SelectorOp, get_name_parts, get_selector_items, is_general_id,
    };
    use crate::TlcVersion;
    use crate::parser::parse_sany_module;

    /// The selector items of `body`, the body of a definition in a module that defines `Op` with
    /// a label and an instance `I`.
    fn get_items(body: &str) -> Vec<SelectorItem> {
        let source = format!(
            "---- MODULE M ----\nOp(a) == lab(b) :: a + b\nI(x) == INSTANCE Naturals\nA == {body}\n===="
        );
        let module = parse_sany_module(&source, None, TlcVersion::Master).expect("a module");
        let definition = module.definitions.last().expect("a definition");
        get_selector_items(&definition.body).expect("a selector")
    }

    fn describe(items: &[SelectorItem]) -> Vec<(SelectorOp, &str, Option<usize>)> {
        items
            .iter()
            .map(|item| (item.op, &*item.name, item.args.as_ref().map(Vec::len)))
            .collect()
    }

    #[test]
    fn splits_a_name_into_its_parts() {
        let items = get_items("Op!lab");
        assert_eq!(
            describe(&items),
            [
                (SelectorOp::Name, "Op", None),
                (SelectorOp::Name, "lab", None)
            ]
        );
        assert!(is_general_id(&items));
    }

    #[test]
    fn gives_each_part_its_arguments() {
        let items = get_items("I(1)!Op(2, 3)");
        assert_eq!(
            describe(&items),
            [
                (SelectorOp::Name, "I", Some(1)),
                (SelectorOp::Name, "Op", Some(2))
            ]
        );
        assert!(!is_general_id(&items));
    }

    #[test]
    fn reads_the_selectors_of_a_subexpression() {
        let items = get_items("Op(1)!lab(2)!:!<<!>>!2!@");
        assert_eq!(
            describe(&items),
            [
                (SelectorOp::Name, "Op", Some(1)),
                (SelectorOp::Name, "lab", Some(1)),
                (SelectorOp::Colon, ":", None),
                (SelectorOp::First, "<<", None),
                (SelectorOp::Last, ">>", None),
                (SelectorOp::Operand(2.0), "2", None),
                (SelectorOp::At, "@", None),
            ]
        );
        assert!(is_general_id(&items));
    }

    #[test]
    fn reads_a_bound_selector() {
        let items = get_items("Op(1)!(3)");
        assert_eq!(describe(&items)[1], (SelectorOp::Null, "!(...)", Some(1)));
        assert!(is_general_id(&items));
    }

    #[test]
    fn keeps_an_operator_that_contains_a_bang_whole() {
        assert_eq!(get_name_parts(&Name::from("!!")), [Name::from("!!")]);
        assert_eq!(
            get_name_parts(&Name::from("I!Op")),
            [Name::from("I"), Name::from("Op")]
        );
    }
}
