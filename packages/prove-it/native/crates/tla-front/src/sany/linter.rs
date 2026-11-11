//! A port of SANY's `tla2sany.linter.Linter`, which warns about a record field named like a
//! definition or declaration of the module.

use crate::errors::SanyError;
use crate::hash::FastSet;
use crate::sany::nodes::{Graph, MessageLocation, NodeId, NodeKind, format_sany_location};
use crate::sany::{Result, not_yet};

/// `SemanticNode.getListOfChildren`.
fn get_children(graph: &Graph, node: NodeId) -> Vec<NodeId> {
    match &graph.node(node).kind {
        NodeKind::OpAppl(node) => node
            .ranges
            .iter()
            .copied()
            .chain(node.operands.iter().flatten().copied())
            .collect(),
        NodeKind::OpDef(node) => node.body.into_iter().collect(),
        NodeKind::ThmOrAssumpDef(node) => vec![node.body],
        NodeKind::Label(node) => vec![node.body],
        NodeKind::LetIn(node) => node
            .op_defs
            .iter()
            .chain(&node.instances)
            .copied()
            .chain([node.body])
            .collect(),
        NodeKind::SubstIn(node) => [node.body]
            .into_iter()
            .chain(node.substs.iter().map(|subst| subst.expr))
            .collect(),
        NodeKind::Instance(node) => node.substs.iter().map(|subst| subst.expr).collect(),
        NodeKind::AssumeProve(node) => node
            .assumptions
            .iter()
            .copied()
            .chain([node.goal])
            .collect(),
        NodeKind::NewSymb { set, .. } => set.iter().copied().collect(),
        NodeKind::Assume { body, .. } => vec![*body],
        NodeKind::Theorem(node) => [node.body].into_iter().chain(node.proof).collect(),
        NodeKind::DefStep { defs, .. } => defs.clone(),
        NodeKind::LeafProof(node) => node.facts.clone(),
        NodeKind::NonLeafProof(node) => node.steps.clone(),
        NodeKind::UseOrHide(node) => node.facts.clone(),
        NodeKind::FormalParam(_)
        | NodeKind::OpDecl(_)
        | NodeKind::Module(_)
        | NodeKind::Numeral { .. }
        | NodeKind::String { .. }
        | NodeKind::Decimal(_)
        | NodeKind::OpArg { .. }
        | NodeKind::At { .. } => Vec::new(),
    }
}

/// The definitions whose application counts as built from declarations: `BOOLEAN`, and the sets of
/// numbers by the module that defines them.
const SET_OPERATORS: &[(&str, &str)] =
    &[("Integers", "Int"), ("Naturals", "Nat"), ("Reals", "Reals")];

/// `Linter.isBuiltFromDeclarations`'s walk: whether an expression applies a declared or bound
/// symbol, BOOLEAN or a standard set of numbers, directly or through the definitions it applies.
struct Walk<'a> {
    graph: &'a Graph,
    found: bool,
    /// The definitions being walked: SANY's walk of a definition that applies itself never ends.
    walking: Vec<NodeId>,
    /// The definitions walked without finding one: walking one again finds nothing again.
    unfound: FastSet<NodeId>,
}

impl Walk<'_> {
    /// `SemanticNode.walkChildren`.
    fn walk(&mut self, node: NodeId) -> Result<()> {
        self.pre_visit(node)?;
        for child in get_children(self.graph, node) {
            if self.found {
                continue;
            }
            self.walk(child)?;
        }
        Ok(())
    }

    fn pre_visit(&mut self, node: NodeId) -> Result<()> {
        let NodeKind::OpAppl(application) = &self.graph.node(node).kind else {
            return Ok(());
        };
        let operator = application.operator;
        match &self.graph.node(operator).kind {
            NodeKind::OpDecl(_) | NodeKind::FormalParam(_) => self.found = true,
            NodeKind::OpDef(definition) => {
                if &*definition.name == "BOOLEAN" {
                    self.found = true;
                    return Ok(());
                }
                let module = definition
                    .module
                    .and_then(|module| self.graph.node(module).symbol_name());
                if module
                    .is_some_and(|module| SET_OPERATORS.contains(&(&**module, &*definition.name)))
                {
                    self.found = true;
                    return Ok(());
                }
                if self.unfound.contains(&operator) {
                    return Ok(());
                }
                if self.walking.contains(&operator) {
                    return not_yet("SANY's linter following a definition that applies itself");
                }
                self.walking.push(operator);
                self.walk(operator)?;
                self.walking.pop();
                if !self.found {
                    self.unfound.insert(operator);
                }
            }
            _ => {}
        }
        Ok(())
    }
}

fn is_built_from_declarations(graph: &Graph, expression: NodeId) -> Result<bool> {
    let mut walk = Walk {
        graph,
        found: false,
        walking: Vec::new(),
        unfound: FastSet::default(),
    };
    walk.walk(expression)?;
    Ok(walk.found)
}

/// `Linter.getFieldPairs`: the `name |-> value` pairs of a record constructor.
fn get_field_pairs(graph: &Graph, record: NodeId) -> Vec<NodeId> {
    match &graph.node(record).kind {
        NodeKind::OpAppl(record) => record
            .operands
            .iter()
            .flatten()
            .copied()
            .filter(|&pair| matches!(graph.node(pair).kind, NodeKind::OpAppl(_)))
            .collect(),
        _ => Vec::new(),
    }
}

fn get_pair_operands(graph: &Graph, pair: NodeId) -> (Option<NodeId>, Option<NodeId>) {
    match &graph.node(pair).kind {
        NodeKind::OpAppl(pair) => (
            pair.operands.first().copied().flatten(),
            pair.operands.get(1).copied().flatten(),
        ),
        _ => (None, None),
    }
}

fn get_field_name(graph: &Graph, pair: NodeId) -> Option<NodeId> {
    get_pair_operands(graph, pair)
        .0
        .filter(|&name| matches!(graph.node(name).kind, NodeKind::String { .. }))
}

fn get_string(graph: &Graph, node: Option<NodeId>) -> Option<&str> {
    match &graph.node(node?).kind {
        NodeKind::String { value, .. } => Some(value),
        _ => None,
    }
}

/// `Records.sameDomain`.
fn is_same_domain(graph: &Graph, record: NodeId, other: NodeId) -> bool {
    if record == other {
        return true;
    }
    let pairs = get_field_pairs(graph, record);
    let others = get_field_pairs(graph, other);
    if pairs.len() != others.len() {
        return false;
    }
    pairs.iter().all(|&pair| {
        let name = get_string(graph, get_field_name(graph, pair));
        others
            .iter()
            .any(|&other| get_string(graph, get_field_name(graph, other)) == name)
    })
}

/// `ModuleNode.getExtendedModuleSet(true)`.
fn get_extended_modules(graph: &Graph, module: NodeId, found: &mut Vec<NodeId>) {
    let NodeKind::Module(node) = &graph.node(module).kind else {
        return;
    };
    for &extendee in &node.extendees {
        if found.contains(&extendee) {
            continue;
        }
        found.push(extendee);
        get_extended_modules(graph, extendee, found);
    }
}

fn get_records(graph: &Graph, module: NodeId) -> &[NodeId] {
    match &graph.node(module).kind {
        NodeKind::Module(node) => &node.records,
        _ => &[],
    }
}

/// `Linter.lintRecords`: the warnings for the records of a module.
pub fn lint_sany_module(graph: &Graph, module: NodeId) -> Result<Vec<SanyError>> {
    let NodeKind::Module(node) = &graph.node(module).kind else {
        return Ok(Vec::new());
    };
    let mut extended = Vec::new();
    get_extended_modules(graph, module, &mut extended);
    let all_records: Vec<NodeId> = extended
        .iter()
        .flat_map(|&extended| get_records(graph, extended))
        .chain(&node.records)
        .copied()
        .collect();
    let mut warnings = Vec::new();
    for &record in &node.records {
        let pairs = get_field_pairs(graph, record);
        for &pair in &pairs {
            let Some(name) = get_field_name(graph, pair) else {
                continue;
            };
            let NodeKind::String { value, location } = &graph.node(name).kind else {
                continue;
            };
            let Some(symbol) = node.context.get_symbol(value) else {
                continue;
            };
            // SANY checks the field's value, the record's fields and the fields of every record
            // with the same domain, which includes the record itself.
            let mut is_exempt = false;
            for &other in [pair].iter().chain(&pairs) {
                if let Some(value) = get_pair_operands(graph, other).1
                    && is_built_from_declarations(graph, value)?
                {
                    is_exempt = true;
                    break;
                }
            }
            for &other in &all_records {
                if is_exempt {
                    break;
                }
                if !is_same_domain(graph, other, record) {
                    continue;
                }
                for other_pair in get_field_pairs(graph, other) {
                    if let Some(value) = get_pair_operands(graph, other_pair).1
                        && is_built_from_declarations(graph, value)?
                    {
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
            let Some(located) = graph.node(symbol).location() else {
                return not_yet("a field named like a symbol without a location");
            };
            let located = format_sany_location(&MessageLocation::At(located.clone()));
            warnings.push(SanyError {
                location: format_sany_location(&MessageLocation::At(location.clone())),
                message: format!(
                    "The field name \"{value}\" in the record constructor is identical to the existing definition or declaration\nnamed {value}, located at {located}.\nThe field in the record will not take the value of the {value} definition or declaration.\nIn TLA+, field names in records are strings, regardless of any similarly named declarations or definitions.\nTherefore, DOMAIN [{value} |-> ...] = {{\"{value}\"}} holds true."
                ),
            });
        }
    }
    Ok(warnings)
}
