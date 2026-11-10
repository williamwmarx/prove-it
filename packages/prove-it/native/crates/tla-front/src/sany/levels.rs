//! A port of `src/sany/levels.ts`: the levelCheck methods of SANY's semantic nodes, which compute
//! the levels, weights and Leibniz flags its XMLExporter writes, and report its level errors. Each
//! check returns what SANY's returns, which is whether the node is free of level errors, or true
//! for the nodes that ignore that.

use crate::levels::{ACTION_LEVEL, CONSTANT_LEVEL, TEMPORAL_LEVEL, VARIABLE_LEVEL};
use crate::ordered_map::OrderedMap;
use crate::sany::nodes::{
    ArgLevelConstraint, ArgLevelParam, CONSTANT_DECL_KIND, DefKind, Graph, LevelFields,
    MessageLocation, Node, NodeId, NodeKind, NodeSet, OpAppl, SanyLocation, SanyMessage, Subst,
    VARIABLE_DECL_KIND, add_sany_message, format_sany_location,
};

type ArgLevelParams = OrderedMap<ArgLevelParam, ArgLevelParam>;
type LevelConstraints = OrderedMap<NodeId, u8>;
type ArgLevelConstraints = OrderedMap<(NodeId, usize), ArgLevelConstraint>;

/// `LevelCheck`: where the check reports SANY's level errors.
pub struct LevelCheck<'a> {
    pub messages: &'a mut Vec<SanyMessage>,
}

/// `addError`.
fn add_error(
    check: &mut LevelCheck,
    location: &SanyLocation,
    text: String,
    code: Option<&'static str>,
) {
    add_sany_message(
        check.messages,
        SanyMessage {
            location: MessageLocation::At(location.clone()),
            text,
            is_warning: false,
            code,
        },
    );
}

/// `addAll`.
fn add_all(target: &mut NodeSet, source: &NodeSet) {
    for &item in source.keys() {
        target.insert(item, ());
    }
}

/// `addArgLevelParam`.
fn add_arg_level_param(target: &mut ArgLevelParams, op: NodeId, index: usize, param: NodeId) {
    let arg_level_param = ArgLevelParam { op, index, param };
    target.insert(arg_level_param, arg_level_param);
}

/// `addArgLevelParams`.
fn add_arg_level_params(
    target: &mut ArgLevelParams,
    source: &ArgLevelParams,
    is_included: impl Fn(&ArgLevelParam) -> bool,
) {
    for (&key, &arg_level_param) in source.iter() {
        if is_included(&arg_level_param) {
            target.insert(key, arg_level_param);
        }
    }
}

/// `putLevelConstraint`: SetOfLevelConstraints.put keeps the lowest bound.
fn put_level_constraint(target: &mut LevelConstraints, param: NodeId, level: u8) {
    let old = target.get(&param).copied().unwrap_or(TEMPORAL_LEVEL);
    target.insert(param, level.min(old));
}

/// `putLevelConstraints`.
fn put_level_constraints(
    target: &mut LevelConstraints,
    source: &LevelConstraints,
    is_included: impl Fn(NodeId) -> bool,
) {
    for (&param, &level) in source.iter() {
        if is_included(param) {
            put_level_constraint(target, param, level);
        }
    }
}

/// `putArgLevelConstraint`: SetOfArgLevelConstraints.put keeps the highest bound.
fn put_arg_level_constraint(
    target: &mut ArgLevelConstraints,
    param: NodeId,
    position: usize,
    level: u8,
) {
    let old = target
        .get(&(param, position))
        .map_or(CONSTANT_LEVEL, |constraint| constraint.level);
    target.insert(
        (param, position),
        ArgLevelConstraint {
            param,
            position,
            level: level.max(old),
        },
    );
}

/// `putArgLevelConstraints`.
fn put_arg_level_constraints(
    target: &mut ArgLevelConstraints,
    source: &ArgLevelConstraints,
    is_included: impl Fn(&ArgLevelConstraint) -> bool,
) {
    for constraint in source.values() {
        if is_included(constraint) {
            put_arg_level_constraint(
                target,
                constraint.param,
                constraint.position,
                constraint.level,
            );
        }
    }
}

/// Runs `update` on the levels of `target` and those of `source`, a copy of them when the two are
/// one node.
fn update_levels(
    graph: &mut Graph,
    target: NodeId,
    source: NodeId,
    update: impl FnOnce(&mut LevelFields, &LevelFields),
) {
    if target == source {
        let source_levels = graph.levels(source).clone();
        return update(graph.levels_mut(target), &source_levels);
    }
    let (target_index, source_index) = (target.0 as usize, source.0 as usize);
    let (low, high) = graph.nodes.split_at_mut(target_index.max(source_index));
    let (target_levels, source_levels) = if target_index < source_index {
        (&mut low[target_index].levels, &high[0].levels)
    } else {
        (&mut high[0].levels, &low[source_index].levels)
    };
    update(target_levels, source_levels);
}

/// `shareLevels`. The TypeScript shares the source's sets and maps with the node; the port copies
/// them, which differs only where the source changes them after its check.
fn share_levels(graph: &mut Graph, node: NodeId, source: NodeId) {
    update_levels(graph, node, source, |node, source| {
        node.level_params = source.level_params.clone();
        node.all_params = source.all_params.clone();
        node.level_constraints = source.level_constraints.clone();
        node.arg_level_constraints = source.arg_level_constraints.clone();
        node.arg_level_params = source.arg_level_params.clone();
    });
}

/// `mergeLevels`.
fn merge_levels(node: &mut LevelFields, part: &LevelFields) {
    add_all(&mut node.level_params, &part.level_params);
    add_all(&mut node.all_params, &part.all_params);
    put_level_constraints(&mut node.level_constraints, &part.level_constraints, |_| {
        true
    });
    put_arg_level_constraints(
        &mut node.arg_level_constraints,
        &part.arg_level_constraints,
        |_| true,
    );
    add_arg_level_params(&mut node.arg_level_params, &part.arg_level_params, |_| true);
}

/// `isOccurring`: ArgLevelParam.occur.
fn is_occurring(arg_level_param: &ArgLevelParam, symbols: &[NodeId]) -> bool {
    symbols.contains(&arg_level_param.op) || symbols.contains(&arg_level_param.param)
}

/// `isParam`.
fn is_param(symbol: &Node) -> bool {
    matches!(symbol.kind, NodeKind::OpDecl(_) | NodeKind::FormalParam(_))
}

/// `isLevelNode`.
fn is_level_node(node: &Node) -> bool {
    !matches!(node.kind, NodeKind::Module(_))
}

/// `isAnyDef`.
fn is_any_def(symbol: &Node) -> bool {
    matches!(
        symbol.kind,
        NodeKind::OpDef(_) | NodeKind::ThmOrAssumpDef(_)
    )
}

/// `getIndex`: the builtins of any number of arguments, whose arity is -1 in the TypeScript and
/// which alone have no parameters, keep one level and weight for all of them.
fn get_index(definition: &Node, index: usize) -> usize {
    match &definition.kind {
        NodeKind::OpDef(node) if node.params.is_none() => 0,
        _ => index,
    }
}

/// `getWeight`.
fn get_weight(definition: &Node, index: usize) -> u8 {
    match &definition.kind {
        NodeKind::OpDef(node) => node
            .weights
            .get(get_index(definition, index))
            .copied()
            .unwrap_or(0),
        _ => 0,
    }
}

/// `getMaxLevel`.
fn get_max_level(definition: &Node, index: usize) -> u8 {
    let max_levels = match &definition.kind {
        NodeKind::OpDef(node) => &node.max_levels,
        NodeKind::ThmOrAssumpDef(node) => &node.max_levels,
        _ => return TEMPORAL_LEVEL,
    };
    max_levels
        .get(get_index(definition, index))
        .copied()
        .unwrap_or(TEMPORAL_LEVEL)
}

/// `getMinMaxLevel`.
fn get_min_max_level(definition: &Node, operand: usize, position: usize) -> u8 {
    let min_max_level = match &definition.kind {
        NodeKind::OpDef(node) => node.min_max_level.as_ref(),
        NodeKind::ThmOrAssumpDef(node) => Some(&node.min_max_level),
        _ => None,
    };
    min_max_level
        .and_then(|levels| levels.get(operand)?.get(position).copied())
        .unwrap_or(CONSTANT_LEVEL)
}

/// `isLeibnizArgument`.
fn is_leibniz_argument(definition: &Node, index: usize) -> bool {
    match &definition.kind {
        NodeKind::OpDef(node) => node
            .is_leibniz_arg
            .as_ref()
            .and_then(|flags| flags.get(get_index(definition, index)).copied())
            .unwrap_or(true),
        NodeKind::ThmOrAssumpDef(node) => node.is_leibniz_arg.get(index).copied().unwrap_or(true),
        _ => true,
    }
}

/// `getOpLevelCond`.
fn get_op_level_cond(definition: &Node, operand: usize, other: usize, index: usize) -> bool {
    let op_level_cond = match &definition.kind {
        NodeKind::OpDef(node) => node.op_level_cond.as_ref(),
        NodeKind::ThmOrAssumpDef(node) => Some(&node.op_level_cond),
        _ => None,
    };
    op_level_cond
        .and_then(|conds| conds.get(operand)?.get(other)?.get(index).copied())
        .unwrap_or(false)
}

/// `getBoundSymbols`.
fn get_bound_symbols(node: &OpAppl) -> Vec<NodeId> {
    let unbounded = node.unbounded.iter().flatten();
    let bounded = node.bounded.iter().flatten().flatten();
    unbounded.chain(bounded).copied().collect()
}

/// `getSubstitute`.
fn get_substitute(symbol: NodeId, substs: &[Subst]) -> Option<NodeId> {
    substs
        .iter()
        .find(|subst| subst.op == symbol)
        .map(|subst| subst.expr)
}

/// `getSubstitutedParams`: Subst.paramSet and Subst.allParamSet.
fn get_substituted_params(graph: &Graph, param: NodeId, substs: &[Subst], is_all: bool) -> NodeSet {
    match get_substitute(param, substs) {
        None => NodeSet::from_iter([(param, ())]),
        Some(substitute) if is_all => graph.levels(substitute).all_params.clone(),
        Some(substitute) => graph.levels(substitute).level_params.clone(),
    }
}

/// `getSubstitutedArgLevelParams`: Subst.getSubALPSet.
fn get_substituted_arg_level_params(
    graph: &Graph,
    source: &ArgLevelParams,
    substs: &[Subst],
) -> ArgLevelParams {
    let mut result = ArgLevelParams::new();
    for (&key, &arg_level_param) in source.iter() {
        let Some(substitute) = get_substitute(arg_level_param.op, substs) else {
            result.insert(key, arg_level_param);
            continue;
        };
        let NodeKind::OpArg { op: operator, .. } = *graph.kind(substitute) else {
            continue;
        };
        if !is_param(graph.node(operator)) {
            continue;
        }
        for &param in get_substituted_params(graph, arg_level_param.param, substs, false).keys() {
            add_arg_level_param(&mut result, operator, arg_level_param.index, param);
        }
    }
    result
}

/// `getSubstitutedLevelConstraints`: Subst.getSubLCSet, of the levels of `body`.
fn get_substituted_level_constraints(
    graph: &mut Graph,
    body: NodeId,
    substs: &[Subst],
    is_constant: bool,
    iteration: u32,
    check: &mut LevelCheck,
) -> LevelConstraints {
    let mut result = LevelConstraints::new();
    let bounds: Vec<(NodeId, u8)> = graph
        .levels(body)
        .level_constraints
        .iter()
        .map(|(&param, &bound)| (param, bound))
        .collect();
    for (param, bound) in bounds {
        let level = match &graph.node(param).kind {
            NodeKind::OpDecl(declaration) if !is_constant => match declaration.decl_kind {
                CONSTANT_DECL_KIND => CONSTANT_LEVEL,
                VARIABLE_DECL_KIND => VARIABLE_LEVEL,
                _ => bound,
            },
            _ => bound,
        };
        for &substituted in get_substituted_params(graph, param, substs, false).keys() {
            put_level_constraint(&mut result, substituted, level);
        }
    }
    let arg_level_params: Vec<ArgLevelParam> = graph
        .levels(body)
        .arg_level_params
        .values()
        .copied()
        .collect();
    for arg_level_param in arg_level_params {
        let Some(substitute) = get_substitute(arg_level_param.op, substs) else {
            continue;
        };
        let NodeKind::OpArg { op: operator, .. } = *graph.kind(substitute) else {
            continue;
        };
        if !matches!(graph.kind(operator), NodeKind::OpDef(_)) {
            continue;
        }
        check_level(graph, operator, iteration, check);
        let level = get_max_level(graph.node(operator), arg_level_param.index);
        for &substituted in
            get_substituted_params(graph, arg_level_param.param, substs, false).keys()
        {
            put_level_constraint(&mut result, substituted, level);
        }
    }
    result
}

/// `getSubstitutedArgLevelConstraints`: Subst.getSubALCSet, of the levels of `body`.
fn get_substituted_arg_level_constraints(
    graph: &mut Graph,
    body: NodeId,
    substs: &[Subst],
    iteration: u32,
    check: &mut LevelCheck,
) -> ArgLevelConstraints {
    let mut result = ArgLevelConstraints::new();
    let constraints: Vec<ArgLevelConstraint> = graph
        .levels(body)
        .arg_level_constraints
        .values()
        .copied()
        .collect();
    for constraint in constraints {
        match get_substitute(constraint.param, substs) {
            None => put_arg_level_constraint(
                &mut result,
                constraint.param,
                constraint.position,
                constraint.level,
            ),
            Some(substitute) => {
                if let NodeKind::OpArg { op, .. } = *graph.kind(substitute)
                    && is_param(graph.node(op))
                {
                    put_arg_level_constraint(
                        &mut result,
                        op,
                        constraint.position,
                        constraint.level,
                    );
                }
            }
        }
    }
    let arg_level_params: Vec<ArgLevelParam> = graph
        .levels(body)
        .arg_level_params
        .values()
        .copied()
        .collect();
    for arg_level_param in arg_level_params {
        let Some(param_substitute) = get_substitute(arg_level_param.param, substs) else {
            continue;
        };
        let operator = match get_substitute(arg_level_param.op, substs) {
            None => Some(arg_level_param.op),
            Some(substitute) => match *graph.kind(substitute) {
                NodeKind::OpArg { op, .. } => Some(op),
                _ => None,
            },
        };
        let Some(operator) = operator.filter(|&operator| is_param(graph.node(operator))) else {
            continue;
        };
        check_level(graph, param_substitute, iteration, check);
        let level = graph.levels(param_substitute).level;
        put_arg_level_constraint(&mut result, operator, arg_level_param.index, level);
    }
    result
}

/// `isConstantModule`: ModuleNode.isConstant.
fn is_constant_module(graph: &mut Graph, module: NodeId, check: &mut LevelCheck) -> bool {
    if !graph
        .get_declarations(module, VARIABLE_DECL_KIND)
        .is_empty()
    {
        return false;
    }
    check_module_levels(graph, module, check);
    let is_any_body_non_constant = graph.get_op_defs(module).into_iter().any(|definition| {
        let body = graph
            .op_def(definition)
            .and_then(|definition| definition.body);
        body.map_or(0, |body| graph.levels(body).level) != CONSTANT_LEVEL
    });
    if is_any_body_non_constant {
        return false;
    }
    let module = graph.module(module).expect("a module");
    module.top_level.iter().all(|&node| {
        !matches!(graph.kind(node), NodeKind::Theorem(_))
            || graph.levels(node).level == CONSTANT_LEVEL
    })
}

/// `checkDefinitionBody`: the parts of OpDefNode.levelCheck and ThmOrAssumpDefNode.levelCheck that
/// follow the body's.
fn check_definition_body(graph: &mut Graph, node: NodeId, params: &[NodeId], body: NodeId) {
    let arities: Vec<usize> = params
        .iter()
        .map(|&param| graph.node(param).symbol_arity())
        .collect();
    let body_levels = graph.levels(body);
    let min_max_level: Vec<Vec<u8>> = params
        .iter()
        .zip(&arities)
        .map(|(&param, &arity)| {
            (0..arity)
                .map(|position| {
                    body_levels
                        .arg_level_constraints
                        .get(&(param, position))
                        .map_or(CONSTANT_LEVEL, |constraint| constraint.level)
                })
                .collect()
        })
        .collect();
    let op_level_cond: Vec<Vec<Vec<bool>>> = params
        .iter()
        .zip(&arities)
        .map(|(&param, &arity)| {
            params
                .iter()
                .map(|&other| {
                    (0..arity)
                        .map(|index| {
                            body_levels.arg_level_params.contains_key(&ArgLevelParam {
                                op: param,
                                index,
                                param: other,
                            })
                        })
                        .collect()
                })
                .collect()
        })
        .collect();
    match &mut graph.node_mut(node).kind {
        NodeKind::OpDef(definition) => {
            definition.min_max_level = Some(min_max_level);
            definition.op_level_cond = Some(op_level_cond);
        }
        NodeKind::ThmOrAssumpDef(definition) => {
            definition.min_max_level = min_max_level;
            definition.op_level_cond = op_level_cond;
        }
        _ => {}
    }
    update_levels(graph, node, body, |node, body| {
        add_all(&mut node.level_params, &body.level_params);
        add_all(&mut node.all_params, &body.all_params);
        add_all(&mut node.non_leibniz_params, &body.non_leibniz_params);
    });
    for (index, &param) in params.iter().enumerate() {
        let levels = graph.levels_mut(node);
        levels.level_params.remove(&param);
        levels.all_params.remove(&param);
        if levels.non_leibniz_params.remove(&param).is_none() {
            continue;
        }
        match &mut graph.node_mut(node).kind {
            NodeKind::OpDef(definition) => {
                if let Some(flag) = definition
                    .is_leibniz_arg
                    .as_mut()
                    .and_then(|flags| flags.get_mut(index))
                {
                    *flag = false;
                }
                definition.is_leibniz = false;
            }
            NodeKind::ThmOrAssumpDef(definition) => {
                if let Some(flag) = definition.is_leibniz_arg.get_mut(index) {
                    *flag = false;
                }
                definition.is_leibniz = false;
            }
            _ => {}
        }
    }
    update_levels(graph, node, body, |node, body| {
        node.level_constraints = body.level_constraints.clone();
        for param in params {
            node.level_constraints.remove(param);
        }
        node.arg_level_constraints = body.arg_level_constraints.clone();
        for (&param, &arity) in params.iter().zip(&arities) {
            for position in 0..arity {
                node.arg_level_constraints.remove(&(param, position));
            }
        }
        add_arg_level_params(
            &mut node.arg_level_params,
            &body.arg_level_params,
            |arg_level_param| {
                !params.contains(&arg_level_param.op) || !params.contains(&arg_level_param.param)
            },
        );
    });
}

/// The OpAppl `node` is.
fn get_op_appl(graph: &Graph, node: NodeId) -> &OpAppl {
    match graph.kind(node) {
        NodeKind::OpAppl(appl) => appl,
        _ => unreachable!("an OpAppl"),
    }
}

/// The name of the symbol `symbol`.
fn get_name(graph: &Graph, symbol: NodeId) -> String {
    graph
        .node(symbol)
        .symbol_name()
        .expect("a symbol")
        .to_string()
}

/// The arity of a symbol, with none for the builtins of any number of arguments (`getIndex`).
fn get_symbol_arity(symbol: &Node) -> usize {
    match &symbol.kind {
        NodeKind::OpDef(definition) if definition.params.is_none() => 0,
        _ => symbol.symbol_arity(),
    }
}

/// `checkArguments`: the checks of OpApplNode.levelCheck that compare the levels of the arguments
/// of a defined operator with the levels it allows.
fn check_arguments(
    graph: &mut Graph,
    node: NodeId,
    operator: NodeId,
    is_operator_correct: bool,
    iteration: u32,
    check: &mut LevelCheck,
) {
    let appl = get_op_appl(graph, node).clone();
    let operator_name = get_name(graph, operator);
    for (index, &operand) in appl.operands.iter().enumerate() {
        let Some(operand) = operand else {
            continue;
        };
        if graph.levels(operand).level > get_max_level(graph.node(operator), index) {
            if is_operator_correct && check_level(graph, operand, iteration, check) {
                add_error(
                    check,
                    &appl.location,
                    format!(
                        "Level error in applying operator {operator_name}:\nThe level of argument {} exceeds the maximum level allowed by the operator.",
                        index + 1
                    ),
                    None,
                );
            }
            graph.levels_mut(node).level_correct = false;
        }
        let NodeKind::OpArg { op: argument, .. } = *graph.kind(operand) else {
            continue;
        };
        if !is_any_def(graph.node(argument)) {
            continue;
        }
        check_level(graph, argument, iteration, check);
        let arity = get_symbol_arity(graph.node(argument));
        for position in 0..arity {
            let minimum = get_min_max_level(graph.node(operator), index, position);
            if get_max_level(graph.node(argument), position) >= minimum {
                continue;
            }
            if is_operator_correct && check_level(graph, operand, iteration, check) {
                add_error(
                    check,
                    &appl.location,
                    format!(
                        "Level error in applying operator {operator_name}:\nThe permitted level of argument {} of the operator argument {} \nmust be at least {minimum}.",
                        position + 1,
                        index + 1
                    ),
                    None,
                );
            }
            graph.levels_mut(node).level_correct = false;
        }
        for (other_index, &other) in appl.operands.iter().enumerate() {
            for position in 0..arity {
                let Some(other) = other else {
                    continue;
                };
                if !get_op_level_cond(graph.node(operator), index, other_index, position)
                    || graph.levels(other).level <= get_max_level(graph.node(argument), position)
                {
                    continue;
                }
                if check_level(graph, operand, iteration, check)
                    && check_level(graph, other, iteration, check)
                {
                    add_error(
                        check,
                        &appl.location,
                        format!(
                            "Level error in applying operator {operator_name}:\nThe level of argument {} exceeds the maximum level allowed by the operator.",
                            other_index + 1
                        ),
                        Some("HIGHER_ORDER_OPERATOR_COPARAMETER_LEVEL_CONSTRAINTS_EXCEEDED"),
                    );
                }
                graph.levels_mut(node).level_correct = false;
            }
        }
    }
    for (index, &range) in appl.ranges.iter().enumerate() {
        let is_range_correct = check_level(graph, range, iteration, check);
        if graph.levels(range).level <= ACTION_LEVEL {
            continue;
        }
        if is_range_correct {
            let bound = appl
                .bounded
                .as_ref()
                .and_then(|bounded| bounded.get(index)?.first().copied());
            let location = bound
                .and_then(|bound| graph.node(bound).location().cloned())
                .map_or(MessageLocation::Unknown, MessageLocation::At);
            add_error(
                check,
                &appl.location,
                format!(
                    "Level error in applying operator {operator_name}:\nThe level of the range for the bounded variable {} \nexceeds the maximum level allowed by the operator.",
                    format_sany_location(&location)
                ),
                None,
            );
        }
        graph.levels_mut(node).level_correct = false;
    }
}

/// `constrainArguments`: the level constraints OpApplNode.levelCheck derives for an application of
/// a defined operator.
fn constrain_arguments(
    graph: &mut Graph,
    node: NodeId,
    operator: NodeId,
    bound_symbols: &NodeSet,
    iteration: u32,
    check: &mut LevelCheck,
) {
    let appl = get_op_appl(graph, node).clone();
    let params = match &graph.node(operator).kind {
        NodeKind::OpDef(definition) => definition.params.clone().unwrap_or_default(),
        NodeKind::ThmOrAssumpDef(definition) => definition.params.clone(),
        _ => Vec::new(),
    };
    let get_argument = |symbol: NodeId| {
        appl.operands
            .iter()
            .enumerate()
            .find(|&(index, _)| params.get(index) == Some(&symbol))
            .and_then(|(_, &operand)| operand)
    };
    let operands: Vec<NodeId> = appl.operands.iter().flatten().copied().collect();
    update_levels(graph, node, operator, |node, operator| {
        put_level_constraints(
            &mut node.level_constraints,
            &operator.level_constraints,
            |_| true,
        );
    });
    for &operand in &operands {
        update_levels(graph, node, operand, |node, operand| {
            put_level_constraints(
                &mut node.level_constraints,
                &operand.level_constraints,
                |param| !bound_symbols.contains_key(&param),
            );
        });
    }
    for &range in &appl.ranges {
        update_levels(graph, node, range, |node, range| {
            put_level_constraints(
                &mut node.level_constraints,
                &range.level_constraints,
                |_| true,
            );
        });
    }
    for (index, &operand) in appl.operands.iter().enumerate() {
        let level = get_max_level(graph.node(operator), index);
        let Some(operand) = operand else {
            continue;
        };
        update_levels(graph, node, operand, |node, operand| {
            for &param in operand.level_params.keys() {
                put_level_constraint(&mut node.level_constraints, param, level);
            }
        });
    }
    for (index, &operand) in appl.operands.iter().enumerate() {
        let Some(operand) = operand else {
            continue;
        };
        let NodeKind::OpArg { op: argument, .. } = *graph.kind(operand) else {
            continue;
        };
        if !is_any_def(graph.node(argument)) {
            continue;
        }
        check_level(graph, argument, iteration, check);
        let arity = get_symbol_arity(graph.node(argument));
        let is_argument_leibniz = match &graph.node(argument).kind {
            NodeKind::OpDef(definition) => definition.is_leibniz,
            NodeKind::ThmOrAssumpDef(definition) => definition.is_leibniz,
            _ => true,
        };
        for (other_index, &other) in appl.operands.iter().enumerate() {
            for position in 0..arity {
                if !get_op_level_cond(graph.node(operator), index, other_index, position) {
                    continue;
                }
                let level = get_max_level(graph.node(argument), position);
                let Some(other) = other else {
                    continue;
                };
                let is_non_leibniz =
                    !is_argument_leibniz && !is_leibniz_argument(graph.node(argument), position);
                update_levels(graph, node, other, |node, other| {
                    for &param in other.level_params.keys() {
                        put_level_constraint(&mut node.level_constraints, param, level);
                    }
                    if is_non_leibniz {
                        add_all(&mut node.non_leibniz_params, &other.all_params);
                    }
                });
            }
        }
    }
    let operator_arg_level_params: Vec<ArgLevelParam> = graph
        .levels(operator)
        .arg_level_params
        .values()
        .copied()
        .collect();
    for arg_level_param in &operator_arg_level_params {
        let Some(argument) = get_argument(arg_level_param.op) else {
            continue;
        };
        let NodeKind::OpArg { op: argument, .. } = *graph.kind(argument) else {
            continue;
        };
        if !is_any_def(graph.node(argument)) {
            continue;
        }
        check_level(graph, argument, iteration, check);
        let level = get_max_level(graph.node(argument), arg_level_param.index);
        put_level_constraint(
            &mut graph.levels_mut(node).level_constraints,
            arg_level_param.param,
            level,
        );
    }
    update_levels(graph, node, operator, |node, operator| {
        put_arg_level_constraints(
            &mut node.arg_level_constraints,
            &operator.arg_level_constraints,
            |_| true,
        );
    });
    for &operand in &operands {
        update_levels(graph, node, operand, |node, operand| {
            put_arg_level_constraints(
                &mut node.arg_level_constraints,
                &operand.arg_level_constraints,
                |_| true,
            );
        });
    }
    for &range in &appl.ranges {
        update_levels(graph, node, range, |node, range| {
            put_arg_level_constraints(
                &mut node.arg_level_constraints,
                &range.arg_level_constraints,
                |_| true,
            );
        });
    }
    for (index, &operand) in appl.operands.iter().enumerate() {
        let Some(operand) = operand else {
            continue;
        };
        let NodeKind::OpArg { op: argument, .. } = *graph.kind(operand) else {
            continue;
        };
        if !is_param(graph.node(argument)) {
            continue;
        }
        let arity = graph.node(argument).symbol_arity();
        for position in 0..arity {
            let level = get_min_max_level(graph.node(operator), index, position);
            put_arg_level_constraint(
                &mut graph.levels_mut(node).arg_level_constraints,
                argument,
                position,
                level,
            );
        }
        for (other_index, &other) in appl.operands.iter().enumerate() {
            for position in 0..arity {
                let Some(other) = other else {
                    continue;
                };
                if !get_op_level_cond(graph.node(operator), index, other_index, position) {
                    continue;
                }
                let level = graph.levels(other).level;
                put_arg_level_constraint(
                    &mut graph.levels_mut(node).arg_level_constraints,
                    argument,
                    position,
                    level,
                );
            }
        }
    }
    for arg_level_param in &operator_arg_level_params {
        let Some(argument) = get_argument(arg_level_param.op) else {
            continue;
        };
        check_level(graph, argument, iteration, check);
        let level = graph.levels(argument).level;
        put_arg_level_constraint(
            &mut graph.levels_mut(node).arg_level_constraints,
            arg_level_param.op,
            arg_level_param.index,
            level,
        );
    }
    for &operand in &operands {
        update_levels(graph, node, operand, |node, operand| {
            add_arg_level_params(
                &mut node.arg_level_params,
                &operand.arg_level_params,
                |arg_level_param| !bound_symbols.contains_key(&arg_level_param.param),
            );
        });
    }
    for &range in &appl.ranges {
        update_levels(graph, node, range, |node, range| {
            add_arg_level_params(&mut node.arg_level_params, &range.arg_level_params, |_| {
                true
            });
        });
    }
    let operator_arg_level_params: Vec<(ArgLevelParam, ArgLevelParam)> = graph
        .levels(operator)
        .arg_level_params
        .iter()
        .map(|(&key, &arg_level_param)| (key, arg_level_param))
        .collect();
    for (key, arg_level_param) in operator_arg_level_params {
        let Some(argument) = get_argument(arg_level_param.op) else {
            match get_argument(arg_level_param.param) {
                None => {
                    graph
                        .levels_mut(node)
                        .arg_level_params
                        .insert(key, arg_level_param);
                }
                Some(param_argument) => {
                    check_level(graph, param_argument, iteration, check);
                    update_levels(graph, node, param_argument, |node, param_argument| {
                        for &param in param_argument.level_params.keys() {
                            add_arg_level_param(
                                &mut node.arg_level_params,
                                arg_level_param.op,
                                arg_level_param.index,
                                param,
                            );
                        }
                    });
                }
            }
            continue;
        };
        if let NodeKind::OpArg { op, .. } = *graph.kind(argument)
            && is_param(graph.node(op))
        {
            add_arg_level_param(
                &mut graph.levels_mut(node).arg_level_params,
                op,
                arg_level_param.index,
                arg_level_param.param,
            );
        }
    }
    for (index, &operand) in appl.operands.iter().enumerate() {
        let Some(operand) = operand else {
            continue;
        };
        let NodeKind::OpArg { op: argument, .. } = *graph.kind(operand) else {
            continue;
        };
        if !is_param(graph.node(argument)) {
            continue;
        }
        let arity = graph.node(argument).symbol_arity();
        for (other_index, &other) in appl.operands.iter().enumerate() {
            for position in 0..arity {
                let Some(other) = other else {
                    continue;
                };
                if !get_op_level_cond(graph.node(operator), index, other_index, position) {
                    continue;
                }
                update_levels(graph, node, other, |node, other| {
                    for &param in other.level_params.keys() {
                        add_arg_level_param(&mut node.arg_level_params, argument, position, param);
                    }
                });
            }
        }
    }
}

/// `LOGICAL_OPERATOR_NAMES`: the operators OpApplNode.levelCheck rejects with both temporal and
/// action arguments, and how its message names them.
fn get_logical_operator_name(name: &str) -> Option<&'static str> {
    match name {
        "\\land" => Some("\\land"),
        "\\lor" => Some("\\lor"),
        "=>" => Some("=>"),
        "\\equiv" => Some("\\equiv"),
        "$ConjList" => Some("Conjunction list"),
        "$DisjList" => Some("Disjunction list"),
        _ => None,
    }
}

/// `checkTemporalApplication`: the checks at the end of OpApplNode.levelCheck of the temporal
/// operators and quantifiers.
fn check_temporal_application(graph: &mut Graph, node: NodeId, check: &mut LevelCheck) {
    let appl = get_op_appl(graph, node);
    let name = get_name(graph, appl.operator);
    let location = appl.location.clone();
    let ranges = appl.ranges.clone();
    let first = appl.operands.first().copied().flatten();
    let second = appl.operands.get(1).copied().flatten();
    let operand_levels: Vec<u8> = appl
        .operands
        .iter()
        .flatten()
        .map(|&operand| graph.levels(operand).level)
        .collect();
    let mut errors: Vec<(SanyLocation, String)> = Vec::new();
    let get_level = |operand: Option<NodeId>| operand.map(|operand| graph.levels(operand).level);
    if (name == "[]" || name == "<>")
        && let Some(first) = first
        && graph.levels(first).level == ACTION_LEVEL
        && let NodeKind::OpAppl(first) = graph.kind(first)
    {
        let is_boxed = name == "[]";
        let expected = if is_boxed { "$SquareAct" } else { "$AngleAct" };
        if get_name(graph, first.operator) != expected {
            let text = if is_boxed {
                "[] followed by action not of form [A]_v."
            } else {
                "<> followed by action not of form <<A>>_v."
            };
            errors.push((location.clone(), text.to_owned()));
        }
    }
    if (name == "~>" || name == "-+->")
        && (get_level(first) == Some(ACTION_LEVEL) || get_level(second) == Some(ACTION_LEVEL))
    {
        errors.push((
            location.clone(),
            "Action used where only temporal formula or state predicate allowed.".to_owned(),
        ));
    }
    if let Some(logical_name) = get_logical_operator_name(&name)
        && operand_levels.contains(&TEMPORAL_LEVEL)
        && operand_levels.contains(&ACTION_LEVEL)
    {
        errors.push((
            location,
            format!("{logical_name} has both temporal formula and action as arguments."),
        ));
    }
    if graph.levels(node).level == TEMPORAL_LEVEL
        && (name == "$BoundedExists" || name == "$BoundedForall")
    {
        for range in ranges {
            if graph.levels(range).level == ACTION_LEVEL {
                let range_location = graph.node(range).location().expect("a location").clone();
                errors.push((
                    range_location,
                    "Action-level bound of quantified temporal formula.".to_owned(),
                ));
            }
        }
    }
    for (location, text) in errors {
        add_error(check, &location, text, None);
        graph.levels_mut(node).level_correct = false;
    }
}

/// `checkApplication`.
fn check_application(
    graph: &mut Graph,
    node: NodeId,
    iteration: u32,
    check: &mut LevelCheck,
) -> bool {
    if graph.levels(node).level_checked >= iteration {
        return graph.levels(node).level_correct;
    }
    graph.levels_mut(node).level_checked = iteration;
    graph.levels_mut(node).level_correct = true;
    let appl = get_op_appl(graph, node).clone();
    let operands: Vec<NodeId> = appl.operands.iter().flatten().copied().collect();
    for &operand in &operands {
        if !check_level(graph, operand, iteration, check) {
            graph.levels_mut(node).level_correct = false;
        }
    }
    for &range in &appl.ranges {
        if !check_level(graph, range, iteration, check) {
            graph.levels_mut(node).level_correct = false;
        }
    }
    let operator = appl.operator;
    if is_any_def(graph.node(operator)) {
        let is_operator_correct = check_level(graph, operator, iteration, check);
        check_arguments(graph, node, operator, is_operator_correct, iteration, check);
        let mut level = graph.levels(operator).level;
        for (index, &operand) in appl.operands.iter().enumerate() {
            if let Some(operand) = operand
                && get_weight(graph.node(operator), index) == 1
            {
                level = level.max(graph.levels(operand).level);
            }
        }
        graph.levels_mut(node).level = level;
        for &range in &appl.ranges {
            let level = graph.levels(node).level.max(graph.levels(range).level);
            graph.levels_mut(node).level = level;
        }
        update_levels(graph, node, operator, |node, operator| {
            add_all(&mut node.level_params, &operator.level_params);
            add_all(&mut node.all_params, &operator.all_params);
            add_all(&mut node.non_leibniz_params, &operator.non_leibniz_params);
        });
        for (index, &operand) in appl.operands.iter().enumerate() {
            let Some(operand) = operand else {
                continue;
            };
            let is_weighted = get_weight(graph.node(operator), index) == 1;
            let is_leibniz = is_leibniz_argument(graph.node(operator), index);
            update_levels(graph, node, operand, |node, operand| {
                if is_weighted {
                    add_all(&mut node.level_params, &operand.level_params);
                }
                add_all(&mut node.all_params, &operand.all_params);
                add_all(&mut node.non_leibniz_params, &operand.non_leibniz_params);
                if !is_leibniz {
                    add_all(&mut node.non_leibniz_params, &operand.all_params);
                }
            });
        }
        for &range in &appl.ranges {
            update_levels(graph, node, range, |node, range| {
                add_all(&mut node.level_params, &range.level_params);
                add_all(&mut node.all_params, &range.all_params);
                add_all(&mut node.non_leibniz_params, &range.non_leibniz_params);
            });
        }
        let bound_symbols: NodeSet = get_bound_symbols(&appl)
            .into_iter()
            .map(|symbol| (symbol, ()))
            .collect();
        let levels = graph.levels_mut(node);
        for symbol in bound_symbols.keys() {
            levels.level_params.remove(symbol);
            levels.all_params.remove(symbol);
            levels.non_leibniz_params.remove(symbol);
        }
        constrain_arguments(graph, node, operator, &bound_symbols, iteration, check);
    } else {
        check_level(graph, operator, iteration, check);
        let initial = match graph.kind(operator) {
            NodeKind::Module(_) => 0,
            _ => graph.levels(operator).level,
        };
        let level = operands.iter().fold(initial, |level, &operand| {
            level.max(graph.levels(operand).level)
        });
        let levels = graph.levels_mut(node);
        levels.level = level;
        levels.level_params = NodeSet::from_iter([(operator, ())]);
        levels.all_params.insert(operator, ());
        for (index, &operand) in operands.iter().enumerate() {
            update_levels(graph, node, operand, |node, operand| {
                add_all(&mut node.level_params, &operand.level_params);
                add_all(&mut node.all_params, &operand.all_params);
                add_all(&mut node.non_leibniz_params, &operand.non_leibniz_params);
                put_level_constraints(
                    &mut node.level_constraints,
                    &operand.level_constraints,
                    |_| true,
                );
                put_arg_level_constraint(
                    &mut node.arg_level_constraints,
                    operator,
                    index,
                    operand.level,
                );
                put_arg_level_constraints(
                    &mut node.arg_level_constraints,
                    &operand.arg_level_constraints,
                    |_| true,
                );
                for &param in operand.level_params.keys() {
                    add_arg_level_param(&mut node.arg_level_params, operator, index, param);
                }
                add_arg_level_params(
                    &mut node.arg_level_params,
                    &operand.arg_level_params,
                    |_| true,
                );
            });
        }
    }
    check_temporal_application(graph, node, check);
    graph.levels(node).level_correct
}

/// `checkDefinition`.
fn check_definition(
    graph: &mut Graph,
    node: NodeId,
    iteration: u32,
    check: &mut LevelCheck,
) -> bool {
    let definition = graph.op_def(node).expect("an OpDef");
    let (body, step, params) = (
        definition.body,
        definition.step,
        definition.params.clone().unwrap_or_default(),
    );
    let level_checked = graph.levels(node).level_checked;
    if level_checked >= iteration || (!definition.in_recursive_section && level_checked > 0) {
        return graph.levels(node).level_correct;
    }
    graph.levels_mut(node).level_checked = iteration;
    let Some(body) = body else {
        let is_correct = step.is_none_or(|step| check_level(graph, step, iteration, check));
        graph.levels_mut(node).level_correct = is_correct;
        return is_correct;
    };
    let is_correct = check_level(graph, body, iteration, check);
    let body_level = graph.levels(body).level;
    let levels = graph.levels_mut(node);
    levels.level_correct = is_correct;
    levels.level = levels.level.max(body_level);
    for (index, param) in params.iter().enumerate() {
        let body_levels = graph.levels(body);
        let bound = body_levels.level_constraints.get(param).copied();
        let is_level_param = body_levels.level_params.contains_key(param);
        let definition = graph.op_def_mut(node).expect("an OpDef");
        if let Some(bound) = bound
            && let Some(max_level) = definition.max_levels.get_mut(index)
        {
            *max_level = (*max_level).min(bound);
        }
        if is_level_param && let Some(weight) = definition.weights.get_mut(index) {
            *weight = (*weight).max(1);
        }
    }
    check_definition_body(graph, node, &params, body);
    graph.levels(node).level_correct
}

/// `checkTheoremDefinition`.
fn check_theorem_definition(
    graph: &mut Graph,
    node: NodeId,
    iteration: u32,
    check: &mut LevelCheck,
) -> bool {
    if graph.levels(node).level_checked >= iteration {
        return graph.levels(node).level_correct;
    }
    graph.levels_mut(node).level_checked = iteration;
    let NodeKind::ThmOrAssumpDef(definition) = &mut graph.node_mut(node).kind else {
        unreachable!("a ThmOrAssumpDef");
    };
    let count = definition.params.len();
    definition.max_levels = vec![TEMPORAL_LEVEL; count];
    // SANY allocates isLeibnizArg anew for each parameter, so only the last one starts out Leibniz.
    definition.is_leibniz_arg = (0..count).map(|index| index + 1 == count).collect();
    if count > 0 {
        definition.is_leibniz = true;
    }
    let (body, params) = (definition.body, definition.params.clone());
    let is_correct = check_level(graph, body, iteration, check);
    let body_level = graph.levels(body).level;
    let levels = graph.levels_mut(node);
    levels.level_correct = is_correct;
    levels.level = body_level;
    for (index, param) in params.iter().enumerate() {
        let bound = graph.levels(body).level_constraints.get(param).copied();
        let NodeKind::ThmOrAssumpDef(definition) = &mut graph.node_mut(node).kind else {
            unreachable!("a ThmOrAssumpDef");
        };
        if let Some(bound) = bound
            && let Some(max_level) = definition.max_levels.get_mut(index)
        {
            *max_level = bound;
        }
    }
    check_definition_body(graph, node, &params, body);
    graph.levels(node).level_correct
}

/// `checkModuleLevels`: ModuleNode.levelCheck. The definitions of each recursive section are
/// checked twice, the second time with the highest level and the parameters of the section's
/// recursive operators.
pub fn check_module_levels(graph: &mut Graph, module: NodeId, check: &mut LevelCheck) -> bool {
    let module_node = graph.module_mut(module).expect("a module");
    if module_node.is_level_checked {
        return graph.levels(module).level_correct;
    }
    module_node.is_level_checked = true;
    let sections = module_node.op_defs_in_recursive_section.clone();
    let get_definition = |graph: &Graph, definition: NodeId| {
        let definition = graph.op_def(definition).expect("an OpDef");
        (definition.recursive_section, definition.in_recursive)
    };
    let mut first = 0;
    while first < sections.len() {
        let section = get_definition(graph, sections[first]).0;
        let mut end = first;
        while end < sections.len() && get_definition(graph, sections[end]).0 == section {
            let definition = sections[end];
            if get_definition(graph, definition).1 {
                graph.levels_mut(definition).level_checked = 1;
                let node = graph.op_def_mut(definition).expect("an OpDef");
                node.max_levels.fill(ACTION_LEVEL);
                node.weights.fill(1);
            } else {
                graph.levels_mut(definition).level_checked = 0;
            }
            end += 1;
        }
        let members = &sections[first..end];
        let mut level_params = NodeSet::new();
        let mut all_params = NodeSet::new();
        let mut max_level = 0;
        for &definition in members {
            let is_recursive = get_definition(graph, definition).1;
            if is_recursive {
                graph.levels_mut(definition).level_checked = 0;
            }
            check_definition(graph, definition, 1, check);
            if !is_recursive {
                continue;
            }
            let node = graph.op_def(definition).expect("an OpDef");
            for (index, &level) in node.max_levels.iter().enumerate() {
                if level >= ACTION_LEVEL {
                    continue;
                }
                add_error(
                    check,
                    &node.location,
                    format!(
                        "Argument {} of recursive operator {} is primed",
                        index + 1,
                        node.name
                    ),
                    None,
                );
            }
            let levels = graph.levels(definition);
            max_level = levels.level.max(max_level);
            add_all(&mut level_params, &levels.level_params);
            add_all(&mut all_params, &levels.all_params);
        }
        for &definition in members {
            if get_definition(graph, definition).1 {
                graph.levels_mut(definition).level_checked = 2;
            }
            let levels = graph.levels_mut(definition);
            levels.level = levels.level.max(max_level);
            add_all(&mut levels.level_params, &level_params);
            add_all(&mut levels.all_params, &all_params);
        }
        for &definition in members {
            if get_definition(graph, definition).1 {
                graph.levels_mut(definition).level_checked = 1;
            }
            check_definition(graph, definition, 2, check);
        }
        first = end;
    }
    graph.levels_mut(module).level_correct = true;
    let record_correctness = |graph: &mut Graph, is_node_correct: bool| {
        if !is_node_correct {
            graph.levels_mut(module).level_correct = false;
        }
    };
    let module_node = graph.module(module).expect("a module");
    let inner_modules: Vec<NodeId> = module_node
        .definitions
        .iter()
        .copied()
        .filter(|&definition| matches!(graph.kind(definition), NodeKind::Module(_)))
        .collect();
    let top_level = module_node.top_level.clone();
    for inner in inner_modules {
        let is_correct = check_module_levels(graph, inner, check);
        record_correctness(graph, is_correct);
    }
    let definitions = graph.get_op_defs(module);
    for &definition in &definitions {
        let is_correct = check_definition(graph, definition, 1, check);
        record_correctness(graph, is_correct);
    }
    for definition in graph.get_thm_or_assump_defs(module) {
        let is_correct = check_theorem_definition(graph, definition, 1, check);
        record_correctness(graph, is_correct);
    }
    for &node in &top_level {
        let is_correct = check_level(graph, node, 1, check);
        record_correctness(graph, is_correct);
    }
    if !is_constant_module(graph, module, check) {
        for declaration in graph.get_declarations(module, CONSTANT_DECL_KIND) {
            put_level_constraint(
                &mut graph.levels_mut(module).level_constraints,
                declaration,
                CONSTANT_LEVEL,
            );
        }
    }
    for &definition in &definitions {
        let params = graph
            .op_def(definition)
            .and_then(|definition| definition.params.clone())
            .unwrap_or_default();
        update_levels(graph, module, definition, |module, definition| {
            put_level_constraints(
                &mut module.level_constraints,
                &definition.level_constraints,
                |_| true,
            );
            put_arg_level_constraints(
                &mut module.arg_level_constraints,
                &definition.arg_level_constraints,
                |_| true,
            );
            add_arg_level_params(
                &mut module.arg_level_params,
                &definition.arg_level_params,
                |arg_level_param| !is_occurring(arg_level_param, &params),
            );
        });
    }
    for &node in &top_level {
        update_levels(graph, module, node, |module, node| {
            put_level_constraints(
                &mut module.level_constraints,
                &node.level_constraints,
                |_| true,
            );
            put_arg_level_constraints(
                &mut module.arg_level_constraints,
                &node.arg_level_constraints,
                |_| true,
            );
            add_arg_level_params(&mut module.arg_level_params, &node.arg_level_params, |_| {
                true
            });
        });
    }
    graph.levels(module).level_correct
}

/// `checkSubnodes`: LevelNode.levelCheckSubnodes, which skips modules.
fn check_subnodes(
    graph: &mut Graph,
    node: NodeId,
    subnodes: &[NodeId],
    iteration: u32,
    check: &mut LevelCheck,
) -> bool {
    if graph.levels(node).level_checked >= iteration {
        return graph.levels(node).level_correct;
    }
    graph.levels_mut(node).level_checked = iteration;
    for &subnode in subnodes {
        if !is_level_node(graph.node(subnode)) {
            continue;
        }
        if matches!(graph.kind(subnode),
            NodeKind::OpDef(definition) if definition.def_kind == DefKind::ModuleInstance)
        {
            continue;
        }
        let is_subnode_correct = check_level(graph, subnode, iteration, check);
        update_levels(graph, node, subnode, |node, subnode| {
            node.level_correct = is_subnode_correct && node.level_correct;
            node.level = node.level.max(subnode.level);
            merge_levels(node, subnode);
            add_all(&mut node.non_leibniz_params, &subnode.non_leibniz_params);
        });
    }
    graph.levels(node).level_correct
}

/// `checkTemporalProof`: TheoremNode.LevelCheckTemporal, the steps of the proof of a temporal
/// theorem that must be constant.
fn check_temporal_proof(graph: &Graph, proof: Option<NodeId>, check: &mut LevelCheck) {
    let Some(NodeKind::NonLeafProof(proof)) = proof.map(|proof| graph.kind(proof)) else {
        return;
    };
    for &step in &proof.steps {
        let NodeKind::Theorem(step) = graph.kind(step) else {
            continue;
        };
        let NodeKind::OpAppl(body) = graph.kind(step.body) else {
            continue;
        };
        let is_constant = graph.levels(step.body).level == CONSTANT_LEVEL;
        match get_name(graph, body.operator).as_str() {
            "$Take" | "$Witness" | "$Have" => {
                if !is_constant {
                    add_error(
                        check,
                        &body.location,
                        "Non-constant TAKE, WITNESS, or HAVE for temporal goal.".to_owned(),
                        None,
                    );
                }
            }
            "$Pfcase" => {
                if !is_constant {
                    add_error(
                        check,
                        &body.location,
                        "Non-constant CASE for temporal goal.".to_owned(),
                        None,
                    );
                }
                check_temporal_proof(graph, step.proof, check);
            }
            "$Qed" => check_temporal_proof(graph, step.proof, check),
            _ => {}
        }
    }
}

/// `checkInstance`: InstanceNode.levelCheck.
fn check_instance(graph: &mut Graph, node: NodeId, iteration: u32, check: &mut LevelCheck) -> bool {
    if graph.levels(node).level_checked >= iteration {
        return graph.levels(node).level_correct;
    }
    let levels = graph.levels_mut(node);
    levels.level_checked = iteration;
    levels.level_params = NodeSet::new();
    levels.level_correct = true;
    let NodeKind::Instance(instance) = graph.kind(node) else {
        unreachable!("an Instance");
    };
    let (module, substs, params, location) = (
        instance.module,
        instance.substs.clone(),
        instance.params.clone(),
        instance.location.clone(),
    );
    let module_name = get_name(graph, module);
    if !check_module_levels(graph, module, check) {
        graph.levels_mut(node).level_correct = false;
    }
    for subst in &substs {
        if !check_level(graph, subst.expr, iteration, check) {
            graph.levels_mut(node).level_correct = false;
        }
    }
    let is_constant = is_constant_module(graph, module, check);
    for subst in &substs {
        let op_level = graph.levels(subst.op).level;
        let op_name = get_name(graph, subst.op);
        if !is_constant && graph.levels(subst.expr).level > op_level {
            if check_level(graph, subst.expr, iteration, check) {
                add_error(
                    check,
                    &location,
                    format!(
                        "Level error in instantiating module '{module_name}':\nThe level of the expression or operator substituted for '{op_name}' \nmust be at most {op_level}."
                    ),
                    None,
                );
            }
            graph.levels_mut(node).level_correct = false;
        }
        if let NodeKind::OpArg { op, .. } = *graph.kind(subst.expr)
            && let NodeKind::OpDef(definition) = graph.kind(op)
            && matches!(definition.def_kind, DefKind::UserDefined | DefKind::BuiltIn)
            && !definition.is_leibniz
        {
            add_error(
                check,
                &location,
                format!(
                    "Error in instantiating module '{module_name}':\n A non-Leibniz operator substituted for '{op_name}'."
                ),
                None,
            );
        }
    }
    for subst in &substs {
        let op_name = get_name(graph, subst.op);
        let bound = graph
            .levels(module)
            .level_constraints
            .get(&subst.op)
            .copied();
        if let Some(bound) = bound
            && graph.levels(subst.expr).level > bound
        {
            if check_level(graph, subst.expr, iteration, check) {
                add_error(
                    check,
                    &location,
                    format!(
                        "Level error in instantiating module '{module_name}':\nThe level of the expression or operator substituted for '{op_name}' \nmust be at most {bound}."
                    ),
                    None,
                );
            }
            graph.levels_mut(node).level_correct = false;
        }
        let arity = graph.node(subst.op).symbol_arity();
        let NodeKind::OpArg { op: definition, .. } = *graph.kind(subst.expr) else {
            continue;
        };
        if arity == 0 || !matches!(graph.kind(definition), NodeKind::OpDef(_)) {
            continue;
        }
        let is_definition_correct = check_level(graph, definition, iteration, check);
        for position in 0..arity {
            let minimum = graph
                .levels(module)
                .arg_level_constraints
                .get(&(subst.op, position))
                .map(|constraint| constraint.level);
            let Some(minimum) = minimum else {
                continue;
            };
            if get_max_level(graph.node(definition), position) >= minimum {
                continue;
            }
            if is_definition_correct {
                add_error(
                    check,
                    &location,
                    format!(
                        "Level error in instantiating module '{module_name}':\nThe level of the argument {} of the operator {} \nmust be at least {minimum}.",
                        position + 1,
                        get_name(graph, definition)
                    ),
                    None,
                );
            }
            graph.levels_mut(node).level_correct = false;
        }
    }
    let module_arg_level_params: Vec<ArgLevelParam> = graph
        .levels(module)
        .arg_level_params
        .values()
        .copied()
        .collect();
    for arg_level_param in &module_arg_level_params {
        for op_subst in &substs {
            for param_subst in &substs {
                if arg_level_param.op != op_subst.op || arg_level_param.param != param_subst.op {
                    continue;
                }
                let NodeKind::OpArg { op: operator, .. } = *graph.kind(op_subst.expr) else {
                    continue;
                };
                let is_operator_correct = check_level(graph, operator, iteration, check);
                if !matches!(graph.kind(operator), NodeKind::OpDef(_)) {
                    continue;
                }
                let maximum = get_max_level(graph.node(operator), arg_level_param.index);
                if graph.levels(param_subst.expr).level <= maximum {
                    continue;
                }
                if is_operator_correct && check_level(graph, param_subst.expr, iteration, check) {
                    add_error(
                        check,
                        &location,
                        format!(
                            "Level error when instantiating module '{module_name}':\nThe level of the argument {} of the operator {}' \nmust be at most {maximum}.",
                            arg_level_param.index,
                            get_name(graph, op_subst.op)
                        ),
                        None,
                    );
                }
                graph.levels_mut(node).level_correct = false;
            }
        }
    }
    let is_outside = |symbol: NodeId| !params.contains(&symbol);
    let level_constraints =
        get_substituted_level_constraints(graph, module, &substs, is_constant, iteration, check);
    put_level_constraints(
        &mut graph.levels_mut(node).level_constraints,
        &level_constraints,
        is_outside,
    );
    for subst in &substs {
        update_levels(graph, node, subst.expr, |node, expr| {
            put_level_constraints(
                &mut node.level_constraints,
                &expr.level_constraints,
                is_outside,
            );
        });
    }
    let arg_level_constraints =
        get_substituted_arg_level_constraints(graph, module, &substs, iteration, check);
    put_arg_level_constraints(
        &mut graph.levels_mut(node).arg_level_constraints,
        &arg_level_constraints,
        |constraint| is_outside(constraint.param),
    );
    for subst in &substs {
        update_levels(graph, node, subst.expr, |node, expr| {
            put_arg_level_constraints(
                &mut node.arg_level_constraints,
                &expr.arg_level_constraints,
                |constraint| is_outside(constraint.param),
            );
        });
    }
    let arg_level_params =
        get_substituted_arg_level_params(graph, &graph.levels(module).arg_level_params, &substs);
    add_arg_level_params(
        &mut graph.levels_mut(node).arg_level_params,
        &arg_level_params,
        |arg_level_param| !is_occurring(arg_level_param, &params),
    );
    for subst in &substs {
        update_levels(graph, node, subst.expr, |node, expr| {
            add_arg_level_params(
                &mut node.arg_level_params,
                &expr.arg_level_params,
                |arg_level_param| !is_occurring(arg_level_param, &params),
            );
        });
    }
    graph.levels(node).level_correct
}

/// `checkLevel`.
fn check_level(graph: &mut Graph, node: NodeId, iteration: u32, check: &mut LevelCheck) -> bool {
    let levels = graph.levels(node);
    let (level_checked, level_correct) = (levels.level_checked, levels.level_correct);
    match graph.kind(node) {
        NodeKind::Module(_) => check_module_levels(graph, node, check),
        NodeKind::OpAppl(_) => check_application(graph, node, iteration, check),
        NodeKind::OpDef(_) => check_definition(graph, node, iteration, check),
        NodeKind::ThmOrAssumpDef(_) => check_theorem_definition(graph, node, iteration, check),
        NodeKind::FormalParam(_) => {
            if level_checked != 0 {
                return true;
            }
            let levels = graph.levels_mut(node);
            levels.level_checked = iteration;
            levels.level_params.insert(node, ());
            levels.all_params.insert(node, ());
            true
        }
        NodeKind::OpDecl(_) => true,
        NodeKind::Numeral { .. } | NodeKind::String { .. } | NodeKind::Decimal(_) => {
            if level_checked < iteration {
                graph.levels_mut(node).level_checked = iteration;
            }
            true
        }
        &NodeKind::OpArg { op: operator, .. } => {
            if level_checked >= iteration {
                return level_correct;
            }
            graph.levels_mut(node).level_checked = iteration;
            let is_correct = check_level(graph, operator, iteration, check);
            graph.levels_mut(node).level_correct = is_correct;
            if matches!(graph.kind(operator), NodeKind::Module(_)) {
                return is_correct;
            }
            graph.levels_mut(node).level = graph.levels(operator).level;
            share_levels(graph, node, operator);
            is_correct
        }
        NodeKind::LetIn(let_in) => {
            if level_checked >= iteration {
                return level_correct;
            }
            let body = let_in.body;
            let instances = let_in.instances.clone();
            let definitions: Vec<NodeId> = let_in
                .op_defs
                .iter()
                .copied()
                .filter(|&definition| {
                    !matches!(graph.kind(definition),
                        NodeKind::OpDef(definition) if definition.def_kind == DefKind::ModuleInstance)
                })
                .collect();
            let levels = graph.levels_mut(node);
            levels.level_checked = iteration;
            levels.level_correct = true;
            for &definition in &definitions {
                if !check_level(graph, definition, iteration, check) {
                    graph.levels_mut(node).level_correct = false;
                }
            }
            if !check_level(graph, body, iteration, check) {
                graph.levels_mut(node).level_correct = false;
            }
            for &instance in &instances {
                if !check_level(graph, instance, iteration, check) {
                    graph.levels_mut(node).level_correct = false;
                }
            }
            update_levels(graph, node, body, |node, body| {
                node.level = body.level;
                node.level_params = body.level_params.clone();
                node.all_params = body.all_params.clone();
                put_level_constraints(&mut node.level_constraints, &body.level_constraints, |_| {
                    true
                });
            });
            for &definition in &definitions {
                update_levels(graph, node, definition, |node, definition| {
                    put_level_constraints(
                        &mut node.level_constraints,
                        &definition.level_constraints,
                        |_| true,
                    );
                });
            }
            update_levels(graph, node, body, |node, body| {
                put_arg_level_constraints(
                    &mut node.arg_level_constraints,
                    &body.arg_level_constraints,
                    |_| true,
                );
            });
            for &definition in &definitions {
                update_levels(graph, node, definition, |node, definition| {
                    put_arg_level_constraints(
                        &mut node.arg_level_constraints,
                        &definition.arg_level_constraints,
                        |_| true,
                    );
                });
            }
            update_levels(graph, node, body, |node, body| {
                add_arg_level_params(&mut node.arg_level_params, &body.arg_level_params, |_| true);
            });
            for &definition in &definitions {
                let params = graph
                    .op_def(definition)
                    .and_then(|definition| definition.params.clone())
                    .unwrap_or_default();
                update_levels(graph, node, definition, |node, definition| {
                    add_arg_level_params(
                        &mut node.arg_level_params,
                        &definition.arg_level_params,
                        |arg_level_param| !is_occurring(arg_level_param, &params),
                    );
                });
            }
            for &instance in &instances {
                update_levels(graph, node, instance, |node, instance| {
                    add_arg_level_params(
                        &mut node.arg_level_params,
                        &instance.arg_level_params,
                        |_| true,
                    );
                });
            }
            graph.levels(node).level_correct
        }
        NodeKind::Label(label) => {
            if level_checked >= iteration {
                return true;
            }
            let (params, body) = (label.params.clone(), label.body);
            graph.levels_mut(node).level_checked = iteration;
            for param in params {
                check_level(graph, param, iteration, check);
            }
            let is_correct = check_level(graph, body, iteration, check);
            graph.levels_mut(node).level = graph.levels(body).level;
            share_levels(graph, node, body);
            is_correct
        }
        &NodeKind::At {
            except, component, ..
        } => {
            if level_checked >= iteration {
                return true;
            }
            graph.levels_mut(node).level_checked = iteration;
            let args = get_op_appl(graph, except).operands.clone();
            let Some(Some(first)) = args.first().copied() else {
                return true;
            };
            check_level(graph, first, iteration, check);
            graph.levels_mut(node).level = graph.levels(first).level;
            let mut parts = vec![first];
            for argument in args.into_iter().skip(1).flatten() {
                check_level(graph, argument, iteration, check);
                if argument == component {
                    break;
                }
                let level = graph.levels(node).level.max(graph.levels(argument).level);
                graph.levels_mut(node).level = level;
                parts.push(argument);
            }
            for part in parts {
                update_levels(graph, node, part, merge_levels);
            }
            true
        }
        NodeKind::SubstIn(subst_in) => {
            if level_checked >= iteration {
                return level_correct;
            }
            let (body, substs, is_assume_prove, instantiated_module) = (
                subst_in.body,
                subst_in.substs.clone(),
                subst_in.is_assume_prove,
                subst_in.instantiated_module,
            );
            let levels = graph.levels_mut(node);
            levels.level_checked = iteration;
            levels.level_correct = true;
            if !check_level(graph, body, iteration, check) {
                graph.levels_mut(node).level_correct = false;
            }
            for subst in &substs {
                if !check_level(graph, subst.expr, iteration, check) {
                    graph.levels_mut(node).level_correct = false;
                }
            }
            let body_levels = graph.levels(body);
            let level = substs.iter().fold(body_levels.level, |level, subst| {
                if body_levels.level_params.contains_key(&subst.op) {
                    level.max(graph.levels(subst.expr).level)
                } else {
                    level
                }
            });
            let mut level_params = graph.levels(node).level_params.clone();
            for &param in body_levels.level_params.keys() {
                add_all(
                    &mut level_params,
                    &get_substituted_params(graph, param, &substs, false),
                );
            }
            let (all_params, non_leibniz_params) = if is_assume_prove {
                let mut all_params = graph.levels(node).all_params.clone();
                for &param in body_levels.all_params.keys() {
                    add_all(
                        &mut all_params,
                        &get_substituted_params(graph, param, &substs, true),
                    );
                }
                (all_params, graph.levels(node).non_leibniz_params.clone())
            } else {
                let mut all_params = body_levels.all_params.clone();
                let mut non_leibniz_params = body_levels.non_leibniz_params.clone();
                for subst in &substs {
                    if all_params.remove(&subst.op).is_none() {
                        continue;
                    }
                    let expr = graph.levels(subst.expr);
                    add_all(&mut all_params, &expr.all_params);
                    add_all(&mut non_leibniz_params, &expr.non_leibniz_params);
                    if non_leibniz_params.remove(&subst.op).is_some() {
                        add_all(&mut non_leibniz_params, &expr.all_params);
                    }
                }
                (all_params, non_leibniz_params)
            };
            let levels = graph.levels_mut(node);
            levels.level = level;
            levels.level_params = level_params;
            levels.all_params = all_params;
            levels.non_leibniz_params = non_leibniz_params;
            let is_constant = is_constant_module(graph, instantiated_module, check);
            let level_constraints = get_substituted_level_constraints(
                graph,
                body,
                &substs,
                is_constant,
                iteration,
                check,
            );
            graph.levels_mut(node).level_constraints = level_constraints;
            let arg_level_constraints =
                get_substituted_arg_level_constraints(graph, body, &substs, iteration, check);
            graph.levels_mut(node).arg_level_constraints = arg_level_constraints;
            let arg_level_params = get_substituted_arg_level_params(
                graph,
                &graph.levels(body).arg_level_params,
                &substs,
            );
            graph.levels_mut(node).arg_level_params = arg_level_params;
            graph.levels(node).level_correct
        }
        NodeKind::Instance(_) => check_instance(graph, node, iteration, check),
        &NodeKind::Assume {
            definition, body, ..
        } => {
            if level_checked >= iteration {
                return true;
            }
            graph.levels_mut(node).level_checked = iteration;
            let is_body_correct = check_level(graph, body, iteration, check);
            let is_definition_correct = definition
                .is_none_or(|definition| check_level(graph, definition, iteration, check));
            // AssumeNode's getters return its expression's levels.
            let level = graph.levels(body).level;
            graph.levels_mut(node).level = level;
            share_levels(graph, node, body);
            if level != CONSTANT_LEVEL {
                let location = graph.node(node).location().expect("a location").clone();
                add_error(
                    check,
                    &location,
                    format!(
                        "Level error: assumptions must be level 0 (Constant), \nbut this one has level {level}."
                    ),
                    None,
                );
            }
            is_body_correct && is_definition_correct
        }
        NodeKind::Theorem(theorem) => {
            // TheoremNode declares its own levelChecked, so levelCheckSubnodes still runs on the
            // theorem's definition, or its statement when it has none, and its proof.
            if level_checked >= iteration {
                return true;
            }
            let (body, proof) = (theorem.body, theorem.proof);
            let subnodes: Vec<NodeId> = [theorem.definition.unwrap_or(body)]
                .into_iter()
                .chain(proof)
                .collect();
            let is_correct = check_subnodes(graph, node, &subnodes, iteration, check);
            let body_level = graph.levels(body).level;
            if let NodeKind::OpAppl(appl) = graph.kind(body)
                && get_name(graph, appl.operator) == "$Pick"
                && body_level == TEMPORAL_LEVEL
            {
                for &range in &appl.ranges {
                    if graph.levels(range).level == CONSTANT_LEVEL {
                        continue;
                    }
                    let location = graph.node(range).location().expect("a location");
                    add_error(
                        check,
                        location,
                        "Non-constant bound of temporal PICK.".to_owned(),
                        None,
                    );
                }
            }
            if body_level == TEMPORAL_LEVEL {
                check_temporal_proof(graph, proof, check);
            }
            is_correct
        }
        NodeKind::LeafProof(proof) => {
            let facts = proof.facts.clone();
            check_subnodes(graph, node, &facts, iteration, check)
        }
        NodeKind::UseOrHide(use_or_hide) => {
            let facts = use_or_hide.facts.clone();
            check_subnodes(graph, node, &facts, iteration, check)
        }
        NodeKind::NonLeafProof(proof) => {
            let subnodes: Vec<NodeId> = proof
                .steps
                .iter()
                .chain(&proof.instances)
                .copied()
                .collect();
            check_subnodes(graph, node, &subnodes, iteration, check)
        }
        NodeKind::DefStep { defs, .. } => {
            let defs = defs.clone();
            check_subnodes(graph, node, &defs, iteration, check)
        }
        &NodeKind::NewSymb {
            declaration,
            set,
            ref location,
        } => {
            if level_checked >= iteration {
                return level_correct;
            }
            let location = location.clone();
            let level = graph.levels(declaration).level;
            let levels = graph.levels_mut(node);
            levels.level_checked = iteration;
            levels.level = level;
            let Some(set) = set else {
                return graph.levels(node).level_correct;
            };
            let is_correct = check_level(graph, set, iteration, check);
            let level = graph.levels(node).level.max(graph.levels(set).level);
            let levels = graph.levels_mut(node);
            levels.level_correct = is_correct;
            levels.level = level;
            if level == TEMPORAL_LEVEL {
                levels.level_correct = false;
                add_error(
                    check,
                    &location,
                    "Level error:\nTemporal formula used as set.".to_owned(),
                    None,
                );
            }
            share_levels(graph, node, set);
            graph.levels(node).level_correct
        }
        NodeKind::AssumeProve(assume_prove) => {
            if level_checked >= iteration {
                return level_correct;
            }
            let (assumptions, goal) = (assume_prove.assumptions.clone(), assume_prove.goal);
            let levels = graph.levels_mut(node);
            levels.level_checked = iteration;
            levels.level_correct = true;
            for &assumption in &assumptions {
                if !check_level(graph, assumption, iteration, check) {
                    graph.levels_mut(node).level_correct = false;
                }
            }
            check_level(graph, goal, iteration, check);
            let level = assumptions
                .iter()
                .fold(graph.levels(goal).level, |level, &assumption| {
                    level.max(graph.levels(assumption).level)
                });
            graph.levels_mut(node).level = level;
            for part in [goal].into_iter().chain(assumptions) {
                update_levels(graph, node, part, merge_levels);
            }
            // LevelNode.addTemporalLevelConstraintToConstants.
            if graph.levels(node).level_correct {
                let constants: Vec<NodeId> = graph
                    .levels(node)
                    .level_params
                    .keys()
                    .copied()
                    .filter(|&param| {
                        matches!(graph.kind(param),
                            NodeKind::OpDecl(declaration) if declaration.decl_kind == CONSTANT_DECL_KIND)
                    })
                    .collect();
                for param in constants {
                    put_level_constraint(
                        &mut graph.levels_mut(node).level_constraints,
                        param,
                        ACTION_LEVEL,
                    );
                }
            }
            graph.levels(node).level_correct
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;
    use crate::sany::nodes::{Context, FormalParam, Module, OpDecl, OpDef};

    fn get_location() -> SanyLocation {
        SanyLocation {
            file: Rc::from("M"),
            begin_line: 1,
            begin_column: 1,
            end_line: 1,
            end_column: 5,
        }
    }

    fn create_op_def(name: &str, params: Vec<NodeId>, body: Option<NodeId>) -> OpDef {
        OpDef {
            def_kind: DefKind::UserDefined,
            name: Rc::from(name),
            arity: params.len(),
            params: Some(params),
            body,
            is_local: false,
            location: get_location(),
            module: None,
            source: None,
            pre_comments: Vec::new(),
            is_defined: true,
            in_recursive: false,
            in_recursive_section: false,
            recursive_section: -1,
            let_in_level: 0,
            weights: Vec::new(),
            is_leibniz_arg: None,
            is_leibniz: true,
            op_level_cond: None,
            max_levels: Vec::new(),
            min_max_level: None,
            labels: OrderedMap::new(),
            step: None,
        }
    }

    /// A builtin of one argument, as `createBuiltins` makes it, with its level and the maximum
    /// level of its argument, whose weight is 0.
    fn add_builtin(graph: &mut Graph, name: &str, level: u8, max_level: u8) -> NodeId {
        let param = graph.add(
            0,
            NodeKind::FormalParam(FormalParam {
                name: Rc::from("Formal_0"),
                arity: 0,
                location: None,
            }),
        );
        let mut definition = create_op_def(name, vec![param], None);
        definition.def_kind = DefKind::BuiltIn;
        definition.max_levels = vec![max_level];
        definition.weights = vec![0];
        definition.is_leibniz_arg = Some(vec![false]);
        definition.is_leibniz = false;
        let builtin = graph.add(0, NodeKind::OpDef(Box::new(definition)));
        let levels = graph.levels_mut(builtin);
        levels.level_checked = 99;
        levels.level = level;
        builtin
    }

    fn add_op_appl(graph: &mut Graph, operator: NodeId, operand: NodeId) -> NodeId {
        graph.add(
            0,
            NodeKind::OpAppl(OpAppl {
                operator,
                operands: vec![Some(operand)],
                unbounded: None,
                bounded: None,
                tuple_ors: None,
                ranges: Vec::new(),
                location: get_location(),
                is_null: false,
                is_absent: false,
            }),
        )
    }

    /// Checks the module `M` with `VARIABLE v` and `A == wrap(v')`.
    fn check_primed_definition(
        wrap: impl FnOnce(&mut Graph, NodeId) -> NodeId,
    ) -> (Graph, NodeId, NodeId, Vec<SanyMessage>) {
        let mut graph = Graph::default();
        let prime = add_builtin(&mut graph, "'", ACTION_LEVEL, VARIABLE_LEVEL);
        let module = graph.add(
            0,
            NodeKind::Module(Box::new(Module {
                name: Rc::from("M"),
                location: get_location(),
                extendees: Vec::new(),
                context: Context::default(),
                top_level: Vec::new(),
                definitions: Vec::new(),
                op_defs_in_recursive_section: Vec::new(),
                is_level_checked: false,
                records: Vec::new(),
            })),
        );
        let variable = graph.add(
            0,
            NodeKind::OpDecl(OpDecl {
                name: Rc::from("v"),
                arity: 0,
                decl_kind: VARIABLE_DECL_KIND,
                location: get_location(),
                module,
            }),
        );
        let levels = graph.levels_mut(variable);
        levels.level_checked = 1;
        levels.level = VARIABLE_LEVEL;
        let primed = add_op_appl(&mut graph, prime, variable);
        let body = wrap(&mut graph, primed);
        let definition = graph.add(
            0,
            NodeKind::OpDef(Box::new(create_op_def("A", Vec::new(), Some(body)))),
        );
        graph.add_to_module_context(module, variable);
        graph.add_to_module_context(module, definition);
        let mut messages = Vec::new();
        let check = &mut LevelCheck {
            messages: &mut messages,
        };
        check_module_levels(&mut graph, module, check);
        (graph, module, definition, messages)
    }

    #[test]
    fn primed_variable_is_an_action() {
        let (graph, module, definition, messages) = check_primed_definition(|_, primed| primed);
        assert!(messages.is_empty());
        assert!(graph.levels(module).level_correct);
        assert_eq!(graph.levels(definition).level, ACTION_LEVEL);
        assert_eq!(graph.levels(definition).level_checked, 1);
    }

    #[test]
    fn box_of_an_action_needs_a_subscript() {
        let (graph, module, definition, messages) = check_primed_definition(|graph, primed| {
            let always = add_builtin(graph, "[]", TEMPORAL_LEVEL, TEMPORAL_LEVEL);
            add_op_appl(graph, always, primed)
        });
        let texts: Vec<&str> = messages
            .iter()
            .map(|message| message.text.as_str())
            .collect();
        assert_eq!(texts, ["[] followed by action not of form [A]_v."]);
        assert!(!graph.levels(module).level_correct);
        assert_eq!(graph.levels(definition).level, TEMPORAL_LEVEL);
    }
}
