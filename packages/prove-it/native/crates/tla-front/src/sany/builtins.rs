//! A port of `src/sany/builtins.ts`: SANY's builtin operators, `tla2sany.semantic.BuiltInOperators`.

use std::rc::Rc;

use crate::ordered_map::OrderedMap;
use crate::sany::nodes::{DefKind, FormalParam, Graph, NodeId, NodeKind, OpDef, SanyLocation};

/// A builtin operator's name, arity, level, maximum argument levels and argument weights. SANY
/// leaves the levels of "." and \neg unset.
type BuiltinOperator = (
    &'static str,
    i32,
    u8,
    Option<&'static [u8]>,
    Option<&'static [u8]>,
);

const BUILTIN_OPERATORS: &[BuiltinOperator] = &[
    ("STRING", 0, 0, Some(&[]), Some(&[])),
    ("FALSE", 0, 0, Some(&[]), Some(&[])),
    ("TRUE", 0, 0, Some(&[]), Some(&[])),
    ("BOOLEAN", 0, 0, Some(&[]), Some(&[])),
    ("=", 2, 0, Some(&[2, 2]), Some(&[1, 1])),
    ("/=", 2, 0, Some(&[2, 2]), Some(&[1, 1])),
    (".", 2, 0, None, None),
    ("'", 1, 2, Some(&[1]), Some(&[0])),
    ("\\lnot", 1, 0, Some(&[3]), Some(&[1])),
    ("\\neg", 1, 0, None, None),
    ("\\land", 2, 0, Some(&[3, 3]), Some(&[1, 1])),
    ("\\lor", 2, 0, Some(&[3, 3]), Some(&[1, 1])),
    ("\\equiv", 2, 0, Some(&[3, 3]), Some(&[1, 1])),
    ("=>", 2, 0, Some(&[3, 3]), Some(&[1, 1])),
    ("SUBSET", 1, 0, Some(&[2]), Some(&[1])),
    ("UNION", 1, 0, Some(&[2]), Some(&[1])),
    ("DOMAIN", 1, 0, Some(&[2]), Some(&[1])),
    ("\\subseteq", 2, 0, Some(&[2, 2]), Some(&[1, 1])),
    ("\\in", 2, 0, Some(&[2, 2]), Some(&[1, 1])),
    ("\\notin", 2, 0, Some(&[2, 2]), Some(&[1, 1])),
    ("\\", 2, 0, Some(&[2, 2]), Some(&[1, 1])),
    ("\\intersect", 2, 0, Some(&[2, 2]), Some(&[1, 1])),
    ("\\union", 2, 0, Some(&[2, 2]), Some(&[1, 1])),
    ("\\times", 2, 0, Some(&[2, 2]), Some(&[1, 1])),
    ("~>", 2, 3, Some(&[3, 3]), Some(&[0, 0])),
    ("[]", 1, 3, Some(&[3]), Some(&[0])),
    ("<>", 1, 3, Some(&[3]), Some(&[0])),
    ("ENABLED", 1, 1, Some(&[2]), Some(&[0])),
    ("UNCHANGED", 1, 2, Some(&[1]), Some(&[0])),
    ("\\cdot", 2, 2, Some(&[2, 2]), Some(&[0, 0])),
    ("-+->", 2, 3, Some(&[3, 3]), Some(&[0, 0])),
    ("$AngleAct", 2, 2, Some(&[2, 1]), Some(&[0, 0])),
    ("$BoundedChoose", -1, 0, Some(&[2]), Some(&[1])),
    ("$BoundedExists", -1, 0, Some(&[3]), Some(&[1])),
    ("$BoundedForall", -1, 0, Some(&[3]), Some(&[1])),
    ("$CartesianProd", -1, 0, Some(&[2]), Some(&[1])),
    ("$Case", -1, 0, Some(&[3]), Some(&[1])),
    ("$ConjList", -1, 0, Some(&[3]), Some(&[1])),
    ("$DisjList", -1, 0, Some(&[3]), Some(&[1])),
    ("$Except", -1, 0, Some(&[2]), Some(&[1])),
    ("$FcnApply", 2, 0, Some(&[2, 2]), Some(&[1, 1])),
    ("$FcnConstructor", -1, 0, Some(&[3]), Some(&[1])),
    ("$IfThenElse", 3, 0, Some(&[3, 3, 3]), Some(&[1, 1, 1])),
    ("$NonRecursiveFcnSpec", 1, 0, Some(&[3]), Some(&[1])),
    ("$Pair", 2, 0, Some(&[3, 3]), Some(&[1, 1])),
    ("$RcdConstructor", -1, 0, Some(&[3]), Some(&[1])),
    ("$RcdSelect", 2, 0, Some(&[2, 0]), Some(&[1, 1])),
    ("$RecursiveFcnSpec", 1, 0, Some(&[3]), Some(&[1])),
    ("$Seq", -1, 0, Some(&[2]), Some(&[1])),
    ("$SetEnumerate", -1, 0, Some(&[2]), Some(&[1])),
    ("$SetOfAll", -1, 0, Some(&[2]), Some(&[1])),
    ("$SetOfFcns", -1, 0, Some(&[2]), Some(&[1])),
    ("$SetOfRcds", -1, 0, Some(&[2]), Some(&[1])),
    ("$SF", 2, 3, Some(&[1, 2]), Some(&[0, 0])),
    ("$SquareAct", 2, 2, Some(&[2, 1]), Some(&[0, 0])),
    ("$SubsetOf", 1, 0, Some(&[2]), Some(&[1])),
    ("$TemporalExists", 1, 3, Some(&[3]), Some(&[0])),
    ("$TemporalForall", 1, 3, Some(&[3]), Some(&[0])),
    ("$TemporalWhile", 2, 3, Some(&[3, 3]), Some(&[0, 0])),
    ("$Tuple", -1, 0, Some(&[2]), Some(&[1])),
    ("$UnboundedChoose", 1, 0, Some(&[2]), Some(&[1])),
    ("$UnboundedExists", 1, 0, Some(&[3]), Some(&[1])),
    ("$UnboundedForall", 1, 0, Some(&[3]), Some(&[1])),
    ("$WF", 2, 3, Some(&[1, 2]), Some(&[0, 0])),
    ("$Nop", 1, 0, Some(&[3]), Some(&[1])),
    ("$Qed", 0, 0, Some(&[]), Some(&[])),
    ("$Pfcase", 1, 0, Some(&[3]), Some(&[1])),
    ("$Have", 1, 0, Some(&[3]), Some(&[1])),
    ("$Take", 1, 0, Some(&[3]), Some(&[1])),
    ("$Pick", 1, 0, Some(&[3]), Some(&[1])),
    ("$Witness", -1, 0, Some(&[2]), Some(&[1])),
    ("$Suffices", 1, 0, Some(&[3]), Some(&[1])),
];

/// The name of the module of `BUILTIN_LOCATION`.
pub const BUILTIN_FILE: &str = "--TLA+ BUILTINS--";

/// `BUILTIN_LOCATION`.
pub fn get_builtin_location() -> SanyLocation {
    SanyLocation {
        file: Rc::from(BUILTIN_FILE),
        begin_line: 0,
        begin_column: 0,
        end_line: 0,
        end_column: 0,
    }
}

/// `createBuiltins`: the builtin operators in the order SANY adds them to its global context.
/// OpDefNode's constructor for a builtin numbers the operator, then its phony parameters. A
/// builtin of arity -1, which takes any number of arguments, has no `params` and arity 0.
pub fn create_builtins(graph: &mut Graph, get_uid: &mut impl FnMut() -> u32) -> Vec<NodeId> {
    BUILTIN_OPERATORS
        .iter()
        .map(|&(name, arity, level, max_levels, weights)| {
            let uid = get_uid();
            let params = usize::try_from(arity).ok().map(|arity| {
                (0..arity)
                    .map(|index| {
                        let uid = get_uid();
                        graph.add(
                            uid,
                            NodeKind::FormalParam(FormalParam {
                                name: Rc::from(format!("Formal_{index}")),
                                arity: 0,
                                location: None,
                            }),
                        )
                    })
                    .collect()
            });
            let is_level_set = max_levels.is_some() && weights.is_some();
            let is_leibniz_arg: Option<Vec<bool>> =
                weights.map(|weights| weights.iter().map(|&weight| weight > 0).collect());
            let get_prefix = |values: Option<&[u8]>| {
                let values = values.unwrap_or_default();
                if arity < 0 {
                    values[..values.len().min(1)].to_vec()
                } else {
                    values.to_vec()
                }
            };
            let id = graph.add(
                uid,
                NodeKind::OpDef(Box::new(OpDef {
                    def_kind: DefKind::BuiltIn,
                    name: Rc::from(name),
                    arity: usize::try_from(arity).unwrap_or(0),
                    params,
                    body: None,
                    is_local: false,
                    location: get_builtin_location(),
                    module: None,
                    source: None,
                    pre_comments: Vec::new(),
                    is_defined: true,
                    in_recursive: false,
                    in_recursive_section: false,
                    recursive_section: -1,
                    let_in_level: 0,
                    weights: get_prefix(weights),
                    is_leibniz: is_leibniz_arg
                        .as_ref()
                        .is_none_or(|arguments| arguments.iter().all(|&argument| argument)),
                    is_leibniz_arg: is_leibniz_arg.filter(|_| is_level_set),
                    op_level_cond: None,
                    max_levels: get_prefix(max_levels),
                    min_max_level: None,
                    labels: OrderedMap::new(),
                    step: None,
                })),
            );
            let levels = graph.levels_mut(id);
            levels.level_checked = if is_level_set { 99 } else { 0 };
            levels.level = level;
            id
        })
        .collect()
}
