//! The builtins, as `compileBuiltin` and `compileNativeBuiltin` compile them. The pure builtins
//! the TypeScript engine runs in the interpreter (`PURE_BUILTINS`) are `bridged.rs`'s, except
//! ToString, which prints as the interpreter's printer does (`format_value`).

use std::sync::Arc;

use tla_ir::{Builtin, Index, NodeKind};
use tla_values::print::{is_printable, write_value};
use tla_values::store::{
    EMPTY_SET, EMPTY_TUPLE, FALSE, KIND_INT, KIND_SET, KIND_STRING, KIND_TUPLE, Outcome, TRUE,
    is_function_kind,
};
use tla_values::{Bail, Id};

use super::fused;
use super::lazy::{Lazy, Operator, Reference};
use super::nodes::{evaluate_set, expect_set};
use super::predicate::{Leaf, Predicate};
use super::sets::not_in;
use super::{
    Binding, Compiled, Compiler, Compiling, Context, DISTINCT_SLOT, LEVEL_SLOT, NEXT_LEVEL_SLOT,
    Operand, OperatorBody, Shape, bind, bool_id, combine_references, decline, eval, leaf, lookup,
    member, operator_context, predicate_node, reference_of, unsupported,
};
use crate::footprint::Footprint;
use crate::machine::{Eval, Machine, Printed};

// Operators whose results depend on more than their arguments, or that print.
const IMPURE_BUILTINS: [&str; 8] = [
    "Print",
    "PrintT",
    "JavaTime",
    "TLCGet",
    "TLCSet",
    "RandomElement",
    "TLCEval",
    "Any",
];

// The builtins the TypeScript engine runs in the reference interpreter.
const PURE_BUILTINS: [&str; 19] = [
    "SubSeq",
    "SelectSeq",
    "IsFiniteSet",
    "Permutations",
    "SortSeq",
    "ToString",
    "EmptyBag",
    "IsABag",
    "BagCardinality",
    "BagIn",
    "CopiesIn",
    "\\oplus",
    "\\ominus",
    "BagUnion",
    "\\sqsubseteq",
    "BagOfAll",
    "SubBag",
    "BagToSet",
    "SetToBag",
];

const MAXIMUM_POWER_SET: u32 = 20;

fn expect_int(machine: &Machine<'_>, id: Id) -> Outcome<i64> {
    if machine.store.kind_of(id) == KIND_INT {
        Ok(i64::from(machine.store.int_of(id)))
    } else {
        Err(Bail("expected an integer"))
    }
}

fn expect_sequence(machine: &Machine<'_>, id: Id) -> Outcome<Id> {
    if machine.store.kind_of(id) == KIND_TUPLE {
        Ok(id)
    } else {
        Err(Bail("expected a sequence"))
    }
}

type Binary = fn(&mut Machine<'_>, Id, Id) -> Outcome<Id>;
type Unary = fn(&mut Machine<'_>, Id) -> Outcome<Id>;

fn binary(
    left: &Compiled,
    right: &Compiled,
    operation: Binary,
    is_costly: bool,
    is_boolean: bool,
) -> Compiled {
    let (left_eval, right_eval) = (left.eval.clone(), right.eval.clone());
    Compiled {
        is_costly,
        is_boolean,
        ..leaf(
            eval(move |machine| {
                let left = left_eval(machine)?;
                let right = right_eval(machine)?;
                operation(machine, left, right)
            }),
            left.footprint.merge(&right.footprint),
        )
    }
}

fn unary(operand: &Compiled, operation: Unary, is_costly: bool) -> Compiled {
    let evaluate = operand.eval.clone();
    Compiled {
        is_costly,
        ..leaf(
            eval(move |machine| {
                let value = evaluate(machine)?;
                operation(machine, value)
            }),
            operand.footprint.clone(),
        )
    }
}

fn arithmetic(
    left: &Compiled,
    right: &Compiled,
    operation: fn(i64, i64) -> Outcome<i64>,
) -> Compiled {
    let (left_eval, right_eval) = (left.eval.clone(), right.eval.clone());
    leaf(
        eval(move |machine| {
            let left = left_eval(machine)?;
            let right = right_eval(machine)?;
            let left = expect_int(machine, left)?;
            let right = expect_int(machine, right)?;
            machine.store.int(operation(left, right)?)
        }),
        left.footprint.merge(&right.footprint),
    )
}

fn comparison(left: &Compiled, right: &Compiled, operation: fn(i64, i64) -> bool) -> Compiled {
    let (left_eval, right_eval) = (left.eval.clone(), right.eval.clone());
    Compiled {
        is_boolean: true,
        ..leaf(
            eval(move |machine| {
                let left = left_eval(machine)?;
                let right = right_eval(machine)?;
                let left = expect_int(machine, left)?;
                let right = expect_int(machine, right)?;
                Ok(bool_id(operation(left, right)))
            }),
            left.footprint.merge(&right.footprint),
        )
    }
}

fn power_set(machine: &mut Machine<'_>, set: Id) -> Outcome<Id> {
    let size = machine.store.size_of(set);
    if size > MAXIMUM_POWER_SET {
        return Err(Bail("a power set too large to build"));
    }
    let elements = machine.store.set_elements(set).to_vec();
    let mut subsets = Vec::with_capacity(1 << size);
    for mask in 0..1u32 << size {
        let subset: Vec<Id> = (0..size)
            .filter(|index| mask & (1 << index) != 0)
            .map(|index| elements[index as usize])
            .collect();
        subsets.push(machine.store.set_of_sorted(&subset));
    }
    machine.store.set_of(&subsets)
}

/// An operator argument compiled once, with its parameters bound to slots, to apply to ids.
pub(crate) struct Applier {
    pub(crate) slots: Vec<u32>,
    pub(crate) body: Eval,
    pub(crate) footprint: Footprint,
    /// Whether its body is a number or string literal.
    pub(crate) is_literal: bool,
}

impl Compiler<'_> {
    pub(crate) fn compile_nullary_builtin(&mut self, index: Index) -> Compiling<Compiled> {
        let builtin = &self.ir.builtins[index as usize];
        let name = self.text(builtin.name);
        if builtin.flags & Builtin::STATE_LEVEL != 0 || IMPURE_BUILTINS.contains(&name) {
            return unsupported(name);
        }
        Ok(match name {
            "TRUE" => super::constant(TRUE),
            "FALSE" => super::constant(FALSE),
            "BOOLEAN" => super::constant(self.store.set_of(&[FALSE, TRUE])?),
            "Nat" => Self::infinite_set("Nat", "enumerated Nat"),
            "Int" => Self::infinite_set("Int", "enumerated Int"),
            "STRING" => Self::infinite_set("STRING", "enumerated STRING"),
            "EmptyBag" => super::constant(EMPTY_TUPLE),
            name => {
                return decline(format!(
                    "the builtin {name}, whose value the interpreter computes"
                ));
            }
        })
    }

    // Nat, Int and STRING, which the engine only tests for membership.
    fn infinite_set(name: &'static str, reason: &'static str) -> Compiled {
        Compiled {
            is_normalized: false,
            infinite: Some(name),
            reference: Some(Arc::new(move |_| Ok(Lazy::Infinite(name)))),
            ..leaf(eval(move |_| Err(Bail(reason))), Footprint::default())
        }
    }

    pub(crate) fn operand(&mut self, operand: &Operand) -> Compiling<Compiled> {
        match operand.slot {
            Some(slot) => Ok(self.read_slot(slot)),
            None => self.compile(operand.node, &operand.context),
        }
    }

    fn boolean_operand(&mut self, operand: &Operand) -> Compiling<Compiled> {
        match operand.slot {
            Some(slot) => Ok(Self::as_boolean(self.read_slot(slot))),
            None => self.compile_boolean(operand.node, &operand.context),
        }
    }

    pub(crate) fn compile_builtin(
        &mut self,
        index: Index,
        operands: &[Operand],
        context: &Context,
    ) -> Compiling<Compiled> {
        let builtin = &self.ir.builtins[index as usize];
        let name = self.text(builtin.name);
        if name == "Print" || name == "PrintT" {
            return self.compile_print(name, operands, context);
        }
        if name == "TLCGet" {
            return self.compile_tlc_get(operands, context);
        }
        if builtin.flags & Builtin::STATE_LEVEL != 0 || IMPURE_BUILTINS.contains(&name) {
            if name == "TLCEval" && operands.len() == 1 {
                return self.operand(&operands[0]);
            }
            return unsupported(name);
        }
        if let Some(native) = self.compile_native_builtin(name, operands, context)? {
            return Ok(native);
        }
        if !PURE_BUILTINS.contains(&name) {
            return unsupported(name);
        }
        if let Some(bridged) = self.compile_bridged(name, operands, context)? {
            return Ok(bridged);
        }
        decline(format!(
            "the builtin {name}, which the TypeScript engine runs in the interpreter"
        ))
    }

    // Print(a, b) and PrintT(a) print as TLC does where the engine evaluates them as TLC does, and
    // only a value whose text doesn't depend on how it was built, which the engine forgets. The
    // search hands what they print to the interpreter's printer once it completes the initial
    // states or an expansion, and drops it if it hands over.
    fn compile_print(
        &mut self,
        name: &str,
        operands: &[Operand],
        context: &Context,
    ) -> Compiling<Compiled> {
        if !context.can_print {
            return unsupported(name);
        }
        let is_print = name == "Print";
        if operands.len() != if is_print { 2 } else { 1 } {
            return unsupported("an operator applied to the wrong number of arguments");
        }
        self.is_printing = true;
        let compiled = operands
            .iter()
            .map(|operand| self.compile(operand.node, &operand.context.without_print()))
            .collect::<Compiling<Vec<Compiled>>>()?;
        let footprint = Footprint::merge_all(compiled.iter().map(|operand| &operand.footprint))
            .merge(&Footprint::slot(super::PRINT_SLOT));
        let is_boolean = !is_print || compiled[1].is_boolean;
        let evaluators: Vec<Eval> = compiled.into_iter().map(|operand| operand.eval).collect();
        Ok(Compiled {
            is_boolean,
            ..leaf(
                eval(move |machine| {
                    let mut values = Vec::with_capacity(evaluators.len());
                    for evaluate in &evaluators {
                        values.push(evaluate(machine)?);
                    }
                    for &value in &values {
                        if !is_printable(&machine.store, value) {
                            return Err(Bail(
                                "printing a value whose text depends on how TLC built it",
                            ));
                        }
                    }
                    let result = if is_print { values[1] } else { TRUE };
                    machine.output.push(Printed::Values(values));
                    Ok(result)
                }),
                footprint,
            )
        })
    }

    // TLCGet("level") and TLCGet("distinct") read the slots the search sets.
    fn compile_tlc_get(&mut self, operands: &[Operand], context: &Context) -> Compiling<Compiled> {
        let key = match operands {
            [operand] if !operand.is_param => match self.node(operand.node).1 {
                NodeKind::String(text) => Some(self.text(*text)),
                _ => None,
            },
            _ => None,
        };
        if key != Some("level") && key != Some("distinct") {
            return unsupported("TLCGet");
        }
        if context.is_init && context.is_primed {
            return unsupported("TLCGet");
        }
        let slot = if key == Some("distinct") {
            self.is_distinct_read = true;
            DISTINCT_SLOT
        } else if context.is_primed {
            NEXT_LEVEL_SLOT
        } else {
            LEVEL_SLOT
        };
        Ok(Compiled {
            shape: Shape::Slot(slot),
            ..leaf(
                eval(move |machine| Ok(machine.locals[slot as usize])),
                Footprint::slot(slot),
            )
        })
    }

    // Whether an argument names or writes an operator, such as Test in SelectSeq(s, Test).
    pub(crate) fn is_operator_argument(&self, operand: &Operand) -> bool {
        if operand.is_param {
            return false;
        }
        match self.node(operand.node).1 {
            NodeKind::Lambda { .. } | NodeKind::OperatorReference(_) => true,
            NodeKind::Identifier(name) => {
                if let Some(found) = lookup(&operand.context.scope, name.text) {
                    return matches!(found.binding, Binding::Operator(_));
                }
                match name.resolution {
                    tla_ir::Resolution::Definition(index) => matches!(
                        &self.definition(self.ir.definitions[index as usize]).form,
                        tla_ir::DefinitionForm::Operator(params) if !params.is_empty()
                    ),
                    tla_ir::Resolution::Builtin(index) => {
                        self.ir.builtins[index as usize].arity > 0
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    pub(crate) fn compile_applier(
        &mut self,
        operand: &Operand,
        context: &Context,
    ) -> Compiling<Applier> {
        let operator =
            self.resolve_operator_argument(operand.node, &operand.context.without_print())?;
        if operator.params.iter().any(|param| param.arity > 0) {
            return unsupported("an operator argument that takes an operator");
        }
        let base = operator_context(&operator);
        let slots: Vec<u32> = operator
            .params
            .iter()
            .map(|_| self.allocate_slot())
            .collect();
        let mut scope = base.scope.clone();
        for (param, &slot) in operator.params.iter().zip(&slots) {
            scope = bind(&scope, param.name, Binding::Slot(slot));
        }
        let body_context = Context {
            scope,
            is_primed: context.is_primed || base.is_primed,
            ..base
        };
        let (body, is_literal) = match operator.body {
            OperatorBody::Node(body) => (
                self.compile(body, &body_context)?,
                matches!(self.node(body).1, NodeKind::Number(_) | NodeKind::String(_)),
            ),
            OperatorBody::Builtin(index) => {
                // The builtin applied to its parameters, as resolveOperatorArgument writes it.
                let operands: Vec<Operand> = slots
                    .iter()
                    .map(|&slot| Operand {
                        node: operand.node,
                        context: body_context.clone(),
                        is_param: true,
                        slot: Some(slot),
                    })
                    .collect();
                (
                    self.compile_builtin(index, &operands, &body_context)?,
                    false,
                )
            }
        };
        Ok(Applier {
            footprint: body.footprint.without_slots(&slots),
            slots,
            body: body.eval,
            is_literal,
        })
    }

    fn compile_native_builtin(
        &mut self,
        name: &str,
        operands: &[Operand],
        context: &Context,
    ) -> Compiling<Option<Compiled>> {
        let arity = |count: usize| -> Compiling<()> {
            if operands.len() < count {
                unsupported("an operator applied to the wrong number of arguments")
            } else {
                Ok(())
            }
        };
        Ok(Some(match name {
            "=" | "#" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                predicate_node(
                    Predicate::Equal {
                        left: Leaf::of(&left),
                        right: Leaf::of(&right),
                        is_equal: name == "=",
                    },
                    left.footprint.merge(&right.footprint),
                )
            }
            "~" => {
                arity(1)?;
                let negated = self.operand(&operands[0])?;
                predicate_node(
                    Predicate::Not(Box::new(Predicate::of(&negated))),
                    negated.footprint.clone(),
                )
            }
            "/\\" | "\\/" => {
                let compiled = operands
                    .iter()
                    .map(|operand| self.operand(operand))
                    .collect::<Compiling<Vec<_>>>()?;
                Self::junction(&compiled, name == "/\\")
            }
            "=>" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                predicate_node(
                    Predicate::Implies(
                        Box::new(Predicate::of(&left)),
                        Box::new(Predicate::of(&right)),
                    ),
                    left.footprint.merge(&right.footprint),
                )
            }
            "<=>" => {
                arity(2)?;
                let left = self.boolean_operand(&operands[0])?;
                let right = self.boolean_operand(&operands[1])?;
                binary(
                    &left,
                    &right,
                    |_, left, right| Ok(bool_id(left == right)),
                    false,
                    false,
                )
            }
            "\\in" | "\\notin" => {
                arity(2)?;
                let element = self.operand(&operands[0])?;
                let set = self.operand(&operands[1])?;
                let is_in = name == "\\in";
                let footprint = element.footprint.merge(&set.footprint);
                if set.member.is_none() && set.infinite.is_none() && set.footprint.width() == 0 {
                    return Ok(Some(predicate_node(
                        Predicate::Member {
                            element: Leaf::of(&element),
                            set: Leaf::of(&set),
                            is_in,
                        },
                        footprint,
                    )));
                }
                let evaluate = fused::member_const(&element, &set, is_in).unwrap_or_else(|| {
                    let test = self.member_test(&set);
                    let element = element.eval.clone();
                    eval(move |machine| {
                        let value = element(machine)?;
                        Ok(bool_id(test(machine, value)? == is_in))
                    })
                });
                // A miss in a set that isn't constant compares the element with the set's elements
                // as TLC's binary search does, to fail where it fails, so it is cached too.
                Compiled {
                    is_costly: set.member.is_some() || set.footprint.width() > 0,
                    is_boolean: true,
                    ..leaf(evaluate, footprint)
                }
            }
            "\\subseteq" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                let footprint = left.footprint.merge(&right.footprint);
                let left_eval = left.eval.clone();
                let evaluate = if right.member.is_some() || right.infinite.is_some() {
                    let test = self.member_test(&right);
                    eval(move |machine| {
                        let set = evaluate_set(machine, &left_eval, "expected a set")?;
                        for index in 0..machine.store.size_of(set) {
                            let element = machine.store.element_at(set, index);
                            if !test(machine, element)? {
                                return Ok(FALSE);
                            }
                        }
                        Ok(TRUE)
                    })
                } else {
                    let right_eval = right.eval.clone();
                    eval(move |machine| {
                        let left = evaluate_set(machine, &left_eval, "expected a set")?;
                        let right = evaluate_set(machine, &right_eval, "expected a set")?;
                        Ok(bool_id(machine.store.is_subset(left, right)?))
                    })
                };
                Compiled {
                    is_costly: true,
                    ..leaf(evaluate, footprint)
                }
            }
            "\\cup" | "\\cap" | "\\" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                return self.compile_set_operation(name, &left, &right);
            }
            "SUBSET" => {
                arity(1)?;
                let base = self.operand(&operands[0])?;
                let base_member = self.member_test(&base);
                let base_parts = Self::parts_of(&base);
                Compiled {
                    is_normalized: false,
                    reference: combine_references(&[&base], |_, mut bases| {
                        Ok(Lazy::Subset(Box::new(bases.remove(0))))
                    }),
                    parts: Some(base_parts.clone()),
                    member: Some(member(move |machine, element| {
                        machine.run_parts(&base_parts)?;
                        // TLC fails on anything it can't enumerate, untyped model values included.
                        if machine.store.kind_of(element) != KIND_SET {
                            return Err(Bail("a membership in SUBSET of a non-set"));
                        }
                        for index in 0..machine.store.size_of(element) {
                            let value = machine.store.element_at(element, index);
                            if !base_member(machine, value)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    })),
                    ..unary(
                        &base,
                        |machine, set| {
                            power_set(machine, expect_set(machine, set, "expected a set")?)
                        },
                        true,
                    )
                }
            }
            "UNION" => {
                arity(1)?;
                let only_node = match self.node(operands[0].node).1 {
                    NodeKind::SetEnumeration(elements)
                        if elements.len() == 1 && !operands[0].is_param =>
                    {
                        Some(elements[0])
                    }
                    _ => None,
                };
                // The one element of UNION {S}, compiled once for the set around it and for
                // membership.
                let single = only_node
                    .map(|node| self.compile(node, &operands[0].context))
                    .transpose()?;
                let outer = match &single {
                    Some(single) => {
                        let enumeration =
                            Self::compile_set_enumeration(std::slice::from_ref(single));
                        self.cached(enumeration)
                    }
                    None => self.operand(&operands[0])?,
                };
                let is_enumerated = outer.is_enumerated && outer.are_elements_enumerated;
                // TLC tests membership in UNION {S} as membership in S.
                let only = if is_enumerated { None } else { single };
                let only = only.filter(|only| only.member.is_some() || only.infinite.is_some());
                let compiled = unary(
                    &outer,
                    |machine, sets| {
                        let sets = expect_set(machine, sets, "expected a set")?;
                        let mut result = EMPTY_SET;
                        for index in 0..machine.store.size_of(sets) {
                            let set = expect_set(
                                machine,
                                machine.store.element_at(sets, index),
                                "expected a set",
                            )?;
                            result = machine.store.union(result, set)?;
                        }
                        Ok(result)
                    },
                    true,
                );
                Compiled {
                    is_normalized: is_enumerated,
                    is_enumerated,
                    member: only.as_ref().map(|only| self.member_test(only)),
                    parts: only.as_ref().map(Self::parts_of),
                    ..compiled
                }
            }
            "DOMAIN" => {
                arity(1)?;
                let function = self.operand(&operands[0])?;
                unary(
                    &function,
                    |machine, function| {
                        if !is_function_kind(machine.store.kind_of(function)) {
                            return Err(Bail("DOMAIN of a non-function"));
                        }
                        Ok(machine.store.domain_of(function))
                    },
                    true,
                )
            }
            "+" | "-" | "*" | "\\div" | "%" | "^" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                arithmetic(
                    &left,
                    &right,
                    match name {
                        "+" => |left, right| Ok(left + right),
                        "-" => |left, right| Ok(left - right),
                        "*" => |left, right| Ok(left * right),
                        "\\div" => {
                            |left: i64, right: i64| {
                                if right == 0 {
                                    return Err(Bail("division by zero"));
                                }
                                let quotient = left / right;
                                Ok(quotient
                                    - i64::from(left % right != 0 && (left < 0) != (right < 0)))
                            }
                        }
                        "%" => |left: i64, right: i64| {
                            if right <= 0 {
                                return Err(Bail("modulus by a non-positive number"));
                            }
                            Ok(left.rem_euclid(right))
                        },
                        _ => |base: i64, exponent: i64| {
                            if exponent < 0 {
                                return Err(Bail("negative exponent"));
                            }
                            // Past 32 bits the store fails as TLC's arithmetic overflows.
                            Ok(u32::try_from(exponent)
                                .ok()
                                .and_then(|exponent| base.checked_pow(exponent))
                                .unwrap_or(i64::MAX))
                        },
                    },
                )
            }
            "-." => {
                arity(1)?;
                let operand = self.operand(&operands[0])?;
                unary(
                    &operand,
                    |machine, value| {
                        let value = expect_int(machine, value)?;
                        machine.store.int(-value)
                    },
                    false,
                )
            }
            "<" | ">" | "<=" | ">=" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                comparison(
                    &left,
                    &right,
                    match name {
                        "<" => |left, right| left < right,
                        ">" => |left, right| left > right,
                        "<=" => |left, right| left <= right,
                        _ => |left, right| left >= right,
                    },
                )
            }
            ".." => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                let (low, high) = (left.eval.clone(), right.eval.clone());
                let bounds = (low.clone(), high.clone());
                Compiled {
                    is_costly: true,
                    interval: Some(bounds),
                    ..leaf(
                        eval(move |machine| fused::interval(machine, &low, &high)),
                        left.footprint.merge(&right.footprint),
                    )
                }
            }
            "ToString" => {
                arity(1)?;
                self.is_ranking = true;
                let value = self.operand(&operands[0])?;
                unary(&value, to_string, true)
            }
            "Len" => {
                arity(1)?;
                let sequence = self.operand(&operands[0])?;
                unary(
                    &sequence,
                    |machine, sequence| {
                        let size = machine.store.size_of(expect_sequence(machine, sequence)?);
                        machine.store.int(i64::from(size))
                    },
                    false,
                )
            }
            "Head" => {
                arity(1)?;
                let sequence = self.operand(&operands[0])?;
                unary(
                    &sequence,
                    |machine, sequence| {
                        let tuple = expect_sequence(machine, sequence)?;
                        if machine.store.size_of(tuple) == 0 {
                            return Err(Bail("Head of an empty sequence"));
                        }
                        Ok(machine.store.get_range_value(tuple, 0))
                    },
                    false,
                )
            }
            "Tail" => {
                arity(1)?;
                let sequence = self.operand(&operands[0])?;
                unary(
                    &sequence,
                    |machine, sequence| {
                        let tuple = expect_sequence(machine, sequence)?;
                        let size = machine.store.size_of(tuple);
                        if size == 0 {
                            return Err(Bail("Tail of an empty sequence"));
                        }
                        Ok(machine.store.slice_tuple(tuple, 1, size))
                    },
                    false,
                )
            }
            "Append" => {
                arity(2)?;
                let sequence = self.operand(&operands[0])?;
                let element = self.operand(&operands[1])?;
                binary(
                    &sequence,
                    &element,
                    |machine, sequence, element| {
                        let tuple = expect_sequence(machine, sequence)?;
                        Ok(machine.store.append_tuple(tuple, element))
                    },
                    false,
                    false,
                )
            }
            "\\o" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                binary(
                    &left,
                    &right,
                    |machine, left, right| {
                        let is_left_text = machine.store.kind_of(left) == KIND_STRING;
                        let is_right_text = machine.store.kind_of(right) == KIND_STRING;
                        if is_left_text && is_right_text {
                            let mut text = machine.store.text_of(left).to_vec();
                            text.extend_from_slice(machine.store.text_of(right));
                            return Ok(machine.store.str(&text));
                        }
                        if is_left_text || is_right_text {
                            return Err(Bail("concatenation of a string and a sequence"));
                        }
                        let left = expect_sequence(machine, left)?;
                        let right = expect_sequence(machine, right)?;
                        Ok(machine.store.concat_tuples(left, right))
                    },
                    false,
                    false,
                )
            }
            "Seq" => {
                arity(1)?;
                let base = self.operand(&operands[0])?;
                let base_member = self.member_test(&base);
                let base_parts = Self::parts_of(&base);
                Compiled {
                    is_normalized: false,
                    infinite: Some("Seq"),
                    parts: Some(base_parts.clone()),
                    member: Some(member(move |machine, element| {
                        machine.run_parts(&base_parts)?;
                        if machine.store.kind_of(element) != KIND_TUPLE {
                            return not_in(machine, element, "a mistyped membership in Seq");
                        }
                        for index in 0..machine.store.size_of(element) {
                            let value = machine.store.get_range_value(element, index);
                            if !base_member(machine, value)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    })),
                    ..leaf(
                        eval(|_| Err(Bail("enumerated Seq(S)"))),
                        base.footprint.clone(),
                    )
                }
            }
            "Assert" => {
                arity(1)?;
                // Assert(P, message) is TRUE when P holds. When it doesn't, TLC fails with the
                // message, which the interpreter reports.
                let condition = self.boolean_operand(&operands[0])?;
                let test = condition.eval.clone();
                Compiled {
                    is_boolean: true,
                    ..leaf(
                        eval(move |machine| {
                            if test(machine)? == TRUE {
                                Ok(TRUE)
                            } else {
                                Err(Bail("an assertion failed"))
                            }
                        }),
                        condition.footprint,
                    )
                }
            }
            "SelectSeq" => {
                arity(2)?;
                let sequence = self.operand(&operands[0])?;
                if !self.is_operator_argument(&operands[1]) {
                    // The interpreter fails on a test that isn't an operator.
                    let test = self.operand(&operands[1])?;
                    let footprint = sequence.footprint.merge(&test.footprint);
                    let (sequence, test) = (sequence.eval, test.eval);
                    return Ok(Some(leaf(
                        eval(move |machine| {
                            sequence(machine)?;
                            test(machine)?;
                            Err(Bail("a SelectSeq test that isn't an operator"))
                        }),
                        footprint,
                    )));
                }
                let test = self.compile_applier(&operands[1], context)?;
                if test.slots.len() != 1 {
                    return unsupported("a SelectSeq test that doesn't take one argument");
                }
                let footprint = sequence.footprint.merge(&test.footprint);
                let sequence = sequence.eval;
                let (slot, body) = (test.slots[0], test.body);
                Compiled {
                    is_costly: true,
                    ..leaf(
                        eval(move |machine| {
                            let tuple = sequence(machine)?;
                            let tuple = expect_sequence(machine, tuple)?;
                            let size = machine.store.size_of(tuple);
                            let at = machine.stack.len();
                            let saved = machine.locals[slot as usize];
                            let mut result = Ok(());
                            for index in 0..size {
                                let value = machine.store.get_range_value(tuple, index);
                                machine.locals[slot as usize] = value;
                                match body(machine) {
                                    Ok(TRUE) => machine.stack.push(value),
                                    Ok(FALSE) => {}
                                    Ok(_) => {
                                        result = Err(Bail("a SelectSeq test that isn't a boolean"))
                                    }
                                    Err(bail) => result = Err(bail),
                                }
                                if result.is_err() {
                                    break;
                                }
                            }
                            machine.locals[slot as usize] = saved;
                            let kept = machine.stack.split_off(at);
                            result?;
                            Ok(if kept.len() == size as usize {
                                tuple
                            } else {
                                machine.store.tuple_of(&kept)
                            })
                        }),
                        footprint,
                    )
                }
            }
            "Cardinality" => {
                arity(1)?;
                let set = self.operand(&operands[0])?;
                match &set.filter {
                    Some(filter) => leaf(
                        fused::cardinality_filter(Arc::clone(filter)),
                        set.footprint.clone(),
                    ),
                    None => unary(
                        &set,
                        |machine, set| {
                            let size =
                                machine
                                    .store
                                    .size_of(expect_set(machine, set, "expected a set")?);
                            machine.store.int(i64::from(size))
                        },
                        false,
                    ),
                }
            }
            ":>" => {
                arity(2)?;
                let key = self.operand(&operands[0])?;
                let value = self.operand(&operands[1])?;
                binary(
                    &key,
                    &value,
                    |machine, key, value| Ok(machine.store.function_of_sorted(&[key], &[value])),
                    false,
                    false,
                )
            }
            "@@" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                binary(
                    &left,
                    &right,
                    |machine, left, right| {
                        if !is_function_kind(machine.store.kind_of(left))
                            || !is_function_kind(machine.store.kind_of(right))
                        {
                            return Err(Bail("@@ of non-functions"));
                        }
                        let mut keys = Vec::new();
                        let mut values = Vec::new();
                        for index in 0..machine.store.size_of(left) {
                            keys.push(machine.store.get_key(left, index));
                            values.push(machine.store.get_range_value(left, index));
                        }
                        for index in 0..machine.store.size_of(right) {
                            let key = machine.store.get_key(right, index);
                            if machine.store.find_key(left, key)? != -1 {
                                continue;
                            }
                            keys.push(key);
                            values.push(machine.store.get_range_value(right, index));
                        }
                        machine.store.function_of(&keys, &values)
                    },
                    true,
                    false,
                )
            }
            _ => return Ok(None),
        }))
    }

    fn compile_set_operation(
        &mut self,
        name: &str,
        left: &Compiled,
        right: &Compiled,
    ) -> Compiling<Option<Compiled>> {
        // A set the engine tests for membership without building it, such as Nat \ {0}, combines
        // the operands' tests.
        let is_lazy = |set: &Compiled| set.infinite.is_some() || set.member.is_some();
        let lazy_member = if is_lazy(left) || is_lazy(right) {
            let (left_member, right_member) = (self.member_test(left), self.member_test(right));
            Some(match name {
                "\\cup" => member(move |machine, element| {
                    Ok(left_member(machine, element)? || right_member(machine, element)?)
                }),
                "\\cap" => member(move |machine, element| {
                    Ok(left_member(machine, element)? && right_member(machine, element)?)
                }),
                _ => member(move |machine, element| {
                    Ok(left_member(machine, element)? && !right_member(machine, element)?)
                }),
            })
        } else {
            None
        };
        if left.infinite.is_some() || right.infinite.is_some() {
            if if name == "\\" {
                right.infinite.is_some()
            } else {
                name != "\\cup"
            } {
                return Ok(None);
            }
            return Ok(Some(Compiled {
                is_normalized: false,
                infinite: Some("Combined"),
                member: lazy_member,
                ..leaf(
                    eval(|_| Err(Bail("an enumerated infinite set"))),
                    left.footprint.merge(&right.footprint),
                )
            }));
        }
        let operation: Binary = match name {
            "\\cup" => |machine, left, right| {
                let left = expect_set(machine, left, "expected a set")?;
                let right = expect_set(machine, right, "expected a set")?;
                machine.store.union(left, right)
            },
            "\\cap" => |machine, left, right| {
                let left = expect_set(machine, left, "expected a set")?;
                let right = expect_set(machine, right, "expected a set")?;
                machine.store.intersection(left, right)
            },
            _ => |machine, left, right| {
                let left = expect_set(machine, left, "expected a set")?;
                let right = expect_set(machine, right, "expected a set")?;
                machine.store.difference(left, right)
            },
        };
        // TLC tests each element of a set enumeration for membership in the other set, so the
        // difference or intersection with one keeps its order whatever the other set is.
        let is_normalized = match name {
            "\\" => left.is_normalized,
            "\\cap" => left.is_normalized || right.is_normalized,
            _ => left.is_normalized && right.is_normalized,
        };
        // TLC combines a set it keeps lazy with another lazily, as the interpreter does. It
        // enumerates the left set of a difference or an intersection and only tests the right one
        // for membership, which any value of it answers alike.
        let reference = if is_normalized {
            None
        } else {
            let operator = match name {
                "\\cup" => Operator::Union,
                "\\cap" => Operator::Intersection,
                _ => Operator::Difference,
            };
            let right_reference = reference_of(right).or_else(|| {
                (operator != Operator::Union).then(|| {
                    let evaluate = right.eval.clone();
                    Arc::new(move |machine: &mut Machine<'_>| Ok(Lazy::Set(evaluate(machine)?)))
                        as Reference
                })
            });
            reference_of(left)
                .zip(right_reference)
                .map(|(left, right)| {
                    Arc::new(move |machine: &mut Machine<'_>| {
                        let left = left(machine)?;
                        let right = right(machine)?;
                        Lazy::combine(machine, operator, left, right)
                    }) as Reference
                })
        };
        Ok(Some(Compiled {
            is_normalized,
            member: lazy_member,
            reference,
            ..binary(left, right, operation, true, false)
        }))
    }
}
// ToString(v): TLC's text of v (`write_value`), as a string TLC ranks as it makes it.
fn to_string(machine: &mut Machine<'_>, value: Id) -> Outcome<Id> {
    if !is_printable(&machine.store, value) {
        return Err(Bail(
            "ToString of a value whose text depends on how TLC built it",
        ));
    }
    let mut text = Vec::new();
    write_value(&machine.store, value, &mut text);
    // A text the engine made before, such as by \o, keeps the rank it had then, -1, which the
    // store's guard on unordered strings doesn't see.
    if let Some(string) = machine.store.find_str(&text)
        && machine.store.text_rank_of(string) < 0
    {
        return Err(Bail("ToString of a text the engine made unranked"));
    }
    machine.store.get_string_rank(&text);
    Ok(machine.store.str(&text))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::Program;
    use tla_values::Store;

    fn to_text(store: &mut Store, id: Id) -> Option<String> {
        let program = Program::default();
        let mut machine = Machine::new(&program, std::mem::take(store));
        let result = to_string(&mut machine, id)
            .ok()
            .map(|string| String::from_utf16(machine.store.text_of(string)).expect("UTF-16"));
        *store = machine.store;
        result
    }

    // The string it makes ranks then, after the strings TLC ranked before, and it stops where the
    // text depends on how TLC built the value.
    #[test]
    fn ranks_the_string_it_makes_and_stops_on_a_value_it_cant_print() {
        let mut store = Store::new();
        store.reset(
            ["z"]
                .map(|text| text.encode_utf16().collect::<Vec<u16>>())
                .iter()
                .map(Vec::as_slice),
        );
        let twelve = store.int(12).expect("an integer");
        let thirteen = store.int(13).expect("an integer");
        assert_eq!(to_text(&mut store, twelve).as_deref(), Some("12"));
        assert_eq!(
            store.get_string_order(),
            [
                &[u16::from(b'z')][..],
                &"12".encode_utf16().collect::<Vec<u16>>()
            ]
        );
        let interval = store.set_of(&[twelve, thirteen]).expect("a set");
        assert_eq!(to_text(&mut store, interval), None);
    }
}
