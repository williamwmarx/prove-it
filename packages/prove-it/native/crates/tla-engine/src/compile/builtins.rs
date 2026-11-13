//! The builtins, as `compileBuiltin` and `compileNativeBuiltin` compile them. The pure builtins
//! the TypeScript engine runs in the interpreter (`PURE_BUILTINS`) are `bridged.rs`'s, except
//! ToString, which prints as the interpreter's printer does (`format_value`).

use std::collections::HashSet;
use std::sync::Arc;

use tla_ir::{Builtin, Index, NodeId, NodeKind, Pattern, Resolution};
use tla_values::json;
use tla_values::print::{Construction, is_printable, write_constructed};
use tla_values::store::{
    EMPTY_SET, EMPTY_TUPLE, FALSE, INT, KIND_INT, KIND_SET, KIND_STRING, KIND_TUPLE, NAT, Outcome,
    STRINGS, TRUE, is_function_kind,
};
use tla_values::transfer::UNENCODABLE;
use tla_values::{Bail, Id, Store};

use super::bridged;
use super::fused;
use super::lazy::{Lazy, Operator, PrintedSet, Reference, UNSIZED_PRINT};
use super::lazy_function;
use super::nodes::{evaluate_set, expect_set};
use super::predicate::{Leaf, Predicate};
use super::random;
use super::sets::not_in;
use super::{
    Binding, Compiled, Compiler, Compiling, Context, DISTINCT_SLOT, LEVEL_SLOT, NEXT_LEVEL_SLOT,
    Operand, OperatorBody, Shape, bind, bool_id, combine_references, decline, eval, leaf, lookup,
    member, operator_context, predicate_node, reference_of, unsupported,
};
use crate::footprint::Footprint;
use crate::machine::{Eval, Machine, Member, Parts, Printed, Prints};
use crate::search::{HostRead, JsonFiles};

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

/// `tlc2.module.Naturals#Divide`: Java's quotient of two ints, less one only where it is below 0
/// and inexact, so -1 \div 2 is 0, and -2147483648 \div -1 wraps to -2147483648. None for a
/// division by zero. The operands are TLC's ints, as the store holds them.
pub(crate) fn naturals_divide(left: i64, right: i64) -> Option<i64> {
    let (left, right) = (left as i32, right as i32);
    if right == 0 {
        return None;
    }
    let quotient = left.wrapping_div(right);
    let is_floored = quotient < 0 && quotient.wrapping_mul(right) != left;
    Some(i64::from(quotient - i32::from(is_floored)))
}

/// A union, an intersection or a difference with an operand that isn't a set, which TLC keeps
/// lazy or builds element by element, failing only where it tests that operand for an element.
pub(crate) const NON_SET_OPERAND: &str = "a set operation on a value that isn't a set";

fn expect_sets(machine: &Machine<'_>, left: Id, right: Id) -> Outcome<(Id, Id)> {
    if machine.store.kind_of(left) != KIND_SET || machine.store.kind_of(right) != KIND_SET {
        return Err(Bail(NON_SET_OPERAND));
    }
    Ok((left, right))
}

pub(crate) fn expect_int(machine: &Machine<'_>, id: Id) -> Outcome<i64> {
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
    if size as usize >= super::lazy::OVERFLOWING_SUBSET_BASE {
        return Err(Bail(super::lazy::SUBSET_OVERFLOW));
    }
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
        // TLCExt's Trace, the behavior up to the state, which the engine doesn't keep: a spec that
        // never evaluates it, such as one that serializes it only once an invariant fails, still
        // searches here, and one that does hands over then.
        if name == "Trace" {
            return Ok(leaf(
                eval(|_| Err(Bail("TLCExt's Trace, the behavior the engine doesn't keep"))),
                Footprint::default(),
            ));
        }
        if builtin.flags & Builtin::STATE_LEVEL != 0 || IMPURE_BUILTINS.contains(&name) {
            return unsupported(name);
        }
        Ok(match name {
            "TRUE" => super::constant(TRUE),
            "FALSE" => super::constant(FALSE),
            "BOOLEAN" => super::constant(self.store.set_of(&[FALSE, TRUE])?),
            "Nat" => Self::infinite_set("Nat", NAT, "enumerated Nat"),
            "Int" => Self::infinite_set("Int", INT, "enumerated Int"),
            "STRING" => Self::infinite_set("STRING", STRINGS, "enumerated STRING"),
            // TLC's Bags class overrides a user's module named Bags too, whose definition the
            // front end keys as `EmptyBag@Bags`.
            "EmptyBag" | "EmptyBag@Bags" => super::constant(EMPTY_TUPLE),
            name => {
                return decline(format!(
                    "the builtin {name}, whose value the interpreter computes"
                ));
            }
        })
    }

    /// `SUBSET S` of a compiled S, which TLC enumerates in the normalized order of S's elements.
    pub(crate) fn compile_subset(&mut self, base: &Compiled) -> Compiled {
        let base_member = self.member_test(base);
        let base_parts = Self::parts_of(base);
        Compiled {
            is_normalized: false,
            subset_base: Some(Box::new(base.clone())),
            // It streams in its order, its elements are set enumerations, and theirs are S's.
            is_in_order: true,
            are_elements_in_order: true,
            are_elements_of_elements_in_order: base.are_elements_in_order,
            // TLC enumerates SUBSET S in the normalized order of S's elements, whatever S's
            // own order (SubsetValue.elementsNormalized), so S's value does where S has no
            // reference.
            has_infinite_part: base.may_be_infinite(),
            is_irreducible: true,
            reference: combine_references(&[base], |_, mut bases| {
                Ok(Lazy::Subset(Box::new(bases.remove(0))))
            })
            .or_else(|| {
                let evaluate = base.eval.clone();
                Some(Arc::new(move |machine| {
                    Ok(Lazy::Subset(Box::new(Lazy::Set(evaluate(machine)?))))
                }))
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
                base,
                |machine, set| power_set(machine, expect_set(machine, set, "expected a set")?),
                true,
            )
        }
    }

    // Nat, Int and STRING, which the engine only tests for membership.
    fn infinite_set(name: &'static str, value: i32, reason: &'static str) -> Compiled {
        Compiled {
            is_normalized: false,
            infinite: Some(name),
            infinite_value: Some(value),
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
        let is_checked = self.is_native && builtin.flags & Builtin::DECLINED == 0;
        if is_checked && name == "AssertEq" {
            return self.compile_assert_eq(operands, context);
        }
        if name == "TLCGet" {
            return self.compile_tlc_get(operands, context);
        }
        if self.is_native && name == "TLCSet" {
            return self.compile_register(operands, context, true);
        }
        if is_checked && matches!(name, "TLCGetOrDefault" | "TLCGetAndSet") {
            return self.compile_get_or_default(operands, context, name == "TLCGetAndSet");
        }
        if is_checked && name == "PickSuccessor" {
            return self.compile_pick_successor(operands);
        }
        if self.is_native && name == "TLCFP" {
            return self.compile_tlc_fp(operands);
        }
        if self.is_native && name == "TLCCache" {
            return self.compile_tlc_cache(operands, context);
        }
        if name == "RandomElement" || name == "RandomSubset" {
            return self.compile_random(name, operands, context);
        }
        if matches!(
            name,
            "JsonSerialize" | "ndJsonSerialize" | "JsonDeserialize" | "ndJsonDeserialize"
        ) && self.is_native
        {
            return self.compile_json_file(name, operands, context);
        }
        if builtin.flags & Builtin::TABLE != 0 {
            return self.compile_table(index, operands);
        }
        // `TLCExt.tlcDefer`: TLC's breadth-first search never runs the deferred expression.
        if name == "TLCDefer" {
            return Ok(super::constant(TRUE));
        }
        // AssertError compares TLC's message for a failure, which the engine doesn't word, so
        // the native checker leaves the assumption it is in to its caller.
        if self.is_native && name == "AssertError" {
            return Ok(leaf(
                eval(|_| Err(Bail(crate::search::DELEGATED_ASSUMPTION))),
                Footprint::default(),
            ));
        }
        if builtin.flags & Builtin::STATE_LEVEL != 0 || IMPURE_BUILTINS.contains(&name) {
            // TLCEval makes a set an enumerated one and a function a built one (`convert`), so
            // what TLC kept lazy of the operand is forgotten: a set of functions is then drawn
            // from and enumerated as its elements.
            if name == "TLCEval" && operands.len() == 1 {
                let operand = self.operand(&operands[0])?;
                if operand.infinite.is_some() || operand.has_infinite_part {
                    return unsupported("TLCEval of a set TLC may not enumerate");
                }
                let evaluate = operand.eval;
                return Ok(Compiled {
                    is_costly: operand.is_costly,
                    is_boolean: operand.is_boolean,
                    is_constant: operand.is_constant,
                    is_enumerated: true,
                    is_in_order: true,
                    ..leaf(
                        eval(move |machine| {
                            let value = evaluate(machine)?;
                            if machine.store.kind_of(value) == tla_values::store::KIND_LAZY_FUNCTION
                            {
                                return Err(Bail(
                                    "unsupported: TLCEval of a function TLC keeps lazy",
                                ));
                            }
                            Ok(value)
                        }),
                        operand.footprint,
                    )
                });
            }
            return unsupported(name);
        }
        if let Some(native) = self.compile_native_builtin(name, builtin.flags, operands, context)? {
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

    // The operands of `=` or `#`: TLC compares a set it keeps lazy, such as Int \X {}, by its
    // enumeration (`SetOfTuplesValue.equals`). Where the other value isn't a set, the failure
    // TLC reports prints the lazy set as built, as the trace's evaluator does.
    fn compared(left: Compiled, right: Compiled) -> (Compiled, Compiled) {
        (Self::listed(&left), Self::listed(&right))
    }

    // `S \subseteq T`, as TLC's isSubsetEq: for two power sets, SUBSET A \subseteq SUBSET B is
    // A \subseteq B, unless TLC can't enumerate A (SubsetValue.isSubsetEq); otherwise each element
    // of S, enumerated, is a member of T.
    fn compile_subseteq(&mut self, left: &Compiled, right: &Compiled) -> Compiled {
        if let (Some(left_base), Some(right_base)) = (&left.subset_base, &right.subset_base)
            && left_base.infinite.is_none()
        {
            return self.compile_subseteq(left_base, right_base);
        }
        let footprint = left.footprint.merge(&right.footprint);
        // TLC enumerates S (`Value.isSubsetEq`).
        let left_eval = Self::listed(left).eval;
        let evaluate = if right.member.is_some() || right.infinite.is_some() {
            let test = self.member_test(right);
            // TLC evaluates T before it tests S's elements in it (OPCODE_subseteq), which runs
            // the tests TLC makes as it builds T even where S is empty.
            let right_parts = Self::parts_of(right);
            eval(move |machine| {
                let set = evaluate_set(machine, &left_eval, "expected a set")?;
                machine.run_parts(&right_parts)?;
                let before = machine.effects();
                let mut is_subset = TRUE;
                for index in 0..machine.store.size_of(set) {
                    let element = machine.store.element_at(set, index);
                    if !test(machine, element)? {
                        is_subset = FALSE;
                        break;
                    }
                }
                // A test may evaluate T's parts again, which an effect shows.
                if machine.effects() != before {
                    return Err(Bail("a subset test of a set with effects"));
                }
                Ok(is_subset)
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

    // A configuration's definition of a constant operator by its values, F(0) = 1, which TLC applies
    // by the first row whose arguments equal the arguments, and fails to apply where none does.
    fn compile_table(&mut self, index: Index, operands: &[Operand]) -> Compiling<Compiled> {
        let ir = self.ir;
        let mut rows = Vec::new();
        for &(arguments, value) in &ir.builtins[index as usize].table {
            let (Some(arguments), Some(value)) = (arguments, value) else {
                return unsupported("a value of an operator's table the IR can't hold");
            };
            rows.push((self.intern_value(arguments)?, self.intern_value(value)?));
        }
        let arguments = operands
            .iter()
            .map(|operand| self.operand(operand))
            .collect::<Compiling<Vec<Compiled>>>()?;
        let footprint = Footprint::merge_all(arguments.iter().map(|argument| &argument.footprint));
        let evals: Vec<Eval> = arguments
            .into_iter()
            .map(|argument| argument.eval)
            .collect();
        Ok(leaf(
            eval(move |machine| {
                let values = evals
                    .iter()
                    .map(|evaluate| evaluate(machine))
                    .collect::<Outcome<Vec<Id>>>()?;
                let tuple = machine.store.tuple_of(&values);
                for &(key, value) in &rows {
                    if machine.store.equals(key, tuple)? {
                        return Ok(value);
                    }
                }
                Err(Bail("an operator's table applied outside its rows"))
            }),
            footprint,
        ))
    }

    // RandomElement(S) and RandomSubset(k, S) draw as TLC does where the engine evaluates them as
    // TLC does, as Print prints: from the interpreter's generator for the initial states, and from
    // one seeded with the fingerprint of each state the search expands.
    fn compile_random(
        &mut self,
        name: &str,
        operands: &[Operand],
        context: &Context,
    ) -> Compiling<Compiled> {
        if !context.can_print {
            return unsupported(name);
        }
        let is_element = name == "RandomElement";
        if operands.len() != if is_element { 1 } else { 2 } {
            return unsupported("an operator applied to the wrong number of arguments");
        }
        self.is_printing = true;
        let compiled = operands
            .iter()
            .map(|operand| self.compile(operand.node, &operand.context.without_print()))
            .collect::<Compiling<Vec<Compiled>>>()?;
        let footprint = Footprint::merge_all(compiled.iter().map(|operand| &operand.footprint))
            .merge(&Footprint::slot(super::PRINT_SLOT));
        let is_174 = self
            .ir
            .model
            .version
            .is_some_and(|version| self.text(version) == "1.7.4");
        let set = compiled.last().expect("an operand");
        let interval = set.interval.clone();
        let reference = set.reference.clone();
        let evaluate_members = set.eval.clone();
        let is_enumerated = set.is_enumerated;
        let evaluate_count = (!is_element).then(|| compiled[0].eval.clone());
        Ok(leaf(
            eval(move |machine| {
                let count = match &evaluate_count {
                    None => None,
                    Some(evaluate) => {
                        let count = evaluate(machine)?;
                        if machine.store.kind_of(count) != KIND_INT
                            || machine.store.int_of(count) < 0
                        {
                            return Err(Bail(
                                "RandomSubset of a count that isn't a natural number",
                            ));
                        }
                        Some(machine.store.int_of(count) as u64)
                    }
                };
                let source = match (&interval, &reference) {
                    (Some((low, high)), _) => {
                        let (low, high) = (low(machine)?, high(machine)?);
                        let (low, high) = (expect_int(machine, low)?, expect_int(machine, high)?);
                        random::Source::Interval(low, high)
                    }
                    (None, Some(reference)) => random::Source::Set(reference(machine)?),
                    (None, None) => {
                        // A set of functions, records or tuples held as its elements, as a
                        // variable holds one, may be one TLC draws component by component.
                        let set = evaluate_members(machine)?;
                        if !is_enumerated && random::is_shape_forgotten(machine, set) {
                            return Err(Bail("drew from a set whose shape the engine forgets"));
                        }
                        random::Source::Set(Lazy::Set(set))
                    }
                };
                match (count, source) {
                    (None, random::Source::Interval(low, high)) => {
                        let offset = random::random_offset(machine, low, high)?;
                        machine.store.int(offset)
                    }
                    (None, random::Source::Set(set)) => random::random_element(machine, &set),
                    (Some(count), source) => {
                        let drawn = random::random_subset(machine, count, &source, is_174)?;
                        machine.store.set_of(&drawn)
                    }
                }
            }),
            footprint,
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
            return self.decline_print(name);
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
        // TLC prints a set of functions, records or tuples it holds lazy by sizing its parts
        // (`Lazy::check_printed`), which may fail where the engine enumerated the set: such an
        // operand is first built as TLC holds it. Where the engine can't tell, a startup
        // definition declines, and elsewhere the engine prints the set it enumerates.
        let is_unsure_declined = self.startup_bodies > 0;
        let checked: Vec<Option<Reference>> = operands
            .iter()
            .zip(&compiled)
            .map(|(operand, compiled)| {
                self.is_print_checked(operand.node)
                    .then(|| compiled.reference.clone())
                    .flatten()
            })
            .collect();
        let is_written = operands
            .iter()
            .any(|operand| self.may_write_held(operand.node, true));
        let evaluators: Vec<Eval> = compiled.into_iter().map(|operand| operand.eval).collect();
        // The native binary's reporter finds what it can't print itself: TLC prints the startup's
        // in the front the binary records, and the binary stops at any later one. It prints each
        // value as TLC prints a value built as the operand writes it, deep-normalized.
        let constructions = self.is_native.then(|| {
            operands
                .iter()
                .map(|operand| self.construction_of(operand))
                .collect::<Vec<_>>()
        });
        Ok(Compiled {
            is_boolean,
            ..leaf(
                eval(move |machine| {
                    let values = evaluate_printed(
                        machine,
                        &evaluators,
                        &checked,
                        is_unsure_declined,
                        is_print,
                    )?;
                    check_written(machine, is_written)?;
                    let result = if is_print { values[1] } else { TRUE };
                    push_prints(machine, values, constructions.as_deref())?;
                    Ok(result)
                }),
                footprint,
            )
        })
    }

    // AssertEq(a, b), which TLCExt defines in TLA+ as `IF a # b THEN PrintT("Assertion failed")
    // /\ PrintT(a) /\ PrintT(b) /\ a = b ELSE a = b`: where a and b differ, it prints the string
    // and each value as PrintT does, and is FALSE. TLC evaluates each argument once, which an
    // argument without effects shows nowhere, so an argument that prints declines.
    fn compile_assert_eq(
        &mut self,
        operands: &[Operand],
        context: &Context,
    ) -> Compiling<Compiled> {
        if !context.can_print {
            return self.decline_print("AssertEq");
        }
        if operands.len() != 2 {
            return unsupported("an operator applied to the wrong number of arguments");
        }
        let operands: Vec<Operand> = operands
            .iter()
            .map(|operand| Operand {
                context: operand.context.without_print(),
                ..operand.clone()
            })
            .collect();
        let differs = self
            .compile_native_builtin("#", 0, &operands, context)?
            .expect("a comparison");
        let printed = [
            self.compile_print("PrintT", &operands[..1], context)?,
            self.compile_print("PrintT", &operands[1..], context)?,
        ];
        let footprint = differs
            .footprint
            .merge(&printed[0].footprint)
            .merge(&printed[1].footprint);
        let message = self
            .store
            .str(&"Assertion failed".encode_utf16().collect::<Vec<u16>>());
        let (differs, printed) = (differs.eval, printed.map(|print| print.eval));
        Ok(Compiled {
            is_boolean: true,
            ..leaf(
                eval(move |machine| {
                    if differs(machine)? != TRUE {
                        return Ok(TRUE);
                    }
                    push_prints(machine, vec![message], Some(&[Construction::Held]))?;
                    for print in &printed {
                        print(machine)?;
                    }
                    Ok(FALSE)
                }),
                footprint,
            )
        })
    }

    // How TLC builds the value of an operand, as far as its text depends on it: from the
    // expression written there, a set enumeration, an interval, a tuple, a record, a function
    // over a set enumeration or an interval, `k :> v`, a SUBSET or a set of functions of a set
    // enumeration or an interval, and any other value as the store holds it. An argument of an
    // operator is a value TLC may have compared, and normalized, before.
    fn construction_of(&self, operand: &Operand) -> Construction {
        if operand.is_param {
            return Construction::Held;
        }
        self.construction_of_node(operand.node)
    }

    fn construction_of_node(&self, node: NodeId) -> Construction {
        let of = |node: &NodeId| self.construction_of_node(*node);
        let as_set = |node: &NodeId| {
            let construction = of(node);
            construction.of_elements().is_some().then_some(construction)
        };
        match self.node(node).1 {
            NodeKind::Apply { name, args } => {
                let builtin = match name.resolution {
                    Resolution::Builtin(index) if !name.is_local => self.builtin_name(index),
                    _ => return Construction::Held,
                };
                match (builtin, args.as_slice()) {
                    ("..", [_, _]) => Construction::Interval,
                    ("SUBSET", [base]) => as_set(base).map_or(Construction::Held, |base| {
                        Construction::Subset(Box::new(base))
                    }),
                    (":>", [key, value]) => {
                        Construction::Function(Box::new(of(key)), Box::new(of(value)))
                    }
                    _ => Construction::Held,
                }
            }
            NodeKind::SetEnumeration(elements) => {
                let constructions: Vec<Construction> = elements.iter().map(of).collect();
                match constructions.split_first() {
                    Some((first, rest)) if rest.iter().all(|other| other == first) => {
                        Construction::Set(Box::new(first.clone()), Some(elements.len() as u32))
                    }
                    None => Construction::Set(Box::new(Construction::Held), Some(0)),
                    _ => Construction::Held,
                }
            }
            NodeKind::Tuple(elements) => Construction::Tuple(elements.iter().map(of).collect()),
            NodeKind::Record(fields) => Construction::Record(
                fields
                    .iter()
                    .map(|(field, value)| (self.text(*field).encode_utf16().collect(), of(value)))
                    .collect(),
            ),
            NodeKind::FunctionConstruction {
                is_recursive: false,
                bounds,
                body,
            } => match bounds.as_slice() {
                // TLC keeps a function lazy unless its domain is reducible (`Tool`'s OPCODE_fc),
                // as a product, a power set, a set of functions or of records isn't.
                [bound]
                    if matches!(bound.pattern, Pattern::Name(_))
                        && matches!(
                            self.node(bound.set).1,
                            NodeKind::Product(_)
                                | NodeKind::FunctionSet { .. }
                                | NodeKind::RecordSet(_)
                        ) =>
                {
                    Construction::LazyFunction(Box::new(Construction::Held), Box::new(of(body)))
                }
                [bound] if matches!(bound.pattern, Pattern::Name(_)) => as_set(&bound.set)
                    .and_then(|domain| domain.of_elements().cloned())
                    .map_or(Construction::Held, |key| {
                        Construction::Function(Box::new(key), Box::new(of(body)))
                    }),
                _ => Construction::Held,
            },
            NodeKind::FunctionSet { domain, range } => match (as_set(domain), as_set(range)) {
                (Some(domain), Some(range)) => {
                    Construction::FunctionSet(Box::new(domain), Box::new(range))
                }
                _ => Construction::Held,
            },
            _ => Construction::Held,
        }
    }

    // The Json module's operators that write a value to the file a string names, as JSON or one
    // element of a sequence per line, or read one, as TLC's Json class does. They read and write
    // the files `Settings::json_files` names.
    // Writing prints in TLC's order, as Print does; reading ranks the strings it reads. Where the
    // model writes a file, a read sees what was last written, so it too is evaluated only where,
    // and as often as, TLC does; where it writes none, every read of a file reads the same, as
    // TLC's reading it once at startup does.
    fn compile_json_file(
        &mut self,
        name: &str,
        operands: &[Operand],
        context: &Context,
    ) -> Compiling<Compiled> {
        let files = self.json_files.clone();
        if let JsonFiles::Declined = files {
            return decline(format!("{name}, whose file the host reads and writes"));
        }
        let is_written = name.ends_with("Serialize");
        let is_ordered = is_written
            || self.ir.builtins.iter().any(|builtin| {
                matches!(self.text(builtin.name), "JsonSerialize" | "ndJsonSerialize")
            });
        if is_ordered && !context.can_print {
            return self.decline_print(name);
        }
        if operands.len() != if is_written { 2 } else { 1 } {
            return unsupported("an operator applied to the wrong number of arguments");
        }
        let compiled = operands
            .iter()
            .map(|operand| self.operand(operand))
            .collect::<Compiling<Vec<Compiled>>>()?;
        let mut footprint = Footprint::merge_all(compiled.iter().map(|operand| &operand.footprint));
        if is_ordered {
            footprint = footprint.merge(&Footprint::slot(super::PRINT_SLOT));
            self.is_printing = true;
        }
        let evaluators: Vec<Eval> = compiled.into_iter().map(|operand| operand.eval).collect();
        let is_lines = name.starts_with("nd");
        let read_path = move |machine: &mut Machine<'_>, evaluate: &Eval| -> Outcome<String> {
            let path = evaluate(machine)?;
            if machine.store.kind_of(path) != KIND_STRING {
                return Err(Bail("a Json operator's file that isn't a string"));
            }
            Ok(String::from_utf16_lossy(machine.store.text_of(path)))
        };
        if !is_written {
            self.is_ranking = true;
            return Ok(leaf(
                eval(move |machine| {
                    let path = read_path(machine, &evaluators[0])?;
                    let bytes = match &files {
                        JsonFiles::Host(host) => match host.read(&path) {
                            HostRead::Bytes(bytes) => Ok(bytes),
                            HostRead::Missing => Err(()),
                            HostRead::Unread => {
                                return Err(Bail(
                                    "unsupported: a Json operator's file the host hasn't read",
                                ));
                            }
                        },
                        _ => std::fs::read(&path).map_err(|_| ()),
                    };
                    let text: Vec<u16> = bytes
                        .map_err(|()| Bail("a Json operator's file that can't be read"))
                        .map(|bytes| String::from_utf8_lossy(&bytes).encode_utf16().collect())?;
                    if is_lines {
                        json::read_nd_json(&mut machine.store, &text)
                    } else {
                        json::read_json(&mut machine.store, &text)
                    }
                }),
                footprint,
            ));
        }
        Ok(Compiled {
            is_boolean: true,
            ..leaf(
                eval(move |machine| {
                    let path = read_path(machine, &evaluators[0])?;
                    let value = evaluators[1](machine)?;
                    let store = &machine.store;
                    if json::holds_ordered_keys(store, value) {
                        return Err(Bail(
                            "a Json operator's record, whose fields TLC writes as it holds them",
                        ));
                    }
                    let mut text = Vec::new();
                    if is_lines {
                        if store.kind_of(value) != KIND_TUPLE {
                            return Err(Bail("ndJsonSerialize of a value that isn't a sequence"));
                        }
                        for index in 0..store.size_of(value) {
                            json::write_json(
                                store,
                                store.get_range_value(value, index),
                                &mut text,
                            )?;
                            text.push(u16::from(b'\n'));
                        }
                    } else {
                        if store.kind_of(value) != KIND_TUPLE && !json::is_json_record(store, value)
                        {
                            return Err(Bail(
                                "JsonSerialize of a value that isn't a sequence or a record",
                            ));
                        }
                        json::write_json(store, value, &mut text)?;
                    }
                    let text = String::from_utf16_lossy(&text);
                    if let JsonFiles::Host(written) = &files {
                        written.write(path, text.into_bytes());
                        return Ok(TRUE);
                    }
                    // TLC makes the file's directories first, whether or not it then can.
                    if let Some(parent) = std::path::Path::new(&path).parent() {
                        let _ = std::fs::create_dir_all(parent);
                    }
                    std::fs::write(&path, text)
                        .map_err(|_| Bail("a Json operator's file that can't be written"))?;
                    Ok(TRUE)
                }),
                footprint,
            )
        })
    }

    // TLCGet("level"), TLCGet("distinct") and TLCGet("diameter") read the slots the search sets,
    // and TLCGet of a number or of a name that starts with "s:" reads a register.
    fn compile_tlc_get(&mut self, operands: &[Operand], context: &Context) -> Compiling<Compiled> {
        let key = match operands {
            // An operand bound to a parameter (TLC's TLCGet through an INSTANCE of TLC) is its
            // argument, unless the builtin is itself an operator argument.
            [operand] if operand.slot.is_none() => {
                self.string_literal(operand.node, &operand.context)
            }
            _ => None,
        };
        // The interpreter would take a search over without TLC's registers, so under the
        // TypeScript engine the engine declines all but the search's own keys, as it does.
        if !self.is_native
            && key.is_none_or(|key| !matches!(key, "level" | "distinct" | "diameter"))
        {
            return unsupported("TLCGet");
        }
        if key.is_none_or(|key| key.starts_with(NAMED_REGISTER_PREFIX)) {
            return self.compile_register(operands, context, false);
        }
        // A simulation's run, its statistics, its configuration and its search keys differ
        // from the model checker's (`Simulator.getStatistics`, `createConfig`).
        if self.simulation.is_some()
            && key.is_some_and(|key| {
                !matches!(key, "level" | "spec" | "config")
                    && !key.starts_with(JAVA_PROPERTY_PREFIX)
            })
        {
            return Ok(leaf(
                eval(|_| {
                    Err(Bail(
                        "unsupported: TLCGet of a key a simulation reads otherwise",
                    ))
                }),
                Footprint::slot(super::REGISTER_SLOT),
            ));
        }
        if key == Some("config") {
            return self.compile_config();
        }
        // A Java system property (`System.getProperty` with the key as the default): the key
        // itself for one nothing sets. The binary declines a command line that sets one the spec
        // names, and the engine one the JVM sets, but for the separators it knows.
        if let Some(key) = key.filter(|key| key.starts_with(JAVA_PROPERTY_PREFIX)) {
            let name = &key[JAVA_PROPERTY_PREFIX.len()..];
            let value = match name {
                "file.separator" => std::path::MAIN_SEPARATOR_STR,
                "path.separator" if cfg!(windows) => ";",
                "path.separator" => ":",
                _ if JVM_PROPERTY_NAMESPACES
                    .iter()
                    .any(|namespace| name.starts_with(namespace)) =>
                {
                    return unsupported("TLCGet of a system property the JVM sets");
                }
                _ => key,
            };
            let units: Vec<u16> = value.encode_utf16().collect();
            return Ok(super::constant(self.store.str(&units)));
        }
        // The specification's record, which the IR holds as the interpreter computes it for TLC's.
        if key == Some("spec")
            && let Some(index) = self.ir.model.tlc_spec
        {
            return Ok(super::constant(self.intern_value(index)?));
        }
        // TLC reads the other keys of its run, which the search doesn't keep: the native checker
        // stops where TLC would read one, which TLC may never do, as where an assumption before
        // it is false.
        if key != Some("level") && key != Some("distinct") && key != Some("diameter") {
            return Ok(leaf(
                eval(|_| Err(Bail("unsupported: TLCGet of a key the search doesn't keep"))),
                Footprint::slot(super::REGISTER_SLOT),
            ));
        }
        if context.is_init && context.is_primed {
            return unsupported("TLCGet");
        }
        let slot = if key == Some("diameter") {
            self.is_diameter_read = true;
            super::DIAMETER_SLOT
        } else if key == Some("distinct") {
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

    // The string an expression is written as, through the parameters bound to it, as TLC's
    // TLC.tla binds TLCGet's to the key an INSTANCE of TLC passes it.
    fn string_literal(&self, node: tla_ir::NodeId, context: &Context) -> Option<&str> {
        match self.node(node).1 {
            NodeKind::String(text) => Some(self.text(*text)),
            NodeKind::Identifier(name) if name.is_local => {
                let found = super::lookup(&context.scope, name.text)?;
                match &found.binding {
                    super::Binding::Argument(argument) => {
                        self.string_literal(argument.expression, &argument.context)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    // TLCGet("config"), the run's settings as TLC's model checker records them
    // (`AbstractChecker.createConfig`). TLC's install is where its jar is, which the native
    // checker has none of, so it is TLC's answer where it can't tell.
    fn compile_config(&mut self) -> Compiling<Compiled> {
        let model = &self.ir.model;
        let text = |text: &str| text.encode_utf16().collect::<Vec<u16>>();
        // A simulation's (`Simulator.createConfig`): the number of traces as Java's int of the
        // workers' total, and -1 for a depth without bound.
        let simulated = self.simulation.map(|simulation| {
            let traces = simulation.traces.map_or(i64::MAX, |traces| traces as i64);
            [
                ("mode", Field::Text("simulate".into())),
                (
                    "depth",
                    Field::Int(if simulation.depth == i32::MAX {
                        -1
                    } else {
                        i64::from(simulation.depth)
                    }),
                ),
                (
                    "traces",
                    Field::Int(i64::from((self.workers as i64).wrapping_mul(traces) as i32)),
                ),
                ("deadlock", Field::Bool(model.check_deadlock)),
                ("seed", Field::Text(simulation.seed.to_string())),
                // TLC caches the record as it builds its simulator, before it reads the aril
                // (`Simulator.createConfig`), so it keeps 0.
                ("aril", Field::Text("0".into())),
                ("worker", Field::Int(self.workers as i64)),
                ("install", Field::Text("unknown".into())),
                ("sched", Field::Text("random".into())),
            ]
        });
        let searched = [
            ("mode", Field::Text("bfs".into())),
            ("deadlock", Field::Bool(model.check_deadlock)),
            ("worker", Field::Int(self.workers as i64)),
            ("seed", Field::Text((model.random_seed as i64).to_string())),
            (
                "fingerprint",
                Field::Text((self.program.polynomial().value() as i64).to_string()),
            ),
            ("install", Field::Text("unknown".into())),
        ];
        let fields: Vec<(&str, Field)> = match simulated {
            Some(fields) => fields.into_iter().collect(),
            None => searched.into_iter().collect(),
        };
        let mut keys = Vec::with_capacity(fields.len());
        let mut values = Vec::with_capacity(fields.len());
        for (name, field) in fields {
            keys.push(self.store.str(&text(name)));
            values.push(match field {
                Field::Text(value) => self.store.str(&text(&value)),
                Field::Bool(value) => bool_id(value),
                Field::Int(value) => self.store.int(value)?,
            });
        }
        Ok(super::constant(self.store.function_of(&keys, &values)?))
    }

    // TLCSet(key, value) and TLCGet(key) of a register, as TLC runs them on one worker
    // (`TLCGetSet.TLCSet`, `TLCGetSet.TLCGetEval`). TLCSet writes in the order TLC evaluates it,
    // so like Print it compiles only where the engine evaluates as TLC does, and nothing caches
    // what reads a register. TLCSet("exit", FALSE) and TLCSet("pause", FALSE) do nothing; the
    // keys that stop or pause TLC, or set a Java property, stop the search.
    fn compile_register(
        &mut self,
        operands: &[Operand],
        context: &Context,
        is_set: bool,
    ) -> Compiling<Compiled> {
        if is_set && !context.can_print {
            return unsupported("TLCSet");
        }
        if operands.len() != if is_set { 2 } else { 1 } {
            return unsupported("an operator applied to the wrong number of arguments");
        }
        self.is_printing = true;
        let compiled = operands
            .iter()
            .map(|operand| self.compile(operand.node, &operand.context))
            .collect::<Compiling<Vec<Compiled>>>()?;
        let footprint = Footprint::merge_all(compiled.iter().map(|operand| &operand.footprint))
            .merge(&Footprint::slot(super::REGISTER_SLOT));
        let footprint = if is_set {
            footprint.merge(&Footprint::slot(super::PRINT_SLOT))
        } else {
            footprint
        };
        let mut evaluators = compiled.into_iter().map(|operand| operand.eval);
        let evaluate_key = evaluators.next().expect("a key");
        let evaluate_value = evaluators.next();
        Ok(Compiled {
            is_boolean: is_set,
            ..leaf(
                eval(move |machine| {
                    let key = evaluate_key(machine)?;
                    let Some(evaluate_value) = &evaluate_value else {
                        return get_register(machine, key);
                    };
                    let value = evaluate_value(machine)?;
                    set_register(machine, key, value)?;
                    Ok(TRUE)
                }),
                footprint,
            )
        })
    }

    // TLCGetOrDefault(key, default), TLCExt's Java method, is the register's value, or the default
    // where the key names no register or TLC hasn't set it. TLCGetAndSet(key, Op, val, default),
    // which TLCExt defines in TLA+ as `LET oldVal == TLCGetOrDefault(key, defaultVal) IN CHOOSE v
    // \in {oldVal} : TLCSet(key, Op(oldVal, val))`, then sets the register to Op(oldVal, val),
    // and is oldVal. TLC evaluates its arguments lazily, which arguments without effects show
    // nowhere but where one fails, within TLCExt's definition, so an argument that prints declines.
    fn compile_get_or_default(
        &mut self,
        operands: &[Operand],
        context: &Context,
        is_set: bool,
    ) -> Compiling<Compiled> {
        if is_set && !context.can_print {
            return unsupported("TLCGetAndSet");
        }
        let (operator, values) = match operands {
            [key, default] if !is_set => (None, [key, default]),
            [key, operator, value, default] if is_set => {
                if !self.is_operator_argument(operator) {
                    return unsupported("TLCGetAndSet of an argument that isn't an operator");
                }
                let operator = self.compile_applier(operator, context)?;
                if operator.slots.len() != 2 {
                    return unsupported("an operator applied to the wrong number of arguments");
                }
                let value = self.operand(&Operand {
                    context: value.context.without_print(),
                    ..value.clone()
                })?;
                (Some((operator, value)), [key, default])
            }
            _ => return unsupported("an operator applied to the wrong number of arguments"),
        };
        self.is_printing = true;
        let [key, default] = values.map(|operand| Operand {
            context: operand.context.without_print(),
            ..operand.clone()
        });
        let (key, default) = (self.operand(&key)?, self.operand(&default)?);
        let mut footprint = key
            .footprint
            .merge(&default.footprint)
            .merge(&Footprint::slot(super::REGISTER_SLOT));
        if let Some((operator, value)) = &operator {
            footprint = footprint
                .merge(&operator.footprint)
                .merge(&value.footprint)
                .merge(&Footprint::slot(super::PRINT_SLOT));
        }
        let (key, default) = (key.eval, default.eval);
        let operator =
            operator.map(|(operator, value)| (operator.slots, operator.body, value.eval));
        Ok(leaf(
            eval(move |machine| {
                let key = key(machine)?;
                let default = default(machine)?;
                let old = match get_register_key(&machine.store, key) {
                    Some(_) => get_register(machine, key).unwrap_or(default),
                    None if machine.store.kind_of(key) == KIND_INT => {
                        return Err(Bail("TLCGetOrDefault of a negative number"));
                    }
                    None => default,
                };
                let Some((slots, body, value)) = &operator else {
                    return Ok(old);
                };
                // A key that stops or configures TLC, such as "exit", which the search and the
                // simulation follow only for TLCSet.
                if get_register_key(&machine.store, key).is_none() {
                    return Err(Bail(
                        "unsupported: TLCGetAndSet of a key that stops or configures TLC",
                    ));
                }
                let value = value(machine)?;
                let saved = [slots[0], slots[1]].map(|slot| machine.locals[slot as usize]);
                machine.locals[slots[0] as usize] = old;
                machine.locals[slots[1] as usize] = value;
                let new = body(machine);
                for (&slot, saved) in slots.iter().zip(saved) {
                    machine.locals[slot as usize] = saved;
                }
                set_register(machine, key, new?)?;
                Ok(old)
            }),
            footprint,
        ))
    }

    // PickSuccessor(exp) as TLC's model checker evaluates it (`TLCExt.pickSuccessor`): TRUE of a
    // successor TLC has seen, then exp where it holds; where it doesn't, TLC asks its user to pick.
    // TLC fingerprints the successor first, which fails where it isn't complete, as in an
    // invariant, so that stops the search, for the trace evaluator to word. The search tells
    // whether TLC has seen the successor only as it checks the action constraints.
    fn compile_pick_successor(&mut self, operands: &[Operand]) -> Compiling<Compiled> {
        let model = &self.ir.model;
        if model.view.is_some() || model.startup.symmetry.is_some() {
            return unsupported("PickSuccessor under a VIEW or SYMMETRY");
        }
        // TLC takes PickSuccessor for an action (its minLevel), which the properties' levels
        // here don't follow.
        if !model.property_invariants.is_empty()
            || !model.action_properties.is_empty()
            || !model.atoms.is_empty()
            || !model.live_formula.is_empty()
        {
            return unsupported("PickSuccessor with temporal properties");
        }
        // TLC's workers share what PickSuccessor has seen, which the counts of its search on
        // several workers follow in an order the engine's don't.
        if self.workers > 1 {
            return unsupported("PickSuccessor on several workers");
        }
        let [operand] = operands else {
            return unsupported("an operator applied to the wrong number of arguments");
        };
        self.is_picking = true;
        let guard = self.operand(&Operand {
            context: operand.context.without_print(),
            ..operand.clone()
        })?;
        let footprint = (0..self.ir.variables.len() as u32)
            .fold(guard.footprint, |footprint, variable| {
                footprint.merge(&Footprint::prime(variable))
            });
        let guard = guard.eval;
        Ok(Compiled {
            is_boolean: true,
            ..leaf(
                eval(move |machine| match machine.is_successor_seen {
                    None => Err(Bail(
                        "PickSuccessor of a successor TLC fingerprints incomplete",
                    )),
                    Some(true) => Ok(TRUE),
                    Some(false) => match guard(machine)? {
                        TRUE => Ok(TRUE),
                        FALSE => Err(Bail("unsupported: PickSuccessor, which asks TLC's user")),
                        _ => Err(Bail("a PickSuccessor condition that isn't a boolean")),
                    },
                }),
                footprint,
            )
        })
    }

    // TLCFP(v), TLC's fingerprint of v as a number: the low 32 bits of the fingerprint of a state
    // of v alone (`TLCExt.tlcFingerprint`).
    fn compile_tlc_fp(&mut self, operands: &[Operand]) -> Compiling<Compiled> {
        let [operand] = operands else {
            return unsupported("an operator applied to the wrong number of arguments");
        };
        let value = self.operand(operand)?;
        let evaluate = value.eval;
        Ok(leaf(
            eval(move |machine| {
                let value = evaluate(machine)?;
                let fingerprint = machine
                    .fingerprints
                    .get_state(&machine.store, &[value], &[0])?;
                machine.store.int(i64::from(fingerprint as i32))
            }),
            value.footprint,
        ))
    }

    // TLCCache(e, key) (`TLCExt.tlcEval2`), by SANY's level of e. Where e is constant, TLC
    // evaluates the key each time and caches e's value by e's node and the key's hash, a
    // fingerprint, for the rest of the run: the bindings of bound identifiers that the key doesn't
    // tell apart share the value first cached, and e's effects happen once, where e is first
    // evaluated, so they may wherever TLCCache is. Where e reads a variable TLC caches nothing,
    // evaluates the key in the current state alone and e twice, and where e reads a primed
    // variable, e alone. A constant e can read a variable through an operator's argument, which
    // the engine can't tell from one that reads it itself, so it declines e that reads one.
    fn compile_tlc_cache(
        &mut self,
        operands: &[Operand],
        context: &Context,
    ) -> Compiling<Compiled> {
        let [expression, key] = operands else {
            return unsupported("an operator applied to the wrong number of arguments");
        };
        if expression.is_param || expression.slot.is_some() {
            return unsupported("TLCCache of an argument");
        }
        let node = expression.node;
        self.is_tlc_cache_used = true;
        let key = self.compile(key.node, &key.context.without_print())?;
        let is_key_constant = key.footprint.width() == 0;
        let value = self.compile(
            node,
            &Context {
                can_print: context.can_print || is_key_constant,
                ..expression.context.clone()
            },
        )?;
        if !value.footprint.vars.is_empty() || !value.footprint.primes.is_empty() {
            return unsupported("TLCCache of an expression that reads variables");
        }
        // What the cache holds then depends on the order in which TLC first evaluates e, with one
        // cache for every worker.
        self.is_cached |= value.footprint.width() > 0;
        let footprint = key.footprint.merge(&if is_key_constant {
            value.footprint.without_slots(&[super::PRINT_SLOT])
        } else {
            value.footprint
        });
        let (evaluate_key, evaluate_value) = (key.eval, value.eval);
        Ok(leaf(
            eval(move |machine| {
                let key = evaluate_key(machine)?;
                let hash = machine
                    .fingerprints
                    .get_state(&machine.store, &[key], &[0])?;
                if let Some(&value) = machine.tlc_caches.get(&(node, hash)) {
                    return Ok(value);
                }
                let value = evaluate_value(machine)?;
                machine.tlc_caches.insert((node, hash), value);
                Ok(value)
            }),
            footprint,
        ))
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

    // The arguments of SubSeq applied in place, rather than through a parameter.
    fn sub_seq_arguments(&self, operand: &Operand) -> Option<Vec<NodeId>> {
        if operand.is_param || operand.slot.is_some() {
            return None;
        }
        let NodeKind::Apply { name, args } = &self.node(operand.node).1 else {
            return None;
        };
        let Resolution::Builtin(index) = name.resolution else {
            return None;
        };
        (self.builtin_name(index) == "SubSeq" && args.len() == 3).then(|| args.clone())
    }

    // `SubSeq(s, m, n) = SubSeq(t, k, l)`, as IsPrefix asks it, compared in place: each SubSeq's
    // arguments are evaluated and checked as SubSeq checks them, the left's first, and the parts
    // compared as the equality of the two tuples compares them, without building either.
    fn compile_sub_seqs_equal(
        &mut self,
        left: &Operand,
        right: &Operand,
        is_equal: bool,
    ) -> Compiling<Option<Compiled>> {
        let (Some(left_arguments), Some(right_arguments)) =
            (self.sub_seq_arguments(left), self.sub_seq_arguments(right))
        else {
            return Ok(None);
        };
        let mut footprint = Footprint::default();
        let mut arguments = Vec::new();
        for (nodes, context) in [
            (left_arguments, &left.context),
            (right_arguments, &right.context),
        ] {
            for node in nodes {
                let compiled = self.compile(node, context)?;
                footprint = footprint.merge(&compiled.footprint);
                arguments.push(compiled.eval);
            }
        }
        let compare = eval(move |machine| {
            let mut slices = [(0, 0, 0); 2];
            for (slice, evaluators) in slices.iter_mut().zip(arguments.chunks(3)) {
                let sequence = evaluators[0](machine)?;
                let start = evaluators[1](machine)?;
                let end = evaluators[2](machine)?;
                let (from, to) = bridged::sub_seq_bounds(machine, sequence, start, end)?;
                *slice = (sequence, from, to);
            }
            let [(left, left_from, left_to), (right, right_from, right_to)] = slices;
            let store = &mut machine.store;
            let is_plain = |store: &Store, sequence: Id| {
                store.kind_of(sequence) == KIND_TUPLE && !store.is_kept_lazy(sequence)
            };
            let equals = if is_plain(store, left) && is_plain(store, right) {
                // Tuples of other lengths differ; of one length, they equal where their first
                // elements to differ do, or are one tuple.
                left_to - left_from == right_to - right_from && {
                    let length = left_to - left_from;
                    let differing = (0..length).find(|&at| {
                        store.get_range_value(left, left_from + at)
                            != store.get_range_value(right, right_from + at)
                    });
                    match differing {
                        Some(at) => store.equals(
                            store.get_range_value(left, left_from + at),
                            store.get_range_value(right, right_from + at),
                        )?,
                        None => true,
                    }
                }
            } else {
                let left = bridged::sub_seq_of(machine, left, left_from, left_to);
                let right = bridged::sub_seq_of(machine, right, right_from, right_to);
                machine.store.equals_asked(left, right)?
            };
            Ok(bool_id(equals == is_equal))
        });
        Ok(Some(Compiled {
            is_boolean: true,
            ..leaf(compare, footprint)
        }))
    }

    fn compile_native_builtin(
        &mut self,
        name: &str,
        flags: i32,
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
                if let Some(compared) =
                    self.compile_sub_seqs_equal(&operands[0], &operands[1], name == "=")?
                {
                    return Ok(Some(compared));
                }
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                let (left, right) = Self::compared(left, right);
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
                // An interval's membership compares with its bounds, which needs no fast path.
                let is_interval = set.interval.is_some();
                if set.member.is_none()
                    && set.infinite.is_none()
                    && !is_interval
                    && set.footprint.width() == 0
                {
                    return Ok(Some(predicate_node(
                        Predicate::Member {
                            element: Leaf::of(&element),
                            set: Leaf::of(&set),
                            is_in,
                        },
                        footprint,
                    )));
                }
                let fast = (!is_interval)
                    .then(|| fused::member_const(&element, &set, is_in))
                    .flatten();
                let evaluate = fast.unwrap_or_else(|| {
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
                    is_costly: set.member.is_some() || is_interval || set.footprint.width() > 0,
                    is_boolean: true,
                    ..leaf(evaluate, footprint)
                }
            }
            "\\subseteq" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                self.compile_subseteq(&left, &right)
            }
            "\\cup" | "\\cap" | "\\" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                let has_effect = operands.iter().any(|operand| {
                    self.may_have_effect_in(operand.node, &operand.context, &mut HashSet::new())
                });
                return self.compile_set_operation(name, &left, &right, has_effect);
            }
            "SUBSET" => {
                arity(1)?;
                let base = self.operand(&operands[0])?;
                self.compile_subset(&base)
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
                // TLC keeps UNION S lazy unless S and its elements are set enumerations, and then
                // streams each element of S in turn (`UnionValue.Enumerator`). An element streams
                // as its normalized set does unless it streams apart itself, which the engine,
                // holding it as an id, follows only where S is a set enumeration that holds it as
                // written.
                let base = match &outer.element_references {
                    Some(elements) => {
                        let elements = elements.clone();
                        Some(Arc::new(move |machine: &mut Machine<'_>| {
                            let mut lazies = Vec::with_capacity(elements.len());
                            for element in &elements {
                                lazies.push(element(machine)?);
                            }
                            Ok(Lazy::Enumeration(lazies))
                        }) as Reference)
                    }
                    None => outer
                        .are_elements_in_order
                        .then(|| reference_of(&outer))
                        .flatten(),
                };
                let reference = base.filter(|_| !is_enumerated).map(|base| {
                    Arc::new(move |machine: &mut Machine<'_>| {
                        Ok(Lazy::Union(Box::new(base(machine)?)))
                    }) as Reference
                });
                Compiled {
                    is_normalized: is_enumerated,
                    is_enumerated,
                    // Its elements are those of S's elements.
                    are_elements_in_order: outer.are_elements_of_elements_in_order,
                    is_reference_exact: reference.is_some(),
                    reference,
                    member: only.as_ref().map(|only| self.member_test(only)),
                    parts: only.as_ref().map(Self::parts_of),
                    ..compiled
                }
            }
            "DOMAIN" => {
                arity(1)?;
                // A recursive function's domain, which TLC reads without applying it.
                let operand = &operands[0];
                if operand.slot.is_none()
                    && let Some(recursive) =
                        self.get_applied_recursive_function(operand.node, &operand.context)?
                {
                    return Ok(Some(recursive.domain.clone()));
                }
                let function = self.operand(operand)?;
                let domain = unary(
                    &function,
                    |machine, function| {
                        if lazy_function::is_lazy(machine, function) {
                            return Err(lazy_function::DOMAIN);
                        }
                        if !is_function_kind(machine.store.kind_of(function)) {
                            return Err(Bail("DOMAIN of a non-function"));
                        }
                        Ok(machine.store.domain_of(function))
                    },
                    true,
                );
                // The domain of a function TLC keeps lazy is its bound's set
                // (`FcnLambdaValue.getDomain`), which the engine has no value for but can test.
                // TLC evaluates the function to make it.
                let function = function.eval;
                let function_part = function.clone();
                Compiled {
                    parts: Some(super::parts(move |machine| {
                        function_part(machine).map(|_| ())
                    })),
                    member: Some(super::member(move |machine, element| {
                        let function = function(machine)?;
                        if lazy_function::is_lazy(machine, function) {
                            return lazy_function::is_in_domain(machine, function, element);
                        }
                        if !is_function_kind(machine.store.kind_of(function)) {
                            return Err(Bail("DOMAIN of a non-function"));
                        }
                        let domain = machine.store.domain_of(function);
                        machine.store.is_member(element, domain)
                    })),
                    ..domain
                }
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
                        "\\div" if flags & Builtin::NATURALS_METHOD != 0 => {
                            |left: i64, right: i64| {
                                naturals_divide(left, right).ok_or(Bail("division by zero"))
                            }
                        }
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
                            if base == 0 && exponent == 0 {
                                return Err(Bail("zero to the power of zero"));
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
                    is_in_order: true,
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
                // The native checker writes a value as TLC does one built as the operand writes
                // it.
                let construction = if self.is_native {
                    self.construction_of(&operands[0])
                } else {
                    Construction::Held
                };
                let is_written = self.may_write_held(operands[0].node, false);
                let evaluate = value.eval.clone();
                Compiled {
                    is_costly: true,
                    ..leaf(
                        eval(move |machine| {
                            let value = evaluate(machine)?;
                            check_written(machine, is_written)?;
                            to_string(machine, value, &construction)
                        }),
                        value.footprint.clone(),
                    )
                }
            }
            "TLCModelValue" => {
                arity(1)?;
                self.is_ranking = true;
                let name = self.operand(&operands[0])?;
                unary(&name, model_value, false)
            }
            "Len" => {
                arity(1)?;
                let sequence = self.operand(&operands[0])?;
                unary(
                    &sequence,
                    // Sequences.Len takes a string too, by its UTF-16 units.
                    |machine, sequence| {
                        if machine.store.kind_of(sequence) == KIND_STRING {
                            let length = machine.store.text_of(sequence).len();
                            return machine.store.int(length as i64);
                        }
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
                    // Sequences.Tail takes a string too, dropping its first UTF-16 unit.
                    |machine, sequence| {
                        if machine.store.kind_of(sequence) == KIND_STRING {
                            let text = machine.store.text_of(sequence);
                            if text.is_empty() {
                                return Err(Bail("Tail of an empty sequence"));
                            }
                            let tail = text[1..].to_vec();
                            return Ok(machine.store.str(&tail));
                        }
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
                    // Seq(S) is never empty, and TLC can't enumerate it.
                    reference: Some(Arc::new(|_| Ok(Lazy::Infinite("Seq")))),
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
                arity(2)?;
                // Assert(P, message) is TRUE when P holds. TLC evaluates the message too, as it
                // does any Java method's arguments, whose effects and failures show. When P
                // doesn't hold, TLC fails with the message, which the interpreter reports.
                let condition = self.boolean_operand(&operands[0])?;
                let message = self.operand(&operands[1])?;
                let (test, evaluate_message) = (condition.eval.clone(), message.eval);
                Compiled {
                    is_boolean: true,
                    ..leaf(
                        eval(move |machine| {
                            let holds = test(machine)?;
                            evaluate_message(machine)?;
                            if holds == TRUE {
                                Ok(TRUE)
                            } else {
                                Err(Bail("an assertion failed"))
                            }
                        }),
                        condition.footprint.merge(&message.footprint),
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
                    // TLC sizes a set of functions, records or tuples by its parts
                    // (`Lazy::size`): an empty part empties it before TLC asks anything of a part
                    // it can't enumerate, as in `[Nat -> {}]`, or of one too large to.
                    // A power set of a set the engine holds is counted as it was, by building it.
                    None if set.reference.is_some()
                        && !set.is_normalized
                        && !set
                            .subset_base
                            .as_ref()
                            .is_some_and(|base| base.is_normalized) =>
                    {
                        let reference = set.reference.clone().expect("a reference");
                        Compiled {
                            is_costly: true,
                            ..leaf(
                                eval(move |machine| {
                                    let size = reference(machine)?.size(machine)?;
                                    machine.store.int(size as i64)
                                }),
                                set.footprint.clone(),
                            )
                        }
                    }
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
                    |machine, key, value| {
                        let function = machine.store.function_of_sorted(&[key], &[value]);
                        Ok(machine.store.mark_built_as_function(function))
                    },
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
                        let function = machine.store.function_of(&keys, &values)?;
                        Ok(machine.store.mark_built_as_function(function))
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
        has_effect: bool,
    ) -> Compiling<Option<Compiled>> {
        // A set the engine tests for membership without building it, such as Nat \ {0}, combines
        // the operands' tests.
        let is_lazy = |set: &Compiled| set.infinite.is_some() || set.member.is_some();
        // Whether TLC's value is Reducible, a set enumeration or an interval, where the compiled
        // set tells: a set with a membership test, such as DOMAIN f, may be either.
        let is_reducible = |set: &Compiled| {
            if set.is_enumerated || set.interval.is_some() || set.is_reducible {
                Some(true)
            } else {
                (set.infinite.is_some() || set.is_irreducible).then_some(false)
            }
        };
        // TLC reduces a union of two Reducible sets, an intersection with one, and a difference
        // from one (OPCODE_cup, OPCODE_cap, OPCODE_setdiff).
        let is_reduced = match name {
            "\\cup" => is_reducible(left) == Some(true) && is_reducible(right) == Some(true),
            "\\cap" => is_reducible(left) == Some(true) || is_reducible(right) == Some(true),
            _ => is_reducible(left) == Some(true),
        };
        // TLC keeps the union of a set it can't reduce with any set as a SetCupValue, and an
        // intersection or a difference it doesn't reduce as a SetCapValue or a SetDiffValue.
        let is_irreducible = match name {
            "\\cup" => is_reducible(left) == Some(false) || is_reducible(right) == Some(false),
            "\\cap" => is_reducible(left) == Some(false) && is_reducible(right) == Some(false),
            _ => is_reducible(left) == Some(false),
        };
        // TLC evaluates both operands, left first, before it tests either for an element
        // (OPCODE_cup, OPCODE_cap, OPCODE_setdiff), so a test that one operand decides runs the
        // other's parts too.
        // TLC then reduces the operation where an operand is Reducible, testing one operand's
        // elements in the other, so a test of the result runs those tests too.
        let reduction = self.reduction(
            name,
            left,
            right,
            (is_reducible(left), is_reducible(right)),
            has_effect,
        );
        let operand_parts =
            self.once_a_round(vec![Self::parts_of(left), Self::parts_of(right), reduction]);
        let lazy_member = if is_lazy(left) || is_lazy(right) {
            let (left_member, right_member) = (self.member_test(left), self.member_test(right));
            let tested = match name {
                // TLC tests the set enumeration it reduced an intersection or a difference to
                // (`Reducible.cap` and `diff`): the elements of the Reducible operand, the left
                // one where both are, that the other holds or lacks.
                "\\cap" | "\\" if is_reduced => {
                    let (enumerated, held_by) =
                        if name == "\\cap" && is_reducible(left) != Some(true) {
                            (right.eval.clone(), left_member)
                        } else {
                            (left.eval.clone(), right_member)
                        };
                    let is_kept_where_held = name == "\\cap";
                    member(move |machine, element| {
                        let set = evaluate_set(machine, &enumerated, "expected a set")?;
                        let mut kept = Vec::new();
                        for index in 0..machine.store.size_of(set) {
                            let held = machine.store.element_at(set, index);
                            if held_by(machine, held)? == is_kept_where_held {
                                kept.push(held);
                            }
                        }
                        let reduced = machine.store.set_of_sorted(&kept);
                        machine.store.is_member(element, reduced)
                    })
                }
                // TLC makes the union of a Reducible set and another with the Reducible one first,
                // and SetCupValue.member asks its first set first, so comparing the element with
                // that set's elements fails first. It builds the union of two Reducible sets
                // (OPCODE_cup: `Reducible.cup`). Where it may build the union or take the right
                // set first, the engine stops.
                "\\cup" => match (is_reducible(left), is_reducible(right)) {
                    (Some(false), Some(true)) => member(move |machine, element| {
                        Ok(right_member(machine, element)? || left_member(machine, element)?)
                    }),
                    (_, Some(false)) => member(move |machine, element| {
                        Ok(left_member(machine, element)? || right_member(machine, element)?)
                    }),
                    _ => member(|_, _| {
                        Err(Bail(
                            "a membership in a union TLC may build or order either way",
                        ))
                    }),
                },
                "\\cap" => member(move |machine, element| {
                    Ok(left_member(machine, element)? && right_member(machine, element)?)
                }),
                _ => member(move |machine, element| {
                    Ok(left_member(machine, element)? && !right_member(machine, element)?)
                }),
            };
            let parts = operand_parts.clone();
            // An operand's test may evaluate it again after its parts, which an effect shows.
            Some(if has_effect {
                member(|_, _| {
                    Err(Bail(
                        "a membership in a set operation on an operand with effects",
                    ))
                })
            } else {
                // A name bound to an operand with effects, as LET binds one, shows them only as
                // they run.
                member(move |machine, element| {
                    let before = machine.effects();
                    machine.run_parts(&parts)?;
                    let is_member = tested(machine, element)?;
                    if machine.effects() != before {
                        return Err(Bail(
                            "a membership in a set operation on an operand with effects",
                        ));
                    }
                    Ok(is_member)
                })
            })
        } else {
            None
        };
        let lazy_parts = lazy_member.as_ref().map(|_| operand_parts.clone());
        // TLC enumerates the left set of an intersection or a difference where it can, testing
        // each element for membership in the right one (SetCapValue.elements and
        // SetDiffValue.elements), so a set enumeration it keeps in order keeps that order.
        // A set TLC keeps lazy with a part it can't enumerate, such as Int \X {}, which the
        // engine doesn't build: TLC reduces an intersection with it to the other operand's
        // elements it holds (`Reducible.cap`).
        let is_unbuilt = |set: &Compiled| set.infinite.is_some() || set.has_infinite_part;
        let tested_from = if name != "\\cup" && !is_unbuilt(left) && is_unbuilt(right) {
            Some((left, right))
        } else if name == "\\cap"
            && is_unbuilt(left)
            && left.infinite.is_none()
            && !is_unbuilt(right)
            && is_reducible(right) == Some(true)
        {
            Some((right, left))
        } else {
            None
        };
        if let Some((enumerated, tested)) = tested_from.filter(|(set, _)| set.is_normalized) {
            let right_member = self.member_test(tested);
            let left_eval = enumerated.eval.clone();
            let is_kept_in_right = name == "\\cap";
            // TLC evaluates both operands, left first, before it tests one's elements in the
            // other, so an effect of either may show in another order than the engine's.
            let is_ordered = !has_effect || (left.infinite.is_none() && right.infinite.is_some());
            // TLC evaluates both operands, left first, whether or not there are elements to test:
            // the one whose elements it tests is evaluated as is, and the other as its parts.
            let is_left_enumerated = std::ptr::eq(enumerated, left);
            let first = (!is_left_enumerated).then(|| Self::parts_of(left));
            let second = is_left_enumerated.then(|| Self::parts_of(right));
            return Ok(Some(Compiled {
                is_costly: true,
                is_reducible: is_reduced,
                member: lazy_member,
                parts: lazy_parts,
                ..leaf(
                    eval(move |machine| {
                        if !is_ordered {
                            return Err(Bail(
                                "a set operation TLC reduces on an operand with effects",
                            ));
                        }
                        if let Some(first) = &first {
                            machine.run_parts(first)?;
                        }
                        let left = left_eval(machine)?;
                        if let Some(second) = &second {
                            machine.run_parts(second)?;
                        }
                        let set = expect_set(machine, left, "expected a set")?;
                        let mut kept = Vec::new();
                        for index in 0..machine.store.size_of(set) {
                            let element = machine.store.element_at(set, index);
                            if right_member(machine, element)? == is_kept_in_right {
                                kept.push(element);
                            }
                        }
                        Ok(machine.store.set_of_sorted(&kept))
                    }),
                    left.footprint.merge(&right.footprint),
                )
            }));
        }
        if left.infinite.is_some() || right.infinite.is_some() {
            // A combination of sets TLC can't enumerate is one it only tests for membership.
            let operator = match name {
                "\\cup" => Operator::Union,
                "\\cap" => Operator::Intersection,
                _ => Operator::Difference,
            };
            return Ok(Some(Compiled {
                is_normalized: false,
                infinite: Some("Combined"),
                is_reducible: is_reduced,
                member: lazy_member,
                parts: lazy_parts,
                reference: combine_references(&[left, right], move |machine, mut sets| {
                    let right = sets.pop().expect("the right set");
                    let left = sets.pop().expect("the left set");
                    Lazy::combine(machine, operator, left, right)
                }),
                ..leaf(
                    eval(|_| Err(Bail("an enumerated infinite set"))),
                    left.footprint.merge(&right.footprint),
                )
            }));
        }
        // TLC builds a union, an intersection or a difference with an operand that isn't a set
        // lazily or element by element (OPCODE_cup, OPCODE_cap, OPCODE_setdiff), and fails only
        // where it tests that operand for an element.
        let operation: Binary = match name {
            "\\cup" => |machine, left, right| {
                let (left, right) = expect_sets(machine, left, right)?;
                machine.store.union(left, right)
            },
            "\\cap" => |machine, left, right| {
                let (left, right) = expect_sets(machine, left, right)?;
                machine.store.intersection(left, right)
            },
            _ => |machine, left, right| {
                let (left, right) = expect_sets(machine, left, right)?;
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
            // TLC streams a `\cup` it keeps lazy from both sets, duplicates and all.
            is_in_order: (is_normalized || name != "\\cup")
                && left.is_in_order
                && right.is_in_order,
            are_elements_in_order: left.are_elements_in_order && right.are_elements_in_order,
            are_elements_of_elements_in_order: left.are_elements_of_elements_in_order
                && right.are_elements_of_elements_in_order,
            is_reference_exact: reference.is_some()
                && [left, right]
                    .iter()
                    .all(|set| set.is_in_order || set.is_reference_exact),
            // TLC keeps an operation it doesn't reduce lazy (SetCupValue, SetCapValue,
            // SetDiffValue), and with it the operands' parts.
            has_infinite_part: !is_reduced && (left.may_be_infinite() || right.may_be_infinite()),
            member: lazy_member,
            parts: lazy_parts,
            reference,
            is_irreducible,
            is_reducible: is_reduced,
            ..binary(left, right, operation, true, false)
        }))
    }

    // The tests TLC makes as it reduces `left name right` (`Tool`'s OPCODE_cup, OPCODE_cap and
    // OPCODE_setdiff): `Reducible.cap` and `diff` test each element of a set enumeration or an
    // interval in the other operand, and `cup` each element of another one in itself unless it is
    // empty. Where the compiled operand doesn't tell whether TLC's value is Reducible
    // (`reducible`), the tests of each case run, since a test that fails stops the engine and TLC
    // makes no test the engine doesn't.
    fn reduction(
        &self,
        name: &str,
        left: &Compiled,
        right: &Compiled,
        reducible: (Option<bool>, Option<bool>),
        has_effect: bool,
    ) -> Parts {
        // Each run of tests: the operand whose elements TLC tests, whether its value is known to
        // be Reducible, the other operand's test, and the operand that makes no test where it is
        // empty.
        let mut runs: Vec<(Eval, bool, Member, Option<Eval>)> = Vec::new();
        let (left_reducible, right_reducible) = reducible;
        match name {
            "\\cup" => {
                if left_reducible != Some(false) && right_reducible != Some(false) {
                    runs.push((
                        right.eval.clone(),
                        right_reducible == Some(true),
                        self.member_test(left),
                        Some(left.eval.clone()),
                    ));
                }
            }
            _ => {
                if left_reducible != Some(false) {
                    runs.push((
                        left.eval.clone(),
                        left_reducible == Some(true),
                        self.member_test(right),
                        None,
                    ));
                }
                if name == "\\cap" && left_reducible != Some(true) && right_reducible != Some(false)
                {
                    runs.push((
                        right.eval.clone(),
                        right_reducible == Some(true),
                        self.member_test(left),
                        None,
                    ));
                }
            }
        }
        if runs.is_empty() {
            return super::parts(|_| Ok(()));
        }
        // The tests evaluate an operand its parts have evaluated, which an effect shows.
        if has_effect {
            return super::parts(|_| {
                Err(Bail(
                    "a set operation TLC reduces on an operand with effects",
                ))
            });
        }
        super::parts(move |machine| {
            let before = machine.effects();
            for (enumerated, is_reducible, tested, unless_empty) in &runs {
                if let Some(receiver) = unless_empty {
                    let receiver = receiver(machine)?;
                    if machine.store.kind_of(receiver) != KIND_SET
                        || machine.store.size_of(receiver) == 0
                    {
                        continue;
                    }
                }
                // A value the engine holds as no set, where TLC's may be Reducible or not, is
                // one TLC keeps lazy, which it doesn't reduce.
                let set = enumerated(machine)?;
                if machine.store.kind_of(set) != KIND_SET {
                    if *is_reducible {
                        return Err(Bail("a set TLC reduces that the engine holds as no set"));
                    }
                    continue;
                }
                for index in 0..machine.store.size_of(set) {
                    let element = machine.store.element_at(set, index);
                    tested(machine, element)?;
                }
            }
            // A name bound to an operand with effects, as LET binds one, shows them only as they
            // run.
            if machine.effects() != before {
                return Err(Bail(
                    "a set operation TLC reduces on an operand with effects",
                ));
            }
            Ok(())
        })
    }
}
// ToString(v): TLC's text of v built as `construction` says (`write_constructed`), as a string
// TLC ranks as it makes it.
fn to_string(machine: &mut Machine<'_>, value: Id, construction: &Construction) -> Outcome<Id> {
    let mut text = Vec::new();
    if !write_constructed(&machine.store, value, construction, false, &mut text) {
        return Err(Bail(
            "ToString of a value whose text depends on how TLC built it",
        ));
    }
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

// The model value of a name, which TLC makes once, ranking the name as it does
// (`TLCExt.tlcModelValue`).
fn model_value(machine: &mut Machine<'_>, name: Id) -> Outcome<Id> {
    if machine.store.kind_of(name) != KIND_STRING {
        return Err(Bail("TLCModelValue of a value that isn't a string"));
    }
    // The name's string, which \o may have made unranked, takes the rank too, as the interpreter's
    // strings read it.
    let text = machine.store.text_of(name).to_vec();
    machine.store.rank_text(&text);
    Ok(machine.store.model(&text))
}

/// The prefix of the names of TLC's named registers (`TLCGetSet.NAMED_REGISTER_PREFIX`).
const NAMED_REGISTER_PREFIX: &str = "s:";

/// The prefix of a key of TLCGet and TLCSet that names a Java system property, whose value
/// `System.getProperty` gives with the key as the default.
const JAVA_PROPERTY_PREFIX: &str = "-D";

// Print's or PrintT's arguments, each evaluated in turn as TLC does, where one with a reference
// (`checked`) is built as TLC holds it, and enumerated only once TLC's `toString` of each such
// argument, in turn, is found to print it (`Lazy::check_printed`). Where the engine can't tell,
// it declines if `is_unsure_declined` and otherwise enumerates the set. An argument only printed
// (all but Print's second, which is its value) that TLC finds empty, or the one function of an
// empty domain, from its parts, is that, where enumerating it may ask a part TLC never asks.
/// What writing a value stops with where the value may hold a set TLC prints by its parts, which
/// the store holds as its enumeration (`Program::holds_collapsed`).
pub(crate) const COLLAPSED_WRITE: Bail =
    Bail("unsupported: writing a value that may hold a set TLC prints by its parts");

fn check_written(machine: &Machine<'_>, is_written: bool) -> Outcome<()> {
    if is_written && machine.program.holds_collapsed() {
        return Err(COLLAPSED_WRITE);
    }
    Ok(())
}

fn evaluate_printed(
    machine: &mut Machine<'_>,
    evaluators: &[Eval],
    checked: &[Option<Reference>],
    is_unsure_declined: bool,
    is_print: bool,
) -> Outcome<Vec<Id>> {
    let mut lazies = Vec::with_capacity(evaluators.len());
    let mut values = Vec::with_capacity(evaluators.len());
    for (evaluate, reference) in evaluators.iter().zip(checked) {
        match reference {
            Some(reference) => {
                lazies.push(Some(reference(machine)?));
                values.push(None);
            }
            None => {
                lazies.push(None);
                values.push(Some(evaluate(machine)?));
            }
        }
    }
    for (position, lazy) in lazies.iter().enumerate() {
        let Some(lazy) = lazy else {
            continue;
        };
        let is_only_printed = !is_print || position == 0;
        match lazy.check_printed(machine) {
            Err(Bail(reason)) if reason != UNSIZED_PRINT && !is_unsure_declined => {}
            Ok(PrintedSet::Empty) if is_only_printed => values[position] = Some(EMPTY_SET),
            Ok(PrintedSet::OfEmptyFunction) if is_only_printed => {
                values[position] = Some(machine.store.set_of(&[EMPTY_TUPLE])?);
            }
            checked => {
                checked?;
            }
        }
    }
    evaluators
        .iter()
        .zip(values)
        .map(|(evaluate, value)| value.map_or_else(|| evaluate(machine), Ok))
        .collect()
}

// Prints the values of a Print or PrintT, with TLC's text of each where the native checker knows
// how TLC built it.
fn push_prints(
    machine: &mut Machine<'_>,
    values: Vec<Id>,
    constructions: Option<&[Construction]>,
) -> Outcome<()> {
    let texts = match constructions {
        Some(constructions) => values
            .iter()
            .zip(constructions)
            .map(|(&value, construction)| {
                let mut text = Vec::new();
                write_constructed(&machine.store, value, construction, true, &mut text)
                    .then_some(text)
            })
            .collect(),
        None => {
            for &value in &values {
                if !is_printable(&machine.store, value) {
                    return Err(Bail(
                        "printing a value whose text depends on how TLC built it",
                    ));
                }
                // The addon hands what it prints to the interpreter, whose encoding has no Nat,
                // Int or STRING.
                if machine.store.holds_lazy_function(value) {
                    return Err(UNENCODABLE);
                }
            }
            None
        }
    };
    machine
        .output
        .push(Printed::Values(Prints { values, texts }));
    Ok(())
}

/// Where the JVM and its libraries name the system properties they set themselves.
const JVM_PROPERTY_NAMESPACES: [&str; 16] = [
    "java.", "javax.", "jdk.", "sun.", "os.", "user.", "file.", "line.", "path.", "native.",
    "stdout.", "stderr.", "awt.", "http.", "https.", "ftp.",
];

// Where TLC keeps a register's value: under a natural number, or under a name that starts with
// "s:".
enum RegisterKey {
    Numbered(usize),
    Named(Id),
}

fn get_register_key(store: &Store, key: Id) -> Option<RegisterKey> {
    match store.kind_of(key) {
        KIND_INT if store.int_of(key) >= 0 => {
            Some(RegisterKey::Numbered(store.int_of(key) as usize))
        }
        KIND_STRING
            if String::from_utf16_lossy(store.text_of(key)).starts_with(NAMED_REGISTER_PREFIX) =>
        {
            Some(RegisterKey::Named(key))
        }
        _ => None,
    }
}

fn get_register(machine: &mut Machine<'_>, key: Id) -> Outcome<Id> {
    let registers = &machine.registers;
    let value = match get_register_key(&machine.store, key) {
        Some(RegisterKey::Numbered(index)) => registers.numbered.get(index).copied().flatten(),
        Some(RegisterKey::Named(name)) => registers
            .named
            .iter()
            .find(|&&(named, _)| named == name)
            .map(|&(_, value)| value),
        None if machine.store.kind_of(key) == KIND_STRING => {
            // A key the spec computes may name a system property, which the search doesn't keep
            // either.
            return Err(Bail("unsupported: TLCGet of a key the search doesn't keep"));
        }
        None => return Err(Bail("TLCGet of a key that isn't a natural number")),
    };
    value.ok_or(Bail("TLCGet of a register TLC hasn't set"))
}

fn set_register(machine: &mut Machine<'_>, key: Id, value: Id) -> Outcome<()> {
    let registers = &mut machine.registers;
    registers.writes += 1;
    match get_register_key(&machine.store, key) {
        Some(RegisterKey::Numbered(index)) => {
            if registers.numbered.len() <= index {
                registers.numbered.resize(index + 1, None);
            }
            registers.numbered[index] = Some(value);
        }
        Some(RegisterKey::Named(name)) => {
            match registers.named.iter_mut().find(|(named, _)| *named == name) {
                Some(entry) => entry.1 = value,
                None => registers.named.push((name, value)),
            }
        }
        None if machine.store.kind_of(key) == KIND_STRING => {
            let text = String::from_utf16_lossy(machine.store.text_of(key));
            if text == "exit" && value == TRUE {
                registers.is_exit = true;
            } else if !(matches!(text.as_str(), "exit" | "pause") && value != TRUE) {
                return Err(Bail(
                    "unsupported: TLCSet of a key that stops or configures TLC",
                ));
            }
        }
        None => return Err(Bail("TLCSet of a key that isn't a natural number")),
    }
    Ok(())
}

// A field of TLCGet("config").
enum Field {
    Text(String),
    Bool(bool),
    Int(i64),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::Program;
    use tla_values::Store;

    fn to_text(store: &mut Store, id: Id) -> Option<String> {
        let program = Program::default();
        let mut machine = Machine::new(&program, std::mem::take(store));
        let result = to_string(&mut machine, id, &Construction::Held)
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
