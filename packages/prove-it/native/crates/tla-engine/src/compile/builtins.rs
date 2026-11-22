//! The builtins, as `compileBuiltin` and `compileNativeBuiltin` compile them. The pure builtins
//! the TypeScript engine runs in the interpreter (`PURE_BUILTINS`) are `bridged.rs`'s, except
//! ToString, which prints as the interpreter's printer does (`format_value`).

use std::collections::HashSet;
use std::sync::Arc;

use tla_ir::{Bound, Builtin, EvaluatedDefinition, Index, NodeId, NodeKind, Pattern, Resolution};
use tla_values::json;
use tla_values::print::{Construction, is_printable, write_constructed};
use tla_values::store::{
    EMPTY_SET, EMPTY_TUPLE, FALSE, INT, KIND_FUNCTION, KIND_INT, KIND_MODEL, KIND_SET, KIND_STRING,
    KIND_TUPLE, NAT, Outcome, STRINGS, TRUE, is_function_kind,
};
use tla_values::transfer::UNENCODABLE;
use tla_values::{
    Bail, Id, JAVA_PROPERTY_PREFIX, JVM_PROPERTY_NAMESPACES, NAMED_REGISTER_PREFIX, Store,
    is_settable_property, is_unknown_tlc_get_key,
};

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

// Engine limits emitted when an infinite built-in value is enumerated.
pub(crate) const ENUMERATED_INT: &str = "enumerated Int";
/// Why the engine stops at a model value TLCModelValue makes of a name TLC numbers otherwise than
/// the IR (`UniqueString.tok`), where it fingerprints it: TLC doesn't fail there.
pub(crate) const UNNUMBERED_MODEL_VALUE: &str =
    "unsupported: TLCModelValue of a name whose number TLC fingerprints the engine doesn't know";
pub(crate) const ENUMERATED_NAT: &str = "enumerated Nat";
pub(crate) const ENUMERATED_STRING: &str = "enumerated STRING";
pub(crate) const ENUMERATED_SEQ: &str = "enumerated Seq(S)";

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
const PURE_BUILTINS: [&str; 21] = [
    "Warshall@TransitiveClosure",
    "Warshall",
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

pub(crate) const MAXIMUM_POWER_SET: u32 = 20;

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

/// A union, an intersection or a difference past `TLCGlobals.setBound` elements, which TLC may
/// reduce or keep lazy.
const UNKNOWN_OPERATION_PAST_SET_BOUND: &str =
    "unsupported: a set operation of more than TLCGlobals.setBound elements TLC may reduce";

/// A union, an intersection or a difference with an operand that isn't a set, which TLC keeps
/// lazy or builds element by element, failing only where it tests that operand for an element.
pub(crate) const NON_SET_OPERAND: &str = "a set operation on a value that isn't a set";

// Whether TLC's value is Reducible, a set enumeration or an interval, where the compiled set
// tells: a set with a membership test, such as DOMAIN f, may be either.
fn reducibility(set: &Compiled) -> Option<bool> {
    if set.is_enumerated || set.interval.is_some() || set.is_reducible {
        Some(true)
    } else {
        (set.infinite.is_some() || set.is_irreducible).then_some(false)
    }
}

// `ValueVec.search` of a SetEnumValue TLC holds as written, unnormalized: each written element
// in turn asks `equals` of the value, up to the first that holds it.
fn written_holds(machine: &mut Machine<'_>, written: &[Id], value: Id) -> Outcome<bool> {
    for &held in written {
        if machine.store.equals_asked(held, value)? {
            return Ok(true);
        }
    }
    Ok(false)
}

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

/// What TLCEvalDefinition stops with where TLC finds no definition without parameters to
/// evaluate, or is given a name that isn't a string (`TLCExt.tlcDefByName`).
pub(crate) const DEFINITION_NOT_EVALUATED: &str =
    "TLCEvalDefinition of a name TLC finds no definition without parameters of";

/// What ToTrace stops with where the spec names CounterExample, whose record the engine holds as
/// any other.
pub(crate) const TO_TRACE_OF_RECORD: &str =
    "unsupported: ToTrace of a value that may be TLC's CounterExample";

/// What TLCEval of a function the engine keeps lazy stops with: TLC builds it
/// (`FcnLambdaValue.toFcnRcd`), which fails over a domain it can't enumerate, as Nat, and the
/// evaluator of failures words that, or finds none.
pub(crate) const TLC_EVAL_OF_LAZY_FUNCTION: &str = "TLCEval of a function TLC keeps lazy";

/// What ToTrace of a value that isn't the record CounterExample builds stops with.
pub(crate) const TO_TRACE_OF_NON_COUNTER_EXAMPLE: &str =
    "ToTrace of a value that isn't a CounterExample";

fn utf16(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
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

pub(crate) fn power_set(machine: &mut Machine<'_>, set: Id) -> Outcome<Id> {
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

// The failures of the Json module's operators TLC reports, which the replay words.
pub(crate) const PRINTED_KEPT_LAZY: &str =
    "printing records in a function TLC may keep lazy, evaluated as the function of an application";
pub(crate) const JSON_FILE_NOT_STRING: &str = "a Json operator's file that isn't a string";
pub(crate) const INDEX_REPLACED: &str = "an operator a TLCOverrides index's Java method replaces";
pub(crate) const JSON_FILE_UNREAD: &str = "a Json operator's file that can't be read";
pub(crate) const JSON_FILE_UNWRITTEN: &str = "a Json operator's file that can't be written";
pub(crate) const ND_JSON_SERIALIZE_NOT_SEQUENCE: &str =
    "ndJsonSerialize of a value that isn't a sequence";
pub(crate) const JSON_SERIALIZE_NOT_SEQUENCE: &str =
    "JsonSerialize of a value that isn't a sequence or a record";

impl Compiler<'_> {
    /// TLCExt's Trace (`Machine::trace`), whose value is a function of the behavior the search
    /// keeps, the level, which tells the state it expands from a successor, and the state. TLC
    /// gives each state's record with its variables in its order, unnormalized, and prints it so
    /// (`RecordValue(TLCState)`), where the engine's records are in the order of their fields: the
    /// engine stops where the two differ, and where the search doesn't keep the behavior, so that
    /// a spec that never evaluates Trace, such as one that serializes it only once an invariant
    /// fails, still searches here.
    fn compile_trace(&mut self) -> Compiled {
        let order: Vec<usize> = self
            .ir
            .tlc_order
            .iter()
            .map(|&variable| variable as usize)
            .collect();
        let keys: Vec<Id> = order
            .iter()
            .map(|&variable| {
                let units: Vec<u16> = self
                    .text(self.ir.variables[variable])
                    .encode_utf16()
                    .collect();
                self.store.str(&units)
            })
            .collect();
        let is_ordered = keys.windows(2).all(|pair| {
            self.store
                .compare(pair[0], pair[1])
                .is_ok_and(|order| order < 0)
        });
        let footprint = Footprint {
            vars: (0..self.ir.variables.len() as u32).collect(),
            primes: Vec::new(),
            slots: vec![super::LEVEL_SLOT, super::TRACE_SLOT],
        };
        if !self.is_native {
            return leaf(eval(|_| Err(Bail(crate::machine::TRACE_UNKEPT))), footprint);
        }
        if !is_ordered {
            return leaf(
                eval(|_| {
                    Err(Bail(
                        "TLCExt's Trace of variables TLC orders otherwise than their names",
                    ))
                }),
                footprint,
            );
        }
        self.is_trace_read = true;
        let shape = self.store.create_record_shape(&keys);
        let model = &self.ir.model;
        let is_init_effectful = self.may_change_again(model.init, &mut HashSet::new());
        let is_next_effectful = model
            .next
            .is_some_and(|next| self.may_change_again(next, &mut HashSet::new()));
        self.program.trace_record = Some(crate::machine::TraceRecord {
            shape,
            order,
            is_init_effectful,
            is_next_effectful,
        });
        leaf(eval(|machine| machine.trace()), footprint)
    }

    pub(crate) fn compile_nullary_builtin(
        &mut self,
        index: Index,
        context: &Context,
    ) -> Compiling<Compiled> {
        let builtin = &self.ir.builtins[index as usize];
        let name = self.text(builtin.name);
        if builtin.flags & Builtin::UNINITIALIZED_LITERAL != 0 {
            return Ok(leaf(
                eval(|_| Err(Bail("an INSTANCE fact literal TLC did not initialize"))),
                Footprint::default(),
            ));
        }
        if builtin.flags & Builtin::INDEX_REPLACED != 0 {
            return Ok(Self::index_replaced());
        }
        // TLC evaluates a primed Trace in the successor, which the walk assigns part by part, and
        // fails there as it isn't assigned (`TLCExt.getTrace`), with an exception it reports
        // otherwise than the failures the engine words.
        if name == "Trace" && context.is_primed {
            return Ok(leaf(
                eval(|_| Err(Bail("TLCExt's Trace in a primed context"))),
                Footprint::default(),
            ));
        }
        if name == "Trace" {
            return Ok(self.compile_trace());
        }
        if name == "Any"
            && builtin.flags & (Builtin::STATE_LEVEL | Builtin::TABLE | Builtin::DECLINED) == 0
        {
            if !self.is_native || builtin.flags & Builtin::EXTERNAL_CLASS != 0 {
                return Ok(Compiled {
                    is_normalized: false,
                    is_irreducible: true,
                    member: Some(member(|_, _| Ok(true))),
                    ..leaf(
                        eval(|_| Err(Bail("unsupported: Any"))),
                        Footprint::default(),
                    )
                });
            }
            let value = self.store.any();
            let evaluate = if self.is_native {
                eval(move |_| Ok(value))
            } else {
                eval(|_| Err(Bail("unsupported: Any")))
            };
            return Ok(Compiled {
                is_normalized: false,
                is_irreducible: true,
                has_infinite_part: true,
                reference: Some(Arc::new(|_| Ok(Lazy::Any))),
                member: Some(member(|_, _| Ok(true))),
                ..leaf(evaluate, Footprint::default())
            });
        }
        // Outside a POSTCONDITION, which the engine doesn't evaluate, TLCExt's CounterExample is
        // the empty one TLC builds where none is bound (`TLCExt.error`, `new CounterExample()`).
        if self.is_counter_example(index) {
            let keys = [
                self.store.str(&utf16("action")),
                self.store.str(&utf16("state")),
            ];
            return Ok(super::constant(
                self.store.function_of(&keys, &[EMPTY_SET, EMPTY_SET])?,
            ));
        }
        if builtin.flags & Builtin::STATE_LEVEL != 0 || IMPURE_BUILTINS.contains(&name) {
            return unsupported(name);
        }
        Ok(match name {
            "TRUE" => super::constant(TRUE),
            "FALSE" => super::constant(FALSE),
            "BOOLEAN" => super::constant(self.store.set_of(&[FALSE, TRUE])?),
            "Nat" => Self::infinite_set("Nat", NAT, ENUMERATED_NAT),
            "Int" => Self::infinite_set("Int", INT, ENUMERATED_INT),
            "STRING" => Self::infinite_set("STRING", STRINGS, ENUMERATED_STRING),
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

    /// A definition a TLCOverrides index's Java method replaces, which stops the search where it
    /// is computed: TLC evaluates the arguments and calls the method there, whose value the
    /// engine doesn't know, and nowhere else.
    fn index_replaced() -> Compiled {
        leaf(eval(|_| Err(Bail(INDEX_REPLACED))), Footprint::default())
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

    // `F = e` and `F # e`, where F filters a product or a set of records of set enumerations and
    // intervals with a predicate that may print, draw or set a register. TLC keeps such a filter
    // lazy (`Tool`'s OPCODE_sso, a `SetPredValue`), evaluates `e` (OPCODE_eq), and then, as it
    // compares (`SetPredValue.equals`, `convertAndCache`), evaluates the predicate once at each
    // element in the order it enumerates the set: each factor's or field's elements in their
    // normalized order, the last varying fastest (`SetOfTuplesValue.Enumerator`,
    // `SetOfRcdsValue.Enumerator`, `SetEnumValue.Enumerator`), as the engine streams them. The
    // engine evaluates `e` first, then the filter whole, which orders the effects as TLC does
    // where neither `e` nor the filtered set has any.
    fn compile_filter_compared(
        &mut self,
        left: &Operand,
        right: &Operand,
        is_equal: bool,
    ) -> Compiling<Option<Compiled>> {
        let NodeKind::SetFilter {
            bound:
                Bound {
                    pattern: Pattern::Name(_),
                    set,
                },
            predicate,
        } = self.node(left.node).1
        else {
            return Ok(None);
        };
        let is_streamed = match self.node(*set).1 {
            NodeKind::Product(factors) => factors.iter().all(|&factor| self.is_reduced_set(factor)),
            NodeKind::RecordSet(fields) => {
                fields.iter().all(|&(_, field)| self.is_reduced_set(field))
            }
            _ => false,
        };
        if !is_streamed
            || left.slot.is_some()
            || right.slot.is_some()
            || !left.context.can_print
            || !self.may_have_effect_in(*predicate, &left.context, &mut HashSet::new())
            || self.may_have_effect_in(*set, &left.context, &mut HashSet::new())
            || self.may_have_effect_in(right.node, &right.context, &mut HashSet::new())
        {
            return Ok(None);
        }
        let outer = self.converted_filter.replace(left.node);
        let filter = self.compile(left.node, &left.context);
        self.converted_filter = outer;
        let filter = filter?;
        let other = self.compile(right.node, &right.context)?;
        let footprint = filter.footprint.merge(&other.footprint);
        let (filter, other) = (filter.eval, other.eval);
        Ok(Some(Compiled {
            is_costly: true,
            is_boolean: true,
            ..leaf(
                eval(move |machine| {
                    let other = other(machine)?;
                    let set = filter(machine)?;
                    Ok(bool_id(machine.store.equals(set, other)? == is_equal))
                }),
                footprint,
            )
        }))
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
        if builtin.flags & Builtin::INDEX_REPLACED != 0 {
            return Ok(Self::index_replaced());
        }
        if name == "$Nop" {
            if operands.len() != 1 {
                return unsupported("an operator applied to the wrong number of arguments");
            }
            let mut operand = self.operand(&operands[0])?;
            operand.shape = Shape::Other;
            return Ok(operand);
        }
        if matches!(name, "Print" | "PrintT") && builtin.flags & Builtin::TABLE == 0 {
            return self.compile_print(name, operands, context);
        }
        let is_checked = self.is_native && builtin.flags & Builtin::DECLINED == 0;
        if is_checked
            && builtin.flags & Builtin::TABLE == 0
            && matches!(name, "ToJson" | "ToJsonArray" | "ToJsonObject")
            && (name == "ToJson"
                || (builtin.flags & Builtin::EXTERNAL_CLASS == 0
                    && builtin.flags & Builtin::PINNED_STANDARD_SOURCES != 0))
        {
            if operands.len() != 1 {
                return unsupported("an operator applied to the wrong number of arguments");
            }
            self.is_ranking = true;
            let operand = self.operand(&operands[0])?;
            let construction = self.construction_of(&operands[0]);
            // `Json.getNode` writes a RecordValue and a FcnRcdValue as `getObjectNode` does, as
            // ToJsonObject writes them.
            if name == "ToJson"
                && !matches!(
                    construction,
                    Construction::Record(_) | Construction::Function(..)
                )
            {
                return Ok(unary(&operand, to_json, true));
            }
            let is_object = name != "ToJsonArray";
            let evaluate = operand.eval.clone();
            return Ok(Compiled {
                is_costly: true,
                ..leaf(
                    eval(move |machine| {
                        let value = evaluate(machine)?;
                        to_json_conversion(machine, value, &construction, is_object)
                    }),
                    operand.footprint.clone(),
                )
            });
        }
        if is_checked && name == "AssertEq" {
            return self.compile_assert_eq(operands, context);
        }
        // `TLCExt.toTrace` takes only the record CounterExample builds, which the engine never
        // computes: any value it computes fails there, after its argument, as the Java method
        // fails, for the evaluator of failures to word.
        if is_checked
            && name == "ToTrace"
            && builtin.flags & (Builtin::TABLE | Builtin::EXTERNAL_CLASS) == 0
        {
            if operands.len() != 1 {
                return unsupported("an operator applied to the wrong number of arguments");
            }
            // Of the CounterExample TLC builds where none is bound, the empty sequence
            // (`CounterExample.toTrace`).
            if !operands[0].is_param
                && let NodeKind::Identifier(name) = self.node(operands[0].node).1
                && let Resolution::Builtin(index) = name.resolution
                && !name.is_local
                && self.is_counter_example(index)
            {
                return Ok(super::constant(EMPTY_TUPLE));
            }
            // Where the spec names CounterExample, the value may be it, which the engine holds
            // as a plain record: the caller's evaluator tells them apart.
            let is_counter_example_named = self
                .ir
                .builtins
                .iter()
                .enumerate()
                .any(|(index, _)| self.is_counter_example(index as Index));
            let operand = self.operand(&operands[0])?;
            return Ok(unary(
                &operand,
                if is_counter_example_named {
                    |_, _| Err(Bail(TO_TRACE_OF_RECORD))
                } else {
                    |_, _| Err(Bail(TO_TRACE_OF_NON_COUNTER_EXAMPLE))
                },
                false,
            ));
        }
        if name == "TLCGet" {
            return self.compile_tlc_get(operands, context);
        }
        if self.is_native && name == "TLCSet" {
            return self.compile_register(operands, context, true);
        }
        if is_checked
            && name == "_Track"
            && builtin.flags & (Builtin::TABLE | Builtin::EXTERNAL_CLASS) == 0
        {
            return self.compile_track(operands, context);
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
        if self.is_native
            && name == "TLCEvalDefinition"
            && builtin.flags & (Builtin::TABLE | Builtin::EXTERNAL_CLASS | Builtin::DECLINED) == 0
        {
            return self.compile_evaluated_definition(operands, context);
        }
        if self.is_native && name == "TLCCache" {
            return self.compile_tlc_cache(operands, context);
        }
        if name == "RandomSetOfSubsets" && builtin.flags & Builtin::TABLE == 0 && builtin.flags != 0
        {
            return Ok(leaf(
                eval(|_| {
                    Err(Bail(
                        "unsupported: RandomSetOfSubsets without default Java method origin",
                    ))
                }),
                Footprint::slot(super::PRINT_SLOT),
            ));
        }
        if name == "TestRandomSetOfSubsets" {
            let operands: Vec<(NodeId, Context)> = operands
                .iter()
                .map(|operand| (operand.node, operand.context.clone()))
                .collect();
            return self.compile_test_random_set_of_subsets(index, &operands, context, None);
        }
        if (name == "RandomSubsetSet" || name == "RandomSetOfSubsets")
            && builtin.flags & Builtin::TABLE == 0
        {
            return self.compile_random_subset_set(name, operands, context);
        }
        if (name == "RandomElement" && builtin.flags & Builtin::TABLE == 0)
            || name == "RandomSubset"
        {
            return self.compile_random(name, operands, context, builtin.flags == 0);
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
        // `TLCExt.tlcNoOp` returns the argument `Tool.evalAppl` evaluated for it; the walk of the
        // initial predicate and of an action evaluates it as a whole, as TLC does a Java method.
        if name == "TLCNoOp"
            && self.is_native
            && builtin.flags & (Builtin::STATE_LEVEL | Builtin::DECLINED | Builtin::EXTERNAL_CLASS)
                == 0
        {
            if operands.len() != 1 {
                return unsupported("an operator applied to the wrong number of arguments");
            }
            let mut operand = self.operand(&operands[0])?;
            operand.shape = Shape::Other;
            return Ok(operand);
        }
        if name == "TLCDefer" {
            if self.simulation.is_none()
                || self.is_defer_legacy
                || self.enabled_depth > 0
                || builtin.flags
                    != Builtin::PACKAGED_TLC_DEFER | Builtin::STATE_LEVEL | Builtin::LAZY
            {
                return Ok(super::constant(TRUE));
            }
            if operands.len() != 1 {
                return unsupported("an operator applied to the wrong number of arguments");
            }
            self.note_effect();
            let operand = &operands[0];
            let mut inner = operand.context.clone();
            inner.can_print = true;
            let deferred = match self.compile(operand.node, &inner) {
                Ok(deferred) => deferred,
                Err(_) => {
                    self.has_unsupported_deferred = true;
                    return Ok(super::constant(TRUE));
                }
            };
            let mut footprint = deferred.footprint;
            footprint.slots.retain(|&slot| slot != super::PRINT_SLOT);
            let footprint = footprint.merge(&Footprint::slot(super::REGISTER_SLOT));
            let evaluate = deferred.eval;
            return Ok(Compiled {
                is_boolean: true,
                ..leaf(
                    eval(move |machine| {
                        machine.deferred = Some(crate::machine::DeferredCall {
                            evaluate: evaluate.clone(),
                            locals: machine.locals.clone(),
                            current: machine.cur.clone(),
                            next: machine.next.clone(),
                        });
                        Ok(TRUE)
                    }),
                    footprint,
                )
            });
        }
        // AssertError compares TLC's message for a failure, which the engine doesn't word, so
        // the native checker leaves the assumption it is in to its caller. One whose value is the
        // same wherever TLC evaluates it the caller computes as the search starts.
        if self.is_native
            && name == "AssertError"
            && let Some(node) = self.get_delegable_assert_error(operands, context)
        {
            let value = match self
                .program
                .delegated
                .iter()
                .find(|(other, _)| *other == node)
            {
                Some((_, value)) => Arc::clone(value),
                None => {
                    let value = Arc::new(std::sync::OnceLock::new());
                    self.program.delegated.push((node, Arc::clone(&value)));
                    value
                }
            };
            return Ok(Compiled {
                is_boolean: true,
                ..leaf(
                    eval(move |_| match value.get() {
                        Some(&holds) => Ok(bool_id(holds)),
                        None => Err(Bail(crate::search::DELEGATED_ASSUMPTION)),
                    }),
                    Footprint::default(),
                )
            });
        }
        // TLC checks that the message is a string written out before it evaluates anything
        // (`Assert.check` in `TLCExt.assertError`), and fails where it isn't: the caller words
        // that.
        if self.is_native
            && name == "AssertError"
            && let [message, _] = operands
            && !message.is_param
            && !matches!(self.node(message.node).1, NodeKind::String(_))
        {
            return Ok(leaf(
                eval(|_| Err(Bail(ASSERT_ERROR_MESSAGE))),
                Footprint::default(),
            ));
        }
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
                // Nat, Int and STRING are no set enumeration (`UserValue`), which TLCEval
                // leaves as they are.
                if operand.infinite_value.is_some() {
                    return Ok(operand);
                }
                // Any other set TLC may not enumerate stops where TLCEval would enumerate it
                // (`toSetEnum`), for the evaluator of failures to word TLC's failure there.
                if operand.infinite.is_some() || operand.has_infinite_part {
                    if operands[0].is_param
                        || self.may_have_effect_in(
                            operands[0].node,
                            &operands[0].context,
                            &mut HashSet::new(),
                        )
                    {
                        return unsupported("TLCEval of a set TLC may not enumerate");
                    }
                    return Ok(leaf(
                        eval(|_| Err(Bail("enumerated an infinite set"))),
                        operand.footprint,
                    ));
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
                                return Err(Bail(TLC_EVAL_OF_LAZY_FUNCTION));
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
    // For `S = T` where S or T may be a set TLC can't enumerate: their references, which TLC's
    // `equals` of S may compare without enumerating either (`Lazy::equals`). Both evaluate again
    // where it can't, so neither may have an effect.
    fn lazy_compared(
        &self,
        left_operand: &Operand,
        left: &Compiled,
        right_operand: &Operand,
        right: &Compiled,
    ) -> Option<(Reference, Reference)> {
        if !left.may_be_infinite() && !right.may_be_infinite() {
            return None;
        }
        for operand in [left_operand, right_operand] {
            if operand.is_param
                || self.may_have_effect_in(operand.node, &operand.context, &mut HashSet::new())
            {
                return None;
            }
        }
        Some((reference_of(left)?, reference_of(right)?))
    }

    // The comparison as TLC's `equals` of the left set answers it from the sets' references where
    // it can, and as compiled otherwise, which stops where the engine can't enumerate a set.
    fn lazy_equal(
        compared: Compiled,
        left: Reference,
        right: Reference,
        is_equal: bool,
    ) -> Compiled {
        let evaluate = compared.eval.clone();
        compared.with_eval(eval(move |machine| {
            if let (Ok(left), Ok(right)) = (left(machine), right(machine))
                && let Some(is_same) = left.equals(machine, &right)
            {
                return Ok(bool_id(is_same == is_equal));
            }
            evaluate(machine)
        }))
    }

    // For `S = T` where S or T is a set TLC keeps lazy, such as `A \X B`: each operand's value,
    // whether TLC keeps it lazy, and its reference. Both evaluate again, so neither may have an
    // effect.
    fn bounded_compared(
        &self,
        left_operand: &Operand,
        left: &Compiled,
        right_operand: &Operand,
        right: &Compiled,
    ) -> Option<[(Eval, bool, Option<Reference>); 2]> {
        // A set with a part TLC can't enumerate is one the engine doesn't build either.
        let is_checked = |set: &Compiled| set.is_kept_lazy() && !set.may_be_infinite();
        if !is_checked(left) && !is_checked(right) {
            return None;
        }
        for operand in [left_operand, right_operand] {
            if operand.is_param
                || self.may_have_effect_in(operand.node, &operand.context, &mut HashSet::new())
            {
                return None;
            }
        }
        Some([left, right].map(|set| (set.eval.clone(), is_checked(set), reference_of(set))))
    }

    // TLC compares a set it keeps lazy with a value of another class as its normalized set
    // (`convertAndCache`, `SetEnumValue.equals`), which `toSetEnum` builds in a ValueVec that
    // fails past `TLCGlobals.setBound` elements, and two of one class by their parts
    // (`Lazy::equals`). It words the failure as it fingerprints the set where it has a source.
    fn bounded_equal(
        compared: Compiled,
        operands: [(Eval, bool, Option<Reference>); 2],
        is_equal: bool,
    ) -> Compiled {
        let evaluate = compared.eval.clone();
        compared.with_eval(eval(move |machine| {
            let mut is_past = false;
            for (operand, is_kept_lazy, _) in &operands {
                if !is_kept_lazy {
                    continue;
                }
                let id = operand(machine)?;
                is_past |= machine.store.kind_of(id) == KIND_SET
                    && machine.store.size_of(id) as usize > tla_values::SET_BOUND;
            }
            if !is_past {
                return evaluate(machine);
            }
            if let [(_, _, Some(left)), (_, _, Some(right))] = &operands {
                let left = left(machine)?;
                let right = right(machine)?;
                if let Some(is_same) = left.equals(machine, &right) {
                    return Ok(bool_id(is_same == is_equal));
                }
            }
            Err(Bail(
                "unsupported: comparing a set TLC builds past TLCGlobals.setBound elements",
            ))
        }))
    }

    // For two intervals `a..b` and `c..d`: their bounds, which TLC's IntervalValue compares
    // without building either interval. Both evaluate again where it can't, so neither may have
    // an effect.
    fn interval_compared(
        &self,
        left_operand: &Operand,
        left: &Compiled,
        right_operand: &Operand,
        right: &Compiled,
    ) -> Option<[Eval; 4]> {
        let ((low, high), (other_low, other_high)) =
            (left.interval.clone()?, right.interval.clone()?);
        for operand in [left_operand, right_operand] {
            if operand.is_param
                || self.may_have_effect_in(operand.node, &operand.context, &mut HashSet::new())
            {
                return None;
            }
        }
        Some([low, high, other_low, other_high])
    }

    // The bounds of two intervals, or None where one isn't an integer, for the caller to
    // evaluate the intervals as compiled, which fails as TLC does.
    fn interval_bounds(machine: &mut Machine<'_>, bounds: &[Eval; 4]) -> Option<[i64; 4]> {
        let mut values = [0; 4];
        for (value, bound) in values.iter_mut().zip(bounds) {
            let bound = bound(machine).ok()?;
            if machine.store.kind_of(bound) != KIND_INT {
                return None;
            }
            *value = i64::from(machine.store.int_of(bound));
        }
        Some(values)
    }

    // `a..b = c..d` as `IntervalValue.equals` answers it: an empty interval equals only an empty
    // one, whatever its bounds, and another by its bounds. TLC counts only the elements of the
    // left one unless it is empty, and fails counting one of more than 2^31 - 1 elements
    // (`IntervalValue.size`), where the comparison is left as compiled.
    fn interval_equal(compared: Compiled, bounds: [Eval; 4], is_equal: bool) -> Compiled {
        let evaluate = compared.eval.clone();
        let size = |low: i64, high: i64| {
            let size = (high - low + 1).max(0);
            (size <= i64::from(i32::MAX)).then_some(size)
        };
        compared.with_eval(eval(move |machine| {
            if let Some([low, high, other_low, other_high]) =
                Self::interval_bounds(machine, &bounds)
                && let Some(left_size) = size(low, high)
            {
                let is_same = if left_size == 0 {
                    size(other_low, other_high).map(|size| size == 0)
                } else {
                    Some(low == other_low && high == other_high)
                };
                if let Some(is_same) = is_same {
                    return Ok(bool_id(is_same == is_equal));
                }
            }
            evaluate(machine)
        }))
    }

    // `a..b \subseteq c..d` as `IntervalValue.isSubsetEq` answers it: TRUE where c..d holds
    // a..b's bounds, and otherwise as `EnumerableValue.isSubsetEq`, which walks a..b without
    // counting it and tests each element against c..d's bounds, which never fails: TRUE only
    // where a..b is empty.
    fn interval_subseteq(compared: Compiled, bounds: [Eval; 4]) -> Compiled {
        let evaluate = compared.eval.clone();
        compared.with_eval(eval(move |machine| {
            if let Some([low, high, other_low, other_high]) =
                Self::interval_bounds(machine, &bounds)
            {
                let is_subset = (other_low <= low && other_high >= high) || low > high;
                return Ok(bool_id(is_subset));
            }
            evaluate(machine)
        }))
    }

    // `S \cap a..b` and `S \ a..b` of a set enumeration S, its integers kept where a..b holds them
    // or lacks them, and as compiled where S isn't a set or holds another value, or a bound isn't
    // an integer, where TLC fails as the compiled set does.
    fn interval_filtered(
        compiled: Compiled,
        set: Eval,
        bounds: [Eval; 2],
        is_kept: bool,
    ) -> Compiled {
        let evaluate = compiled.eval.clone();
        compiled.with_eval(eval(move |machine| {
            let filtered = (|| {
                let set = set(machine).ok()?;
                if machine.store.kind_of(set) != KIND_SET {
                    return None;
                }
                let mut values = [0; 2];
                for (value, bound) in values.iter_mut().zip(&bounds) {
                    let bound = bound(machine).ok()?;
                    if machine.store.kind_of(bound) != KIND_INT {
                        return None;
                    }
                    *value = machine.store.int_of(bound);
                }
                let mut kept = Vec::new();
                for index in 0..machine.store.size_of(set) {
                    let element = machine.store.element_at(set, index);
                    if machine.store.kind_of(element) != KIND_INT {
                        return None;
                    }
                    let value = machine.store.int_of(element);
                    if (values[0] <= value && value <= values[1]) == is_kept {
                        kept.push(element);
                    }
                }
                Some(machine.store.set_of_sorted(&kept))
            })();
            match filtered {
                Some(filtered) => Ok(filtered),
                None => evaluate(machine),
            }
        }))
    }

    fn compared(left: Compiled, right: Compiled) -> (Compiled, Compiled) {
        (
            Self::referenced_value(&left),
            Self::referenced_value(&right),
        )
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
            // `IntervalValue.member` of an integer compares it with the bounds, so TLC tests a set
            // of integers against `a..b` without building it, however large. Where S holds
            // anything else, the test goes as compiled.
            let right_bounds = right.interval.clone().filter(|_| !right.is_printing());
            eval(move |machine| {
                let left = evaluate_set(machine, &left_eval, "expected a set")?;
                if let Some((low, high)) = &right_bounds {
                    let (low, high) = (low(machine)?, high(machine)?);
                    let size = machine.store.size_of(left);
                    let elements: Vec<Id> = (0..size)
                        .map(|index| machine.store.element_at(left, index))
                        .collect();
                    if machine.store.kind_of(low) == KIND_INT
                        && machine.store.kind_of(high) == KIND_INT
                        && elements
                            .iter()
                            .all(|&element| machine.store.kind_of(element) == KIND_INT)
                    {
                        let (low, high) = (machine.store.int_of(low), machine.store.int_of(high));
                        return Ok(bool_id(elements.iter().all(|&element| {
                            (low..=high).contains(&machine.store.int_of(element))
                        })));
                    }
                }
                let right = right_eval(machine)?;
                // `EnumerableValue.isSubsetEq` tests T only for S's elements, so an empty S is a
                // subset of T whatever T is.
                if machine.store.kind_of(right) != KIND_SET && machine.store.size_of(left) == 0 {
                    return Ok(TRUE);
                }
                let right = expect_set(machine, right, "expected a set")?;
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
        let arguments = operands
            .iter()
            .map(|operand| self.operand(operand))
            .collect::<Compiling<Vec<Compiled>>>()?;
        let footprint = Footprint::merge_all(arguments.iter().map(|argument| &argument.footprint));
        let evals: Vec<Eval> = arguments
            .into_iter()
            .map(|argument| argument.eval)
            .collect();
        let mut rows = Vec::new();
        let phase_known = ir.builtins[index as usize].flags & Builtin::TABLE_PHASE_KNOWN != 0;
        for &(arguments, value) in &ir.builtins[index as usize].table {
            if phase_known {
                // An unused result need not normalize, and arguments run before any row key.
                // Failed interning is therefore unavailable row data, not a compile-time error.
                rows.push((
                    arguments.and_then(|index| self.intern_value(index).ok()),
                    value.and_then(|index| self.intern_value(index).ok()),
                ));
            } else {
                let (Some(arguments), Some(value)) = (arguments, value) else {
                    return unsupported("a value of an operator's table the IR can't hold");
                };
                rows.push((
                    Some(self.intern_value(arguments)?),
                    Some(self.intern_value(value)?),
                ));
            }
        }
        Ok(leaf(
            eval(move |machine| {
                let values = evals
                    .iter()
                    .map(|evaluate| evaluate(machine))
                    .collect::<Outcome<Vec<Id>>>()?;
                let tuple = machine.store.tuple_of(&values);
                for &(key, value) in &rows {
                    let key = key.ok_or(Bail(
                        "unsupported: a value of an operator's table the IR can't hold",
                    ))?;
                    if machine.store.kind_of(key) != KIND_TUPLE {
                        return Err(Bail(
                            "unsupported: an operator table without an argument tuple",
                        ));
                    }
                    if machine.store.size_of(key) as usize != values.len() {
                        return Err(Bail(
                            "an operator's table applied to the wrong number of arguments",
                        ));
                    }
                    if machine.store.equals(key, tuple)? {
                        return value.ok_or(Bail(
                            "unsupported: a value of an operator's table the IR can't hold",
                        ));
                    }
                }
                Err(Bail("an operator's table applied outside its rows"))
            }),
            footprint,
        ))
    }

    fn compile_random_subset_set(
        &mut self,
        name: &str,
        operands: &[Operand],
        context: &Context,
    ) -> Compiling<Compiled> {
        if !context.can_print {
            return unsupported("RandomSubsetSet");
        }
        if operands.len() != 3 {
            return unsupported("an operator applied to the wrong number of arguments");
        }
        self.note_effect();
        let compiled = operands
            .iter()
            .map(|operand| self.compile(operand.node, &operand.context.without_print()))
            .collect::<Compiling<Vec<_>>>()?;
        let footprint = Footprint::merge_all(compiled.iter().map(|value| &value.footprint))
            .merge(&Footprint::slot(super::PRINT_SLOT));
        let draw = SubsetSetDraw::new(&compiled, name == "RandomSetOfSubsets");
        Ok(leaf(
            eval(move |machine| {
                let arguments = draw.arguments(machine)?;
                draw.draw(machine, &arguments)
            }),
            footprint,
        ))
    }

    /// Randomization's TestRandomSetOfSubsets(k, n, S), which no Java method overrides: TLC
    /// evaluates its definition, `[i \in 1..5 |-> Cardinality(RandomSetOfSubsets(k, n, S))]`,
    /// binding the arguments to `LazyValue`s (`Tool.getOpContext`). Where the application isn't
    /// applied, TLC builds the function (`FcnLambdaValue.toFcnRcd`): five draws, in order, from
    /// arguments it evaluates once, at the first. Applied to a key, `Tool.evalAppl` keeps the
    /// constructor lazy (`EvalControl.KeepLazy`), evaluates the key, and draws once for it
    /// (`FcnLambdaValue.apply`). The engine compiles only arguments without effects, so it
    /// needn't follow when TLC evaluates them, and declines where TLC may keep the function lazy
    /// otherwise: where the function of an application or a field's record may reach the
    /// operator, through a definition or a name bound to an argument.
    pub(super) fn compile_test_random_set_of_subsets(
        &mut self,
        index: Index,
        operands: &[(NodeId, Context)],
        context: &Context,
        key: Option<NodeId>,
    ) -> Compiling<Compiled> {
        if self.ir.builtins[index as usize].flags != 0 {
            return Ok(leaf(
                eval(|_| {
                    Err(Bail(
                        "unsupported: TestRandomSetOfSubsets without default Java method origin",
                    ))
                }),
                Footprint::slot(super::PRINT_SLOT),
            ));
        }
        // Where the engine may not evaluate the application exactly when TLC does, it stops
        // where it evaluates it, and nowhere else, so it draws and prints nothing: TLC never
        // evaluates it under `\E x \in {}`.
        if !context.can_print {
            return Ok(leaf(
                eval(|_| Err(Bail("unsupported: TestRandomSetOfSubsets"))),
                Footprint::default(),
            ));
        }
        if operands.len() != 3 {
            return unsupported("an operator applied to the wrong number of arguments");
        }
        if operands
            .iter()
            .map(|(node, _)| *node)
            .chain(key)
            .any(|node| self.may_have_effect(node, &mut HashSet::new()))
        {
            return unsupported("TestRandomSetOfSubsets of an argument with effects");
        }
        if key.is_none() && self.ir.may_keep_test_draws_lazy() {
            return unsupported("TestRandomSetOfSubsets where TLC may keep its function lazy");
        }
        self.note_effect();
        let compiled = operands
            .iter()
            .map(|(node, context)| self.compile(*node, &context.without_print()))
            .collect::<Compiling<Vec<_>>>()?;
        let key = key
            .map(|key| self.compile(key, &context.without_print()))
            .transpose()?;
        let footprint =
            Footprint::merge_all(compiled.iter().chain(&key).map(|value| &value.footprint))
                .merge(&Footprint::slot(super::PRINT_SLOT));
        let draw = SubsetSetDraw::new(&compiled, true);
        let key = key.map(|key| key.eval);
        Ok(leaf(
            eval(move |machine| {
                let Some(key) = &key else {
                    let arguments = draw.arguments(machine)?;
                    let mut sizes = Vec::with_capacity(5);
                    for _ in 1..=5 {
                        let drawn = draw.draw(machine, &arguments)?;
                        sizes.push(machine.store.int(machine.store.size_of(drawn) as i64)?);
                    }
                    let function = machine.store.tuple_of(&sizes);
                    return Ok(machine.store.mark_built_as_function(function));
                };
                let key = key(machine)?;
                // `FcnLambdaValue.apply` of a key outside 1..5 fails, printing the function,
                // which draws it whole.
                if machine.store.kind_of(key) != KIND_INT
                    || !(1..=5).contains(&machine.store.int_of(key))
                {
                    return Err(Bail(
                        "unsupported: TestRandomSetOfSubsets applied outside its domain",
                    ));
                }
                let arguments = draw.arguments(machine)?;
                let drawn = draw.draw(machine, &arguments)?;
                machine.store.int(machine.store.size_of(drawn) as i64)
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
        default_method: bool,
    ) -> Compiling<Compiled> {
        if !context.can_print {
            return unsupported(name);
        }
        let is_element = name == "RandomElement";
        if operands.len() != if is_element { 1 } else { 2 } {
            return unsupported("an operator applied to the wrong number of arguments");
        }
        self.note_effect();
        // `Randomization.RandomSubset` and `RandomElement` are Java methods, whose arguments TLC
        // evaluates in order before it calls them (`Tool.evalAppl`): a print there that nothing
        // keeps lazy prints before the draw, as the engine prints it.
        let compiled = operands
            .iter()
            .map(|operand| {
                let mut inner = operand.context.without_print();
                inner.can_print = self.is_eager_print_operand(operand.node);
                self.compile(operand.node, &inner)
            })
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
                    (None, random::Source::Set(set)) => {
                        random::random_element(machine, &set, default_method)
                    }
                    (Some(count), source) => {
                        let drawn = random::random_subset(machine, count, &source, is_174)?;
                        machine.store.set_of(&drawn)
                    }
                }
            }),
            footprint,
        ))
    }

    // A Print or PrintT of arguments without effects, or a set enumeration of such prints and
    // expressions without effects, which TLC evaluates in full, and prints, where it evaluates
    // the operand, nothing of it kept lazy.
    fn is_eager_print_operand(&self, node: NodeId) -> bool {
        let is_quiet = |node: NodeId| self.is_walk_repeatable(node, &mut HashSet::new());
        let is_direct_print = |node: NodeId| match self.node(node).1 {
            NodeKind::Apply { name, args, .. } if !name.is_local => {
                matches!(name.resolution, Resolution::Builtin(index)
                    if matches!(self.builtin_name(index), "Print" | "PrintT")
                        && self.ir.builtins[index as usize].flags & Builtin::TABLE == 0)
                    && args.iter().all(|&arg| is_quiet(arg))
            }
            _ => false,
        };
        match self.node(node).1 {
            NodeKind::SetEnumeration(elements) => {
                elements.iter().any(|&element| is_direct_print(element))
                    && elements
                        .iter()
                        .all(|&element| is_direct_print(element) || is_quiet(element))
            }
            _ => is_direct_print(node),
        }
    }

    // A LET definition or an argument kept from its first use (`Argument::once_slot`) whose
    // expression is a direct draw Print may print, or a tuple of such names, direct draws,
    // numbers and strings: Print evaluates the draw at the name's first use, as TLC's
    // `LazyValue` does, and prints the value it keeps.
    fn is_kept_draw_print_operand(&self, node: NodeId, context: &Context) -> bool {
        match self.node(node).1 {
            NodeKind::Identifier(name) if name.is_local => lookup(&context.scope, name.text)
                .is_some_and(|found| {
                    matches!(&found.binding, Binding::Argument(argument)
                        if argument.once_slot.is_some()
                            && self.is_random_element_print_operand(argument.expression))
                }),
            NodeKind::Tuple(elements) => {
                !elements.is_empty()
                    && elements.iter().all(|&element| {
                        self.is_kept_draw_print_operand(element, context)
                            || self.is_random_element_print_operand(element)
                            || matches!(
                                self.node(element).1,
                                NodeKind::Number(_) | NodeKind::String(_)
                            )
                    })
            }
            _ => false,
        }
    }

    fn is_random_element_print_operand(&self, node: NodeId) -> bool {
        match self.node(node).1 {
            NodeKind::Apply { name, .. } if !name.is_local => {
                matches!(name.resolution, Resolution::Builtin(index) if matches!(self.builtin_name(index), "RandomElement" | "RandomSubset") && self.ir.builtins[index as usize].flags == 0)
            }
            NodeKind::Tuple(elements) => {
                !elements.is_empty()
                    && elements.iter().all(|&element| {
                        self.is_random_element_print_operand(element)
                            || matches!(
                                self.node(element).1,
                                NodeKind::Number(_) | NodeKind::String(_)
                            )
                    })
            }
            _ => false,
        }
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
        self.note_effect();
        let compiled = operands
            .iter()
            .map(|operand| {
                let mut inner = operand.context.without_print();
                // Print evaluates this direct draw once before printing its normalized result.
                if self.is_random_element_print_operand(operand.node)
                    || self.is_kept_draw_print_operand(operand.node, &operand.context)
                    || self.is_random_set_cardinality(operand.node)
                    || self.is_applied_test_draws(operand.node)
                    || matches!(self.ir.nodes.arena[operand.node as usize].kind,
                    NodeKind::Apply { name, .. } if !name.is_local
                        && matches!(name.resolution, Resolution::Builtin(index)
                            if matches!(self.builtin_name(index), "RandomSubsetSet" | "RandomSetOfSubsets" | "TestRandomSetOfSubsets")))
                {
                    inner.can_print = true;
                }
                // TLC evaluates the arguments of the Java method once, in order, before it prints
                // (`Tool.evalAppl`), so an argument that is itself a print or a TLCSet runs then.
                if !operand.is_param
                    && !self.is_print_checked(operand.node)
                    && matches!(self.node(operand.node).1, NodeKind::Apply { name, .. }
                        if !name.is_local
                            && matches!(name.resolution, Resolution::Builtin(index)
                                if matches!(self.builtin_name(index), "Print" | "PrintT" | "TLCSet")
                                    && self.ir.builtins[index as usize].flags & Builtin::TABLE == 0))
                {
                    inner.can_print = true;
                }
                // A simulation's run prints as TLC holds it, but for the empty sequence.
                self.compile(operand.node, &inner).map(unguarded)
            })
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
        // TLC prints Nat, Int and STRING by their names (`UserValue.toString`), which the engine
        // holds as values to print them.
        let evaluators: Vec<Eval> = compiled
            .into_iter()
            .map(|operand| match operand.infinite_value {
                Some(name) => eval(move |machine| Ok(machine.store.infinite_set(name))),
                None => operand.eval,
            })
            .collect();
        // The native binary's reporter finds what it can't print itself: TLC prints the startup's
        // in the front the binary records, and the binary stops at any later one. It prints each
        // value as TLC prints a value built as the operand writes it, deep-normalized.
        // A printed expression that builds its value afresh, naming no local name but its own
        // binders, no variable, no definition and no register, evaluates to a value no use kept
        // lazy (`kept_lazy_records`), whatever value the store shares it with.
        let may_hold_kept = operands.iter().any(|operand| {
            operand.is_param || !self.is_built_afresh(operand.node, &operand.context)
        });
        let constructions = self.is_native.then(|| {
            operands
                .iter()
                .map(|operand| self.printed_construction_of(operand))
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
                    push_prints(machine, values, constructions.as_deref(), may_hold_kept)?;
                    Ok(result)
                }),
                footprint,
            )
        })
    }

    // Whether a printed expression names an operator's argument, or a LET definition a use may
    // evaluate with KeepLazy, whose expression holds a function constructor whose values hold a record constructor TLC may print
    // with its fields as written, not as it sorts them (names it doesn't rank, or written out of
    // their ranks): TLC holds such a name's function as a `FcnLambdaValue`, whose values
    // `deepNormalize` doesn't reach, where a use evaluated it with KeepLazy first (`f[1]` before
    // `PrintT(f)`), and the engine prints the records sorted wherever it is.
    pub(super) fn names_argument_with_written_records(
        &self,
        node: NodeId,
        context: &Context,
        depth: u32,
    ) -> bool {
        self.names_written_records(node, context, depth, &mut HashSet::new())
    }

    // `names_argument_with_written_records`, each argument walked once (`arguments`).
    fn names_written_records(
        &self,
        node: NodeId,
        context: &Context,
        depth: u32,
        arguments: &mut HashSet<usize>,
    ) -> bool {
        if depth > 16 {
            return true;
        }
        let mut pending = vec![node];
        let mut seen = HashSet::new();
        while let Some(node) = pending.pop() {
            let (node, kind) = self.node(node);
            if !seen.insert(node) {
                continue;
            }
            if let NodeKind::Identifier(name) = kind
                && name.is_local
                && let Some(found) = super::lookup(&context.scope, name.text)
                && let super::Binding::Argument(argument) = &found.binding
            {
                // A LET definition no use evaluates with KeepLazy, or named once, the engine
                // prints as TLC builds it (`named_once_expression`). Reached through another
                // name's expression (`h == g`), it is read wherever that name is, and either may
                // be evaluated with KeepLazy.
                if (depth == 0 && (argument.is_named_once || argument.is_built_alike))
                    || !arguments.insert(std::rc::Rc::as_ptr(argument) as usize)
                {
                    continue;
                }
                let known = self
                    .written_records
                    .borrow()
                    .get(&argument.expression)
                    .copied();
                let holds = known.unwrap_or_else(|| {
                    let holds =
                        self.holds_written_records(argument.expression, false, &mut HashSet::new());
                    self.written_records
                        .borrow_mut()
                        .insert(argument.expression, holds);
                    holds
                });
                if holds
                    || self.names_written_records(
                        argument.expression,
                        &super::argument_context(argument),
                        depth + 1,
                        arguments,
                    )
                {
                    return true;
                }
                continue;
            }
            pending.extend(self.children(node));
        }
        false
    }

    // Whether an expression holds, inside a function constructor (`in_function`), a record
    // constructor of more than one field whose names TLC may sort otherwise than written, through
    // the definitions it names.
    fn holds_written_records(
        &self,
        node: NodeId,
        in_function: bool,
        seen: &mut HashSet<(NodeId, bool)>,
    ) -> bool {
        let (node, kind) = self.node(node);
        if !seen.insert((node, in_function)) {
            return false;
        }
        match kind {
            NodeKind::Record(fields) if in_function && fields.len() > 1 => {
                if fields.iter().any(|&(name, _)| name >= self.ir.ranked_count)
                    || fields.windows(2).any(|pair| pair[0].0 > pair[1].0)
                {
                    return true;
                }
            }
            NodeKind::FunctionConstruction { body, .. } => {
                return self.holds_written_records(*body, true, seen)
                    || self
                        .children(node)
                        .into_iter()
                        .any(|child| self.holds_written_records(child, in_function, seen));
            }
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. }
                if !name.is_local
                    && let Resolution::Definition(index) = name.resolution =>
            {
                let definition = self.definition(self.ir.definitions[index as usize]);
                if self.holds_written_records(definition.body, in_function, seen) {
                    return true;
                }
            }
            _ => {}
        }
        self.children(node)
            .into_iter()
            .any(|child| self.holds_written_records(child, in_function, seen))
    }

    // Whether an expression builds its value afresh at each evaluation: it names no local name
    // but its own binders, no variable, no definition, and no builtin that reads a register.
    fn is_built_afresh(&self, node: NodeId, context: &Context) -> bool {
        let mut pending = vec![node];
        let mut seen = HashSet::new();
        while let Some(node) = pending.pop() {
            let (node, kind) = self.node(node);
            if !seen.insert(node) {
                continue;
            }
            match kind {
                NodeKind::Identifier(name)
                | NodeKind::Apply { name, .. }
                | NodeKind::OperatorReference(name) => {
                    let is_fresh = if name.is_local {
                        super::lookup(&context.scope, name.text).is_none()
                    } else {
                        match name.resolution {
                            Resolution::Builtin(index) => {
                                !matches!(self.builtin_name(index), "TLCGet" | "TLCGetAndSet")
                            }
                            Resolution::Constant(_) => true,
                            _ => false,
                        }
                    };
                    if !is_fresh {
                        return false;
                    }
                }
                NodeKind::Prime(_)
                | NodeKind::Unchanged(_)
                | NodeKind::Enabled(_)
                | NodeKind::Subexpression(_)
                | NodeKind::Reference(_) => return false,
                _ => {}
            }
            pending.extend(self.children(node));
        }
        true
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
                    push_prints(machine, vec![message], Some(&[Construction::Held]), true)?;
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
        self.construction_of_node(operand.node, None, false)
    }

    // How TLC builds the value of a Print's or PrintT's operand, as `construction_of` finds it,
    // and, where the print is a conjunct the walk compiles, a variable the walk assigned on its
    // path as its assignment built it (`walker::Assigned`): TLC prints the value the variable is
    // bound to, not the state's, which keeps the value first found of the states equal to it.
    // A primed expression is built as the expression is, and a filter of a set enumeration or an
    // interval as the set enumeration of the elements it keeps, which its `toString` builds
    // (`SetPredValue.toSetEnum`).
    fn printed_construction_of(&self, operand: &Operand) -> Construction {
        if operand.is_param {
            return Construction::Held;
        }
        let sources = self.print_sources.as_ref().filter(|sources| {
            operand.context.scope.is_none()
                && matches!(self.node(sources.item).1,
                    NodeKind::Apply { args, .. } if args.contains(&operand.node))
        });
        self.printed_construction(operand.node, sources, false, Some(&operand.context))
    }

    // `scope`, where known, is the context the expression is written in, whose LET definitions
    // named once are built as their expressions are (`named_once_expression`).
    fn printed_construction(
        &self,
        node: NodeId,
        sources: Option<&super::walker::PrintSources>,
        is_primed: bool,
        scope: Option<&Context>,
    ) -> Construction {
        let of = |node: &NodeId| self.printed_construction(*node, sources, is_primed, scope);
        match self.node(node).1 {
            NodeKind::Identifier(name) if !name.is_local => {
                let assigned = match (name.resolution, sources) {
                    (Resolution::Variable(variable), Some(sources))
                        if sources.is_init != is_primed =>
                    {
                        sources.known.source(variable)
                    }
                    _ => None,
                };
                match assigned {
                    Some(super::walker::Assigned::Value(value)) => {
                        self.printed_construction(value, None, false, None)
                    }
                    Some(super::walker::Assigned::Element(set)) => {
                        element_construction(&self.printed_construction(set, None, false, None))
                    }
                    Some(super::walker::Assigned::Subset(set)) => self
                        .printed_construction(set, None, false, None)
                        .of_elements()
                        .map_or(Construction::Held, |element| {
                            Construction::Set(Box::new(element.clone()), None)
                        }),
                    None => self.construction_of_node(node, scope, true),
                }
            }
            NodeKind::Prime(inner) => self.printed_construction(*inner, sources, true, scope),
            NodeKind::Tuple(elements) => Construction::Tuple(elements.iter().map(of).collect()),
            NodeKind::Record(fields) => Construction::Record(
                fields
                    .iter()
                    .map(|(field, value)| (self.text(*field).encode_utf16().collect(), of(value)))
                    .collect(),
            ),
            NodeKind::SetEnumeration(elements) => {
                let joined = elements.iter().map(of).try_fold(
                    None,
                    |joined: Option<Construction>, element| {
                        Some(Some(match joined {
                            None => element,
                            Some(joined) => join_printed(joined, element)?,
                        }))
                    },
                );
                match joined {
                    Some(Some(element)) => {
                        Construction::Set(Box::new(element), Some(elements.len() as u32))
                    }
                    Some(None) => Construction::Set(Box::new(Construction::Held), Some(0)),
                    None => Construction::Held,
                }
            }
            NodeKind::SetFilter { bound, .. } if matches!(bound.pattern, Pattern::Name(_)) => {
                let base = self.printed_construction(bound.set, sources, is_primed, scope);
                base.of_elements().map_or(Construction::Held, |element| {
                    Construction::Set(Box::new(element.clone()), None)
                })
            }
            NodeKind::Identifier(_) => match self.named_once_expression(node, scope, true) {
                Some((expression, context)) => {
                    self.printed_construction(expression, None, is_primed, Some(&context))
                }
                None => self.construction_of_node(node, scope, true),
            },
            _ => self.construction_of_node(node, scope, true),
        }
    }

    // The expression and context of a LET definition without parameters a local name names, where
    // the LET names it once (`Argument::is_named_once`): TLC computes its `LazyValue` only there,
    // with that use's `EvalControl`, as it computes the expression written in its place. A value
    // printed (`is_printed`), which Print and PrintT normalize, is built so too where no use of
    // the name may evaluate it with `EvalControl.KeepLazy` (`Argument::is_built_alike`), however
    // many there are.
    fn named_once_expression(
        &self,
        node: NodeId,
        scope: Option<&Context>,
        is_printed: bool,
    ) -> Option<(NodeId, Context)> {
        let NodeKind::Identifier(name) = self.node(node).1 else {
            return None;
        };
        if !name.is_local {
            return None;
        }
        let found = super::lookup(&scope?.scope, name.text)?;
        match &found.binding {
            super::Binding::Argument(argument)
                if argument.is_named_once || (is_printed && argument.is_built_alike) =>
            {
                Some((argument.expression, super::argument_context(argument)))
            }
            _ => None,
        }
    }

    // Whether TLC holds a set an expression builds as a set enumeration or an interval
    // (`Reducible`): a set enumeration (OPCODE_se), a map (OPCODE_soa) or `a..b`, written there or
    // as a LET definition built as it is written (`named_once_expression`).
    fn is_enumerated(&self, node: NodeId, scope: Option<&Context>) -> bool {
        if let Some((expression, context)) = self.named_once_expression(node, scope, true) {
            return self.is_enumerated(expression, Some(&context));
        }
        match self.node(node).1 {
            NodeKind::SetEnumeration(_) | NodeKind::SetMap { .. } => true,
            NodeKind::Apply { name, args } => {
                !name.is_local
                    && args.len() == 2
                    && matches!(name.resolution, Resolution::Builtin(index)
                        if self.builtin_name(index) == "..")
            }
            _ => false,
        }
    }

    // How the keys of `DOMAIN f` are built, where TLC holds that domain as a set enumeration or
    // an interval (`Reducible`) whatever it did with f: f a tuple (`TupleValue.getDomain`, also
    // of `\o`, Append and Tail, which build a `TupleValue` where they don't fail), a record (its
    // fields), `k :> v` (`FcnRcdValue`), or a function constructor over such a set, whose
    // `FcnLambdaValue.getDomain` is the set it evaluated, or the domain of the `FcnRcdValue` it
    // built (`toFcnRcd`), the same keys.
    fn reducible_domain_keys(&self, node: NodeId, scope: Option<&Context>) -> Option<Construction> {
        let NodeKind::Apply { name, args } = self.node(node).1 else {
            return None;
        };
        if name.is_local
            || !matches!(name.resolution, Resolution::Builtin(index)
                if self.builtin_name(index) == "DOMAIN")
        {
            return None;
        }
        let [function] = args.as_slice() else {
            return None;
        };
        let mut function = *function;
        let mut scope = scope.cloned();
        while let Some((expression, context)) =
            self.named_once_expression(function, scope.as_ref(), true)
        {
            function = expression;
            scope = Some(context);
        }
        let scope = scope.as_ref();
        match self.node(function).1 {
            NodeKind::Tuple(_) | NodeKind::Record(_) => Some(Construction::Held),
            NodeKind::Apply { name, args } if !name.is_local => {
                let Resolution::Builtin(index) = name.resolution else {
                    return None;
                };
                match (self.builtin_name(index), args.as_slice()) {
                    ("\\o" | "Append", [_, _]) | ("Tail", [_]) => Some(Construction::Held),
                    (":>", [key, _]) => Some(self.construction_of_node(*key, scope, true)),
                    _ => None,
                }
            }
            NodeKind::FunctionConstruction {
                is_recursive: false,
                bounds,
                ..
            } => match bounds.as_slice() {
                [bound]
                    if matches!(bound.pattern, Pattern::Name(_))
                        && self.is_enumerated(bound.set, scope) =>
                {
                    self.construction_of_node(bound.set, scope, true)
                        .of_elements()
                        .cloned()
                }
                _ => None,
            },
            _ => None,
        }
    }

    // `scope` as `printed_construction` takes it. With `is_printed`, the value is one Print or
    // PrintT prints, normalized (`deepNormalize`), whose text doesn't show how many elements a set
    // enumeration wrote: sets whose elements are built alike but for that join (`join_printed`).
    fn construction_of_node(
        &self,
        node: NodeId,
        scope: Option<&Context>,
        is_printed: bool,
    ) -> Construction {
        if let Some((expression, context)) = self.named_once_expression(node, scope, is_printed) {
            return self.construction_of_node(expression, Some(&context), is_printed);
        }
        let of = |node: &NodeId| self.construction_of_node(*node, scope, is_printed);
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
                    ("RandomSubsetSet" | "RandomSetOfSubsets", [_, _, base]) => as_set(base)
                        .and_then(|base| base.of_elements().cloned())
                        .filter(random_hash_shape_is_known)
                        .map_or(Construction::Held, |element| {
                            Construction::Set(
                                Box::new(Construction::Set(Box::new(element), None)),
                                None,
                            )
                        }),
                    ("SUBSET", [base]) => as_set(base).map_or(Construction::Held, |base| {
                        Construction::Subset(Box::new(base))
                    }),
                    (":>", [key, value]) => {
                        Construction::Function(Box::new(of(key)), Box::new(of(value)))
                    }
                    // `Tool`'s OPCODE_cup, OPCODE_cap and OPCODE_setdiff. Of two set
                    // enumerations, `SetEnumValue.cup`, `cap` and `diff` build a set enumeration
                    // of the operands' elements as they are, which prints as one; `cup` of an
                    // empty one is the other as it is. Of an interval, `IntervalValue.cap` and
                    // `diff` build one too, but its `cup` of an empty interval is the other set,
                    // which may be an interval, so a union of an interval stays unknown.
                    ("\\cup", [left, right]) if is_printed => printed_union(of(left), of(right)),
                    ("\\cup", [left, right]) => match (of(left), of(right)) {
                        (Construction::Set(left, _), Construction::Set(right, _))
                            if left == right =>
                        {
                            Construction::Set(left, None)
                        }
                        _ => Construction::Held,
                    },
                    ("\\cap", [left_node, right]) => match (as_set(left_node), as_set(right)) {
                        (Some(left), Some(right)) if left.of_elements() == right.of_elements() => {
                            left.of_elements().map_or(Construction::Held, |element| {
                                Construction::Set(Box::new(element.clone()), None)
                            })
                        }
                        // `SetEnumValue.cap` and `IntervalValue.cap` keep the left operand's
                        // elements that are members of the right, as they are, whatever the
                        // right is, where the left is one of them (`Reducible`).
                        (Some(left), _) if is_printed && self.is_enumerated(*left_node, scope) => {
                            left.of_elements().map_or(Construction::Held, |element| {
                                Construction::Set(Box::new(element.clone()), None)
                            })
                        }
                        (Some(left), Some(right)) if is_printed => left
                            .of_elements()
                            .zip(right.of_elements())
                            .and_then(|(left, right)| join_printed(left.clone(), right.clone()))
                            .map_or(Construction::Held, |element| {
                                Construction::Set(Box::new(element), None)
                            }),
                        _ => Construction::Held,
                    },
                    ("\\", [left, _]) => as_set(left)
                        .and_then(|left| left.of_elements().cloned())
                        .map_or(Construction::Held, |element| {
                            Construction::Set(Box::new(element), None)
                        }),
                    // `UnionValue.union`: of a set enumeration of set enumerations, a set
                    // enumeration of their elements as they are; otherwise a `UnionValue`, which
                    // prints as the set enumeration of them (`toSetEnum`).
                    ("UNION", [base]) => as_set(base)
                        .and_then(|base| {
                            base.of_elements()
                                .and_then(Construction::of_elements)
                                .cloned()
                        })
                        .map_or(Construction::Held, |element| {
                            Construction::Set(Box::new(element), None)
                        }),
                    _ => Construction::Held,
                }
            }
            // `Tool`'s OPCODE_soa builds a set enumeration of the expression's values.
            NodeKind::SetMap { expression, .. } => {
                Construction::Set(Box::new(of(expression)), None)
            }
            NodeKind::SetEnumeration(elements) if is_printed => {
                printed_enumeration(elements.iter().map(of), elements.len())
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
            // `new CounterExample()`, whose fields `TLCExt.error` writes as TLC sorts them.
            NodeKind::Identifier(name)
                if !name.is_local
                    && matches!(name.resolution, Resolution::Builtin(index)
                        if self.is_counter_example(index)) =>
            {
                let empty = || Construction::Set(Box::new(Construction::Held), Some(0));
                Construction::Record(vec![(utf16("action"), empty()), (utf16("state"), empty())])
            }
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
                // The domain of a tuple is an interval (`TupleValue.getDomain`).
                [bound]
                    if matches!(bound.pattern, Pattern::Name(_))
                        && matches!(self.node(bound.set).1, NodeKind::Apply { name, args }
                            if !name.is_local
                                && matches!(name.resolution, Resolution::Builtin(index)
                                    if self.builtin_name(index) == "DOMAIN")
                                && matches!(args.as_slice(), [tuple]
                                    if matches!(of(tuple), Construction::Tuple(_)))) =>
                {
                    Construction::Function(Box::new(Construction::Held), Box::new(of(body)))
                }
                // A function over the domain of a function TLC holds as one whose domain is a
                // set enumeration or an interval (`Reducible`): of a tuple, a record, or a
                // function built over such a set, TLC's `getDomain` is an interval or a set
                // enumeration of the keys as they are, whether or not TLC kept the function lazy
                // (`TupleValue`, `RecordValue`, `FcnRcdValue` and `FcnLambdaValue.getDomain`),
                // so OPCODE_fc builds a `FcnRcdValue` over those keys.
                [bound] if is_printed && matches!(bound.pattern, Pattern::Name(_)) => {
                    match self.reducible_domain_keys(bound.set, scope) {
                        Some(key) => Construction::Function(Box::new(key), Box::new(of(body))),
                        None => as_set(&bound.set)
                            .and_then(|domain| domain.of_elements().cloned())
                            .map_or(Construction::Held, |key| {
                                Construction::Function(Box::new(key), Box::new(of(body)))
                            }),
                    }
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
            })
            || self.writes_text_files();
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
            self.note_effect();
        }
        let evaluators: Vec<Eval> = compiled.into_iter().map(|operand| operand.eval).collect();
        let is_lines = name.starts_with("nd");
        // TLC evaluates the arguments before `MethodValue` casts the file to a StringValue.
        let read_path = move |machine: &Machine<'_>, path: Id| -> Outcome<String> {
            if machine.store.kind_of(path) != KIND_STRING {
                return Err(Bail(JSON_FILE_NOT_STRING));
            }
            String::from_utf16(machine.store.text_of(path))
                .map_err(|_| Bail("a Json operator's file with a lone surrogate"))
        };
        if !is_written {
            self.is_ranking = true;
            return Ok(leaf(
                eval(move |machine| {
                    let path = evaluators[0](machine)?;
                    let path = read_path(machine, path)?;
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
                    // TLC reads the file through a `FileReader`, which decodes it as Java does.
                    let text: Vec<u16> = bytes
                        .map_err(|()| Bail(JSON_FILE_UNREAD))
                        .map(|bytes| json::decode_file_text(&bytes))?;
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
                    let path = evaluators[0](machine)?;
                    let value = evaluators[1](machine)?;
                    let path = read_path(machine, path)?;
                    let store = &machine.store;
                    // `Value.toTuple` (and for JsonSerialize `Value.toRcd`) comes first.
                    if is_lines && store.kind_of(value) != KIND_TUPLE {
                        return Err(Bail(ND_JSON_SERIALIZE_NOT_SEQUENCE));
                    }
                    if !is_lines
                        && store.kind_of(value) != KIND_TUPLE
                        && !json::is_json_record(store, value)
                    {
                        return Err(Bail(JSON_SERIALIZE_NOT_SEQUENCE));
                    }
                    if json::holds_ordered_keys(store, value) {
                        return Err(Bail(
                            "a Json operator's record, whose fields TLC writes as it holds them",
                        ));
                    }
                    let mut text = Vec::new();
                    if is_lines {
                        for index in 0..store.size_of(value) {
                            json::write_json(
                                store,
                                store.get_range_value(value, index),
                                &mut text,
                            )?;
                            text.push(u16::from(b'\n'));
                        }
                    } else {
                        json::write_json(store, value, &mut text)?;
                    }
                    let text = String::from_utf16_lossy(&text);
                    if let JsonFiles::Host(written) = &files {
                        written.write(path, text.into_bytes());
                        return Ok(TRUE);
                    }
                    // TLC makes the file's directories first, whether or not it then can. A run
                    // that declines puts them and the file back as they were
                    // (`tla_values::written::restore`).
                    if let Some(parent) = std::path::Path::new(&path).parent() {
                        let _ = tla_values::written::create_dir_all(parent);
                    }
                    if tla_values::written::keep_file(std::path::Path::new(&path)).is_err() {
                        return Err(Bail(
                            "unsupported: a Json operator's file that can't be read before it is written",
                        ));
                    }
                    std::fs::write(&path, text).map_err(|_| Bail(JSON_FILE_UNWRITTEN))?;
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
            [operand] if operand.slot.is_none() => self
                .string_literal(operand.node, &operand.context)
                .map(str::to_owned),
            _ => None,
        };
        let key = key.as_deref();
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
        // A simulation has no model checker (`TLCGlobals.mainChecker` is null), whose counts
        // `TLCGetStringValue` fails to read: it words the NullPointerException as an undefined
        // key.
        if self.simulation.is_some()
            && key.is_some_and(|key| matches!(key, "generated" | "distinct" | "queue"))
        {
            return Ok(leaf(
                eval(|_| Err(Bail(TLC_GET_UNDEFINED_IN_SIMULATION))),
                Footprint::slot(super::REGISTER_SLOT),
            ));
        }
        // What a simulation reads of its run once TLC's simulator runs: as TLC starts, it has
        // none, and TLCGet fails, which the engine leaves (`TLCGetStringValue`).
        if self.simulation.is_some()
            && let Some(key) = key
                .filter(|key| matches!(*key, "diameter" | "action" | "stats" | "all" | "all:named"))
        {
            // The diameter is the number of the trace the worker generates, and 0 on TLC's main
            // thread, as it computes and checks the initial states: the slot the simulation
            // sets.
            if key == "diameter" {
                self.is_simulated_diameter_read = true;
                let slot = super::DIAMETER_SLOT;
                return Ok(leaf(
                    eval(move |machine| {
                        if !machine.simulation.is_running {
                            return Err(Bail(SIMULATION_NOT_RUNNING));
                        }
                        if machine.simulation.is_endless {
                            return Err(Bail(SIMULATION_ENDLESS_COUNT));
                        }
                        Ok(machine.locals[slot as usize])
                    }),
                    Footprint::slot(slot),
                ));
            }
            // TLC holds the record of its statistics with empty records, and the function of its
            // registers may be empty, which the store holds as the empty sequence.
            if key != "action" {
                let run = match key {
                    "stats" => SimulationRun::Stats,
                    _ => SimulationRun::Registers {
                        is_named: key == "all:named",
                    },
                };
                self.store.set_empty_tuple_ambiguous();
                return Ok(Compiled {
                    shape: Shape::SimulationRun(run),
                    ..leaf(run.guarded(), Footprint::slot(super::REGISTER_SLOT))
                });
            }
            return Ok(leaf(
                eval(move |machine| {
                    if !machine.simulation.is_running {
                        return Err(Bail(SIMULATION_NOT_RUNNING));
                    }
                    machine.simulation.action.ok_or(Bail(
                        "unsupported: TLCGet(\"action\") of an action the simulation doesn't record",
                    ))
                }),
                Footprint::slot(super::REGISTER_SLOT),
            ));
        }
        // A simulation's run, its statistics and its search keys differ from the model
        // checker's (`Simulator.getStatistics`).
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
        if key.is_some_and(is_unknown_tlc_get_key) {
            return Ok(leaf(
                eval(|_| Err(Bail(TLC_GET_UNKNOWN_KEY))),
                Footprint::slot(super::REGISTER_SLOT),
            ));
        }
        // A Java system property (`System.getProperty` with the key as the default): the key
        // itself for one nothing sets. The binary declines a command line that sets one the spec
        // names, and the engine one the JVM sets, but for the separators it knows.
        if let Some(key) = key.filter(|key| key.starts_with(JAVA_PROPERTY_PREFIX)) {
            let key = key.to_owned();
            let name = &key[JAVA_PROPERTY_PREFIX.len()..];
            // `System.getProperty` of an empty name throws ("key can't be empty"), which the
            // engine doesn't word.
            if name.is_empty() {
                return unsupported("TLCGet of a system property without a name");
            }
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
                _ => &key,
            };
            let units: Vec<u16> = value.encode_utf16().collect();
            let default = self.store.str(&units);
            // One TLCSet may have set (`System.setProperty`), which the run then reads.
            if !is_settable_property(name) || !self.may_set_registers() {
                return Ok(super::constant(default));
            }
            let name: Vec<u16> = name.encode_utf16().collect();
            return Ok(leaf(
                eval(move |machine| {
                    Ok(machine
                        .registers
                        .properties
                        .iter()
                        .find(|(set, _)| *set == name)
                        .map_or(default, |&(_, value)| value))
                }),
                Footprint::slot(super::REGISTER_SLOT),
            ));
        }
        // The specification's record, which the IR holds as the interpreter computes it for TLC's.
        if key == Some("spec")
            && let Some(index) = self.ir.model.tlc_spec
        {
            return Ok(super::constant(self.intern_value(index)?));
        }
        // A state of TLC's breadth-first search holds no action (`TLCState.getAction`), so
        // TLCGet("action") is the record of `Action.UNKNOWN` wherever it is evaluated.
        if key == Some("action") {
            return Ok(super::constant(self.unknown_action()?));
        }
        // The numbered registers, each the tuple of every worker's value
        // (`AbstractChecker.getAllValues`).
        if key == Some("all") && self.workers <= 1 {
            return Ok(leaf(
                eval(all_registers),
                Footprint::slot(super::REGISTER_SLOT),
            ));
        }
        // The counts of TLC's model checker as its one worker updates them, which the search
        // keeps where the spec reads them (`Search::set_counts`); the diameter only where the
        // search checks no temporal property, whose atoms read it otherwise.
        if let Some(slot) = self.count_slot(key.filter(|key| *key != "initial")) {
            if context.is_init && context.is_primed {
                return unsupported("TLCGet");
            }
            self.is_count_read = true;
            self.is_distinct_read = true;
            return Ok(Compiled {
                shape: Shape::Slot(slot),
                ..leaf(
                    eval(move |machine| Ok(machine.locals[slot as usize])),
                    Footprint::slot(slot),
                )
            });
        }
        if let Some(run_key @ ("stats" | "revision")) = key
            && let Some(compiled) = self.compile_run_record(run_key == "revision")?
        {
            return Ok(compiled);
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

    // TLCGet("stats") of TLC's model checker as its one worker reads it
    // (`AbstractChecker.getStatistics`): the counts the search keeps, the worker's number, 0 for
    // TLC's one worker and its main thread alike, and the seconds TLC has run; and
    // TLCGet("revision"), the record of TLC's build. Only TLC knows the time it has run and its
    // build, so the engine builds them only where the front end found the spec never reads them
    // (`Builtin::RUN_UNKNOWNS_UNREAD`): then they hold 0 and empty strings, which nothing shows.
    fn compile_run_record(&mut self, is_revision: bool) -> Compiling<Option<Compiled>> {
        let is_unread = self.ir.builtins.iter().any(|builtin| {
            builtin.flags & Builtin::RUN_UNKNOWNS_UNREAD != 0 && self.text(builtin.name) == "TLCGet"
        });
        if !is_unread {
            return Ok(None);
        }
        let text = |text: &str| text.encode_utf16().collect::<Vec<u16>>();
        if is_revision {
            let mut keys = Vec::new();
            let mut values = Vec::new();
            for (field, is_text) in [
                ("count", false),
                ("timestamp", false),
                ("date", true),
                ("tag", true),
                ("calver", true),
            ] {
                keys.push(self.store.str(&text(field)));
                values.push(if is_text {
                    self.store.str(&[])
                } else {
                    self.store.int(0)?
                });
            }
            return Ok(Some(super::constant(
                self.store.function_of(&keys, &values)?,
            )));
        }
        let mut slots = Vec::new();
        for field in ["queue", "initial", "generated", "diameter"] {
            let Some(slot) = self.count_slot(Some(field)) else {
                return Ok(None);
            };
            slots.push((field, slot));
        }
        slots.push(("distinct", DISTINCT_SLOT));
        self.is_count_read = true;
        self.is_distinct_read = true;
        let footprint = slots
            .iter()
            .fold(Footprint::default(), |footprint, &(_, slot)| {
                footprint.merge(&Footprint::slot(slot))
            });
        let mut keys: Vec<Id> = slots
            .iter()
            .map(|&(field, _)| self.store.str(&text(field)))
            .collect();
        keys.push(self.store.str(&text("duration")));
        keys.push(self.store.str(&text("worker")));
        let zero = self.store.int(0)?;
        let slots: Vec<u32> = slots.into_iter().map(|(_, slot)| slot).collect();
        Ok(Some(leaf(
            eval(move |machine| {
                let mut values: Vec<Id> = slots
                    .iter()
                    .map(|&slot| machine.locals[slot as usize])
                    .collect();
                values.extend([zero, zero]);
                machine.store.function_of(&keys, &values)
            }),
            footprint,
        )))
    }

    // Whether the builtin is TLCExt's CounterExample, as TLC's Java method computes it.
    fn is_counter_example(&self, index: Index) -> bool {
        let builtin = &self.ir.builtins[index as usize];
        self.is_native
            && builtin.arity == 0
            && builtin.flags & (Builtin::TABLE | Builtin::EXTERNAL_CLASS | Builtin::DECLINED) == 0
            && self.text(builtin.name) == "CounterExample"
    }

    // The record of `Action.UNKNOWN` (`new RecordValue(Action)`): its name and its location.
    fn unknown_action(&mut self) -> Outcome<Id> {
        let text = |text: &str| text.encode_utf16().collect::<Vec<u16>>();
        let mut keys = Vec::new();
        let mut values = Vec::new();
        for field in ["beginLine", "beginColumn", "endLine", "endColumn"] {
            keys.push(self.store.str(&text(field)));
            values.push(self.store.int(0)?);
        }
        keys.push(self.store.str(&text("module")));
        values.push(self.store.str(&text("--TLA+ BUILTINS--")));
        let location = self.store.function_of(&keys, &values)?;
        let keys = [
            self.store.str(&text("name")),
            self.store.str(&text("location")),
        ];
        let values = [self.store.str(&text("UnnamedAction")), location];
        self.store.function_of(&keys, &values)
    }

    // The slot the search keeps a count of TLC's model checker in, where it keeps it.
    fn count_slot(&self, key: Option<&str>) -> Option<u32> {
        if !self.is_native || self.workers > 1 || self.simulation.is_some() {
            return None;
        }
        match key? {
            "generated" => Some(super::GENERATED_SLOT),
            "queue" => Some(super::QUEUE_SLOT),
            "initial" => Some(super::INITIAL_SLOT),
            "diameter" if !self.ir.model.is_recording_graph => Some(super::DIAMETER_SLOT),
            _ => None,
        }
    }

    // A field of TLCGet("stats") written as TLCGet("stats").field, but its duration, which only
    // TLC knows (`AbstractChecker.getStatistics`): the count the search keeps, or the worker's
    // number, 0 for TLC's one worker and its main thread alike.
    pub(super) fn compile_statistic(
        &mut self,
        record: NodeId,
        field: tla_ir::TextId,
        context: &Context,
    ) -> Compiling<Option<Compiled>> {
        let NodeKind::Apply { name, args } = self.node(record).1 else {
            return Ok(None);
        };
        let Resolution::Builtin(index) = name.resolution else {
            return Ok(None);
        };
        let [key] = args.as_slice() else {
            return Ok(None);
        };
        if name.is_local
            || self.builtin_name(index) != "TLCGet"
            || self.ir.builtins[index as usize].flags & (Builtin::TABLE | Builtin::EXTERNAL_CLASS)
                != 0
            || self.string_literal(*key, context) != Some("stats")
        {
            return Ok(None);
        }
        let field = self.text(field);
        if field == "worker" && self.is_native && self.workers <= 1 && self.simulation.is_none() {
            return Ok(Some(super::constant(self.store.int(0)?)));
        }
        let key = match field {
            "distinct" => {
                if !self.is_native || self.workers > 1 || self.simulation.is_some() {
                    return Ok(None);
                }
                self.is_distinct_read = true;
                return Ok(Some(Compiled {
                    shape: Shape::Slot(DISTINCT_SLOT),
                    ..leaf(
                        eval(move |machine| Ok(machine.locals[DISTINCT_SLOT as usize])),
                        Footprint::slot(DISTINCT_SLOT),
                    )
                }));
            }
            "generated" | "queue" | "initial" | "diameter" => field,
            _ => return Ok(None),
        };
        let Some(slot) = self.count_slot(Some(key)) else {
            return Ok(None);
        };
        if context.is_init && context.is_primed {
            return unsupported("TLCGet");
        }
        self.is_count_read = true;
        self.is_distinct_read = true;
        Ok(Some(Compiled {
            shape: Shape::Slot(slot),
            ..leaf(
                eval(move |machine| Ok(machine.locals[slot as usize])),
                Footprint::slot(slot),
            )
        }))
    }

    // Whether the spec applies TLCSet, or TLCGetAndSet, which sets as it does.
    fn may_set_registers(&self) -> bool {
        self.ir
            .builtins
            .iter()
            .any(|builtin| matches!(self.text(builtin.name), "TLCSet" | "TLCGetAndSet"))
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
                (
                    "mode",
                    Field::Text(
                        if simulation.is_generated {
                            "generate"
                        } else {
                            "simulate"
                        }
                        .into(),
                    ),
                ),
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
    // The AssertError application of these operands whose value TLC computes the same wherever
    // it evaluates it (`TLCExt.assertError`): its message is a string written out, which TLC
    // checks it is, and its expression, written where no name is bound around it, reads no
    // variable, no register and nothing of the search, and has no effect, as TLC catches what it
    // throws. The caller's evaluator computes it.
    fn get_delegable_assert_error(
        &self,
        operands: &[Operand],
        context: &Context,
    ) -> Option<NodeId> {
        let [message, expression] = operands else {
            return None;
        };
        if message.is_param
            || expression.is_param
            || context.scope.is_some()
            || message.context.scope.is_some()
            || expression.context.scope.is_some()
            || !matches!(self.node(message.node).1, NodeKind::String(_))
            || !self.is_constant_and_pure(expression.node, &mut HashSet::new())
        {
            return None;
        }
        self.ir
            .nodes
            .arena
            .iter()
            .position(|candidate| {
                matches!(&candidate.kind, NodeKind::Apply { args, .. }
                if args.as_slice() == [message.node, expression.node])
            })
            .map(|node| node as NodeId)
    }

    // Whether an expression, through the definitions it names, reads no variable, no state of the
    // search and no register, applies no operator bound around it, and has no effect.
    fn is_constant_and_pure(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> bool {
        let (node, kind) = self.node(node);
        if !seen.insert(node) {
            return true;
        }
        let is_pure = match kind {
            NodeKind::Prime(_)
            | NodeKind::Unchanged(_)
            | NodeKind::Enabled(_)
            | NodeKind::Subexpression(_)
            | NodeKind::BoxAction { .. }
            | NodeKind::AngleAction { .. }
            | NodeKind::Always(_)
            | NodeKind::Eventually(_)
            | NodeKind::WeakFairness { .. }
            | NodeKind::StrongFairness { .. } => false,
            NodeKind::Apply { name, .. } if name.is_local => false,
            // TLCGet of a register written out as a number, in a spec that sets no register
            // (no TLCSet, TLCGetAndSet or _Track, and no Java class of the user's): TLC finds it
            // unset on every thread, and fails alike wherever it evaluates it
            // (`TLCGetSet.TLCGetEval`).
            NodeKind::Apply { name, args }
                if !name.is_local
                    && matches!(name.resolution, Resolution::Builtin(index)
                    if self.builtin_name(index) == "TLCGet"
                        && self.ir.builtins[index as usize].flags
                            & (Builtin::TABLE | Builtin::EXTERNAL_CLASS | Builtin::DECLINED)
                            == 0)
                    && matches!(args.as_slice(), [key] if matches!(self.node(*key).1, NodeKind::Number(index) if *index >= 0))
                    && !self.ir.builtins.iter().any(|builtin| {
                        builtin.flags & Builtin::EXTERNAL_CLASS != 0
                            || matches!(
                                self.text(builtin.name),
                                "TLCSet" | "TLCGetAndSet" | "_Track"
                            )
                    }) =>
            {
                true
            }
            NodeKind::Identifier(name)
            | NodeKind::Apply { name, .. }
            | NodeKind::OperatorReference(name)
                if !name.is_local =>
            {
                match name.resolution {
                    Resolution::Variable(_) | Resolution::None => false,
                    Resolution::Constant(_) => true,
                    Resolution::Definition(index) => {
                        let definition = self.definition(self.ir.definitions[index as usize]);
                        definition.flags & tla_ir::Definition::SUBSTITUTED == 0
                            && self.is_constant_and_pure(definition.body, seen)
                    }
                    Resolution::Builtin(index) => {
                        let builtin = &self.ir.builtins[index as usize];
                        let name = self.builtin_name(index);
                        (name == "AssertError"
                            || builtin.flags & (Builtin::STATE_LEVEL | Builtin::TABLE) == 0)
                            && !matches!(
                                name,
                                "Print"
                                    | "PrintT"
                                    | "AssertEq"
                                    | "JavaTime"
                                    | "RandomElement"
                                    | "RandomSubset"
                                    | "RandomSubsetSet"
                                    | "RandomSetOfSubsets"
                                    | "TestRandomSetOfSubsets"
                                    | "TLCSet"
                                    | "TLCGet"
                                    | "TLCGetOrDefault"
                                    | "TLCGetAndSet"
                                    | "_Track"
                                    | "TLCCache"
                                    | "TLCDefer"
                                    | "TLCModelValue"
                                    | "TLCEvalDefinition"
                                    | "PickSuccessor"
                                    | "Trace"
                                    | "CounterExample"
                                    | "ToTrace"
                                    | "\\cdot"
                                    | "JsonSerialize"
                                    | "ndJsonSerialize"
                                    | "JsonDeserialize"
                                    | "ndJsonDeserialize"
                                    | "IOExec"
                                    | "IOEnv"
                                    | "IOEnvExec"
                                    | "IOExecTemplate"
                                    | "IOEnvExecTemplate"
                                    | "Serialize"
                                    | "Deserialize"
                            )
                    }
                }
            }
            _ => true,
        };
        is_pure
            && kind
                .children()
                .into_iter()
                .all(|child| self.is_constant_and_pure(child, seen))
    }

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
        self.note_effect();
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
                    if machine.is_probing_registers {
                        // TLCSet of a named register, "exit" or "pause" sets nothing as TLC
                        // starts, with no checker or simulator yet, and gives TRUE.
                        let probed = probe_register(&machine.store, key);
                        if probed != PROBED_REGISTER_UNSET {
                            return Err(Bail(probed));
                        }
                        machine.has_probed_unset_register = true;
                        return Ok(TRUE);
                    }
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
        self.note_effect();
        // A Java method's arguments are evaluated once each, in order, before it runs
        // (`MethodValue.apply`), so the key and the default print where TLC computes them.
        let [key, default] = values.map(|operand| operand.clone());
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
                // As TLC processes the spec, before it has made its checker, TLCExt's
                // `tlcGetOrDefault` finds no register for any key, and gives the default.
                if machine.is_processing_constants && operator.is_none() {
                    return Ok(default);
                }
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

    // _Track(expr, name), which _Possible.tla defines as
    // `TLCSet("s:_possible", Op(TLCGetOrDefault("s:_possible", <<>>), expr))` with Op the LAMBDA
    // that counts name once more where expr holds, and adds it with a count of none where it
    // doesn't: TRUE, having counted. The LAMBDA tests expr first, then reads the register. TLC
    // builds the register's function in an order of its own, which shows only where the spec
    // reads it otherwise than through `_Counts`, so a spec that reads or sets registers itself,
    // checks `_POSSIBLE` predicates in the same register, or runs on several workers, whose
    // registers `_Counts` merges in an order of theirs, declines; so does a condition or a name
    // that fails in _Possible.tla's frames.
    fn compile_track(&mut self, operands: &[Operand], context: &Context) -> Compiling<Compiled> {
        if !context.can_print {
            return unsupported("_Track");
        }
        if self.workers > 1 {
            return unsupported("_Track on several workers");
        }
        if !self.ir.model.possible.is_empty()
            || self.ir.builtins.iter().any(|builtin| {
                matches!(
                    self.text(builtin.name),
                    "TLCGet" | "TLCSet" | "TLCGetOrDefault" | "TLCGetAndSet"
                )
            })
        {
            return unsupported("_Track in a spec that reads or sets registers otherwise");
        }
        let [condition, name] = operands else {
            return unsupported("an operator applied to the wrong number of arguments");
        };
        self.note_effect();
        let condition = self.operand(condition)?;
        let name = self.operand(&Operand {
            context: name.context.without_print(),
            ..name.clone()
        })?;
        // _Track of constants is of constant level, as TLCSet and TLCGetOrDefault have no
        // minimum level: TLC computes a definition without parameters that applies it as it
        // starts (`processConstantDefns`), on its main thread, which counts in no worker's
        // register.
        if condition.footprint.width() == 0 && name.footprint.width() == 0 {
            return unsupported("_Track of constants, which TLC may compute as it starts");
        }
        let footprint = condition
            .footprint
            .merge(&name.footprint)
            .merge(&Footprint::slot(super::REGISTER_SLOT))
            .merge(&Footprint::slot(super::PRINT_SLOT));
        let (condition, name) = (condition.eval, name.eval);
        Ok(Compiled {
            is_boolean: true,
            ..leaf(
                eval(move |machine| {
                    let holds = match condition(machine)? {
                        TRUE => true,
                        FALSE => false,
                        _ => {
                            return Err(Bail(
                                "unsupported: a _Track condition that isn't a boolean",
                            ));
                        }
                    };
                    let name = name(machine)?;
                    if machine.store.kind_of(name) != KIND_STRING {
                        return Err(Bail("unsupported: _Track of a name that isn't a string"));
                    }
                    let register: Vec<u16> = "s:_possible".encode_utf16().collect();
                    let register = machine.store.str(&register);
                    let old = machine
                        .registers
                        .named
                        .iter()
                        .find(|&&(named, _)| named == register)
                        .map(|&(_, value)| value);
                    let (mut keys, mut counts) = (Vec::new(), Vec::new());
                    if let Some(old) = old {
                        if machine.store.kind_of(old) != KIND_FUNCTION {
                            return Err(Bail("unsupported: _Track of a register set otherwise"));
                        }
                        for index in 0..machine.store.size_of(old) {
                            keys.push(machine.store.get_key(old, index));
                            counts.push(machine.store.get_range_value(old, index));
                        }
                    }
                    match keys.iter().position(|&key| key == name) {
                        Some(position) if holds => {
                            let count = counts[position];
                            if machine.store.kind_of(count) != KIND_INT
                                || machine.store.int_of(count) == i32::MAX
                            {
                                return Err(Bail("unsupported: _Track of a count past an int"));
                            }
                            counts[position] = machine
                                .store
                                .int(i64::from(machine.store.int_of(count)) + 1)?;
                        }
                        Some(_) => {}
                        None => {
                            keys.push(name);
                            counts.push(machine.store.int(i64::from(holds))?);
                        }
                    }
                    let new = machine.store.function_of(&keys, &counts)?;
                    set_register(machine, register, new)?;
                    Ok(TRUE)
                }),
                footprint,
            )
        })
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

    // TLCEvalDefinition(name) (`TLCExt.tlcDefByName`): the body of the root module's definition
    // of that name, evaluated as written where TLCEvalDefinition is, in its states, not the value
    // TLC keeps for the definition. Where TLC finds no such definition, one with parameters, or a
    // name that isn't a string, it fails, for the evaluator of failures to word.
    fn compile_evaluated_definition(
        &mut self,
        operands: &[Operand],
        context: &Context,
    ) -> Compiling<Compiled> {
        let [operand] = operands else {
            return unsupported("an operator applied to the wrong number of arguments");
        };
        if !operand.is_param
            && operand.slot.is_none()
            && let NodeKind::String(text) = self.node(operand.node).1
        {
            let text = *text;
            let found = self
                .ir
                .model
                .evaluated_definitions
                .iter()
                .find(|(name, _)| *name == text)
                .map(|(_, found)| *found);
            return match found {
                Some(EvaluatedDefinition::Body(index)) => {
                    let node = self.ir.definitions[index as usize];
                    if context.is_expanding(node) {
                        return unsupported("TLCEvalDefinition of a definition it is written in");
                    }
                    let body = self.definition(node).body;
                    let body_context = Context {
                        expanding: context.expanding_with(node),
                        ..context.global(context.can_print)
                    };
                    let compiled = self.compile(body, &body_context)?;
                    Ok(Self::mark_costly(compiled))
                }
                Some(EvaluatedDefinition::Signature(_) | EvaluatedDefinition::Missing) => Ok(leaf(
                    eval(|_| Err(Bail(DEFINITION_NOT_EVALUATED))),
                    Footprint::default(),
                )),
                None => unsupported("TLCEvalDefinition of a name the front end didn't look up"),
            };
        }
        let operand = self.operand(operand)?;
        Ok(unary(
            &operand,
            |machine, name| {
                Err(Bail(if machine.store.kind_of(name) == KIND_STRING {
                    "unsupported: TLCEvalDefinition of a name the front end didn't look up"
                } else {
                    DEFINITION_NOT_EVALUATED
                }))
            },
            false,
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
        // TLC reads its cache as the tool object of e's node, which for a numeral or a string is
        // the value `SpecProcessor.processConstants` gave it: the cast to a HashMap fails after
        // the key is evaluated, which the evaluator reports.
        if matches!(self.node(node).1, NodeKind::Number(_) | NodeKind::String(_)) {
            let (evaluate_key, footprint) = (key.eval, key.footprint);
            return Ok(leaf(
                eval(move |machine| {
                    evaluate_key(machine)?;
                    Err(Bail(TLC_CACHE_OF_LITERAL))
                }),
                footprint,
            ));
        }
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
                // TLC initializes the value it caches (`value.initialize()`), which normalizes
                // and fingerprints it, and fails where it can't.
                machine
                    .fingerprints
                    .get_state(&machine.store, &[value], &[0])?;
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
                store.kind_of(sequence) == KIND_TUPLE && !store.comparison_can_fail(sequence)
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

    // Direct scalar literals can be held in TLC's SetEnumValue without interning or sorting.
    // This capability belongs to the consuming expression and never follows a binding.
    fn written_scalar_elements(&mut self, operand: &Operand) -> Compiling<Option<Vec<Eval>>> {
        if operand.is_param || operand.slot.is_some() {
            return Ok(None);
        }
        let NodeKind::SetEnumeration(items) = self.node(operand.node).1 else {
            return Ok(None);
        };
        let items = items.clone();
        if !items.iter().all(|&node| self.is_scalar_literal(node)) {
            return Ok(None);
        }
        items
            .iter()
            .map(|&node| self.compile(node, &operand.context).map(|c| c.eval))
            .collect::<Compiling<Vec<_>>>()
            .map(Some)
    }

    fn direct_named_infinite(&self, operand: &Operand) -> bool {
        !operand.is_param
            && operand.slot.is_none()
            && matches!(self.node(operand.node).1, NodeKind::Identifier(name)
                if !name.is_local && matches!(name.resolution, Resolution::Builtin(index)
                    if matches!(self.builtin_name(index), "Int" | "Nat" | "STRING")))
    }

    pub(crate) fn mixed_scalar_elements(&self, operand: &Operand) -> bool {
        if operand.is_param || operand.slot.is_some() {
            return false;
        }
        let NodeKind::SetEnumeration(items) = self.node(operand.node).1 else {
            return false;
        };
        let mut kinds = HashSet::new();
        for &item in items {
            let kind = match self.node(item).1 {
                NodeKind::Number(_) => 0,
                NodeKind::String(_) => 1,
                NodeKind::Identifier(name)
                    if !name.is_local
                        && matches!(name.resolution, Resolution::Builtin(index)
                    if matches!(self.builtin_name(index), "TRUE" | "FALSE")) =>
                {
                    2
                }
                _ => return false,
            };
            kinds.insert(kind);
        }
        kinds.len() > 1
    }

    // A set enumeration written in place whose elements are number, string or boolean literals
    // and at least one INSTANCE fact literal TLC did not initialize: `Tool`'s OPCODE_se holds the
    // nulls in a `SetEnumValue` without reading them, and `FiniteSets.IsFiniteSet` asks it
    // `isFinite`, which is TRUE without reading its elements. None of them has an effect or fails.
    pub(crate) fn null_literal_elements(&self, operand: &Operand) -> bool {
        if operand.is_param || operand.slot.is_some() {
            return false;
        }
        let NodeKind::SetEnumeration(items) = self.node(operand.node).1 else {
            return false;
        };
        let mut has_null = false;
        for &item in items {
            if self.is_uninitialized_literal(item) {
                has_null = true;
                continue;
            }
            match self.node(item).1 {
                NodeKind::Number(_) | NodeKind::String(_) => {}
                NodeKind::Identifier(name)
                    if !name.is_local
                        && matches!(name.resolution, Resolution::Builtin(index)
                    if matches!(self.builtin_name(index), "TRUE" | "FALSE")) => {}
                _ => return false,
            }
        }
        has_null
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
                    self.compile_filter_compared(&operands[0], &operands[1], name == "=")?
                {
                    return Ok(Some(compared));
                }
                if let Some(compared) =
                    self.compile_sub_seqs_equal(&operands[0], &operands[1], name == "=")?
                {
                    return Ok(Some(compared));
                }
                if let Some(compared) =
                    self.compile_seq_equal(&operands[0], &operands[1], name == "=")?
                {
                    return Ok(Some(compared));
                }
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                let lazy = self.lazy_compared(&operands[0], &left, &operands[1], &right);
                let intervals = self.interval_compared(&operands[0], &left, &operands[1], &right);
                let bounded = self.bounded_compared(&operands[0], &left, &operands[1], &right);
                let (left, right) = Self::compared(left, right);
                let is_equal = name == "=";
                let compiled = predicate_node(
                    Predicate::Equal {
                        left: Leaf::of(&left),
                        right: Leaf::of(&right),
                        is_equal,
                    },
                    left.footprint.merge(&right.footprint),
                );
                let compiled = match (lazy, intervals) {
                    (Some((left, right)), _) => Self::lazy_equal(compiled, left, right, is_equal),
                    (None, Some(bounds)) => Self::interval_equal(compiled, bounds, is_equal),
                    (None, None) => compiled,
                };
                let compiled = match bounded {
                    Some(bounded) => Self::bounded_equal(compiled, bounded, is_equal),
                    None => compiled,
                };
                let mixed = [0, 1].map(|index| self.mixed_scalar_elements(&operands[index]));
                let other = usize::from(mixed[0]);
                if mixed[0] == mixed[1]
                    || self.may_have_effect_in(
                        operands[other].node,
                        &operands[other].context,
                        &mut HashSet::new(),
                    )
                {
                    return Ok(Some(compiled));
                }
                // An untyped model value equals no other value, which neither its `equals` nor a
                // set enumeration's asks anything of (`ModelValue.equals`, `modelValueEquals`), so
                // TLC never normalizes a set enumeration held as written there, whose elements
                // don't compare. The engine can't hold one; elsewhere the equality as compiled
                // fails as before.
                let other_eval = if other == 0 { &left } else { &right }.eval.clone();
                let fallback = compiled.eval.clone();
                Compiled {
                    is_costly: true,
                    is_boolean: true,
                    ..leaf(
                        eval(move |machine| match other_eval(machine) {
                            Ok(id)
                                if machine.store.kind_of(id) == KIND_MODEL
                                    && machine.store.get_model_type(id) == 0 =>
                            {
                                Ok(bool_id(!is_equal))
                            }
                            _ => fallback(machine),
                        }),
                        compiled.footprint.clone(),
                    )
                }
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
                if self.mixed_scalar_elements(&operands[0])
                    && !self.mixed_scalar_elements(&operands[1])
                    && reducibility(&set) == Some(true)
                    && !self.may_have_effect_in(
                        operands[1].node,
                        &operands[1].context,
                        &mut HashSet::new(),
                    )
                {
                    // An empty set enumeration or interval holds nothing, without asking the
                    // element anything (`ValueVec.search`, `IntervalValue.member`), so TLC never
                    // normalizes a set enumeration held as written there, whose elements don't
                    // compare. The engine can't hold one; elsewhere the membership as compiled
                    // fails as before.
                    let set_eval = set.eval.clone();
                    let test = self.member_test(&set);
                    let element_eval = element.eval.clone();
                    return Ok(Some(Compiled {
                        is_costly: true,
                        is_boolean: true,
                        ..leaf(
                            eval(move |machine| match set_eval(machine) {
                                Ok(id)
                                    if machine.store.kind_of(id) == KIND_SET
                                        && machine.store.size_of(id) == 0 =>
                                {
                                    Ok(bool_id(!is_in))
                                }
                                _ => {
                                    let value = element_eval(machine)?;
                                    Ok(bool_id(test(machine, value)? == is_in))
                                }
                            }),
                            footprint,
                        )
                    }));
                }
                if self.mixed_scalar_elements(&operands[1])
                    && let Some(written) = self.written_scalar_elements(&operands[1])?
                {
                    let evaluate = element.eval.clone();
                    return Ok(Some(Compiled {
                        is_boolean: true,
                        ..leaf(
                            eval(move |machine| {
                                let value = evaluate(machine)?;
                                let values = written
                                    .iter()
                                    .map(|evaluate| evaluate(machine))
                                    .collect::<Outcome<Vec<_>>>()?;
                                for held in values {
                                    if machine.store.equals_asked(held, value)? {
                                        return Ok(bool_id(is_in));
                                    }
                                }
                                Ok(bool_id(!is_in))
                            }),
                            footprint,
                        )
                    }));
                }
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
                let intervals = self.interval_compared(&operands[0], &left, &operands[1], &right);
                let compiled = self.compile_subseteq(&left, &right);
                let compiled = match intervals {
                    Some(bounds) => Self::interval_subseteq(compiled, bounds),
                    None => compiled,
                };
                if !self.mixed_scalar_elements(&operands[1])
                    || self.mixed_scalar_elements(&operands[0])
                    || reducibility(&left) != Some(true)
                    || self.may_have_effect_in(
                        operands[0].node,
                        &operands[0].context,
                        &mut HashSet::new(),
                    )
                {
                    return Ok(Some(compiled));
                }
                let Some(written) = self.written_scalar_elements(&operands[1])? else {
                    return Ok(Some(compiled));
                };
                // `EnumerableValue.isSubsetEq` of a set enumeration or an interval S asks a set
                // enumeration T held as written whether it holds each of S's elements in turn,
                // in S's normalized order, up to the first T lacks: T's `member` searches its
                // written elements, normalizing nothing (`ValueVec.search`). The engine can't
                // hold T, whose elements don't compare; wherever this doesn't compute, the
                // operation as compiled fails as before.
                let fallback = compiled.eval.clone();
                let left_eval = left.eval.clone();
                compiled.with_eval(eval(move |machine| {
                    let mut computed = || -> Outcome<Id> {
                        let set = evaluate_set(machine, &left_eval, "expected a set")?;
                        let values = written
                            .iter()
                            .map(|evaluate| evaluate(machine))
                            .collect::<Outcome<Vec<_>>>()?;
                        for index in 0..machine.store.size_of(set) {
                            let element = machine.store.element_at(set, index);
                            if !written_holds(machine, &values, element)? {
                                return Ok(FALSE);
                            }
                        }
                        Ok(TRUE)
                    };
                    match computed() {
                        Ok(value) => Ok(value),
                        Err(_) => fallback(machine),
                    }
                }))
            }
            "\\cup" | "\\cap" | "\\" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                let direct = if name != "\\cup"
                    && self.mixed_scalar_elements(&operands[0])
                    && self.direct_named_infinite(&operands[1])
                {
                    Some((0, &right))
                } else if name == "\\cap"
                    && self.direct_named_infinite(&operands[0])
                    && self.mixed_scalar_elements(&operands[1])
                {
                    Some((1, &left))
                } else {
                    None
                };
                if let Some((index, tested)) = direct
                    && let Some(written) = self.written_scalar_elements(&operands[index])?
                {
                    let test = self.member_test(tested);
                    return Ok(Some(leaf(
                        eval(move |machine| {
                            let values = written
                                .iter()
                                .map(|evaluate| evaluate(machine))
                                .collect::<Outcome<Vec<_>>>()?;
                            for value in values {
                                test(machine, value)?;
                            }
                            Err(Bail("a mixed scalar set tested against an infinite set"))
                        }),
                        left.footprint.merge(&right.footprint),
                    )));
                }
                let has_effect = operands.iter().any(|operand| {
                    self.may_have_effect_in(operand.node, &operand.context, &mut HashSet::new())
                });
                let mixed = [0, 1].map(|index| self.mixed_scalar_elements(&operands[index]));
                let compiled = self.compile_set_operation(name, &left, &right, has_effect)?;
                // `SetEnumValue.cap` and `diff` test the set enumeration's elements in the other
                // set, an interval by its bounds (`IntervalValue.member`), without building it.
                let is_filtered = name != "\\cup"
                    && !has_effect
                    && operands.iter().all(|operand| !operand.is_param)
                    && left.is_enumerated
                    && left.infinite.is_none()
                    && !left.has_infinite_part;
                let compiled = match (compiled, right.interval.clone()) {
                    (Some(compiled), Some((low, high))) if is_filtered => {
                        Some(Self::interval_filtered(
                            compiled,
                            left.eval.clone(),
                            [low, high],
                            name == "\\cap",
                        ))
                    }
                    (compiled, _) => compiled,
                };
                let compiled =
                    compiled.map(|compiled| Self::bounded_operation(compiled, name == "\\cup"));
                if name == "\\cup" || mixed[0] == mixed[1] || has_effect {
                    return Ok(compiled);
                }
                let Some(compiled) = compiled else {
                    return Ok(None);
                };
                let index = usize::from(mixed[1]);
                let Some(written) = self.written_scalar_elements(&operands[index])? else {
                    return Ok(Some(compiled));
                };
                let other = if index == 0 { &right } else { &left };
                return Ok(Some(Self::bounded_operation(
                    self.compile_written_reduction(
                        name == "\\cap",
                        index == 0,
                        written,
                        other,
                        compiled,
                    ),
                    false,
                )));
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
                // `UnionValue.union` of set enumerations adds each element it lacks to a
                // ValueVec, which fails once it holds `TLCGlobals.setBound` elements and is given
                // another. TLC builds a UNION it keeps lazy only where it enumerates it.
                let compiled = if is_enumerated || reference.is_none() {
                    let built = compiled.eval.clone();
                    compiled.with_eval(eval(move |machine| {
                        let id = built(machine)?;
                        if machine.store.kind_of(id) == KIND_SET
                            && machine.store.size_of(id) as usize > tla_values::SET_BOUND
                        {
                            return Err(if is_enumerated {
                                tla_values::SET_BOUND_EXCEEDED
                            } else {
                                Bail(UNKNOWN_OPERATION_PAST_SET_BOUND)
                            });
                        }
                        Ok(id)
                    }))
                } else {
                    compiled
                };
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
                let operand = &operands[0];
                // TLC evaluates DOMAIN's operand once, as it evaluates the application
                // (`Tool`'s OPCODE_domain), so TestRandomSetOfSubsets there draws its five
                // subsets before the domain is read.
                if operand.slot.is_none() && self.is_test_draws(operand.node) {
                    let drawn = self.compile(operand.node, &operand.context)?;
                    let footprint = drawn.footprint.clone();
                    let drawn = drawn.eval;
                    return Ok(Some(leaf(
                        eval(move |machine| {
                            let function = drawn(machine)?;
                            Ok(machine.store.domain_of(function))
                        }),
                        footprint,
                    )));
                }
                // A recursive function's domain, which TLC reads without applying it.
                if operand.slot.is_none()
                    && let Some(recursive) =
                        self.get_applied_recursive_function(operand.node, &operand.context)?
                {
                    return Ok(Some(recursive.domain.clone()));
                }
                // `RecordValue.getDomain` and `TupleValue.getDomain` read none of the values.
                let nulls: Vec<NodeId> = if operand.slot.is_none() {
                    self.null_fields(operand.node)
                        .into_iter()
                        .flatten()
                        .map(|(node, _)| node)
                        .collect()
                } else {
                    Vec::new()
                };
                let function =
                    self.with_null_substituted(&nulls, |compiler| compiler.operand(operand))?;
                // `RecordValue.getDomain` and `FcnRcdValue.getDomain` of a simulation's run.
                let function = unguarded(function);
                let domain = unary(
                    &function,
                    |machine, function| {
                        if lazy_function::is_lazy(machine, function) {
                            return lazy_function::domain_value(machine, function);
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
                // TLC's text of a simulation's run, which the engine declines to write where it
                // holds the empty sequence.
                let value = unguarded(self.operand(&operands[0])?);
                // The native checker writes a value as TLC does one built as the operand writes
                // it.
                let construction = if self.is_native {
                    self.construction_of(&operands[0])
                } else {
                    Construction::Held
                };
                let is_written = self.may_write_held(operands[0].node, false);
                // TLC writes Nat, Int and STRING by their names (`UserValue.toString`), which the
                // engine holds as values to write them.
                let evaluate = match value.infinite_value {
                    Some(name) => eval(move |machine| Ok(machine.store.infinite_set(name))),
                    None => value.eval.clone(),
                };
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
                // TLC fingerprints a model value by the intern number of its name
                // (`ModelValue.fingerPrint`, `UniqueString.fingerPrint`'s `tok`), which TLCFP
                // shows and which seeds the draws of each state a worker expands. The IR ranks
                // texts in TLC's order, but as TLC numbers them only those it interns first.
                let is_fingerprint_shown = self.ir.builtins.iter().any(|builtin| {
                    matches!(
                        &*self.ir.texts[builtin.name as usize],
                        "TLCFP"
                            | "RandomElement"
                            | "RandomSubset"
                            | "RandomSetOfSubsets"
                            | "RandomSubsetSet"
                            | "TestRandomSetOfSubsets"
                    )
                });
                if !is_fingerprint_shown {
                    return Ok(Some(unary(&name, model_value, false)));
                }
                let numbered = self.ir.get_numbered_rank_count();
                // The root module's name TLC numbers as the IR ranks it, which TLCFP shows as
                // TLC prints it; a model that draws from a set that may hold a model value, which
                // TLC orders by its number as it draws, declines it still, as main did. A draw of
                // TLC's or Randomization's from a set of numbers it writes (`RandomElement({1,
                // 2})`, `RandomSubset(1, {1, 2})`) holds none.
                let is_draw = |name: &str| {
                    matches!(
                        name,
                        "RandomElement"
                            | "RandomSubset"
                            | "RandomSetOfSubsets"
                            | "RandomSubsetSet"
                            | "TestRandomSetOfSubsets"
                    )
                };
                let is_numbers = |node: NodeId| match &self.ir.nodes.arena[node as usize].kind {
                    NodeKind::SetEnumeration(elements) => elements.iter().all(|&element| {
                        matches!(
                            self.ir.nodes.arena[element as usize].kind,
                            NodeKind::Number(_)
                        )
                    }),
                    _ => false,
                };
                let is_drawn = self
                    .ir
                    .builtins
                    .iter()
                    .any(|builtin| is_draw(&self.ir.texts[builtin.name as usize]))
                    && self.ir.nodes.arena.iter().any(|node| {
                        let NodeKind::Apply { name, args } = &node.kind else {
                            return false;
                        };
                        let Resolution::Builtin(index) = name.resolution else {
                            return is_draw(&self.ir.texts[name.text as usize]);
                        };
                        let builtin = &self.ir.builtins[index as usize];
                        let builtin_name = &*self.ir.texts[builtin.name as usize];
                        is_draw(builtin_name)
                            && !match (builtin_name, &args[..]) {
                                ("RandomElement", [set]) => is_numbers(*set),
                                ("RandomSubset", [size, set]) => {
                                    matches!(
                                        self.ir.nodes.arena[*size as usize].kind,
                                        NodeKind::Number(_)
                                    ) && is_numbers(*set)
                                }
                                _ => false,
                            }
                    });
                let root_name = self.ir.get_root_name_rank().filter(|_| !is_drawn);
                let evaluate = name.eval.clone();
                leaf(
                    eval(move |machine| {
                        let name = evaluate(machine)?;
                        let value = model_value(machine, name)?;
                        let rank = machine.store.text_rank_of(value);
                        if rank >= numbered && Some(rank) != root_name {
                            return Err(Bail(UNNUMBERED_MODEL_VALUE));
                        }
                        Ok(value)
                    }),
                    name.footprint.clone(),
                )
            }
            "Len" => {
                arity(1)?;
                // `Sequences.Len` of a TupleValue reads its size, none of its elements.
                let operand = &operands[0];
                let nulls: Vec<NodeId> = if operand.slot.is_none()
                    && matches!(self.node(operand.node).1, NodeKind::Tuple(_))
                {
                    self.null_fields(operand.node)
                        .into_iter()
                        .flatten()
                        .map(|(node, _)| node)
                        .collect()
                } else {
                    Vec::new()
                };
                let sequence =
                    self.with_null_substituted(&nulls, |compiler| compiler.operand(operand))?;
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
                let is_packaged = self.ir.builtins.iter().all(|builtin| {
                    builtin.flags & Builtin::EXTERNAL_CLASS == 0
                        && (!matches!(self.text(builtin.name), "Nat" | "Int" | "STRING" | "Seq")
                            || builtin.flags == 0)
                });
                if !is_packaged {
                    return Ok(Some(binary(
                        &sequence,
                        &element,
                        |machine, sequence, element| {
                            let tuple = expect_sequence(machine, sequence)?;
                            Ok(machine.store.append_tuple(tuple, element))
                        },
                        false,
                        false,
                    )));
                }
                let sequence_parts = (sequence.infinite_value.is_some()
                    || sequence.infinite == Some("Seq"))
                .then(|| Self::parts_of(&sequence));
                let element_parts = Self::parts_of(&element);
                let footprint = sequence.footprint.merge(&element.footprint);
                let sequence = sequence.eval;
                let element = element.eval;
                leaf(
                    eval(move |machine| {
                        // TLC builds both values before Append converts its first argument. A named
                        // infinite set is a nonsequence; its construction needn't enumerate it.
                        if let Some(parts) = &sequence_parts {
                            machine.run_parts(parts)?;
                            machine.run_parts(&element_parts)?;
                            return Err(Bail("expected a sequence"));
                        }
                        let sequence = sequence(machine)?;
                        if machine.store.kind_of(sequence) != KIND_TUPLE {
                            machine.run_parts(&element_parts)?;
                            return Err(Bail("expected a sequence"));
                        }
                        let element = element(machine)?;
                        Ok(machine.store.append_tuple(sequence, element))
                    }),
                    footprint,
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
                    ..leaf(eval(|_| Err(Bail(ENUMERATED_SEQ))), base.footprint.clone())
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
                        && (!set.is_normalized || set.is_enumerated)
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
                    // `IntervalValue.size`, which counts the interval without building it and
                    // fails where it has more than 2^31 - 1 elements.
                    None if set.interval.is_some() => {
                        let (low, high) = set.interval.clone().expect("an interval");
                        Compiled {
                            is_costly: true,
                            ..leaf(
                                eval(move |machine| {
                                    let size = match fused::interval_size(machine, &low, &high)? {
                                        Some(size) => size,
                                        None => return Err(Bail("an interval too large to build")),
                                    };
                                    machine.store.int(size)
                                }),
                                set.footprint.clone(),
                            )
                        }
                    }
                    // `SubsetValue.size`: 2^n of a base of n elements, which fails from 31 on.
                    None if set
                        .subset_base
                        .as_ref()
                        .is_some_and(|base| base.is_normalized && base.infinite.is_none()) =>
                    {
                        let base = set.subset_base.as_ref().expect("a base").eval.clone();
                        Compiled {
                            is_costly: true,
                            ..leaf(
                                eval(move |machine| {
                                    let base = base(machine)?;
                                    let base = expect_set(machine, base, "expected a set")?;
                                    let size = machine.store.size_of(base) as usize;
                                    if size >= super::lazy::OVERFLOWING_SUBSET_BASE {
                                        return Err(Bail(super::lazy::SUBSET_OVERFLOW));
                                    }
                                    machine.store.int(1 << size)
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
                let mut key = self.operand(&operands[0])?;
                let mut value = self.operand(&operands[1])?;
                // MakeFcn holds its operands as values without enumerating either one.
                for operand in [&mut key, &mut value] {
                    if let Some(name) = operand.infinite_value {
                        operand.eval = eval(move |machine| Ok(machine.store.infinite_set(name)));
                    }
                }
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

    // `S \cap T` or `S \ T` where one operand is a set enumeration of scalars of more than one
    // kind, which TLC holds as written, unnormalized (`SetEnumValue`), and the engine can't hold.
    // TLC reduces the operation by the left operand where it is Reducible, else an intersection
    // by the right one (OPCODE_cap, OPCODE_setdiff): `SetEnumValue.cap` and `diff` keep the
    // elements of the set they reduce that the other operand holds or lacks, asking the other's
    // `member`, which for the written set searches its written elements, normalizing nothing
    // (`ValueVec.search`). The engine computes that where every element kept compares with every
    // other; wherever it doesn't, the operation as compiled fails as before. Neither operand has
    // an effect, so evaluating them again changes nothing.
    fn compile_written_reduction(
        &self,
        is_cap: bool,
        is_written_left: bool,
        written: Vec<Eval>,
        other: &Compiled,
        compiled: Compiled,
    ) -> Compiled {
        let other_reducible = reducibility(other);
        let reduces_written = is_written_left || (is_cap && other_reducible == Some(false));
        let reduces_other = !is_written_left && other_reducible == Some(true);
        if !reduces_written && !reduces_other {
            return compiled;
        }
        let fallback = compiled.eval.clone();
        let other_eval = other.eval.clone();
        let other_test = self.member_test(other);
        compiled.with_eval(eval(move |machine| {
            let mut computed = || -> Outcome<Id> {
                let values = written
                    .iter()
                    .map(|evaluate| evaluate(machine))
                    .collect::<Outcome<Vec<_>>>()?;
                let other = other_eval(machine)?;
                let mut kept = Vec::new();
                if reduces_written {
                    for value in values {
                        if other_test(machine, value)? == is_cap {
                            kept.push(value);
                        }
                    }
                } else {
                    let other = expect_set(machine, other, "expected a set")?;
                    for index in 0..machine.store.size_of(other) {
                        let element = machine.store.element_at(other, index);
                        if written_holds(machine, &values, element)? == is_cap {
                            kept.push(element);
                        }
                    }
                }
                machine.store.set_of(&kept)
            };
            match computed() {
                Ok(value) => Ok(value),
                Err(_) => fallback(machine),
            }
        }))
    }

    // TLC reduces a union of two Reducible sets, an intersection with one and a difference from
    // one at once (`IntervalValue.cup`, `SetEnumValue.cap`, `diff`), adding each element it keeps
    // to a ValueVec, which fails once it holds `TLCGlobals.setBound` elements and is given
    // another. A set it keeps lazy (SetCupValue, SetCapValue, SetDiffValue) is built only where
    // it is enumerated.
    fn bounded_operation(compiled: Compiled, is_cup: bool) -> Compiled {
        // A union TLC reduces is bounded as it is computed, where its receiver is known.
        if compiled.is_irreducible || (is_cup && compiled.is_reducible) {
            return compiled;
        }
        let is_reduced = compiled.is_reducible;
        let built = compiled.eval.clone();
        compiled.with_eval(eval(move |machine| {
            let id = built(machine)?;
            if machine.store.kind_of(id) == KIND_SET
                && machine.store.size_of(id) as usize > tla_values::SET_BOUND
            {
                return Err(if is_reduced {
                    tla_values::SET_BOUND_EXCEEDED
                } else {
                    Bail(UNKNOWN_OPERATION_PAST_SET_BOUND)
                });
            }
            Ok(id)
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
        let is_reducible = reducibility;
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
        let operand_parts = self.once_a_round(
            vec![Self::parts_of(left), Self::parts_of(right), reduction],
            &[left, right],
        );
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
                        // `cap` and `diff` collect what they keep, which fails past TLC's bound.
                        if kept.len() > tla_values::SET_BOUND {
                            return Err(Bail(super::lazy::COLLECTED_PAST_BOUND));
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
        // Where an operand isn't a set, TLC still computes the operation when the Reducible
        // operand it reduces by is empty, without testing the other for an element: an empty
        // SetEnumValue or IntervalValue's `cup` returns the other operand as it is, and its `cap`
        // and `diff` the empty set (OPCODE_cup, OPCODE_cap, OPCODE_setdiff, which take the left
        // operand's method where it is Reducible, else the right one's for `\cup` and `\cap`).
        // A non-set value is never Reducible.
        let empty_reducing = (
            is_reducible(left) == Some(true),
            is_reducible(right) == Some(true),
        );
        let is_cup = name == "\\cup";
        let is_diff = name == "\\";
        let collected_operator = match name {
            "\\cup" => Operator::Union,
            "\\cap" => Operator::Intersection,
            _ => Operator::Difference,
        };
        let mut compiled = binary(left, right, operation, true, false);
        let (left_eval, right_eval) = (left.eval.clone(), right.eval.clone());
        compiled = compiled.with_eval(eval(move |machine| {
            let left = left_eval(machine)?;
            let right = right_eval(machine)?;
            let is_set = |machine: &Machine<'_>, id| machine.store.kind_of(id) == KIND_SET;
            if is_set(machine, left) && is_set(machine, right) {
                let result = operation(machine, left, right)?;
                // Where TLC may reduce the operation, it collects the elements at once, which
                // fails past its bound (`IntervalValue.cup` and `SetEnumValue.cup` return the
                // other set where they are empty); one it keeps lazy collects them only where it
                // converts it.
                return if is_irreducible {
                    Ok(result)
                } else {
                    super::lazy::collected(machine, collected_operator, left, result)
                };
            }
            let is_empty = |machine: &Machine<'_>, id| machine.store.size_of(id) == 0;
            let (left_reducible, right_reducible) = empty_reducing;
            if is_set(machine, left) && left_reducible && is_empty(machine, left) {
                return Ok(if is_cup { right } else { EMPTY_SET });
            }
            if !is_diff
                && !is_set(machine, left)
                && is_set(machine, right)
                && right_reducible
                && is_empty(machine, right)
            {
                return Ok(if is_cup { left } else { EMPTY_SET });
            }
            Err(Bail(NON_SET_OPERAND))
        }));
        if name != "\\cup" && is_reduced && (is_lazy(left) || is_lazy(right)) {
            let operator = if name == "\\cap" {
                Operator::Intersection
            } else {
                Operator::Difference
            };
            if let Some(reference) = combine_references(&[left, right], move |machine, mut sets| {
                let right = sets.pop().expect("the right set");
                let left = sets.pop().expect("the left set");
                Lazy::combine(machine, operator, left, right)
            }) {
                compiled = compiled.with_eval(eval(move |machine| {
                    let values = reference(machine)?.enumerate(machine)?;
                    machine.store.set_of(&values)
                }));
            }
        }
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
            ..compiled
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
fn to_json_conversion(
    machine: &mut Machine<'_>,
    value: Id,
    construction: &Construction,
    is_object: bool,
) -> Outcome<Id> {
    match construction {
        Construction::Tuple(_) if is_object => {
            json::check_json_string_value(&machine.store, value)?;
            if json::holds_ordered_keys(&machine.store, value) {
                return Err(Bail(
                    "a Json conversion whose nested key order was not retained",
                ));
            }
            let mut text: Vec<u16> = "{".encode_utf16().collect();
            for index in 0..machine.store.size_of(value) {
                if index > 0 {
                    text.push(u16::from(b','));
                }
                text.extend(format!("\"{index}\":").encode_utf16());
                json::write_json(
                    &machine.store,
                    machine.store.get_range_value(value, index),
                    &mut text,
                )?;
            }
            text.push(u16::from(b'}'));
            ranked_json(machine, text)
        }
        Construction::Record(fields) if is_object => {
            json::check_json_string_value(&machine.store, value)?;
            let mut text: Vec<u16> = "{".encode_utf16().collect();
            for (index, (name, _)) in fields.iter().enumerate() {
                let Some(position) = (0..machine.store.size_of(value)).find(|&position| {
                    machine.store.peek_key(value, position).is_some_and(|key| {
                        machine.store.kind_of(key) == KIND_STRING
                            && machine.store.text_of(key) == name
                    })
                }) else {
                    return Err(Bail(
                        "a Json conversion whose record fields were not retained",
                    ));
                };
                let field = machine.store.get_range_value(value, position);
                if json::holds_ordered_keys(&machine.store, field) {
                    return Err(Bail(
                        "a Json conversion whose nested key order was not retained",
                    ));
                }
                if index > 0 {
                    text.push(u16::from(b','));
                }
                let key = machine.store.peek_key(value, position).ok_or(Bail(
                    "a Json conversion whose record fields were not retained",
                ))?;
                json::write_json(&machine.store, key, &mut text)?;
                text.push(u16::from(b':'));
                json::write_json(&machine.store, field, &mut text)?;
            }
            text.push(u16::from(b'}'));
            ranked_json(machine, text)
        }
        Construction::Record(_) => Err(Bail(
            "a Json conversion of an unsupported physical input class",
        )),
        // A FcnRcdValue holds its keys in their sorted order, as the store does where they are of
        // one kind, whose texts differ, so only the values' own keys may be held otherwise
        // (`getObjectNode`; a JsonObject keeps one member of a text).
        Construction::Function(..)
            if machine.store.kind_of(value) == tla_values::store::KIND_FUNCTION
                && machine.store.size_of(value) > 1 =>
        {
            json::check_json_string_value(&machine.store, value)?;
            let store = &machine.store;
            let key_kinds: Vec<Option<u8>> = (0..store.size_of(value))
                .map(|index| store.peek_key(value, index).map(|key| store.kind_of(key)))
                .collect();
            if key_kinds
                .iter()
                .any(|kind| !matches!(kind, Some(KIND_INT | KIND_STRING)) || *kind != key_kinds[0])
            {
                return Err(Bail(
                    "a Json conversion of a function whose keys are of several kinds",
                ));
            }
            if (0..store.size_of(value))
                .any(|index| json::holds_ordered_keys(store, store.get_range_value(value, index)))
            {
                return Err(Bail(
                    "a Json conversion whose nested key order was not retained",
                ));
            }
            let mut text = Vec::new();
            json::write_json(&machine.store, value, &mut text)?;
            ranked_json(machine, text)
        }
        // A function of one key that isn't a string writes the key as TLC's text of the key it
        // built (`getObjectNode`), as `k :> v` writes it, where TLC's text of it is the same
        // normalized or not.
        Construction::Function(key, _)
            if machine.store.kind_of(value) == tla_values::store::KIND_FUNCTION
                && machine.store.size_of(value) == 1
                && machine
                    .store
                    .peek_key(value, 0)
                    .is_some_and(|key| machine.store.kind_of(key) != KIND_STRING) =>
        {
            let store = &machine.store;
            let id = store.peek_key(value, 0).expect("a key");
            let (mut text, mut normalized) = (Vec::new(), Vec::new());
            if !write_constructed(store, id, key, false, &mut text)
                || !write_constructed(store, id, key, true, &mut normalized)
                || text != normalized
            {
                return Err(Bail("a JSON key whose text depends on how TLC built it"));
            }
            json::check_json_string_value(store, value)?;
            if json::holds_ordered_keys(store, value) {
                return Err(Bail(
                    "a Json operator's record, whose fields TLC writes as it holds them",
                ));
            }
            let mut written = Vec::new();
            json::write_json_with_key(store, value, &text, &mut written)?;
            ranked_json(machine, written)
        }
        Construction::Tuple(_) | Construction::Function(..) | Construction::LazyFunction(..) => {
            to_json(machine, value)
        }
        Construction::Interval
        | Construction::Set(..)
        | Construction::Subset(_)
        | Construction::FunctionSet(..)
            if !is_object =>
        {
            to_json(machine, value)
        }
        Construction::Interval
        | Construction::Set(..)
        | Construction::Subset(_)
        | Construction::FunctionSet(..) => Err(Bail(
            "a Json conversion of an unsupported physical input class",
        )),
        _ if matches!(
            machine.store.kind_of(value),
            tla_values::store::KIND_BOOL | KIND_INT | KIND_STRING | tla_values::store::KIND_MODEL
        ) =>
        {
            Err(Bail(
                "a Json conversion of an unsupported physical input class",
            ))
        }
        _ => Err(Bail(
            "a Json conversion whose physical input class was not retained",
        )),
    }
}

fn to_json(machine: &mut Machine<'_>, value: Id) -> Outcome<Id> {
    json::check_json_string_value(&machine.store, value)?;
    if json::holds_ordered_keys(&machine.store, value) {
        return Err(Bail(
            "a Json operator's record, whose fields TLC writes as it holds them",
        ));
    }
    let mut text = Vec::new();
    json::write_json(&machine.store, value, &mut text)?;
    ranked_json(machine, text)
}

fn ranked_json(machine: &mut Machine<'_>, text: Vec<u16>) -> Outcome<Id> {
    if let Some(string) = machine.store.find_str(&text)
        && machine.store.text_rank_of(string) < 0
    {
        return Err(Bail("ToJson of a text the engine made unranked"));
    }
    machine.store.get_string_rank(&text);
    Ok(machine.store.str(&text))
}

// ToString(v): TLC's text of v built as `construction` says (`write_constructed`), as a string
// TLC ranks as it makes it.
// Whether a value holds the install of TLCGet("config"), which the engine writes "unknown" and
// TLC as where its jar is (`TLCGlobals.Version.installLocation`), so that TLC prints or writes
// it otherwise. The string is the store's only where the model may read the record.
fn holds_install(machine: &Machine<'_>, value: Id) -> bool {
    machine.program.reads_config
        && machine
            .store
            .find_str(&"unknown".encode_utf16().collect::<Vec<_>>())
            .is_some_and(|install| machine.store.holds_value(value, install))
}

fn to_string(machine: &mut Machine<'_>, value: Id, construction: &Construction) -> Outcome<Id> {
    if holds_install(machine, value) {
        return Err(Bail(
            "unsupported: ToString of TLC's install, where its jar is",
        ));
    }
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

// Print's or PrintT's arguments, each evaluated in turn as TLC does, where one with a reference
// (`checked`) is built as TLC holds it, and enumerated only once TLC's `toString` of each such
// argument, in turn, is found to print it (`Lazy::check_printed`). Where the engine can't tell,
// it declines if `is_unsure_declined` and otherwise enumerates the set. An argument only printed
// (all but Print's second, which is its value) that TLC finds empty, or the one function of an
// empty domain, from its parts, is that, where enumerating it may ask a part TLC never asks.
// How the elements of a set enumeration a Print or PrintT prints are built, where they are built
// alike but for how many elements the sets among them write, which a print, normalizing them,
// doesn't show: an empty set enumeration is built as any other.
fn join_printed(left: Construction, right: Construction) -> Option<Construction> {
    if left == right {
        return Some(left);
    }
    match (left, right) {
        (Construction::Set(_, Some(0)), set @ Construction::Set(..))
        | (set @ Construction::Set(..), Construction::Set(_, Some(0))) => match set {
            Construction::Set(element, _) => Some(Construction::Set(element, None)),
            _ => unreachable!("a set"),
        },
        (Construction::Set(left, _), Construction::Set(right, _)) => Some(Construction::Set(
            Box::new(join_printed(*left, *right)?),
            None,
        )),
        _ => None,
    }
}

// How a set enumeration a Print or PrintT prints is built, of its elements' constructions:
// alike but for how many elements the sets among them write (`join_printed`).
fn printed_enumeration(
    mut elements: impl Iterator<Item = Construction>,
    written: usize,
) -> Construction {
    let joined = elements.try_fold(None, |joined: Option<Construction>, element| {
        Some(Some(match joined {
            None => element,
            Some(joined) => join_printed(joined, element)?,
        }))
    });
    match joined {
        Some(Some(element)) => Construction::Set(Box::new(element), Some(written as u32)),
        Some(None) => Construction::Set(Box::new(Construction::Held), Some(0)),
        None => Construction::Held,
    }
}

// How a union a Print or PrintT prints is built (`Tool`'s OPCODE_cup). Where the left operand
// is a set enumeration or an interval (`Reducible`), `cup` gives the right operand as it is if
// the left is empty, and otherwise a set enumeration of the left's elements and the right's
// that aren't among them, as they are, where the right is one too, or a `SetCupValue` of both,
// which prints as such a set (`toSetEnum`). Where only the right is, `cup` of it gives the left
// as it is if the right is empty and otherwise a `SetCupValue`. So:
// - an empty set enumeration written on the left gives the right as it is;
// - one on the right gives the left as it is, or a set enumeration of its elements, which
//   prints alike where the left prints as a set enumeration, and as `{}` where empty;
// - otherwise, of two sets whose elements are built alike, a set enumeration of them, where
//   the right may be the result as it is only if it prints as a set enumeration, or the left
//   is a set enumeration written with an element, which isn't empty. Elements built otherwise
//   on each side, which TLC takes from the left where both hold an equal one, stay unknown.
fn printed_union(left: Construction, right: Construction) -> Construction {
    let is_written_empty = |set: &Construction| matches!(set, Construction::Set(_, Some(0)));
    if is_written_empty(&left) {
        return right;
    }
    if is_written_empty(&right) {
        return match left {
            Construction::Interval => Construction::Set(Box::new(Construction::Held), None),
            set @ Construction::Set(..) => set,
            _ => Construction::Held,
        };
    }
    let is_left_nonempty = matches!(left, Construction::Set(_, Some(written)) if written > 0);
    if right == Construction::Interval && !is_left_nonempty {
        return Construction::Held;
    }
    left.of_elements()
        .zip(right.of_elements())
        .and_then(|(left, right)| join_printed(left.clone(), right.clone()))
        .map_or(Construction::Held, |element| {
            Construction::Set(Box::new(element), None)
        })
}

// How the elements of a set built so are built: those of a set enumeration or an interval, and
// those of SUBSET S, each a set enumeration of elements of S (`SubsetValue.elements`).
fn element_construction(set: &Construction) -> Construction {
    match set {
        Construction::Subset(base) => base.of_elements().map_or(Construction::Held, |element| {
            Construction::Set(Box::new(element.clone()), None)
        }),
        _ => set.of_elements().cloned().unwrap_or(Construction::Held),
    }
}

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
    may_hold_kept: bool,
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
    if values.iter().any(|&value| holds_install(machine, value)) {
        return Err(Bail(
            "unsupported: printing TLC's install, where its jar is",
        ));
    }
    // A print evaluated as the function of an application is evaluated with KeepLazy (`Tool`'s
    // OPCODE_fa), so a function constructor in what it prints stays a `FcnLambdaValue`, whose
    // values `deepNormalize` doesn't reach: a record among them prints its fields as written,
    // where the store holds them in the order TLC sorts them.
    if machine.keeping_lazy_function_value
        && values
            .iter()
            .any(|&value| machine.store.holds_inner_record(value))
    {
        return Err(Bail(PRINTED_KEPT_LAZY));
    }
    // A function an application evaluated with KeepLazy where it read an argument holding such
    // records (`kept_lazy_records`): TLC's `LazyValue` keeps the `FcnLambdaValue`, which prints the
    // records as written.
    if may_hold_kept
        && !machine.kept_lazy_records.is_empty()
        && values.iter().any(|&value| {
            machine
                .store
                .holds_found(value, &|held| machine.kept_lazy_records.contains(&held))
        })
    {
        return Err(Bail(PRINTED_KEPT_LAZY));
    }
    let prints = Prints {
        values,
        texts,
        is_pause_prompt: false,
    };
    // With several workers, what one prints as another may print comes in either order, which
    // shows unless they all print the same.
    let is_raced = machine.is_print_raced;
    if machine.is_worker_evaluating {
        let worker_prints = &mut machine.worker_prints;
        worker_prints.is_raced |= is_raced;
        match &worker_prints.first {
            None => worker_prints.first = Some(prints.clone()),
            Some(first) => worker_prints.is_mixed |= *first != prints,
        }
        if worker_prints.is_raced && worker_prints.is_mixed {
            return Err(Bail("prints TLC's workers may make in any order"));
        }
    }
    machine.output.push(Printed::Values(prints));
    Ok(())
}

/// What TLCSet("pause", TRUE) prints (`TLCGetSet.TLCSet`).
const PAUSE_PROMPT: &str = "Press enter to resume model checking.";

// Where TLC keeps a register's value: under a natural number, or under a name that starts with
// "s:".
enum RegisterKey {
    Numbered(usize),
    Named(Id),
}

/// What TLCGet of a simulation's run stops with as TLC starts, before it has a simulator.
const SIMULATION_NOT_RUNNING: &str = "unsupported: TLCGet of a simulation's run as TLC starts";

/// What TLCGet of a trace's count (the diameter, the statistics) stops with as the worker of a
/// simulation without end runs (`SimulationRun::is_endless`).
const SIMULATION_ENDLESS_COUNT: &str =
    "unsupported: TLCGet of a trace's count in a simulation without end";

// `Simulator.getStatistics` of the state TLC evaluates in, as one worker runs it: the traces
// started, the seconds since the simulator started, the states generated, the behavior's count of
// each action and its number (`getTraceStatistics`), the worker's number, the extended
// statistics as -1 or an empty record, and the mean and variance of the finished traces'
// lengths, each as Java's int.
fn simulation_statistics(machine: &mut Machine<'_>) -> Outcome<Id> {
    let run = &machine.simulation;
    if run.is_endless {
        return Err(Bail(SIMULATION_ENDLESS_COUNT));
    }
    let narrow = |value: u64| i64::from(i32::try_from(value).unwrap_or(i32::MAX));
    let traces = narrow(run.traces);
    let duration = run
        .started
        .map_or(0, |started| narrow(started.elapsed().as_secs()));
    let generated = narrow(run.generated);
    let mean = run.lengths as u64 & 0xFFFF_FFFF;
    let variance = ((run.lengths as u64) >> 32) as f64 / (run.traces as f64 + 1.0);
    let variance = (variance + 0.5).floor() as i64;
    if mean > i32::MAX as u64 || variance > i64::from(i32::MAX) {
        return Err(Bail("unsupported: a simulation's statistics past an int"));
    }
    let mut counts: Vec<(Id, i64)> = Vec::new();
    for &step in &run.steps {
        let name = *run
            .action_names
            .get(step as usize)
            .ok_or(Bail("unsupported: an action the simulation doesn't name"))?;
        match counts.iter_mut().find(|(counted, _)| *counted == name) {
            Some((_, count)) => *count += 1,
            None => counts.push((name, 1)),
        }
    }
    let store = &mut machine.store;
    let text =
        |store: &mut Store, name: &str| store.str(&name.encode_utf16().collect::<Vec<u16>>());
    let (names, values): (Vec<Id>, Vec<i64>) = counts.into_iter().unzip();
    let values = values
        .into_iter()
        .map(|count| store.int(count))
        .collect::<Outcome<Vec<Id>>>()?;
    let actions = store.function_of(&names, &values)?;
    let behavior_keys = [text(store, "actions"), text(store, "id")];
    let behavior_values = [actions, store.int(traces)?];
    let behavior = store.function_of(&behavior_keys, &behavior_values)?;
    let fields: [(&str, Id); 11] = [
        ("traces", store.int(traces)?),
        ("duration", store.int(duration)?),
        ("generated", store.int(generated)?),
        ("behavior", behavior),
        ("worker", store.int(0)?),
        ("distinct", store.int(-1)?),
        ("distinctvalues", store.int(-1)?),
        ("retries", store.int(-1)?),
        ("actions", EMPTY_TUPLE),
        ("levelmean", store.int(mean as i64)?),
        ("levelvariance", store.int(variance)?),
    ];
    let keys: Vec<Id> = fields.iter().map(|&(name, _)| text(store, name)).collect();
    let values: Vec<Id> = fields.iter().map(|&(_, value)| value).collect();
    store.function_of(&keys, &values)
}

/// What TLCGet of a simulation's run gives, the engine holding TLC's empty records
/// (`RecordValue.EmptyRcd`, the statistics' `actions` and an initial state's behavior's) and its
/// empty functions (`FcnRcdValue` of no registers) as the empty sequence, and the function of its
/// named registers, TLC's `FcnRcdValue`, as a record. TLC applies, compares and updates those
/// apart from the empty sequence and a record (`RecordValue.equals` of a tuple fails, as does its
/// EXCEPT of a number, and `FcnRcdValue`'s of a key outside its domain warns): the value
/// evaluates only where it is printed or its domain or a field that holds none of them is read,
/// and elsewhere declines.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SimulationRun {
    /// TLCGet("stats") (`Simulator.getStatistics`).
    Stats,
    /// Its `behavior` (`SimulationWorker.getTraceStatistics`).
    Behavior,
    /// TLCGet("all") or TLCGet("all:named").
    Registers { is_named: bool },
}

/// What a decline of a simulation's run where its value may differ from TLC's stops with.
const SIMULATION_RUN_UNSURE: &str =
    "unsupported: TLCGet of a simulation's run where its empty records may matter";

impl SimulationRun {
    /// The value, where the empty sequence and records in it are only printed, or its domain or a
    /// field read that holds none of them.
    pub(crate) fn value(self) -> Eval {
        eval(move |machine| {
            if !machine.simulation.is_running {
                return Err(Bail(SIMULATION_NOT_RUNNING));
            }
            match self {
                SimulationRun::Stats => simulation_statistics(machine),
                SimulationRun::Behavior => simulation_behavior(machine),
                SimulationRun::Registers { is_named } => simulation_registers(machine, is_named),
            }
        })
    }

    /// The value where it is used otherwise: only a behavior whose record of actions isn't empty.
    pub(crate) fn guarded(self) -> Eval {
        eval(move |machine| {
            if !machine.simulation.is_running {
                return Err(Bail(SIMULATION_NOT_RUNNING));
            }
            if self != SimulationRun::Behavior {
                return Err(Bail(SIMULATION_RUN_UNSURE));
            }
            let behavior = simulation_behavior(machine)?;
            let actions = behavior_actions(machine, behavior)?;
            if machine.store.size_of(actions) == 0 {
                return Err(Bail(SIMULATION_RUN_UNSURE));
            }
            Ok(behavior)
        })
    }
}

/// A compiled expression that TLCGet of a simulation's run is evaluated through, where its value is
/// only printed or its domain read (`SimulationRun::value`).
pub(crate) fn unguarded(compiled: Compiled) -> Compiled {
    match compiled.shape {
        Shape::SimulationRun(run) => Compiled {
            shape: Shape::Other,
            ..compiled.with_eval(run.value())
        },
        _ => compiled,
    }
}

fn simulation_behavior(machine: &mut Machine<'_>) -> Outcome<Id> {
    let statistics = simulation_statistics(machine)?;
    let key = machine
        .store
        .str(&"behavior".encode_utf16().collect::<Vec<u16>>());
    machine.store.apply(statistics, key)
}

fn behavior_actions(machine: &mut Machine<'_>, behavior: Id) -> Outcome<Id> {
    let key = machine
        .store
        .str(&"actions".encode_utf16().collect::<Vec<u16>>());
    machine.store.apply(behavior, key)
}

// TLCGet("all") or TLCGet("all:named") of a simulation on one worker
// (`Simulator.getAllValues`, `getAllNamedRegisterValues`): each register the worker set, to the
// tuple of its one value.
fn simulation_registers(machine: &mut Machine<'_>, is_named: bool) -> Outcome<Id> {
    let registers = &machine.registers;
    let pairs: Vec<(Option<usize>, Option<Id>, Id)> = if is_named {
        registers
            .named
            .iter()
            .map(|&(name, value)| (None, Some(name), value))
            .collect()
    } else {
        registers
            .numbered
            .iter()
            .enumerate()
            .filter_map(|(index, value)| value.map(|value| (Some(index), None, value)))
            .collect()
    };
    let store = &mut machine.store;
    let mut keys = Vec::with_capacity(pairs.len());
    let mut values = Vec::with_capacity(pairs.len());
    for (index, name, value) in pairs {
        keys.push(match (index, name) {
            (Some(index), _) => store.int(index as i64)?,
            (_, Some(name)) => name,
            _ => unreachable!("a register's key"),
        });
        values.push(store.tuple_of(&[value]));
    }
    store.function_of(&keys, &values)
}

/// What TLCCache of a numeral or a string stops with: its node holds its value where TLC reads a
/// cache.
pub(crate) const TLC_CACHE_OF_LITERAL: &str =
    "TLCCache of a literal, whose tool object isn't a cache";

/// What TLCGet of a count only the model checker keeps stops with in a simulation.
pub(crate) const TLC_GET_UNDEFINED_IN_SIMULATION: &str = "TLCGet of a count a simulation lacks";

/// What TLCGet of a string key `TLCGetSet.TLCGetStringValue` doesn't know stops with.
pub(crate) const TLC_GET_UNKNOWN_KEY: &str = "TLCGet of a key TLC doesn't know";

/// AssertError of a message other than a string written out, which TLC fails on.
pub(crate) const ASSERT_ERROR_MESSAGE: &str = "AssertError of a message that isn't a string";

/// Where a definition the engine computes as TLC does as it starts reaches TLCSet of a key TLC
/// throws on there (`tla_ir::Startup::register_probes`): a number, as TLC has no checker or
/// simulator yet whose registers it would set (`TLCGetSet.TLCSet`), or a string TLC doesn't take
/// for a key (`TLC_MODULE_ARGUMENT_ERROR`). `processConstantDefns` swallows that.
pub(crate) const PROBED_REGISTER_FAILS: &str = "TLCSet of a key TLC fails on as it starts";
/// Where such a definition reaches TLCSet of any other key, a system property's, which TLC sets
/// there, or another write of a register.
pub(crate) const PROBED_REGISTER_SET: &str =
    "unsupported: a constant definition TLC computes as it starts that sets a register";
/// Where such a definition reaches TLCSet of a named register, "exit" or "pause", which sets
/// nothing as TLC starts (`TLCGetSet.TLCSet` finds no checker or simulator) and gives TRUE.
const PROBED_REGISTER_UNSET: &str = "TLCSet of a key that sets nothing as TLC starts";

// What TLCSet of a key does where the engine computes a definition as TLC does as it starts.
fn probe_register(store: &Store, key: Id) -> &'static str {
    match store.kind_of(key) {
        KIND_INT => PROBED_REGISTER_FAILS,
        KIND_STRING => {
            let text = String::from_utf16_lossy(store.text_of(key));
            if text == "exit" || text == "pause" || text.starts_with(NAMED_REGISTER_PREFIX) {
                PROBED_REGISTER_UNSET
            } else if text.starts_with(JAVA_PROPERTY_PREFIX) {
                PROBED_REGISTER_SET
            } else {
                PROBED_REGISTER_FAILS
            }
        }
        _ => PROBED_REGISTER_SET,
    }
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
            if let Ok(text) = String::from_utf16(machine.store.text_of(key))
                && is_unknown_tlc_get_key(&text)
            {
                return Err(Bail(TLC_GET_UNKNOWN_KEY));
            }
            // A system property TLCSet set, or else the key (`System.getProperty`).
            if let Ok(text) = String::from_utf16(machine.store.text_of(key))
                && let Some(name) = text.strip_prefix(JAVA_PROPERTY_PREFIX)
                && is_settable_property(name)
            {
                let name: Vec<u16> = name.encode_utf16().collect();
                return Ok(registers
                    .properties
                    .iter()
                    .find(|(set, _)| *set == name)
                    .map_or(key, |&(_, value)| value));
            }
            // A key the spec computes may name a system property, which the search doesn't keep
            // either.
            return Err(Bail("unsupported: TLCGet of a key the search doesn't keep"));
        }
        None => return Err(Bail("TLCGet of a key that isn't a natural number")),
    };
    value.ok_or(Bail("TLCGet of a register TLC hasn't set"))
}

// TLCGet("all") of TLC's one worker: each numbered register set, the tuple of its value. TLC
// builds the function from a HashMap, in its order, but sorts a function whose keys are all
// integers wherever it compares, fingerprints or writes it (`FcnRcdValue.isTuple` normalizes),
// so the function of the sorted keys is the same.
fn all_registers(machine: &mut Machine<'_>) -> Outcome<Id> {
    let set: Vec<(usize, Id)> = (machine.registers.numbered.iter().enumerate())
        .filter_map(|(index, value)| Some((index, (*value)?)))
        .collect();
    let mut keys = Vec::with_capacity(set.len());
    let mut values = Vec::with_capacity(set.len());
    for (index, value) in set {
        keys.push(machine.store.int(index as i64)?);
        values.push(machine.store.tuple_of(&[value]));
    }
    machine.store.function_of(&keys, &values)
}

fn set_register(machine: &mut Machine<'_>, key: Id, value: Id) -> Outcome<()> {
    if machine.is_probing_registers {
        return Err(Bail(PROBED_REGISTER_SET));
    }
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
            } else if let Some(name) = text.strip_prefix(JAVA_PROPERTY_PREFIX)
                && is_settable_property(name)
                && machine.program.workers <= 1
            {
                // `System.setProperty(name, value.toString())`.
                if !is_printable(&machine.store, value) {
                    return Err(Bail(
                        "unsupported: TLCSet of a system property to a value whose text depends on how TLC built it",
                    ));
                }
                let text = tla_values::print::format_value(&machine.store, value)?;
                let text: Vec<u16> = text.encode_utf16().collect();
                let value = machine.store.str(&text);
                let name: Vec<u16> = name.encode_utf16().collect();
                let properties = &mut machine.registers.properties;
                match properties.iter_mut().find(|(set, _)| *set == name) {
                    Some(entry) => entry.1 = value,
                    None => properties.push((name, value)),
                }
            } else if text == "pause" && value == TRUE && machine.simulation.is_simulated {
                // A simulation has no model checker (`TLCGlobals.mainChecker` is null), so
                // TLCSet("pause", TRUE) does nothing there.
            } else if text == "pause" && value == TRUE && machine.is_pause_prompted {
                // `TLCGetSet.TLCSet` prints the prompt and reads a byte of the standard input,
                // the model checker's queue locked.
                let prompt: Vec<u16> = PAUSE_PROMPT.encode_utf16().collect();
                let value = machine.store.str(&prompt);
                machine.output.push(Printed::Values(Prints {
                    values: vec![value],
                    texts: Some(vec![prompt]),
                    is_pause_prompt: true,
                }));
            } else if !matches!(text.as_str(), "exit" | "pause") && !text.starts_with("-D") {
                // `TLCGetSet.TLCSet` takes no other string.
                return Err(Bail("TLCSet of a key that isn't a natural number"));
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

fn random_hash_shape_is_known(construction: &Construction) -> bool {
    match construction {
        Construction::Held | Construction::Interval => true,
        Construction::Set(element, _) => random_hash_shape_is_known(element),
        Construction::Tuple(elements) => elements.iter().all(random_hash_shape_is_known),
        Construction::Record(fields) => fields
            .iter()
            .all(|(_, value)| random_hash_shape_is_known(value)),
        Construction::Function(key, value) => {
            random_hash_shape_is_known(key) && random_hash_shape_is_known(value)
        }
        Construction::LazyFunction(..)
        | Construction::Subset(_)
        | Construction::FunctionSet(..) => false,
    }
}

/// The arguments of RandomSubsetSet or RandomSetOfSubsets as compiled, and a draw from them as
/// `Randomization.RandomSubsetSet` and `Randomization.RandomSetOfSubsets` check and make it.
struct SubsetSetDraw {
    count: Eval,
    probability: Eval,
    set: Eval,
    interval: Option<(Eval, Eval)>,
    reference: Option<Reference>,
    average_mode: bool,
}

/// The values a draw takes: the count, the probability or the average, and the set.
struct SubsetSetArguments {
    count: Id,
    probability: Id,
    source: random::Source,
}

impl SubsetSetDraw {
    fn new(compiled: &[Compiled], average_mode: bool) -> Self {
        SubsetSetDraw {
            count: compiled[0].eval.clone(),
            probability: compiled[1].eval.clone(),
            set: compiled[2].eval.clone(),
            interval: compiled[2].interval.clone(),
            reference: compiled[2].reference.clone(),
            average_mode,
        }
    }

    fn arguments(&self, machine: &mut Machine<'_>) -> Outcome<SubsetSetArguments> {
        let count = (self.count)(machine)?;
        let probability = (self.probability)(machine)?;
        let source = match (&self.interval, &self.reference) {
            (Some((low, high)), _) => {
                let low = low(machine)?;
                let high = high(machine)?;
                random::Source::Interval(expect_int(machine, low)?, expect_int(machine, high)?)
            }
            (None, Some(reference)) => random::Source::Set(reference(machine)?),
            (None, None) => random::Source::Set(Lazy::Set((self.set)(machine)?)),
        };
        Ok(SubsetSetArguments {
            count,
            probability,
            source,
        })
    }

    fn draw(&self, machine: &mut Machine<'_>, arguments: &SubsetSetArguments) -> Outcome<Id> {
        let SubsetSetArguments {
            count,
            probability,
            source,
        } = arguments;
        let (count, probability) = (*count, *probability);
        if machine.store.kind_of(count) != KIND_INT || machine.store.int_of(count) < 0 {
            return Err(Bail(
                "RandomSubsetSet of a count that isn't a natural number",
            ));
        }
        let average = if self.average_mode {
            if machine.store.kind_of(probability) != KIND_INT
                || machine.store.int_of(probability) < 0
            {
                return Err(Bail(
                    "RandomSetOfSubsets of an average that isn't a natural number",
                ));
            }
            Some(machine.store.int_of(probability) as u32)
        } else {
            None
        };
        if !self.average_mode && machine.store.kind_of(probability) != KIND_STRING {
            return Err(Bail("RandomSubsetSet of a probability that isn't a string"));
        }
        let probability = if self.average_mode {
            f64::NAN
        } else {
            tla_values::random::parse_java_double(machine.store.text_of(probability))
                .filter(|value| !(*value < 0.0 || *value > 1.0))
                .ok_or(Bail("RandomSubsetSet of a string that isn't a probability"))?
        };
        if let random::Source::Set(set) = source
            && (set.is_finite(machine) == Some(false)
                || matches!(set, Lazy::Set(id) if machine.store.kind_of(*id) != KIND_SET))
        {
            return Err(Bail("RandomSubsetSet of a value that isn't a finite set"));
        }
        match average {
            Some(average) => random::random_set_of_subsets(
                machine,
                machine.store.int_of(count) as u32,
                average,
                source,
            ),
            None => random::random_subset_set(
                machine,
                machine.store.int_of(count) as u32,
                probability,
                source,
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::{CompileError, Options};
    use crate::machine::Program;
    use tla_ir::{Name, Value};
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

    fn table_with_uninternable_row(
        kind: usize,
        failing_argument: bool,
        phase_known: bool,
    ) -> Result<Result<Id, String>, CompileError> {
        let bytes = std::fs::read(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../tests/conformance/ir/examples/specifications/ReadersWriters/MC.ir"
        ))
        .unwrap();
        let mut ir = tla_ir::decode(&bytes).unwrap();
        let text = ir.texts.len() as u32;
        ir.texts.extend(["a".into(), "F".into(), "\\div".into()]);
        ir.values.strings = vec![text];
        let mixed = Value::Set(vec![Value::Int(1), Value::String(0)]);
        let bad = match kind {
            0 => mixed,
            1 => Value::Function {
                class: 3,
                domain: vec![Value::String(0)],
                range: vec![mixed],
            },
            _ => Value::Function {
                class: 0,
                domain: vec![Value::Int(1)],
                range: vec![mixed],
            },
        };
        ir.values.list = vec![
            Value::IntervalFunction {
                class: 2,
                low: 1,
                range: vec![Value::Int(2)],
            },
            bad,
            Value::IntervalFunction {
                class: 2,
                low: 1,
                range: vec![Value::Int(1)],
            },
            Value::Bool(true),
        ];
        ir.builtins = vec![
            Builtin {
                name: text + 1,
                arity: 1,
                flags: Builtin::TABLE
                    | if phase_known {
                        Builtin::TABLE_PHASE_KNOWN
                    } else {
                        0
                    },
                table: vec![(Some(0), Some(1)), (Some(2), Some(3))],
            },
            Builtin {
                name: text + 2,
                arity: 2,
                flags: 0,
                table: Vec::new(),
            },
        ];
        let one = ir.nodes.arena.len() as u32;
        for kind in [
            NodeKind::Number(1),
            NodeKind::Number(0),
            NodeKind::Apply {
                name: Name {
                    text: text + 2,
                    resolution: Resolution::Builtin(1),
                    is_local: false,
                },
                args: vec![one, one + 1],
            },
        ] {
            ir.nodes.arena.push(tla_ir::Node {
                line: 1,
                column: 1,
                range: None,
                kind,
            });
        }
        let operand = Operand {
            node: one + if failing_argument { 2 } else { 0 },
            context: Context::ROOT,
            is_param: false,
            slot: None,
        };
        let mut store = Store::new();
        let mut compiler = Compiler::new(&ir, &mut store, Options::default());
        let compiled = compiler.compile_table(0, &[operand])?;
        let program = compiler.finish();
        let mut machine = Machine::new(&program, store);
        Ok((compiled.eval)(&mut machine).map_err(|error| error.0.to_owned()))
    }

    // `OpRcdValue.eval` compares the arguments with each row's keys in turn and returns the
    // matched row's value, so it never compares the elements of an unused row's value, where
    // `initialize`, which normalizes every key and value, fails on a mixed set ("Attempted to
    // compare string "a" with non-string"). Each is representable as Some IR data.
    #[test]
    fn ignores_uninternable_unused_results_only_with_a_known_table_phase() {
        for kind in 0..3 {
            assert_eq!(
                table_with_uninternable_row(kind, false, true).unwrap(),
                Ok(TRUE)
            );
            assert!(table_with_uninternable_row(kind, false, false).is_err());
            let error = table_with_uninternable_row(kind, true, true)
                .unwrap()
                .unwrap_err();
            assert!(error.contains("div") || error.contains("zero"), "{error}");
        }
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
