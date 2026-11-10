//! The pure builtins the TypeScript engine runs in the interpreter (`compileBridgedBuiltin`), on
//! ids: SubSeq, SortSeq, Permutations, IsFiniteSet and the Bags operators. Each evaluates its
//! value arguments in order and computes what the interpreter's builtin computes, and stops
//! wherever the interpreter's fails, which then reports TLC's error.

use tla_values::store::{
    EMPTY_TUPLE, FALSE, KIND_INT, KIND_LAZY_FUNCTION, KIND_SET, KIND_STRING, KIND_TUPLE, Outcome,
    TRUE, is_function_kind,
};
use tla_values::{Bail, Id};

use super::builtins::Applier;
use super::{Compiled, Compiler, Compiling, Context, Operand, eval, leaf, unsupported};
use crate::footprint::Footprint;
use crate::machine::Machine;

// Beyond these the interpreter would build more values than a model can use.
const MAXIMUM_PERMUTED: usize = 10;
const MAXIMUM_SUB_BAGS: f64 = 1e6;

type Bridged = fn(&mut Machine<'_>, &[Id], &[Applier]) -> Outcome<Id>;

impl Compiler<'_> {
    pub(crate) fn compile_bridged(
        &mut self,
        name: &str,
        operands: &[Operand],
        context: &Context,
    ) -> Compiling<Option<Compiled>> {
        let (arity, compute): (usize, Bridged) = match name {
            "SubSeq" => (3, sub_seq),
            "SortSeq" => (2, sort_seq),
            "Permutations" => (1, permutations),
            "IsFiniteSet" => (1, is_finite_set),
            "IsABag" => (1, is_a_bag),
            "BagCardinality" => (1, bag_cardinality),
            "BagIn" => (2, bag_in),
            "CopiesIn" => (2, copies_in),
            "\\oplus" => (2, bag_sum),
            "\\ominus" => (2, bag_difference),
            "BagUnion" => (1, bag_union),
            "\\sqsubseteq" => (2, bag_subset),
            "BagOfAll" => (2, bag_of_all),
            "SubBag" => (1, sub_bags),
            "BagToSet" => (1, bag_to_set),
            "SetToBag" => (1, set_to_bag),
            _ => return Ok(None),
        };
        if operands.len() != arity {
            return unsupported("an operator applied to the wrong number of arguments");
        }
        let mut footprint = Footprint::default();
        let mut values = Vec::new();
        let mut operators: Vec<Applier> = Vec::new();
        for operand in operands {
            if self.is_operator_argument(operand) {
                let applier = self.compile_applier(operand, context)?;
                footprint = footprint.merge(&applier.footprint);
                operators.push(applier);
            } else {
                let value = self.operand(operand)?;
                // TLC asks a set it keeps lazy whether it is finite by its parts
                // (`SetOfFcnsValue.isFinite` and the like), where the engine would enumerate it.
                if name == "IsFiniteSet" && value.may_be_infinite() {
                    return Ok(Some(leaf(
                        eval(|_| Err(Bail("unsupported: IsFiniteSet of a set TLC keeps lazy"))),
                        value.footprint,
                    )));
                }
                footprint = footprint.merge(&value.footprint);
                values.push(value.eval);
            }
        }
        let expected = usize::from(name == "SortSeq" || name == "BagOfAll");
        if operators.len() != expected {
            return unsupported(format!("{name} of an operator where it takes a value"));
        }
        if name == "BagOfAll" && operators[0].is_literal {
            // TLC passes an operator whose body is a literal to Bags.java as the literal.
            return Ok(Some(leaf(
                eval(|_| Err(Bail("BagOfAll of a literal"))),
                footprint,
            )));
        }
        Ok(Some(Compiled {
            is_costly: true,
            // TLC.Permutations makes a SetEnumValue, which TLC normalizes before it enumerates it.
            is_normalized: name == "Permutations",
            ..leaf(
                eval(move |machine| {
                    let mut ids = Vec::with_capacity(values.len());
                    for value in &values {
                        ids.push(value(machine)?);
                    }
                    compute(machine, &ids, &operators)
                }),
                footprint,
            )
        }))
    }
}

impl Applier {
    /// Applies the operator to ids bound to its parameters, restoring the slots after.
    pub(crate) fn apply(&self, machine: &mut Machine<'_>, args: &[Id]) -> Outcome<Id> {
        let saved: Vec<Id> = self
            .slots
            .iter()
            .map(|&slot| machine.locals[slot as usize])
            .collect();
        for (&slot, &arg) in self.slots.iter().zip(args) {
            machine.locals[slot as usize] = arg;
        }
        let result = (self.body)(machine);
        for (&slot, &value) in self.slots.iter().zip(&saved) {
            machine.locals[slot as usize] = value;
        }
        result
    }
}

fn expect_int(machine: &Machine<'_>, id: Id) -> Outcome<i64> {
    if machine.store.kind_of(id) == KIND_INT {
        Ok(i64::from(machine.store.int_of(id)))
    } else {
        Err(Bail("expected an integer"))
    }
}

fn expect_function(machine: &Machine<'_>, id: Id) -> Outcome<Id> {
    if is_function_kind(machine.store.kind_of(id)) {
        Ok(id)
    } else {
        Err(Bail("expected a function"))
    }
}

fn expect_set(machine: &Machine<'_>, id: Id) -> Outcome<Id> {
    if machine.store.kind_of(id) == KIND_SET {
        Ok(id)
    } else {
        Err(Bail("expected a set"))
    }
}

fn pairs_of(machine: &mut Machine<'_>, function: Id) -> (Vec<Id>, Vec<Id>) {
    let size = machine.store.size_of(function);
    let keys = (0..size)
        .map(|index| machine.store.get_key(function, index))
        .collect();
    let values = (0..size)
        .map(|index| machine.store.get_range_value(function, index))
        .collect();
    (keys, values)
}

/// The positions `SubSeq(sequence, start, end)` takes, from and to, where TLC's SubSeq takes them,
/// failing where it fails.
pub(crate) fn sub_seq_bounds(
    machine: &Machine<'_>,
    sequence: Id,
    start: Id,
    end: Id,
) -> Outcome<(u32, u32)> {
    let is_text = machine.store.kind_of(sequence) == KIND_STRING;
    if !is_text && machine.store.kind_of(sequence) != KIND_TUPLE {
        return Err(Bail("SubSeq of a non-sequence"));
    }
    let start = expect_int(machine, start)?;
    let end = expect_int(machine, end)?;
    let length = if is_text {
        machine.store.text_of(sequence).len() as i64
    } else {
        i64::from(machine.store.size_of(sequence))
    };
    if start > end {
        Ok((0, 0))
    } else if start < 1 || start > length || end > length {
        Err(Bail("SubSeq outside the sequence's domain"))
    } else {
        Ok(((start - 1) as u32, end as u32))
    }
}

pub(crate) fn sub_seq_of(machine: &mut Machine<'_>, sequence: Id, from: u32, to: u32) -> Id {
    if machine.store.kind_of(sequence) == KIND_STRING {
        let text = machine.store.text_of(sequence)[from as usize..to as usize].to_vec();
        return machine.store.str(&text);
    }
    machine.store.slice_tuple(sequence, from, to)
}

fn sub_seq(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let (from, to) = sub_seq_bounds(machine, args[0], args[1], args[2])?;
    Ok(sub_seq_of(machine, args[0], from, to))
}

// TLC inserts each element before the first one sorted so far that it precedes.
fn sort_seq(machine: &mut Machine<'_>, args: &[Id], operators: &[Applier]) -> Outcome<Id> {
    let sequence = args[0];
    if machine.store.kind_of(sequence) != KIND_TUPLE {
        return Err(Bail("SortSeq of a non-sequence"));
    }
    let precedes = &operators[0];
    let mut sorted: Vec<Id> = Vec::new();
    for index in 0..machine.store.size_of(sequence) {
        let element = machine.store.get_range_value(sequence, index);
        let mut position = sorted.len();
        for (at, &existing) in sorted.iter().enumerate() {
            if precedes.apply(machine, &[element, existing])? == TRUE {
                position = at;
                break;
            }
        }
        sorted.insert(position, element);
    }
    Ok(machine.store.tuple_of(&sorted))
}

fn permutations(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let set = expect_set(machine, args[0])?;
    let elements = machine.store.set_elements(set).to_vec();
    if elements.len() > MAXIMUM_PERMUTED {
        return Err(Bail("Permutations of a set too large to build"));
    }
    let mut functions = Vec::new();
    let mut order: Vec<Id> = elements.clone();
    permute(machine, &elements, &mut order, 0, &mut functions);
    machine.store.set_of(&functions)
}

fn permute(
    machine: &mut Machine<'_>,
    keys: &[Id],
    order: &mut [Id],
    from: usize,
    functions: &mut Vec<Id>,
) {
    if from == order.len() {
        functions.push(machine.store.function_of_sorted(keys, order));
        return;
    }
    for index in from..order.len() {
        order.swap(from, index);
        permute(machine, keys, order, from + 1, functions);
        order.swap(from, index);
    }
}

// The engine holds only finite sets and functions; the interpreter fails on anything else.
fn is_finite_set(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let kind = machine.store.kind_of(args[0]);
    if kind == KIND_SET || is_function_kind(kind) {
        Ok(TRUE)
    } else {
        Err(Bail("IsFiniteSet of a non-set"))
    }
}

fn is_a_bag(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let bag = args[0];
    let kind = machine.store.kind_of(bag);
    // TLC fails to enumerate the domain of a function it keeps lazy (`toFcnRcd`).
    if kind == KIND_LAZY_FUNCTION {
        return Err(Bail("unsupported: IsABag of a function TLC keeps lazy"));
    }
    if !is_function_kind(kind) {
        return Ok(FALSE);
    }
    let is_bag = (0..machine.store.size_of(bag)).all(|index| {
        let count = machine.store.get_range_value(bag, index);
        machine.store.kind_of(count) == KIND_INT && machine.store.int_of(count) > 0
    });
    Ok(machine.store.bool(is_bag))
}

fn bag_cardinality(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let bag = expect_function(machine, args[0])?;
    let mut total = 0;
    for index in 0..machine.store.size_of(bag) {
        let count = machine.store.get_range_value(bag, index);
        if machine.store.kind_of(count) != KIND_INT || machine.store.int_of(count) <= 0 {
            return Err(Bail("BagCardinality of a non-bag"));
        }
        total = add_counts(total, i64::from(machine.store.int_of(count)))?;
    }
    machine.store.int(total)
}

fn add_counts(left: i64, right: i64) -> Outcome<i64> {
    let sum = left + right;
    if i32::try_from(sum).is_err() {
        return Err(Bail("integer overflow"));
    }
    Ok(sum)
}

// The count of an element in a bag, found by TLC's equality, which fails on values it can't
// compare.
fn find_count(machine: &mut Machine<'_>, bag: Id, element: Id) -> Outcome<Option<Id>> {
    for index in 0..machine.store.size_of(bag) {
        let key = machine.store.get_key(bag, index);
        if machine.store.equals(key, element)? {
            return Ok(Some(machine.store.get_range_value(bag, index)));
        }
    }
    Ok(None)
}

fn bag_in(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let bag = expect_function(machine, args[1])?;
    match find_count(machine, bag, args[0])? {
        None => Ok(FALSE),
        Some(count) => {
            let count = expect_int(machine, count)?;
            Ok(machine.store.bool(count > 0))
        }
    }
}

fn copies_in(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let bag = expect_function(machine, args[1])?;
    match find_count(machine, bag, args[0])? {
        None => machine.store.int(0),
        Some(count) => {
            expect_int(machine, count)?;
            Ok(count)
        }
    }
}

fn expect_bag(machine: &mut Machine<'_>, id: Id) -> Outcome<Id> {
    let bag = expect_function(machine, id)?;
    let Ok(is_bag) = is_a_bag(machine, &[bag], &[]) else {
        unreachable!("IsABag doesn't fail");
    };
    if is_bag == TRUE {
        Ok(bag)
    } else {
        Err(Bail("expected a bag"))
    }
}

// The bags' pairs merged in order, the counts of equal elements added.
fn merge_bags(machine: &mut Machine<'_>, bags: &[(Vec<Id>, Vec<Id>)]) -> Outcome<Id> {
    let mut keys: Vec<Id> = Vec::new();
    let mut counts: Vec<Id> = Vec::new();
    for (bag_keys, bag_counts) in bags {
        for (&key, &count) in bag_keys.iter().zip(bag_counts) {
            let mut found = None;
            for (at, &existing) in keys.iter().enumerate() {
                if machine.store.equals(existing, key)? {
                    found = Some(at);
                    break;
                }
            }
            match found {
                Some(at) => {
                    let left = expect_int(machine, counts[at])?;
                    let right = expect_int(machine, count)?;
                    counts[at] = machine.store.int(add_counts(left, right)?)?;
                }
                None => {
                    keys.push(key);
                    counts.push(count);
                }
            }
        }
    }
    machine.store.function_of(&keys, &counts)
}

fn bag_sum(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let left = expect_bag(machine, args[0])?;
    let right = expect_bag(machine, args[1])?;
    let bags = [pairs_of(machine, left), pairs_of(machine, right)];
    merge_bags(machine, &bags)
}

// TLC subtracts counts as Java ints, which wrap.
fn subtract_counts(machine: &mut Machine<'_>, count: Id, key: Id, other: Id) -> Outcome<i64> {
    let removed = find_count(machine, other, key)?;
    let count = expect_int(machine, count)?;
    Ok(match removed {
        None => count,
        Some(removed) => {
            let removed = expect_int(machine, removed)?;
            i64::from((count as i32).wrapping_sub(removed as i32))
        }
    })
}

fn bag_difference(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let left = expect_function(machine, args[0])?;
    let right = expect_function(machine, args[1])?;
    let (keys, counts) = pairs_of(machine, left);
    let mut kept_keys = Vec::new();
    let mut kept_counts = Vec::new();
    for (key, count) in keys.into_iter().zip(counts) {
        let count = subtract_counts(machine, count, key, right)?;
        if count > 0 {
            kept_keys.push(key);
            kept_counts.push(machine.store.int(count)?);
        }
    }
    machine.store.function_of(&kept_keys, &kept_counts)
}

fn bag_union(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let set = expect_set(machine, args[0])?;
    let elements = machine.store.set_elements(set).to_vec();
    if elements.len() < 2 {
        return Ok(elements.first().copied().unwrap_or(EMPTY_TUPLE));
    }
    let mut bags = Vec::new();
    for element in elements {
        let bag = expect_function(machine, element)?;
        bags.push(pairs_of(machine, bag));
    }
    merge_bags(machine, &bags)
}

fn bag_subset(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let left = expect_function(machine, args[0])?;
    let right = expect_function(machine, args[1])?;
    let (keys, counts) = pairs_of(machine, left);
    for (key, count) in keys.into_iter().zip(counts) {
        if subtract_counts(machine, count, key, right)? > 0 {
            return Ok(FALSE);
        }
    }
    Ok(TRUE)
}

fn bag_of_all(machine: &mut Machine<'_>, args: &[Id], operators: &[Applier]) -> Outcome<Id> {
    let function = expect_function(machine, args[0])?;
    let (keys, counts) = pairs_of(machine, function);
    let mut bags = Vec::new();
    for (key, count) in keys.into_iter().zip(counts) {
        let image = operators[0].apply(machine, &[key])?;
        bags.push((vec![image], vec![count]));
    }
    merge_bags(machine, &bags)
}

fn sub_bags(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let bag = expect_function(machine, args[0])?;
    let (keys, counts) = pairs_of(machine, bag);
    // The interpreter sorts the counts first, which fails on two it can't compare.
    machine.store.set_of(&counts)?;
    let mut copies = Vec::with_capacity(counts.len());
    for &count in &counts {
        let count = expect_int(machine, count)?;
        if count < 1 {
            return Err(Bail("SubBag of a non-bag"));
        }
        copies.push(count);
    }
    let size: f64 = copies.iter().map(|&count| (count + 1) as f64).product();
    if size > MAXIMUM_SUB_BAGS {
        return Err(Bail("SubBag of a bag too large to build"));
    }
    let mut entries: Vec<(Vec<Id>, Vec<Id>)> = vec![(Vec::new(), Vec::new())];
    for (&key, &count) in keys.iter().zip(&copies) {
        let mut next = Vec::new();
        for (entry_keys, entry_counts) in entries {
            next.push((entry_keys.clone(), entry_counts.clone()));
            for copy in 1..=count {
                let mut with_keys = entry_keys.clone();
                let mut with_counts = entry_counts.clone();
                with_keys.push(key);
                with_counts.push(machine.store.int(copy)?);
                next.push((with_keys, with_counts));
            }
        }
        entries = next;
    }
    let functions: Vec<Id> = entries
        .iter()
        .map(|(entry_keys, entry_counts)| {
            machine.store.function_of_sorted(entry_keys, entry_counts)
        })
        .collect();
    machine.store.set_of(&functions)
}

fn bag_to_set(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let bag = expect_function(machine, args[0])?;
    Ok(machine.store.domain_of(bag))
}

fn set_to_bag(machine: &mut Machine<'_>, args: &[Id], _: &[Applier]) -> Outcome<Id> {
    let set = expect_set(machine, args[0])?;
    let elements = machine.store.set_elements(set).to_vec();
    let one = machine.store.int(1)?;
    let counts = vec![one; elements.len()];
    Ok(machine.store.function_of_sorted(&elements, &counts))
}
