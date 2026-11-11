//! Sets the engine tests for membership without building them, and the sets of functions, records
//! and tuples, which it builds only when it must, as `compileLazySet` and `memberTest` do.

use tla_ir::{NodeId, NodeKind};
use tla_values::store::{
    KIND_FUNCTION, KIND_INT, KIND_MODEL, KIND_SET, KIND_STRING, KIND_TUPLE, Outcome,
    is_tested_set_kind,
};
use tla_values::{Bail, Id};

use super::builtins::expect_int;
use super::lazy::Lazy;
use super::nodes::expect_set;
use super::{
    Compiled, Compiler, Compiling, Context, combine_references, eval, leaf, member, parts,
};
use crate::footprint::Footprint;
use crate::machine::{Eval, Machine, Member, Parts};

// Past this many functions the interpreter builds the set instead, before memory runs short.
const MAXIMUM_FUNCTIONS: f64 = (1u64 << 24) as f64;

/// TLC fails to test a value other than a model value for membership in a set of another kind:
/// an untyped model value isn't a member, and anything else, a typed model value included, fails.
/// Membership in Nat, Int or STRING (`IntValue`'s and `StringValue`'s `member`), which fails for
/// a value of another kind but an untyped model value.
pub(crate) fn is_in_named(machine: &Machine<'_>, name: &str, element: Id) -> Outcome<bool> {
    let kind = machine.store.kind_of(element);
    match (name, kind) {
        ("Nat", KIND_INT) => Ok(machine.store.int_of(element) >= 0),
        ("Int", KIND_INT) | ("STRING", KIND_STRING) => Ok(true),
        ("Nat", _) => not_in(machine, element, "a mistyped membership in Nat"),
        ("Int", _) => not_in(machine, element, "a mistyped membership in Int"),
        ("STRING", _) => not_in(machine, element, "a mistyped membership in STRING"),
        _ => Err(Bail(
            "unsupported: membership in an infinite set by its name alone",
        )),
    }
}

pub(crate) fn not_in(machine: &Machine<'_>, element: Id, reason: &'static str) -> Outcome<bool> {
    if machine.store.kind_of(element) == KIND_MODEL && machine.store.get_model_type(element) == 0 {
        Ok(false)
    } else {
        Err(Bail(reason))
    }
}

// TLC compares the domains element by element, and fails on two values it can't compare.
fn equals_domain(machine: &mut Machine<'_>, function: Id, domain: Id) -> Outcome<bool> {
    if machine.store.kind_of(domain) != KIND_SET {
        return Err(Bail("a function set over a non-set domain"));
    }
    let size = machine.store.size_of(function);
    if size != machine.store.size_of(domain) {
        return Ok(false);
    }
    for index in 0..size {
        let key = machine.store.get_key(function, index);
        let element = machine.store.element_at(domain, index);
        if key != element {
            return Ok(machine.store.compare(key, element)? == 0);
        }
    }
    Ok(true)
}

fn enumerate_function_set(machine: &mut Machine<'_>, domain: Id, range: Id) -> Outcome<Id> {
    if machine.store.kind_of(domain) != KIND_SET || machine.store.kind_of(range) != KIND_SET {
        return Err(Bail("a function set of non-sets"));
    }
    let domain_size = machine.store.size_of(domain);
    let range_size = machine.store.size_of(range);
    if f64::from(range_size).powf(f64::from(domain_size)) > MAXIMUM_FUNCTIONS {
        return Err(Bail("a function set too large to build"));
    }
    let keys = machine.store.set_elements(domain).to_vec();
    let choices = machine.store.set_elements(range).to_vec();
    let mut functions = Vec::new();
    let mut values = vec![0; keys.len()];
    let mut positions = vec![0usize; keys.len()];
    // An odometer whose last key turns fastest, as the recursion over the keys in compile.ts.
    if keys.is_empty() || !choices.is_empty() {
        loop {
            for (index, &position) in positions.iter().enumerate() {
                values[index] = choices[position];
            }
            let function = machine.store.function_of_sorted(&keys, &values);
            functions.push(machine.store.mark_built_as_function(function));
            let Some(turning) = (0..keys.len())
                .rev()
                .find(|&index| positions[index] + 1 < choices.len())
            else {
                break;
            };
            positions[turning] += 1;
            for position in &mut positions[turning + 1..] {
                *position = 0;
            }
        }
    }
    machine.store.set_of(&functions)
}

// Every combination of one element from each set, the first set's turning slowest.
fn combinations(machine: &Machine<'_>, sets: &[Id]) -> Outcome<Vec<Vec<Id>>> {
    // An empty set empties the whole, however large the others are.
    if sets.iter().any(|&set| machine.store.size_of(set) == 0) {
        return Ok(Vec::new());
    }
    let total: f64 = sets
        .iter()
        .map(|&set| f64::from(machine.store.size_of(set)))
        .product();
    if total > super::lazy::MAXIMUM_ELEMENTS {
        return Err(Bail("a lazy set too large to enumerate"));
    }
    let mut partial: Vec<Vec<Id>> = vec![Vec::new()];
    for &set in sets {
        let mut next = Vec::new();
        for prefix in &partial {
            for &element in machine.store.set_elements(set) {
                let mut combination = prefix.clone();
                combination.push(element);
                next.push(combination);
            }
        }
        partial = next;
    }
    Ok(partial)
}

const NO_PARTS: fn(&mut Machine<'_>) -> Outcome<()> = |_| Ok(());

impl Compiler<'_> {
    /// A membership test for a compiled set, which builds the set only when it must.
    pub(crate) fn member_test(&self, set: &Compiled) -> Member {
        if let Some(test) = &set.member {
            return test.clone();
        }
        // IntervalValue.member compares an integer with the bounds, building nothing.
        if let Some((low, high)) = set.interval.clone() {
            return member(move |machine, element| {
                let (low, high) = (low(machine)?, high(machine)?);
                let (low, high) = (expect_int(machine, low)?, expect_int(machine, high)?);
                // An empty interval holds nothing, whatever TLC asks it of.
                if machine.store.kind_of(element) != KIND_INT {
                    if low > high {
                        return Ok(false);
                    }
                    return not_in(machine, element, "values TLC can't compare");
                }
                let value = i64::from(machine.store.int_of(element));
                Ok(low <= value && value <= high)
            });
        }
        match set.infinite {
            Some(name @ ("Nat" | "Int")) => {
                member(move |machine, element| is_in_named(machine, name, element))
            }
            Some(_) => member(|machine, element| is_in_named(machine, "STRING", element)),
            None => {
                let evaluate = set.eval.clone();
                member(move |machine, element| {
                    let id = evaluate(machine)?;
                    if !is_tested_set_kind(machine.store.kind_of(id)) {
                        return Err(Bail("membership in a non-set"));
                    }
                    machine.store.is_member(element, id)
                })
            }
        }
    }

    // The parts of a set TLC evaluates to make its value: a lazy set's own, none for a set such
    // as Nat, and otherwise the set itself.
    pub(crate) fn parts_of(set: &Compiled) -> Parts {
        if let Some(own) = &set.parts {
            return own.clone();
        }
        if set.member.is_some() || set.infinite.is_some() {
            return parts(NO_PARTS);
        }
        let evaluate = set.eval.clone();
        parts(move |machine| evaluate(machine).map(|_| ()))
    }

    // A membership test evaluates its set's parts in a round of its own, in which each lazy set's
    // parts run once: definitions can share a set, as Sn == [a : Sm, b : Sm] does, and bindings
    // don't change within a round.
    pub(crate) fn once_a_round(&mut self, inner: Vec<Parts>) -> Parts {
        let round = self.allocate_round();
        parts(move |machine| {
            if machine.rounds[round] == machine.parts_round {
                return Ok(());
            }
            for part in &inner {
                part(machine)?;
            }
            machine.rounds[round] = machine.parts_round;
            Ok(())
        })
    }

    pub(crate) fn compile_lazy_set(
        &mut self,
        kind: &NodeKind,
        context: &Context,
    ) -> Compiling<Compiled> {
        let set = match kind {
            NodeKind::FunctionSet { domain, range } => {
                self.compile_function_set(*domain, *range, context)
            }
            NodeKind::RecordSet(fields) => self.compile_record_set(fields, context),
            NodeKind::Product(factors) => self.compile_product(factors, context),
            _ => unreachable!("a lazy set of another kind"),
        }?;
        // Where a part may be a set TLC can't enumerate, TLC's own enumeration decides: it finds
        // the set empty, or its one function of an empty domain, before it asks that part.
        let is_lazy = set.has_infinite_part;
        Ok(Self::enumerated_lazily(set, is_lazy))
    }

    // A set of functions, records or tuples whose value is TLC's enumeration of it where
    // `is_lazy`, which asks nothing of a part it doesn't need.
    fn enumerated_lazily(set: Compiled, is_lazy: bool) -> Compiled {
        let Some(reference) = set.reference.clone().filter(|_| is_lazy) else {
            return set;
        };
        Compiled {
            eval: eval(move |machine| {
                let elements = reference(machine)?.enumerate(machine)?;
                machine.store.set_of(&elements)
            }),
            ..set
        }
    }

    fn compile_function_set(
        &mut self,
        domain: NodeId,
        range: NodeId,
        context: &Context,
    ) -> Compiling<Compiled> {
        let domain = self.compile(domain, context)?;
        let range = self.compile(range, context)?;
        let range_member = self.member_test(&range);
        let footprint = domain.footprint.merge(&range.footprint);
        let set_parts = self.once_a_round(vec![Self::parts_of(&domain), Self::parts_of(&range)]);
        let (domain_eval, range_eval) = (domain.eval.clone(), range.eval.clone());
        let member_domain = domain.eval.clone();
        let member_parts = set_parts.clone();
        // A part TLC keeps lazy, as SUBSET S, isn't built to find the one function of an empty
        // domain.
        let is_part_lazy = !domain.is_normalized || !range.is_normalized;
        let set = Compiled {
            is_costly: true,
            // TLC enumerates [S -> T] in its own order, which the reference gives.
            is_normalized: false,
            is_in_order: range.is_in_order,
            has_infinite_part: domain.may_be_infinite() || range.may_be_infinite(),
            reference: combine_references(&[&domain, &range], |_, mut sets| {
                let range = sets.pop().expect("a range");
                let domain = sets.pop().expect("a domain");
                Ok(Lazy::FunctionSet(Box::new(domain), Box::new(range)))
            }),
            parts: Some(set_parts),
            member: Some(member(move |machine, element| {
                machine.run_parts(&member_parts)?;
                let kind = machine.store.kind_of(element);
                if kind != KIND_FUNCTION && kind != KIND_TUPLE {
                    return not_in(
                        machine,
                        element,
                        "a mistyped membership in a set of functions",
                    );
                }
                let domain_set = member_domain(machine)?;
                if !equals_domain(machine, element, domain_set)? {
                    return Ok(false);
                }
                for index in 0..machine.store.size_of(element) {
                    let value = machine.store.get_range_value(element, index);
                    if !range_member(machine, value)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            })),
            ..leaf(
                eval(move |machine| {
                    let domain_set = domain_eval(machine)?;
                    let range_set = range_eval(machine)?;
                    enumerate_function_set(machine, domain_set, range_set)
                }),
                footprint,
            )
        };
        Ok(Self::enumerated_lazily(set, is_part_lazy))
    }

    fn compile_record_set(
        &mut self,
        fields: &[(u32, NodeId)],
        context: &Context,
    ) -> Compiling<Compiled> {
        let mut written = Vec::new();
        for &(name, value) in fields {
            let units = self.units(name);
            let key = self.store.str(&units);
            written.push((key, self.compile(value, context)?));
        }
        // TLC evaluates the fields' sets in the order they're written.
        let set_parts = self.once_a_round(
            written
                .iter()
                .map(|field| Self::parts_of(&field.1))
                .collect(),
        );
        let mut sorted = written;
        let mut sort_error = None;
        sorted.sort_by(|left, right| match self.store.compare(left.0, right.0) {
            Ok(order) => order.cmp(&0),
            Err(bail) => {
                sort_error = Some(bail);
                std::cmp::Ordering::Equal
            }
        });
        if let Some(bail) = sort_error {
            return Err(bail.into());
        }
        let keys: Vec<Id> = sorted.iter().map(|field| field.0).collect();
        let members: Vec<Member> = sorted
            .iter()
            .map(|field| self.member_test(&field.1))
            .collect();
        let sets: Vec<Eval> = sorted.iter().map(|field| field.1.eval.clone()).collect();
        let footprint = Footprint::merge_all(sorted.iter().map(|field| &field.1.footprint));
        let member_keys = keys.clone();
        let reference_keys = keys.clone();
        let member_parts = set_parts.clone();
        let fields: Vec<&Compiled> = sorted.iter().map(|field| &field.1).collect();
        Ok(Compiled {
            is_costly: true,
            is_normalized: false,
            is_in_order: fields.iter().all(|field| field.is_in_order),
            has_infinite_part: fields.iter().any(|field| field.may_be_infinite()),
            reference: combine_references(&fields, move |_, sets| {
                Ok(Lazy::RecordSet(reference_keys.clone(), sets))
            }),
            parts: Some(set_parts),
            member: Some(member(move |machine, element| {
                machine.run_parts(&member_parts)?;
                if machine.store.kind_of(element) != KIND_FUNCTION {
                    return not_in(
                        machine,
                        element,
                        "a mistyped membership in a set of records",
                    );
                }
                if machine.store.size_of(element) as usize != member_keys.len() {
                    return Ok(false);
                }
                for (index, (&key, test)) in member_keys.iter().zip(&members).enumerate() {
                    if machine.store.get_key(element, index as u32) != key {
                        return Ok(false);
                    }
                    let value = machine.store.get_range_value(element, index as u32);
                    if !test(machine, value)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            })),
            ..leaf(
                eval(move |machine| {
                    let mut values = Vec::with_capacity(sets.len());
                    for set in &sets {
                        values.push(set(machine)?);
                    }
                    for &set in &values {
                        expect_set(machine, set, "a record set of a non-set")?;
                    }
                    let records: Vec<Id> = combinations(machine, &values)?
                        .iter()
                        .map(|combination| machine.store.function_of_sorted(&keys, combination))
                        .collect();
                    machine.store.set_of(&records)
                }),
                footprint,
            )
        })
    }

    fn compile_product(&mut self, factors: &[NodeId], context: &Context) -> Compiling<Compiled> {
        let factors = factors
            .iter()
            .map(|&factor| self.compile(factor, context))
            .collect::<Compiling<Vec<Compiled>>>()?;
        Ok(self.product_of(&factors))
    }

    // The product of compiled sets, `\X`'s value and a function's domain of several bounds.
    pub(crate) fn product_of(&mut self, factors: &[Compiled]) -> Compiled {
        let members: Vec<Member> = factors
            .iter()
            .map(|factor| self.member_test(factor))
            .collect();
        let set_parts = self.once_a_round(factors.iter().map(Self::parts_of).collect());
        let sets: Vec<Eval> = factors.iter().map(|factor| factor.eval.clone()).collect();
        let member_parts = set_parts.clone();
        let components: Vec<&Compiled> = factors.iter().collect();
        Compiled {
            is_costly: true,
            is_normalized: false,
            is_in_order: factors.iter().all(|factor| factor.is_in_order),
            has_infinite_part: components.iter().any(|factor| factor.may_be_infinite()),
            reference: combine_references(&components, |_, sets| Ok(Lazy::Product(sets))),
            parts: Some(set_parts),
            member: Some(member(move |machine, element| {
                machine.run_parts(&member_parts)?;
                // A function that isn't a tuple, with integers for its domain, is in no set of
                // tuples (`SetOfTuplesValue.member`); any other value fails.
                let kind = machine.store.kind_of(element);
                if kind == KIND_FUNCTION
                    && (0..machine.store.size_of(element)).all(|index| {
                        let key = machine.store.get_key(element, index);
                        machine.store.kind_of(key) == KIND_INT
                    })
                {
                    return Ok(false);
                }
                if kind != KIND_TUPLE {
                    return not_in(machine, element, "a mistyped membership in a set of tuples");
                }
                if machine.store.size_of(element) as usize != members.len() {
                    return Ok(false);
                }
                for (index, test) in members.iter().enumerate() {
                    let value = machine.store.get_range_value(element, index as u32);
                    if !test(machine, value)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            })),
            ..leaf(
                eval(move |machine| {
                    // Each factor is evaluated and checked before the next, as the loop over
                    // them in compile.ts does.
                    let mut values = Vec::with_capacity(sets.len());
                    for set in &sets {
                        let set = set(machine)?;
                        values.push(expect_set(machine, set, "a product of a non-set")?);
                    }
                    let tuples: Vec<Id> = combinations(machine, &values)?
                        .iter()
                        .map(|combination| machine.store.tuple_of(combination))
                        .collect();
                    machine.store.set_of(&tuples)
                }),
                Footprint::merge_all(factors.iter().map(|factor| &factor.footprint)),
            )
        }
    }
}
