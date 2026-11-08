//! The store's cases from tests/unit/engine-store.test.ts, the ids the TypeScript store gives the
//! prototype's workload, and the laws of TLC's order on generated values.

mod common;

use common::workload;
use tla_values::store::{Bail, EMPTY_SET, EMPTY_TUPLE, FALSE, Id, KIND_INT, KIND_SET, Store, TRUE};

fn utf16(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
}

fn ints(store: &mut Store, values: &[i64]) -> Vec<Id> {
    values
        .iter()
        .map(|&value| store.int(value).unwrap())
        .collect()
}

fn str(store: &mut Store, text: &str) -> Id {
    store.str(&utf16(text))
}

#[test]
fn interns_the_constants_first() {
    let store = Store::new();
    assert_eq!((FALSE, TRUE, EMPTY_SET, EMPTY_TUPLE), (0, 1, 2, 3));
    assert_eq!(store.kind_of(EMPTY_SET), KIND_SET);
    // The small integers -256..=4096 follow, in order.
    assert_eq!(store.value_count(), 4 + 4353);
    assert_eq!(store.int_of(4), -256);
    assert_eq!(store.kind_of(4 + 4352), KIND_INT);
}

// Its expected numbers are of exactly 20,000 steps, which take Miri too long.
#[test]
#[cfg_attr(miri, ignore)]
fn gives_the_typescript_stores_ids_to_the_workload() {
    let mut store = Store::new();
    let result = workload::run(&mut store, 20_000);
    assert_eq!((result.values, result.checksum), (10_132, 511_025_568));
    // The same store, reset, gives the same ids again.
    let again = workload::run(&mut store, 20_000);
    assert_eq!((again.values, again.checksum), (10_132, 511_025_568));
}

#[test]
fn gives_an_except_result_the_id_of_the_same_tuple_built_directly() {
    let mut store = Store::new();
    let elements = ints(&mut store, &[1, 2, 3]);
    let tuple = store.tuple_of(&elements);
    let (two, seven) = (store.int(2).unwrap(), store.int(7).unwrap());
    let built = store.except(tuple, two, seven).unwrap();
    let direct = ints(&mut store, &[1, 7, 3]);
    assert_eq!(store.tuple_of(&direct), built);
}

#[test]
fn gives_an_except_result_the_id_of_the_same_function_built_directly() {
    let mut store = Store::new();
    let strings = vec![
        str(&mut store, "a"),
        str(&mut store, "b"),
        str(&mut store, "c"),
    ];
    for domain in [ints(&mut store, &[0, 1, 2]), strings] {
        let range = ints(&mut store, &[5, 6, 7]);
        let function = store.function_of_sorted(&domain, &range);
        let eight = store.int(8).unwrap();
        let first = store.except(function, domain[0], eight).unwrap();
        let changed = ints(&mut store, &[8, 6, 7]);
        assert_eq!(store.function_of_sorted(&domain, &changed), first);
        // Updates out of order, and a key updated twice.
        let values = ints(&mut store, &[1, 4, 2, 3]);
        let updated = store.except_at(function, &[2, 1, 0, 1], &values);
        let expected = ints(&mut store, &[2, 3, 1]);
        assert_eq!(updated, store.function_of_sorted(&domain, &expected));
        let same = ints(&mut store, &[4, 6]);
        assert_eq!(store.except_at(function, &[1, 1], &same), function);
    }
}

#[test]
fn gives_a_record_the_id_of_the_same_function_built_directly() {
    let mut store = Store::new();
    let keys = [str(&mut store, "x"), str(&mut store, "y")];
    let shape = store.create_record_shape(&keys);
    let values = ints(&mut store, &[1, 2]);
    let record = store.record_of(&shape, &values);
    assert_eq!(store.function_of_sorted(&keys, &values), record);
    assert!(store.is_record(record));
    let four = store.int(4).unwrap();
    let changed = store.except(record, keys[1], four).unwrap();
    let expected = ints(&mut store, &[1, 4]);
    assert_eq!(store.record_of(&shape, &expected), changed);
}

#[test]
fn finds_values_again_after_the_table_and_the_heap_grow() {
    let mut store = Store::new();
    let keys = [str(&mut store, "k")];
    let shape = store.create_record_shape(&keys);
    let records: Vec<Id> = (0..if cfg!(miri) { 2_000 } else { 20_000 })
        .map(|index| {
            let value = store.int(index).unwrap();
            store.record_of(&shape, &[value])
        })
        .collect();
    let count = store.value_count();
    for (index, &record) in records.iter().enumerate() {
        let value = store.int(index as i64).unwrap();
        assert_eq!(store.function_of_sorted(&keys, &[value]), record);
    }
    assert_eq!(store.value_count(), count);
}

#[test]
fn sorts_a_sets_elements_and_drops_duplicates_short_or_long() {
    let mut store = Store::new();
    for length in [3usize, 16, 17, 100] {
        let sorted = ints(&mut store, &(0..length as i64).collect::<Vec<_>>());
        let shuffled: Vec<Id> = (0..2 * length)
            .map(|index| sorted[(index * 37) % length])
            .collect();
        let set = store.set_of_sorted(&sorted);
        assert_eq!(store.set_of(&shuffled), Ok(set));
        assert_eq!(store.set_of_range(&shuffled), Ok(set));
    }
}

#[test]
fn sorts_a_functions_keys_with_their_values() {
    let mut store = Store::new();
    let keys = [
        str(&mut store, "c"),
        str(&mut store, "a"),
        str(&mut store, "b"),
    ];
    let values = ints(&mut store, &[3, 1, 2]);
    let sorted = [keys[1], keys[2], keys[0]];
    let expected = ints(&mut store, &[1, 2, 3]);
    let function = store.function_of_sorted(&sorted, &expected);
    assert_eq!(store.function_of(&keys, &values), Ok(function));
    // Positions 1..n make a tuple, sorted by insertion or, past 16 keys, by merging.
    for length in [3, 40] {
        let keys = ints(&mut store, &(1..=length).rev().collect::<Vec<_>>());
        let values = ints(&mut store, &(0..length).collect::<Vec<_>>());
        let reversed: Vec<Id> = values.iter().rev().copied().collect();
        let tuple = store.tuple_of(&reversed);
        assert_eq!(store.function_of(&keys, &values), Ok(tuple));
        assert_eq!(store.domain_of(tuple), {
            let positions = ints(&mut store, &(1..=length).collect::<Vec<_>>());
            store.set_of_sorted(&positions)
        });
    }
}

#[test]
fn builds_a_sequences_tail_append_and_concatenation_as_the_tuple_of_their_elements() {
    let mut store = Store::new();
    let elements = ints(&mut store, &[1, 2, 3]);
    let tuple = store.tuple_of(&elements);
    let tail = store.tuple_of(&elements[1..]);
    assert_eq!(store.slice_tuple(tuple, 1, 3), tail);
    assert_eq!(store.slice_tuple(tuple, 1, 1), EMPTY_TUPLE);
    let four = store.int(4).unwrap();
    let longer = ints(&mut store, &[1, 2, 3, 4]);
    assert_eq!(store.append_tuple(tuple, four), store.tuple_of(&longer));
    let twice = [elements.clone(), elements].concat();
    assert_eq!(store.concat_tuples(tuple, tuple), store.tuple_of(&twice));
    assert_eq!(store.concat_tuples(EMPTY_TUPLE, tuple), tuple);
}

#[test]
fn orders_strings_by_rank_ranked_before_unranked_and_unranked_by_text() {
    let mut store = Store::new();
    store.reset([&utf16("b")[..], &utf16("a")[..]]);
    let (a, b, zz, c) = (
        str(&mut store, "a"),
        str(&mut store, "b"),
        str(&mut store, "zz"),
        str(&mut store, "c"),
    );
    assert_eq!(store.compare(a, b), Ok(1));
    assert_eq!(store.compare(b, zz), Ok(-1));
    assert_eq!(store.compare(c, zz), Ok(-1));
    let set = store.set_of_sorted(&[b, a, c, zz]);
    assert_eq!(store.set_of(&[zz, c, a, b]), Ok(set));
    // A model value is ranked when it is made, a string built at run time is not.
    let m = store.model(&utf16("m"));
    assert_eq!(store.text_rank_of(m), 2);
    assert_eq!(store.text_rank_of(zz), -1);
    let order: Vec<String> = store
        .get_string_order()
        .into_iter()
        .map(String::from_utf16_lossy)
        .collect();
    assert_eq!(order, ["b", "a", "m"]);
}

#[test]
fn stops_where_tlc_fails_to_compare_for_the_typescript_stores_reasons() {
    let mut store = Store::new();
    let key = str(&mut store, "a");
    let one = store.int(1).unwrap();
    let shape = store.create_record_shape(&[key]);
    let record = store.record_of(&shape, &[one]);
    let domain = ints(&mut store, &[0, 1]);
    let range = ints(&mut store, &[1, 2]);
    let function = store.function_of_sorted(&domain, &range);
    let typed = store.model(&utf16("A_x"));
    let other_type = store.model(&utf16("B_y"));
    let untyped = store.model(&utf16("m"));
    let set = store.set_of(&range).unwrap();
    assert_eq!(
        store.compare(record, function),
        Err(Bail("record compared with a function"))
    );
    assert_eq!(
        store.equals(function, record),
        Err(Bail("record compared with a function"))
    );
    assert_eq!(
        store.compare(one, key),
        Err(Bail("values TLC can't compare"))
    );
    assert_eq!(
        store.equals(one, key),
        Err(Bail("equality of values TLC can't compare"))
    );
    assert_eq!(store.compare(typed, one), Err(Bail("typed model value")));
    assert_eq!(
        store.equals(typed, other_type),
        Err(Bail("differently typed model values"))
    );
    assert_eq!(store.equals(typed, untyped), Ok(false));
    assert_eq!(
        store.is_member(key, set),
        Err(Bail("membership of a value TLC can't compare"))
    );
    // The first element fails where the last doesn't: models come first, ordered by rank.
    let models = [other_type, untyped];
    let sorted_models = store.set_of(&models).unwrap();
    assert_eq!(store.set_elements(sorted_models), models);
    assert_eq!(
        store.is_member(typed, sorted_models),
        Err(Bail("differently typed model values"))
    );
    assert_eq!(
        store.set_of(&[one, key]),
        Err(Bail("values TLC can't compare"))
    );
    let five = store.int(5).unwrap();
    assert_eq!(
        store.except(function, five, one),
        Err(Bail("EXCEPT outside the domain"))
    );
    assert_eq!(
        store.except(one, five, one),
        Err(Bail("EXCEPT on a non-function"))
    );
    assert_eq!(
        store.apply(function, five),
        Err(Bail("applied a function outside its domain"))
    );
    assert_eq!(store.apply(one, five), Err(Bail("applied a non-function")));
    assert_eq!(store.int(1 << 31), Err(Bail("integer overflow")));
    // An untyped model value is less than any other value.
    let sorted = store.set_of_sorted(&[untyped, one]);
    assert_eq!(store.set_of(&[one, untyped]), Ok(sorted));
}

// A deterministic generator, so that a failure names its seed.
struct Random(u64);

impl Random {
    fn next(&mut self, bound: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % bound
    }
}

// A value of a kind TLC compares with others of its kind, often, and with others, sometimes.
fn generate(store: &mut Store, random: &mut Random, depth: u32) -> Id {
    let choice = random.next(if depth == 0 { 4 } else { 9 });
    match choice {
        0 => store.int(random.next(7) as i64 - 3).unwrap(),
        1 => {
            let texts = ["a", "b", "zz", "c", "é", "\u{3b1}"];
            store.str(&utf16(texts[random.next(texts.len() as u64) as usize]))
        }
        2 => store.bool(random.next(2) == 1),
        3 => {
            let names = ["m1", "m2", "A_x", "A_y", "B_z"];
            store.model(&utf16(names[random.next(names.len() as u64) as usize]))
        }
        4 | 5 => {
            let length = random.next(4) as usize;
            let kind = random.next(3);
            let elements: Vec<Id> = (0..length)
                .map(|_| match kind {
                    0 => store.int(random.next(5) as i64).unwrap(),
                    1 => generate(store, random, 0),
                    _ => generate(store, random, depth - 1),
                })
                .collect();
            store.set_of(&elements).unwrap_or(EMPTY_SET)
        }
        6 => {
            let length = random.next(4) as usize;
            let elements: Vec<Id> = (0..length)
                .map(|_| generate(store, random, depth - 1))
                .collect();
            store.tuple_of(&elements)
        }
        _ => {
            let keys = ["a", "b", "c"];
            let length = 1 + random.next(3) as usize;
            let keys: Vec<Id> = keys[..length].iter().map(|key| str(store, key)).collect();
            let values: Vec<Id> = (0..length)
                .map(|_| generate(store, random, depth - 1))
                .collect();
            if choice == 7 {
                let shape = store.create_record_shape(&keys);
                store.record_of(&shape, &values)
            } else {
                let domain = ints(store, &(0..length as i64).collect::<Vec<_>>());
                store.function_of_sorted(&domain, &values)
            }
        }
    }
}

#[test]
fn orders_generated_values_antisymmetrically_and_transitively() {
    let mut store = Store::new();
    store.reset(
        ["b", "a", "m1"]
            .map(|text| text.encode_utf16().collect::<Vec<_>>())
            .iter()
            .map(Vec::as_slice),
    );
    let mut random = Random(0x9e3779b97f4a7c15);
    let values: Vec<Id> = (0..if cfg!(miri) { 30 } else { 300 })
        .map(|_| generate(&mut store, &mut random, 3))
        .collect();
    let mut compared = 0;
    for &left in &values {
        for &right in &values {
            let forward = store.compare(left, right);
            let backward = store.compare(right, left);
            assert_eq!(forward.is_ok(), backward.is_ok(), "{left} and {right}");
            let (Ok(forward), Ok(backward)) = (forward, backward) else {
                continue;
            };
            compared += 1;
            assert_eq!(forward.signum(), -backward.signum(), "{left} and {right}");
            assert_eq!(forward == 0, left == right);
            assert_eq!(store.equals(left, right), Ok(left == right));
        }
    }
    assert!(
        compared > values.len() * values.len() / 10,
        "only {compared} pairs compared"
    );
    for _ in 0..if cfg!(miri) { 300 } else { 20_000 } {
        let pick = |random: &mut Random| values[random.next(values.len() as u64) as usize];
        let (first, second, third) = (pick(&mut random), pick(&mut random), pick(&mut random));
        // A typed model value makes the order partial: A_x < m1 < 1, yet A_x and 1 fail.
        if let (Ok(-1), Ok(-1), Ok(sign)) = (
            store.compare(first, second).map(i32::signum),
            store.compare(second, third).map(i32::signum),
            store.compare(first, third).map(i32::signum),
        ) {
            assert_eq!(sign, -1, "{first}, {second} and {third}");
        }
    }
}

#[test]
fn builds_one_set_from_any_order_of_its_elements() {
    let mut store = Store::new();
    let mut random = Random(12345);
    for _ in 0..if cfg!(miri) { 30 } else { 2_000 } {
        let length = 1 + random.next(40) as usize;
        let elements: Vec<Id> = (0..length)
            .map(|_| generate(&mut store, &mut random, 2))
            .collect();
        // Which pairs a sort compares depends on the order, so where some pairs fail to compare,
        // one order can fail and another succeed. Where none fail, every order succeeds.
        let is_comparable = elements.iter().all(|&left| {
            elements
                .iter()
                .all(|&right| store.compare(left, right).is_ok())
        });
        let Ok(set) = store.set_of(&elements) else {
            assert!(!is_comparable);
            continue;
        };
        let members = store.set_elements(set).to_vec();
        for pair in members.windows(2) {
            assert_eq!(store.compare(pair[0], pair[1]).map(i32::signum), Ok(-1));
        }
        let mut shuffled = elements.clone();
        for index in (1..shuffled.len()).rev() {
            shuffled.swap(index, random.next(index as u64 + 1) as usize);
        }
        match store.set_of(&shuffled) {
            Ok(other) => assert_eq!(other, set),
            Err(_) => assert!(!is_comparable),
        }
        for &element in &elements {
            assert_eq!(store.is_member(element, set), Ok(true));
        }
    }
}
