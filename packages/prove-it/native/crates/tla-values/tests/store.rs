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
fn asks_a_function_that_is_no_record_whether_it_equals_a_record() {
    // FcnRcdValue.equals takes any function; RecordValue.equals fails on one that is no record.
    let mut store = Store::new();
    let keys = [str(&mut store, "a"), str(&mut store, "b")];
    let ones = ints(&mut store, &[1, 1]);
    let shape = store.create_record_shape(&keys);
    let record = store.record_of(&shape, &ones);
    let nodes = [store.model(&utf16("m")), store.model(&utf16("n"))];
    let by_node = store.function_of_sorted(&nodes, &ones);
    let tuple = store.tuple_of(&ones);
    assert_eq!(store.equals_asked(by_node, record), Ok(false));
    assert_eq!(
        store.equals_asked(record, by_node),
        Err(Bail("record compared with a function"))
    );
    // A tuple asks the record's keys whether they equal its positions, which fails.
    assert_eq!(
        store.equals_asked(tuple, record),
        Err(Bail("equality of values TLC can't compare"))
    );
    assert_eq!(store.equals_asked(record, record), Ok(true));
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
        Err(Bail("values TLC can't compare"))
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

// Cases the value oracle found: TLC's SetEnumValue.member binary-searches the set with the
// element's compareTo, and fails where that fails.
#[test]
fn stops_a_membership_where_tlcs_search_of_the_set_fails_to_compare() {
    let mut store = Store::new();
    let keys = [str(&mut store, "a"), str(&mut store, "b")];
    let record = |store: &mut Store, values: &[i64]| {
        let shape = store.create_record_shape(&keys[..values.len()]);
        let values = ints(store, values);
        store.record_of(&shape, &values)
    };
    let (one, two) = (store.int(1).unwrap(), store.int(2).unwrap());
    let tuples = [store.tuple_of(&[one]), store.tuple_of(&[two])];
    let tuples = store.set_of(&tuples).unwrap();
    let small = record(&mut store, &[0]);
    let pair = record(&mut store, &[0, 1]);
    let inner = record(&mut store, &[1]);
    let records = store.set_of(&[inner]).unwrap();
    let nested = store.tuple_of(&[inner]);
    let nested = store.set_of(&[nested]).unwrap();
    let long: Vec<Id> = (0..40)
        .map(|value| {
            let value = store.int(value).unwrap();
            store.tuple_of(&[value])
        })
        .collect();
    let long = store.set_of(&long).unwrap();
    let domain = ints(&mut store, &[0, 1]);
    let range = ints(&mut store, &[5, 5]);
    let function = store.function_of_sorted(&domain, &range);
    let functions = store.set_of(&[function]).unwrap();
    let tuple = store.tuple_of(&[one]);
    let deep = store.tuple_of(&[two]);
    let deep = store.tuple_of(&[deep]);
    let cases = [
        (small, tuples, "values TLC can't compare"),
        (pair, tuples, "record compared with a function"),
        (tuple, records, "values TLC can't compare"),
        (deep, nested, "values TLC can't compare"),
        (small, long, "values TLC can't compare"),
        (small, functions, "record compared with a function"),
    ];
    for (element, set, reason) in cases {
        assert_eq!(store.is_member(element, set), Err(Bail(reason)));
    }
}

#[test]
fn stops_a_membership_tlcs_search_passes_but_its_equals_of_a_set_enumeration_fails() {
    let mut store = Store::new();
    // A_x ranks before m, so TRUE's search ends past m without comparing it with A_x. TLC checks a
    // set it hasn't normalized with each element's equals, which fails on A_x.
    let elements = [store.model(&utf16("A_x")), store.model(&utf16("m"))];
    let set = store.set_of(&elements).unwrap();
    assert_eq!(store.is_member(TRUE, set), Err(Bail("typed model value")));
    let other = store.model(&utf16("p"));
    assert_eq!(store.is_member(other, set), Ok(false));
}

#[test]
fn misses_a_scalar_in_a_set_of_its_own_kind() {
    let mut store = Store::new();
    let words = ["ncs", "e1", "exit", "cs"].map(|word| store.str(&utf16(word)));
    let strings = store.set_of(&words[..3]).unwrap();
    assert_eq!(store.is_member(words[3], strings), Ok(false));
    assert_eq!(store.is_member(words[1], strings), Ok(true));
    let numbers = (0..20)
        .map(|value| store.int(value * 2).unwrap())
        .collect::<Vec<_>>();
    let evens = store.set_of(&numbers).unwrap();
    for value in -3..43 {
        let element = store.int(value).unwrap();
        assert_eq!(
            store.is_member(element, evens),
            Ok((0..40).contains(&value) && value % 2 == 0)
        );
    }
    let booleans = store.set_of(&[TRUE]).unwrap();
    assert_eq!(store.is_member(FALSE, booleans), Ok(false));
    assert_eq!(
        store.is_member(words[3], evens),
        Err(Bail("values TLC can't compare"))
    );
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

// TLC's SetEnumValue.member of a set it has normalized: ValueVec.search, a binary search with the
// element's compareTo.
fn search(store: &mut Store, element: Id, set: Id) -> Result<bool, Bail> {
    let elements = store.set_elements(set).to_vec();
    let (mut low, mut high) = (0, elements.len());
    while low < high {
        let middle = low + ((high - low) >> 1);
        let comparison = store.compare(element, elements[middle])?;
        if comparison == 0 {
            return Ok(true);
        }
        if comparison < 0 {
            high = middle;
        } else {
            low = middle + 1;
        }
    }
    Ok(false)
}

// The store answers some memberships by id, without comparing: it must fail wherever TLC's search
// fails, and find what it finds.
#[test]
fn fails_a_membership_wherever_tlcs_search_fails() {
    let mut store = Store::new();
    store.reset(
        ["b", "a", "m1"]
            .map(|text| text.encode_utf16().collect::<Vec<_>>())
            .iter()
            .map(Vec::as_slice),
    );
    let mut random = Random(0x2545f4914f6cdd1d);
    let mut values: Vec<Id> = (0..if cfg!(miri) { 30 } else { 400 })
        .map(|_| generate(&mut store, &mut random, 3))
        .collect();
    values.extend([EMPTY_TUPLE, EMPTY_SET]);
    // Functions over model values, untyped and typed, and over a mix of keys, with values of any
    // kind: 1 at one key and FALSE at another, say.
    let keys = ["m1", "m2", "A_x"].map(|name| store.model(&utf16(name)));
    let one = store.int(1).unwrap();
    for _ in 0..if cfg!(miri) { 10 } else { 200 } {
        let pick = |random: &mut Random| values[random.next(values.len() as u64) as usize];
        let domain = match random.next(3) {
            0 => vec![keys[0], keys[1]],
            1 => vec![keys[0], keys[2]],
            _ => vec![keys[0], one],
        };
        let range = [pick(&mut random), pick(&mut random)];
        if let Ok(function) = store.function_of(&domain, &range) {
            values.push(function);
        }
    }
    let mut sets: Vec<Id> = values
        .iter()
        .filter_map(|&value| store.set_of(&[value]).ok())
        .collect();
    for _ in 0..if cfg!(miri) { 30 } else { 2_000 } {
        let length = random.next(30) as usize;
        let elements: Vec<Id> = (0..length)
            .map(|_| values[random.next(values.len() as u64) as usize])
            .collect();
        if let Ok(set) = store.set_of(&elements) {
            sets.push(set);
        }
    }
    let (mut failed, mut found) = (0, 0);
    for &set in &sets {
        let mut elements = store.set_elements(set).to_vec();
        elements.extend((0..20).map(|_| values[random.next(values.len() as u64) as usize]));
        for element in elements {
            let member = store.is_member(element, set);
            match search(&mut store, element, set) {
                Err(_) => {
                    failed += 1;
                    assert!(member.is_err(), "{element} in {set}");
                }
                Ok(true) => {
                    found += 1;
                    assert_eq!(member, Ok(true), "{element} in {set}");
                }
                // TLC's equals of a set it hasn't normalized may still fail.
                Ok(false) => assert!(member != Ok(true), "{element} in {set}"),
            }
        }
    }
    assert!(
        failed > 1_000 && found > 500,
        "{failed} failed, {found} found"
    );
}

// Records of many other keys join to a class of all their keys only so far: past that, membership
// in a set of them compares, and answers as it did.
#[test]
fn answers_a_membership_among_records_of_many_keys() {
    let mut store = Store::new();
    let one = store.int(1).unwrap();
    let records: Vec<Id> = (0..if cfg!(miri) { 100 } else { 2_000 })
        .map(|index| {
            let key = str(&mut store, &format!("k{index}"));
            store.function_of(&[key], &[one]).unwrap()
        })
        .collect();
    let set = store.set_of(&records).unwrap();
    for &record in records.iter().step_by(97) {
        assert_eq!(store.is_member(record, set), Ok(true));
    }
    let other = str(&mut store, "other");
    let missing = store.function_of(&[other], &[one]).unwrap();
    assert_eq!(store.is_member(missing, set), Ok(false));
}

// A string ranked after the order is frozen, as ToString ranks one in a search, compares only
// with itself; a reset orders all strings again.
#[test]
fn bails_on_ordering_a_string_ranked_after_the_order_is_frozen() {
    let mut store = Store::new();
    store.reset([&utf16("a")[..]]);
    let a = str(&mut store, "a");
    let set = store.set_of(&[a]).unwrap();
    assert_eq!(store.is_member(a, set), Ok(true));
    store.freeze_string_order();
    assert!(!store.has_unordered_strings());
    store.get_string_rank(&utf16("12"));
    let twelve = str(&mut store, "12");
    assert!(store.has_unordered_strings());
    assert_eq!(store.compare(twelve, twelve), Ok(0));
    assert!(store.compare(a, twelve).is_err());
    assert!(store.set_of(&[a, twelve]).is_err());
    // A string misses in a set of strings in any order.
    assert_eq!(store.is_member(twelve, set), Ok(false));
    let pair = store.tuple_of(&[twelve]);
    let pairs = store.tuple_of(&[a]);
    let pairs = store.set_of(&[pairs]).unwrap();
    assert!(store.is_member(pair, pairs).is_err());
    store.reset([&utf16("a")[..]]);
    let (a, twelve) = (str(&mut store, "a"), str(&mut store, "12"));
    assert!(store.compare(a, twelve).is_ok());
}

// A string the store held unranked, ranked after the order is frozen, as TLCModelValue ranks one,
// compares with no other string: a membership that compared it before is no longer answered by id.
#[test]
fn bails_on_a_membership_of_a_string_ranked_after_the_order_is_frozen() {
    let mut store = Store::new();
    store.reset([&utf16("a")[..]]);
    store.freeze_string_order();
    let (a, b) = (str(&mut store, "a"), str(&mut store, "b"));
    let (tuple_a, tuple_b) = (store.tuple_of(&[a]), store.tuple_of(&[b]));
    let set = store.set_of(&[tuple_a]).unwrap();
    assert_eq!(store.is_member(tuple_b, set), Ok(false));
    store.rank_text(&utf16("b"));
    assert!(store.compare(tuple_b, tuple_a).is_err());
    assert!(store.is_member(tuple_b, set).is_err());
}

// Values built from a store's: some it holds, and some it doesn't, made every way the store makes
// a block, from blocks of the store and from blocks of their own.
fn build_on(store: &mut Store) -> Vec<Id> {
    let keys = [str(store, "a"), str(store, "b")];
    let shape = store.create_record_shape(&keys);
    let small = ints(store, &[1, 2, 3]);
    let held = store.record_of(&shape, &small[..2]);
    let large = ints(store, &[1_000_000, -5_000, 3]);
    let fresh = store.record_of(&shape, &large[..2]);
    let text = str(store, "zz");
    let from_held = store.except(held, keys[0], text).unwrap();
    let from_fresh = store.except(fresh, keys[1], text).unwrap();
    let tuple = store.tuple_of(&large);
    let tail = store.slice_tuple(tuple, 1, 3);
    let joined = store.concat_tuples(tuple, tail);
    let set = store.set_of(&[joined, tuple, tail]).unwrap();
    let nested = store.set_of(&[set, EMPTY_SET]).unwrap();
    let domain = store.set_of(&large).unwrap();
    let function = store.function_over_set(domain, &[text, text, keys[0]]);
    let others = store.set_of(&[small[2], large[0]]).unwrap();
    let union = store.union(domain, others).unwrap();
    vec![
        held, fresh, from_held, from_fresh, joined, nested, function, union, text,
    ]
}

fn base_store() -> Store {
    let mut store = Store::new();
    store.reset([utf16("b"), utf16("a")].iter().map(Vec::as_slice));
    let keys = [str(&mut store, "a"), str(&mut store, "b")];
    let shape = store.create_record_shape(&keys);
    let small = ints(&mut store, &[1, 2]);
    store.record_of(&shape, &small);
    store
}

#[test]
fn an_overlay_names_its_bases_values_by_their_ids_and_its_own_after_them() {
    let base = std::sync::Arc::new(base_store());
    let count = base.value_count() as Id;
    let mut overlay = Store::overlay(base.clone());
    let built = build_on(&mut overlay);
    let held = {
        let mut store = base_store();
        build_on(&mut store)[0]
    };
    assert_eq!(built[0], held);
    assert!(built[1..].iter().all(|&id| id >= count));
    assert_eq!(base.value_count() as Id, count);
    // TLC's order and equality read values of both.
    assert_eq!(overlay.compare(built[0], built[1]).unwrap(), -1);
    assert!(!overlay.equals(built[0], built[1]).unwrap());
    let (zz, b) = (str(&mut overlay, "zz"), str(&mut overlay, "b"));
    assert_eq!(overlay.compare(zz, b).unwrap(), 1);
    assert_eq!(overlay.text_rank_of(zz), -1);
}

#[test]
fn imports_an_overlays_values_with_the_ids_the_store_then_gives_them() {
    let base = std::sync::Arc::new(base_store());
    let mut overlay = Store::overlay(base.clone());
    let built = build_on(&mut overlay);
    overlay.detach();
    drop(base);
    let mut store = base_store();
    let mut imported = Vec::new();
    let ids: Vec<Id> = built
        .iter()
        .map(|&id| store.import(&overlay, id, &mut imported))
        .collect();
    assert_eq!(build_on(&mut store), ids);
    // An overlay laid on the store again finds them there.
    let base = std::sync::Arc::new(store);
    overlay.attach(base.clone());
    assert_eq!(build_on(&mut overlay), ids);
    assert_eq!(overlay.value_count(), base.value_count());
}

// An overlay laid on another store copies that store's values whole, though both stores are of
// one generation, and a store that was an overlay is reset to one of its own.
#[test]
fn an_overlay_laid_on_another_store_copies_it_whole() {
    let mut first = Store::new();
    let held = first.int(10_000).unwrap();
    let mut second = Store::new();
    assert_eq!(second.int(20_000).unwrap(), held);
    assert_eq!(first.generation(), second.generation());
    let mut overlay = Store::overlay(std::sync::Arc::new(first));
    overlay.detach();
    overlay.attach(std::sync::Arc::new(second));
    assert_eq!(overlay.int_of(held), 20_000);
    overlay.detach();
    overlay.reset(std::iter::empty::<&[u16]>());
    assert_eq!(overlay.value_count(), Store::new().value_count());
    assert_eq!(overlay.int(20_000).unwrap(), held);
}
