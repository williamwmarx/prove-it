//! TLC's fingerprints of the store's values and states, against those the prototype checked with
//! src/tlc/fingerprint.ts (DESIGN.md 10.3), and the engine's ways of fingerprinting a state against
//! each other.

use tla_values::fingerprint::{Fingerprints, INITIAL, Overlaid, Parent, extend_byte, extend_int};
use tla_values::store::{Id, Store, TRUE};

fn utf16(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
}

#[test]
fn match_tlc_on_a_sample_of_each_kind() {
    let mut store = Store::new();
    let int = |store: &mut Store, value: i64| store.int(value).unwrap();
    let (one, two, three) = (int(&mut store, 1), int(&mut store, 2), int(&mut store, 3));
    let set = store.set_of(&[three, one, two]).unwrap();
    let (a, b) = (store.str(&utf16("a")), store.str(&utf16("b")));
    let x = store.str(&utf16("x"));
    let record = store.function_of(&[b, a], &[x, one]).unwrap();
    let (p, q) = (store.str(&utf16("p")), store.str(&utf16("q")));
    let tuple = store.tuple_of(&[p, q]);
    let state = [
        int(&mut store, 7),
        int(&mut store, -(1 << 31)),
        store.str(&utf16("hello")),
        TRUE,
        set,
        record,
        tuple,
    ];
    let order: Vec<usize> = (0..state.len()).collect();
    let mut fingerprints = Fingerprints::new();
    let expected = -2179341659381351120i64 as u64;
    assert_eq!(fingerprints.get_state(&store, &state, &order), expected);
    assert_eq!(
        fingerprints.get_states(&store, &state, state.len(), &order, None),
        [expected]
    );
    assert_eq!(
        fingerprints.get_states_reference(&store, &state, state.len(), &order),
        [expected]
    );
}

#[test]
fn match_tlc_on_model_values_by_their_rank() {
    // TLC's fingerprints, from native/oracle/ValueOracle.java, with "a", "m1" and "B_y" interned
    // first, so that m1 is UniqueString token 2.
    let mut store = Store::new();
    store.reset(["a", "m1", "B_y"].map(utf16).iter().map(Vec::as_slice));
    let model = store.model(&utf16("m1"));
    let seven = store.int(7).unwrap();
    let set = store.set_of(&[seven, model]).unwrap();
    let mut fingerprints = Fingerprints::new();
    assert_eq!(
        fingerprints.get_state(&store, &[model], &[0]),
        5068397444161466873
    );
    assert_eq!(
        fingerprints.get_state(&store, &[set], &[0]),
        -1941079772221809000i64 as u64
    );
}

// Its expected xor is of exactly a million states, which take Miri hours.
#[test]
#[cfg_attr(miri, ignore)]
fn match_tlc_on_a_million_states_of_five_integers() {
    let mut store = Store::new();
    let states: Vec<Id> = (0..1_000_000i64)
        .flat_map(|state| (1..=5).map(move |variable| (state * variable) & 1023))
        .map(|value| store.int(value).unwrap())
        .collect();
    let order: Vec<usize> = (0..5).collect();
    let mut fingerprints = Fingerprints::new();
    let xor = |fingerprints: Vec<u64>| {
        fingerprints
            .into_iter()
            .fold(0, |sum, fingerprint| sum ^ fingerprint)
    };
    assert_eq!(
        xor(fingerprints.get_states(&store, &states, 5, &order, None)),
        8882444436892305134
    );
    // The states from scratch, extending FP64 byte by byte as TLC does.
    let bytes = (0..1_000_000i32)
        .map(|state| {
            (1..=5).fold(INITIAL, |fingerprint, variable| {
                extend_int(
                    extend_byte(fingerprint, 1),
                    state.wrapping_mul(variable) & 1023,
                )
            })
        })
        .collect();
    assert_eq!(xor(bytes), 8882444436892305134);
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

#[test]
fn are_the_same_from_a_parent_from_the_state_before_and_from_scratch() {
    let mut store = Store::new();
    store.reset([&utf16("m1")[..]]);
    let int = |store: &mut Store, value: i64| store.int(value).unwrap();
    // Values of a few lengths, several sharing one, so that most changes keep the lengths.
    let (one, two, big) = (
        int(&mut store, 1),
        int(&mut store, 2),
        int(&mut store, 1 << 20),
    );
    let long: Vec<Id> = (0..5000).map(|value| int(&mut store, value)).collect();
    let values = vec![
        one,
        two,
        big,
        TRUE,
        store.str(&utf16("a")),
        store.str(&utf16("bb")),
        store.str(&utf16("long string ".repeat(30).as_str())),
        store.model(&utf16("m1")),
        store.model(&utf16("m2")),
        store.set_of(&[one]).unwrap(),
        store.set_of(&[two]).unwrap(),
        store.set_of(&[one, two]).unwrap(),
        store.tuple_of(&[one, two]),
        // A tuple longer than the integers the store interns first, whose keys aren't interned.
        store.tuple_of(&long),
    ];
    let mut random = Random(42);
    let width = 6;
    let mut states: Vec<Id> = Vec::new();
    let mut parents = Vec::new();
    for state in 0..if cfg!(miri) { 100 } else { 3000 } {
        let parent = if state < 3 {
            -1
        } else {
            random.next(state as u64 + 1) as i32 - 1
        };
        let mut row: Vec<Id> = if parent >= 0 {
            states[parent as usize * width..][..width].to_vec()
        } else {
            (0..width)
                .map(|_| values[random.next(values.len() as u64) as usize])
                .collect()
        };
        for _ in 0..random.next(3) {
            row[random.next(width as u64) as usize] =
                values[random.next(values.len() as u64) as usize];
        }
        states.extend(row);
        parents.push(parent);
    }
    let order = [3, 0, 5, 4, 1, 2];
    let mut fingerprints = Fingerprints::new();
    let scratch: Vec<u64> = states
        .chunks_exact(width)
        .map(|row| fingerprints.get_state(&store, row, &order))
        .collect();
    assert_eq!(
        fingerprints.get_states(&store, &states, width, &order, Some(&parents)),
        scratch
    );
    assert_eq!(
        fingerprints.get_states(&store, &states, width, &order, None),
        scratch
    );
    assert_eq!(
        Fingerprints::new().get_states_reference(&store, &states, width, &order),
        scratch
    );
    // As the search fingerprints a successor, from the parent being expanded, whether or not the
    // values that changed keep their lengths, on fingerprints that start out knowing no value.
    let mut from_parents = Fingerprints::new();
    let mut parent = Parent::default();
    for (state, row) in states.chunks_exact(width).enumerate() {
        let Ok(index) = usize::try_from(parents[state]) else {
            continue;
        };
        let parent_row = &states[index * width..][..width];
        from_parents.set_parent(&store, parent_row, &order, scratch[index], &mut parent);
        assert_eq!(
            from_parents.get_child(&store, &mut parent, parent_row, row, &order),
            scratch[state]
        );
    }
    // A tuple's keys are fingerprinted, not interned.
    let count = store.value_count();
    let mut fresh = Fingerprints::new();
    fresh.get_value(&store, values[13]);
    assert_eq!(store.value_count(), count);
}

#[test]
fn forget_the_values_of_a_store_that_was_reset() {
    let mut store = Store::new();
    let mut fingerprints = Fingerprints::new();
    let first = store.str(&utf16("first"));
    let before = fingerprints.get_value(&store, first);
    store.reset(std::iter::empty::<&[u16]>());
    let second = store.str(&utf16("second"));
    assert_eq!(first, second);
    assert_ne!(fingerprints.get_value(&store, second), before);
    assert_eq!(
        fingerprints.get_value(&store, second),
        Fingerprints::new().get_value(&store, second)
    );
}

// Parents whose tails take more lengths than the tables made for tails, so later successors are
// fingerprinted from the parent's prefix, still as from scratch.
#[test]
fn are_the_same_from_a_parent_past_the_tables_for_tails() {
    let mut store = Store::new();
    let (one, two) = (store.int(1).unwrap(), store.int(2).unwrap());
    let order = [0, 1];
    let mut fingerprints = Fingerprints::new();
    let mut parent = Parent::default();
    for length in 1..if cfg!(miri) { 20 } else { 700 } {
        let text = store.str(&utf16(&"x".repeat(length)));
        let (parent_row, row) = ([one, text], [two, text]);
        let expected = Fingerprints::new().get_state(&store, &parent_row, &order);
        fingerprints.set_parent(&store, &parent_row, &order, expected, &mut parent);
        assert_eq!(
            fingerprints.get_child(&store, &mut parent, &parent_row, &row, &order),
            Fingerprints::new().get_state(&store, &row, &order)
        );
    }
}

#[test]
fn absorb_what_an_overlay_computed_by_the_ids_its_values_were_imported_as() {
    let mut store = Store::new();
    store.reset(std::iter::empty::<&[u16]>());
    let one = store.int(1).unwrap();
    let unseen = store.set_of(&[one]).unwrap();
    // The search fingerprints some of the store's values, and lends them to a thread's cache.
    let mut search = Fingerprints::new();
    search.get_value(&store, one);
    let base = std::sync::Arc::new(store);
    let bound = base.value_count() as Id;
    let shared = search.share();
    let mut overlay = Store::overlay(base.clone());
    let mut worker: Fingerprints<Overlaid> = Fingerprints::default();
    worker.attach(&shared, bound);
    // The thread makes values the store doesn't hold, and fingerprints them and a value of the
    // store the search hadn't.
    let made: Vec<Id> = (2..6)
        .map(|value| {
            let element = overlay.int(value).unwrap();
            overlay.set_of(&[one, element]).unwrap()
        })
        .collect();
    let computed: Vec<(u64, u64)> = made
        .iter()
        .map(|&id| worker.get_value(&overlay, id))
        .collect();
    let unseen_value = worker.get_value(&overlay, unseen);
    overlay.detach();
    worker.detach();
    search.take_back(shared);
    // The store imports two of them, in another order, and the search takes what the thread
    // computed, which is what fingerprinting the values afresh gives.
    let mut store = std::sync::Arc::into_inner(base).unwrap();
    let mut imported = Vec::new();
    let ids = [made[2], made[0]].map(|id| store.import(&overlay, id, &mut imported));
    search.absorb(&worker, &imported);
    let fresh = |id: Id| Fingerprints::new().get_value(&store, id);
    assert_eq!(search.get_value(&store, ids[0]), computed[2]);
    assert_eq!(search.get_value(&store, ids[1]), computed[0]);
    assert_eq!(search.get_value(&store, unseen), unseen_value);
    for id in ids.into_iter().chain([one, unseen]) {
        assert_eq!(search.get_value(&store, id), fresh(id));
    }
}
