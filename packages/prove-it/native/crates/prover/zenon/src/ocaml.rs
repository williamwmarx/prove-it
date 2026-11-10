// Ported from OCaml: LGPL-2.1 with OCaml's linking exception, not MIT (THIRD_PARTY_NOTICES.md).
//! The parts of OCaml's standard library whose exact behavior steers Zenon's search.
//!
//! `Hashtbl.hash` on the values Zenon hashes: strings, and the (int, string list) pairs that Expr
//! hashes. Zenon orders record fields by these hashes. Ints are 63-bit in OCaml, held here in an
//! `i64` that [`combine`] keeps within 63 bits.

use std::cmp::Ordering;

/// A block's header with its color bits cleared: two fields and tag 0, for a pair or a list cell.
const PAIR_HEADER: u32 = 0x800;

const MEANINGFUL_LIMIT: u32 = 10;

fn mix(hash: u32, data: u32) -> u32 {
    let scrambled = data
        .wrapping_mul(0xcc9e_2d51)
        .rotate_left(15)
        .wrapping_mul(0x1b87_3593);
    (hash ^ scrambled)
        .rotate_left(13)
        .wrapping_mul(5)
        .wrapping_add(0xe654_6b64)
}

fn final_mix(hash: u32) -> u32 {
    let first = (hash ^ (hash >> 16)).wrapping_mul(0x85eb_ca6b);
    let second = (first ^ (first >> 13)).wrapping_mul(0xc2b2_ae35);
    (second ^ (second >> 16)) & 0x3fff_ffff
}

/// caml_hash_mix_string: the UTF-8 bytes as little-endian words, the last one partial, then the
/// length.
fn mix_string(hash: u32, value: &str) -> u32 {
    let bytes = value.as_bytes();
    let mixed = bytes.chunks(4).fold(hash, |mixed, chunk| {
        let word = chunk
            .iter()
            .enumerate()
            .fold(0u32, |word, (position, byte)| {
                word | (u32::from(*byte) << (8 * position))
            });
        mix(mixed, word)
    });
    mixed ^ bytes.len() as u32
}

/// caml_hash_mix_intnat on the tagged value 2n + 1 of the int n.
fn mix_int(hash: u32, value: i64) -> u32 {
    let tagged = value.wrapping_mul(2).wrapping_add(1);
    mix(hash, ((tagged >> 32) ^ (tagged >> 63) ^ tagged) as u32)
}

/// `Hashtbl.hash` on a string.
pub fn hash_string(value: &str) -> u32 {
    final_mix(mix_string(0, value))
}

/// `Hashtbl.hash` on an (int, string list) pair.
pub fn hash_int_and_strings<S: AsRef<str>>(value: i64, strings: &[S]) -> u32 {
    let mut hash = mix_int(mix(0, PAIR_HEADER), value);
    let mut meaningful = MEANINGFUL_LIMIT - 1;
    for string in strings {
        if meaningful == 0 {
            return final_mix(hash);
        }
        hash = mix_string(mix(hash, PAIR_HEADER), string.as_ref());
        meaningful -= 1;
    }
    final_mix(if meaningful == 0 {
        hash
    } else {
        mix_int(hash, 0)
    })
}

/// Wraps an integer to OCaml's 63 bits.
fn wrap(value: i64) -> i64 {
    (value << 1) >> 1
}

/// Expr's combine: x + y * 131 + 1, wrapping like OCaml's 63-bit ints.
pub fn combine(left: i64, right: i64) -> i64 {
    wrap(left.wrapping_add(right.wrapping_mul(131)).wrapping_add(1))
}

/// The merges of OCaml's List.stable_sort. Each returns its result reversed, as OCaml's rev_merge
/// and rev_merge_rev do.
fn merge_reversed<T>(
    first: Vec<T>,
    second: Vec<T>,
    takes_first: impl Fn(&T, &T) -> bool,
) -> Vec<T> {
    let mut merged = Vec::with_capacity(first.len() + second.len());
    let mut first = first.into_iter().peekable();
    let mut second = second.into_iter().peekable();
    while let (Some(left), Some(right)) = (first.peek(), second.peek()) {
        let item = if takes_first(left, right) {
            first.next()
        } else {
            second.next()
        };
        merged.extend(item);
    }
    merged.extend(first);
    merged.extend(second);
    merged.reverse();
    merged
}

/// OCaml's List.sort, step for step, so that a comparison that isn't a total order still gives
/// Zenon's result.
pub fn stable_sort<T: Clone>(items: &[T], compare: &impl Fn(&T, &T) -> Ordering) -> Vec<T> {
    fn sort_run<T: Clone>(
        items: &[T],
        compare: &impl Fn(&T, &T) -> Ordering,
        is_reversed: bool,
    ) -> Vec<T> {
        let is_before = |left: &T, right: &T| {
            if is_reversed {
                compare(left, right) == Ordering::Greater
            } else {
                compare(left, right) != Ordering::Greater
            }
        };
        match items {
            [first, second] => {
                if is_before(first, second) {
                    vec![first.clone(), second.clone()]
                } else {
                    vec![second.clone(), first.clone()]
                }
            }
            [first, second, third] => {
                let order = if is_before(first, second) {
                    if is_before(second, third) {
                        [first, second, third]
                    } else if is_before(first, third) {
                        [first, third, second]
                    } else {
                        [third, first, second]
                    }
                } else if is_before(first, third) {
                    [second, first, third]
                } else if is_before(second, third) {
                    [second, third, first]
                } else {
                    [third, second, first]
                };
                order.into_iter().cloned().collect()
            }
            _ => {
                let first_count = items.len() >> 1;
                let left = sort_run(&items[..first_count], compare, !is_reversed);
                let right = sort_run(&items[first_count..], compare, !is_reversed);
                if is_reversed {
                    merge_reversed(left, right, |first, second| {
                        compare(first, second) != Ordering::Greater
                    })
                } else {
                    merge_reversed(left, right, |first, second| {
                        compare(first, second) == Ordering::Greater
                    })
                }
            }
        }
    }
    if items.len() < 2 {
        items.to_vec()
    } else {
        sort_run(items, compare, false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hashes_strings_as_ocaml_does() {
        // Hashtbl.hash "" and Hashtbl.hash "abc" in OCaml 4.14.
        assert_eq!(hash_string(""), 0);
        assert_eq!(hash_string("abc"), 767_105_082);
    }

    #[test]
    fn hashes_pairs_as_the_typescript_does() {
        assert_eq!(hash_int_and_strings::<&str>(0xb063cd7, &[]), 530_869_405);
        let strings = ["a", "bb", "ccc", "dddd", "eeeee"];
        assert_eq!(
            hash_int_and_strings(-5000 * (1 << 32) + 123_456, &strings),
            37_385_419
        );
        assert_eq!(hash_string("zenon_Vfoo_bar"), 416_704_623);
    }

    #[test]
    fn combine_wraps_at_63_bits() {
        assert_eq!(combine(0, 1), 132);
        assert_eq!(combine(i64::MAX >> 1, 0), -(1 << 62));
    }

    #[test]
    fn sorts_like_list_sort() {
        let items = [5, 3, 9, 1, 3, 7, 2, 8];
        assert_eq!(
            stable_sort(&items, &|a: &i32, b: &i32| a.cmp(b)),
            [1, 2, 3, 3, 5, 7, 8, 9]
        );
    }
}
