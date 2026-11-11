//! `sort.ts`. `Array.prototype.sort` copies its array before sorting, which makes most of the
//! garbage of short clauses and disjunctions. Insertion sort is stable like it and sorts a short
//! array in place, so both give the same order.

const MAX_INSERTION_SORT_LENGTH: usize = 16;

pub fn sort_by_key(values: &mut [u32], mut get_key: impl FnMut(u32) -> u32) {
    if values.len() > MAX_INSERTION_SORT_LENGTH {
        values.sort_by_key(|value| get_key(*value));
        return;
    }
    for index in 1..values.len() {
        let value = values[index];
        let key = get_key(value);
        let mut position = index;
        while position > 0 && get_key(values[position - 1]) > key {
            values[position] = values[position - 1];
            position -= 1;
        }
        values[position] = value;
    }
}

/// std::sort of literals: `sort_by_key` with the number as its key, which a call site of its own
/// keeps cheap.
pub fn sort_numbers(values: &mut [u32]) {
    if values.len() > MAX_INSERTION_SORT_LENGTH {
        values.sort();
        return;
    }
    for index in 1..values.len() {
        let value = values[index];
        let mut position = index;
        while position > 0 && values[position - 1] > value {
            values[position] = values[position - 1];
            position -= 1;
        }
        values[position] = value;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The values are distinct and their key is the value divided by 10, so a stable sort keeps the
    // values of one key in the order they came.
    fn check_stable(values: &[u32]) {
        let mut sorted = values.to_vec();
        sort_by_key(&mut sorted, |value| value / 10);
        for pair in sorted.windows(2) {
            assert!(pair[0] / 10 <= pair[1] / 10);
            if pair[0] / 10 == pair[1] / 10 {
                let first = values.iter().position(|value| *value == pair[0]);
                let second = values.iter().position(|value| *value == pair[1]);
                assert!(first < second);
            }
        }
    }

    #[test]
    fn sorts_a_short_array_stably_by_insertion() {
        let values = [31, 12, 39, 10, 35, 17, 3, 30, 15, 1];
        let mut sorted = values;
        sort_by_key(&mut sorted, |value| value / 10);
        assert_eq!(sorted, [3, 1, 12, 10, 17, 15, 31, 39, 35, 30]);
        check_stable(&values);
        // The longest array insertion sort takes.
        let longest = [
            95, 14, 52, 13, 91, 58, 17, 50, 12, 99, 56, 11, 93, 55, 10, 92,
        ];
        let mut sorted = longest;
        sort_by_key(&mut sorted, |value| value / 10);
        assert_eq!(
            sorted,
            [
                14, 13, 17, 12, 11, 10, 52, 58, 50, 56, 55, 95, 91, 99, 93, 92
            ]
        );
        check_stable(&longest);
    }

    #[test]
    fn sorts_a_long_array_stably() {
        let mut sorted = vec![
            41, 7, 45, 3, 49, 1, 40, 8, 44, 2, 48, 6, 42, 0, 46, 5, 43, 9,
        ];
        sort_by_key(&mut sorted, |value| value / 10);
        assert_eq!(
            sorted,
            [
                7, 3, 1, 8, 2, 6, 0, 5, 9, 41, 45, 49, 40, 44, 48, 42, 46, 43
            ]
        );
        let values: Vec<u32> = (0..40).map(|index| (index * 37) % 100).collect();
        check_stable(&values);
    }

    #[test]
    fn sorts_numbers() {
        let mut short = vec![5, 3, 9, 3, 0];
        sort_numbers(&mut short);
        assert_eq!(short, [0, 3, 3, 5, 9]);
        let mut long: Vec<u32> = (0..30).map(|index| (index * 7) % 30).collect();
        sort_numbers(&mut long);
        assert_eq!(long, (0..30).collect::<Vec<u32>>());
    }
}
