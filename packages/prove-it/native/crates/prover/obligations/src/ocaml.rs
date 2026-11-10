//! The parts of OCaml's standard library whose exact order steers what tlapm prints. A port of
//! `src/prover/ocaml.ts`.

/// `OcamlValue`: an int, a string, or a list of values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OcamlValue {
    Int(i64),
    Text(String),
    List(Vec<OcamlValue>),
}

// String.compare: byte by byte, on the UTF-8 bytes. Code units order the same way for the ASCII
// names tlapm compares.
pub fn compare_strings(left: &str, right: &str) -> i64 {
    match left.encode_utf16().cmp(right.encode_utf16()) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

// Stdlib.compare on ints, strings, and lists, where a list is smaller than any longer list it
// starts.
pub fn compare_values(left: &OcamlValue, right: &OcamlValue) -> i64 {
    match (left, right) {
        (OcamlValue::Int(left), OcamlValue::Int(right)) => left.saturating_sub(*right),
        (OcamlValue::Text(left), OcamlValue::Text(right)) => compare_strings(left, right),
        (OcamlValue::List(left), OcamlValue::List(right)) => {
            let index = left.iter().enumerate().position(|(position, item)| {
                position >= right.len() || compare_values(item, &right[position]) != 0
            });
            match index {
                None => left.len() as i64 - right.len() as i64,
                Some(index) if index >= right.len() => 1,
                Some(index) => compare_values(&left[index], &right[index]),
            }
        }
        _ => 0,
    }
}

// Expected values from running the TypeScript.
#[cfg(test)]
mod tests {
    use super::*;

    fn int(value: i64) -> OcamlValue {
        OcamlValue::Int(value)
    }

    fn text(value: &str) -> OcamlValue {
        OcamlValue::Text(value.to_string())
    }

    fn list(values: Vec<OcamlValue>) -> OcamlValue {
        OcamlValue::List(values)
    }

    #[test]
    fn compares_strings() {
        assert_eq!(compare_strings("a", "b"), -1);
        assert_eq!(compare_strings("b", "a"), 1);
        assert_eq!(compare_strings("ab", "ab"), 0);
        assert_eq!(compare_strings("ab", "a"), 1);
        assert_eq!(compare_strings("", "a"), -1);
        assert_eq!(compare_strings("Z", "a"), -1);
        assert_eq!(compare_strings("\u{ff5e}", "\u{1f600}"), 1);
    }

    #[test]
    fn compares_values() {
        assert_eq!(compare_values(&int(3), &int(7)), -4);
        assert_eq!(compare_values(&int(7), &int(3)), 4);
        assert_eq!(compare_values(&text("x"), &text("y")), -1);
        assert_eq!(compare_values(&int(1), &text("y")), 0);
        assert_eq!(compare_values(&list(vec![]), &int(1)), 0);
        assert_eq!(
            compare_values(&list(vec![int(1)]), &list(vec![int(1), int(2)])),
            -1
        );
        assert_eq!(
            compare_values(&list(vec![int(1), int(2)]), &list(vec![int(1)])),
            1
        );
        assert_eq!(
            compare_values(&list(vec![int(1), int(2)]), &list(vec![int(1), int(2)])),
            0
        );
        assert_eq!(
            compare_values(
                &list(vec![int(2), list(vec![text("a"), text("c")])]),
                &list(vec![int(2), list(vec![text("a"), text("b"), text("z")])])
            ),
            1
        );
        assert_eq!(
            compare_values(&list(vec![int(5)]), &list(vec![int(9), int(0)])),
            -4
        );
        assert_eq!(
            compare_values(&list(vec![text("b")]), &list(vec![text("a"), int(3)])),
            1
        );
    }
}
