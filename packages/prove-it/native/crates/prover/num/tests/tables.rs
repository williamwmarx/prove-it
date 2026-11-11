//! prove-num against JavaScript: the tables `scripts/smt-foundation-tables.ts` recorded from
//! `bigint` and `rational.ts`.

use std::cmp::Ordering;

use prove_num::{Int, Rational, get_euclidean_div, get_euclidean_mod, get_gcd, get_lcm};

fn parse(text: &str) -> Int {
    text.parse()
        .unwrap_or_else(|_| panic!("not an integer: {text}"))
}

fn check(line: &str, expected: &str, actual: impl ToString) {
    assert_eq!(actual.to_string(), expected, "{line}");
}

#[test]
fn integers_compute_as_javascript_bigint() {
    let table = include_str!("tables/int.txt");
    for line in table.lines() {
        let fields: Vec<&str> = line.split(' ').collect();
        match fields[0] {
            "unary" => {
                let value = parse(fields[1]);
                check(line, fields[1], &value);
                check(line, fields[2], -&value);
                check(line, fields[3], value.abs());
                check(line, fields[4], format!("{:x}", value.to_f64().to_bits()));
                check(line, fields[5], value.bit_length().max(1));
            }
            "binary" => {
                let left = parse(fields[1]);
                let right = parse(fields[2]);
                check(line, fields[3], &left + &right);
                check(line, fields[4], &left - &right);
                check(line, fields[5], &left * &right);
                if !right.is_zero() {
                    let (quotient, remainder) = left.div_rem(&right);
                    check(line, fields[6], &quotient);
                    check(line, fields[7], &remainder);
                    check(line, fields[6], &left / &right);
                    check(line, fields[7], &left % &right);
                    check(line, fields[10], get_euclidean_div(&left, &right));
                    check(line, fields[11], get_euclidean_mod(&left, &right));
                }
                check(line, fields[8], &left & &right);
                check(line, fields[9], get_gcd(&left, &right));
                if !(left.is_zero() && right.is_zero()) {
                    check(line, fields[12], get_lcm(&left, &right));
                }
                let ordering = if left < right {
                    Ordering::Less
                } else if left > right {
                    Ordering::Greater
                } else {
                    Ordering::Equal
                };
                assert_eq!(left.cmp(&right), ordering, "{line}");
                assert_eq!((&left - &right).signum(), ordering as i32, "{line}");
            }
            "shift" => {
                let value = parse(fields[1]);
                let bits: u64 = fields[2].parse().unwrap();
                check(line, fields[3], &value << bits);
                check(line, fields[4], &value >> bits);
            }
            "pow" => {
                let value = parse(fields[1]);
                check(line, fields[3], value.pow(fields[2].parse().unwrap()));
            }
            kind => panic!("unknown kind {kind}"),
        }
    }
}

#[test]
fn rationals_compute_as_rational_ts() {
    let table = include_str!("tables/rational.txt");
    for line in table.lines() {
        let fields: Vec<&str> = line.split(' ').collect();
        let optional =
            |value: Option<Rational>| value.map_or("-".into(), |value| value.to_string());
        match fields[0] {
            "unary" => {
                let value = Rational::of(parse(fields[1]), parse(fields[2]));
                check(line, fields[3], &value);
                check(line, fields[4], -&value);
                check(line, fields[5], value.abs());
                check(line, fields[6], value.floor());
                check(line, fields[7], value.ceil());
                check(line, fields[8], value.is_big());
                check(line, fields[9], optional(value.root(2)));
                check(line, fields[10], optional(value.root(3)));
                check(line, fields[11], value.pow(3));
            }
            "binary" => {
                let left = Rational::of(parse(fields[1]), parse(fields[2]));
                let right = Rational::of(parse(fields[3]), parse(fields[4]));
                check(line, fields[5], &left + &right);
                check(line, fields[6], &left - &right);
                check(line, fields[7], &left * &right);
                if !right.is_zero() {
                    check(line, fields[8], &left / &right);
                }
                check(line, fields[9], left.compare(&right) as i32);
            }
            kind => panic!("unknown kind {kind}"),
        }
    }
}

#[test]
fn integers_parse_only_decimal_text() {
    for text in ["", "-", "+1", "1.5", "0x10", " 1", "1 ", "--1"] {
        assert!(text.parse::<Int>().is_err(), "{text:?}");
    }
    assert_eq!("-0".parse::<Int>().unwrap(), Int::zero());
    assert_eq!(
        "000000000000000000000000012".parse::<Int>().unwrap(),
        Int::from(12)
    );
}

#[test]
fn parity_and_trailing_zeros_read_the_magnitude() {
    for (text, is_odd, zeros) in [
        ("0", false, 0),
        ("-3", true, 0),
        ("-12", false, 2),
        ("18446744073709551616", false, 64),
        ("-18446744073709551617", true, 0),
        ("-36893488147419103232", false, 65),
    ] {
        let value: Int = text.parse().unwrap();
        assert_eq!(value.is_odd(), is_odd, "{text}");
        assert_eq!(value.trailing_zeros(), zeros, "{text}");
        assert_eq!(value.is_odd(), !(&value & &Int::one()).is_zero(), "{text}");
    }
}
