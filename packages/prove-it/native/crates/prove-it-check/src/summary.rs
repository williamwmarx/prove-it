//! What TLC reports at the end of a search, as `src/tlc/summary.ts` computes it: the estimates of a
//! fingerprint collision and the outdegree of the state graph.

/// TLC's optimistic estimate of a fingerprint collision, from AbstractChecker.
pub fn optimistic_probability(distinct: u64, generated: u64) -> f64 {
    distinct as f64 * ((generated as f64 - distinct as f64) / 2f64.powi(64))
}

/// TLC computes the estimate from the actual fingerprints only when the optimistic one is this high.
const ACTUAL_PROBABILITY_THRESHOLD: f64 = 1e-10;

fn with_decimal_point(text: &str) -> String {
    if text.contains('.') {
        text.to_string()
    } else {
        format!("{text}.0")
    }
}

/// Java's Double.toString, which prints a number below 1E-3 or from 1E7 up in scientific notation.
fn to_java_string(value: f64) -> String {
    let magnitude = value.abs();
    if (1e-3..1e7).contains(&magnitude) {
        return with_decimal_point(&format!("{value}"));
    }
    let exponential = format!("{value:e}");
    let (mantissa, exponent) = exponential.split_once('e').unwrap_or((&exponential, "0"));
    format!("{}E{exponent}", with_decimal_point(mantissa))
}

/// Adds one to the last digit and carries it over nines and the decimal point.
fn round_up(digits: &str) -> String {
    let Some(last) = digits.chars().last() else {
        return "1".to_string();
    };
    let front = &digits[..digits.len() - 1];
    match last {
        '.' => format!("{}.", round_up(front)),
        '9' => format!("{}0", round_up(front)),
        _ => format!("{front}{}", char::from(last as u8 + 1)),
    }
}

/// TLC's ProbabilityToString, which keeps two significant digits and drops a leading zero.
pub fn format_probability(value: f64) -> String {
    if value == 0.0 {
        return "0.0".to_string();
    }
    let text = to_java_string(value);
    let bytes = text.as_bytes();
    let is_digit = |index: usize| bytes.get(index).is_some_and(u8::is_ascii_digit);
    let mut next = 0;
    let mut digits = 0;
    let mut result = String::new();
    while bytes.get(next) == Some(&b'0') {
        next += 1;
    }
    while is_digit(next) {
        result.push(bytes[next] as char);
        next += 1;
        digits += 1;
    }
    if next == bytes.len() {
        return result;
    }
    if bytes[next] != b'.' {
        return text;
    }
    next += 1;
    if digits >= 2 {
        while is_digit(next) {
            next += 1;
        }
    } else {
        result.push('.');
        if digits == 0 {
            while bytes.get(next) == Some(&b'0') {
                result.push('0');
                next += 1;
            }
        }
        while is_digit(next) && digits < 2 {
            result.push(bytes[next] as char);
            next += 1;
            digits += 1;
        }
        if is_digit(next) && bytes[next] >= b'5' {
            result = round_up(&result);
        }
        while is_digit(next) {
            next += 1;
        }
    }
    if next >= bytes.len() {
        return result;
    }
    if bytes[next] == b'E' {
        return format!("{result}{}", &text[next..]);
    }
    text
}

/// 1 divided by the distance, rounded half up to two significant digits like Java's BigDecimal.
pub fn actual_probability(distance: u64) -> f64 {
    let distance = u128::from(distance);
    let mut exponent = 0;
    while 10u128.pow(exponent + 1) < distance * 10 {
        exponent += 1;
    }
    let scale = 10u128.pow(exponent + 1);
    let quotient = scale / distance + u128::from((scale % distance) * 2 >= distance);
    format!("{quotient}e-{}", exponent + 1)
        .parse()
        .expect("a number")
}

/// TLC splits its fingerprints into two sets by their top bit and reports the smallest distance
/// between two fingerprints in the same set, when the optimistic estimate is high enough. The
/// fingerprints are sorted on threads, each taking those whose top bits, in the order of the signed
/// fingerprints, are its own, so that their runs follow one another in the order.
pub fn fingerprint_distance(
    distinct: u64,
    generated: u64,
    fingerprints: &[u64],
    threads: usize,
) -> Option<u64> {
    if optimistic_probability(distinct, generated) < ACTUAL_PROBABILITY_THRESHOLD {
        return None;
    }
    let ranges = threads.next_power_of_two();
    let shift = u64::BITS - ranges.trailing_zeros();
    let sorted: Vec<Vec<i64>> = std::thread::scope(|scope| {
        let sorting: Vec<_> = (0..ranges)
            .map(|range| {
                scope.spawn(move || {
                    let mut sorted: Vec<i64> = fingerprints
                        .iter()
                        .filter(|&&fingerprint| {
                            (fingerprint ^ 1 << 63).checked_shr(shift).unwrap_or(0) as usize
                                == range
                        })
                        .map(|&fingerprint| fingerprint as i64)
                        .collect();
                    sorted.sort_unstable();
                    sorted
                })
            })
            .collect();
        sorting
            .into_iter()
            .map(|thread| {
                thread
                    .join()
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            })
            .collect()
    });
    let sorted = sorted.iter().flatten();
    Some(
        sorted
            .clone()
            .zip(sorted.skip(1))
            .filter(|(low, high)| (**low < 0) == (**high < 0))
            .map(|(low, high)| (high - low) as u64)
            .fold(i64::MAX as u64, u64::min),
    )
}

/// TLC counts how many new states each expanded state yields in buckets, the last of which holds
/// every count from its index up.
pub fn out_degree_summary(buckets: &[u64]) -> Option<String> {
    let observations: u64 = buckets.iter().sum();
    if observations == 0 {
        return None;
    }
    let degrees: Vec<usize> = (0..buckets.len())
        .filter(|&degree| buckets[degree] > 0)
        .collect();
    let total: u64 = buckets
        .iter()
        .enumerate()
        .map(|(degree, count)| count * degree as u64)
        .sum();
    let position = (observations as f64 * 0.95).floor() as u64;
    let mut cumulative = 0;
    let percentile = degrees.iter().find(|&&degree| {
        cumulative += buckets[degree];
        cumulative > position
    })?;
    Some(format!(
        "The average outdegree of the complete state graph is {} (minimum is {}, the maximum {} and the 95th percentile is {percentile}).",
        (total as f64 / observations as f64).round(),
        degrees[0],
        degrees[degrees.len() - 1],
    ))
}

/// A count as JavaScript's `toLocaleString("en-US")` writes it, with a comma between thousands.
pub fn format_count(count: u64) -> String {
    let digits = count.to_string();
    let mut result = String::new();
    for (index, digit) in digits.chars().enumerate() {
        if index > 0 && (digits.len() - index).is_multiple_of(3) {
            result.push(',');
        }
        result.push(digit);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats_probabilities_as_tlc() {
        assert_eq!(format_probability(0.0), "0.0");
        assert_eq!(
            format_probability(optimistic_probability(34, 94)),
            "1.1E-16"
        );
        assert_eq!(format_probability(1.0 / 3.0), ".33");
        assert_eq!(format_probability(0.0996), ".100");
        assert_eq!(format_probability(0.00996), ".0100");
        assert_eq!(format_probability(12.345), "12");
        assert_eq!(format_probability(2.5e-7), "2.5E-7");
        assert_eq!(format_probability(1.96e-7), "2.0E-7");
        assert_eq!(format_probability(3e20), "3.0E20");
    }

    #[test]
    fn rounds_the_actual_probability_half_up() {
        assert_eq!(actual_probability(3), 0.33);
        assert_eq!(actual_probability(8), 0.13);
        assert_eq!(actual_probability(1 << 40), 9.1e-13);
    }

    #[test]
    fn measures_the_distance_within_each_half() {
        let fingerprints = [10, 30, 25, 1 << 63, (1 << 63) + 2];
        for threads in [1, 3, 4] {
            assert_eq!(
                fingerprint_distance(5, 1 << 40, &fingerprints, threads),
                Some(2)
            );
            assert_eq!(fingerprint_distance(5, 10, &fingerprints, threads), None);
            assert_eq!(
                fingerprint_distance(1, 1 << 40, &[7], threads),
                Some(i64::MAX as u64)
            );
        }
        // Next to one another in the order, sorted by different threads.
        let fingerprints = [u64::MAX - 1, (1 << 62) - 1, 1 << 62, 0, 5];
        for threads in [1, 2, 4, 16] {
            assert_eq!(
                fingerprint_distance(5, 1 << 40, &fingerprints, threads),
                Some(1)
            );
        }
    }

    #[test]
    fn summarises_the_outdegree() {
        let mut buckets = [0; 32];
        buckets[0] = 10;
        buckets[1] = 12;
        buckets[4] = 2;
        buckets[6] = 1;
        assert_eq!(
            out_degree_summary(&buckets).as_deref(),
            Some(
                "The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 6 and the 95th percentile is 4)."
            )
        );
        assert_eq!(out_degree_summary(&[0; 32]), None);
    }

    #[test]
    fn groups_thousands() {
        assert_eq!(format_count(0), "0");
        assert_eq!(format_count(999), "999");
        assert_eq!(format_count(104_444), "104,444");
        assert_eq!(format_count(1_234_567), "1,234,567");
    }
}
