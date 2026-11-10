//! The local time zone, as the TypeScript CLI's JavaScript runtime finds it: `TZ`, or else
//! `/etc/localtime`, read as a TZif file (RFC 8536) with the POSIX TZ rule in its footer for the
//! times after its last transition.

/// A POSIX TZ rule, such as `EST5EDT,M3.2.0,M11.1.0`: the standard offset east of UTC, and the
/// daylight offset with when it starts and ends, in seconds.
#[derive(Debug, PartialEq)]
pub struct Rule {
    standard: i64,
    daylight: Option<(i64, Transition, Transition)>,
}

/// When daylight time starts or ends: a day of the year and the local time of day.
#[derive(Debug, PartialEq, Clone, Copy)]
struct Transition {
    day: Day,
    time: i64,
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum Day {
    /// `Jn`: day 1 to 365, February 29th never counted.
    Julian(i64),
    /// `n`: day 0 to 365, February 29th counted in leap years.
    Zero(i64),
    /// `Mm.w.d`: weekday d (0 is Sunday) of week w (5 is the last) of month m.
    Month(i64, i64, i64),
}

/// A zone: its transitions as (UTC second, offset), and the rule after them.
#[derive(Debug, PartialEq)]
pub struct Zone {
    transitions: Vec<(i64, i64)>,
    /// The offset before the first transition.
    initial: i64,
    rule: Option<Rule>,
}

impl Zone {
    pub const UTC: Self = Self {
        transitions: Vec::new(),
        initial: 0,
        rule: None,
    };

    /// The zone of this process.
    pub fn local() -> Self {
        match std::env::var("TZ") {
            Ok(name) => Self::named(name.strip_prefix(':').unwrap_or(&name)),
            Err(_) => std::fs::read("/etc/localtime")
                .ok()
                .and_then(|bytes| read_tzif(&bytes))
                .unwrap_or(Self::UTC),
        }
    }

    fn named(name: &str) -> Self {
        if name.is_empty() {
            return Self::UTC;
        }
        let path = if name.starts_with('/') {
            name.to_string()
        } else {
            format!("/usr/share/zoneinfo/{name}")
        };
        let is_safe = !name.split('/').any(|part| part == "..");
        is_safe
            .then(|| std::fs::read(path).ok())
            .flatten()
            .and_then(|bytes| read_tzif(&bytes))
            .unwrap_or(Self::UTC)
    }

    pub fn from_rule(rule: Rule) -> Self {
        Self {
            transitions: Vec::new(),
            initial: rule.standard,
            rule: Some(rule),
        }
    }

    /// The offset east of UTC, in seconds, at a UTC second.
    pub fn offset(&self, utc: i64) -> i64 {
        let after = self.transitions.partition_point(|&(at, _)| at <= utc);
        match (after, &self.rule) {
            (count, Some(rule)) if count == self.transitions.len() => rule.offset(utc),
            (0, _) => self.initial,
            (count, _) => self.transitions[count - 1].1,
        }
    }
}

fn be_u32(bytes: &[u8], at: usize) -> Option<usize> {
    Some(u32::from_be_bytes(bytes.get(at..at + 4)?.try_into().ok()?) as usize)
}

fn be_i64(bytes: &[u8], at: usize) -> Option<i64> {
    Some(i64::from_be_bytes(bytes.get(at..at + 8)?.try_into().ok()?))
}

/// Reads a TZif file: its version 2 data with 64-bit times when it has them, and its footer.
pub fn read_tzif(bytes: &[u8]) -> Option<Zone> {
    let header = |at: usize| -> Option<[usize; 6]> {
        if bytes.get(at..at + 4)? != b"TZif" {
            return None;
        }
        let mut counts = [0; 6];
        for (index, count) in counts.iter_mut().enumerate() {
            *count = be_u32(bytes, at + 20 + index * 4)?;
        }
        Some(counts)
    };
    // isutcnt, isstdcnt, leapcnt, timecnt, typecnt, charcnt.
    let [utc, std, leap, times, types, chars] = header(0)?;
    let version = *bytes.get(4)?;
    let v1_size = times * 5 + types * 6 + chars + leap * 8 + std + utc;
    let (start, width) = if version >= b'2' {
        (44 + v1_size, 8)
    } else {
        (0, 4)
    };
    let [utc, std, leap, times, types, chars] = header(start)?;
    let data = start + 44;
    let indices = data + times * width;
    let records = indices + times;
    let offset_of = |index: usize| -> Option<i64> {
        let at = records + index * 6;
        Some(i64::from(i32::from_be_bytes(
            bytes.get(at..at + 4)?.try_into().ok()?,
        )))
    };
    let mut transitions = Vec::with_capacity(times);
    for index in 0..times {
        let at = data + index * width;
        let time = if width == 8 {
            be_i64(bytes, at)?
        } else {
            i64::from(i32::from_be_bytes(bytes.get(at..at + 4)?.try_into().ok()?))
        };
        transitions.push((time, offset_of(usize::from(*bytes.get(indices + index)?))?));
    }
    let end = records + types * 6 + chars + leap * (width + 4) + std + utc;
    let rule = (width == 8)
        .then(|| {
            let footer = bytes.get(end..)?.strip_prefix(b"\n")?;
            let text = std::str::from_utf8(footer.split(|&byte| byte == b'\n').next()?).ok()?;
            parse_rule(text)
        })
        .flatten();
    Some(Zone {
        transitions,
        initial: offset_of(0)?,
        rule,
    })
}

/// Parses a POSIX TZ rule; `None` for a text that isn't one.
pub fn parse_rule(text: &str) -> Option<Rule> {
    let mut rest = text;
    skip_name(&mut rest)?;
    let standard = -parse_time(&mut rest)?;
    if rest.is_empty() {
        return Some(Rule {
            standard,
            daylight: None,
        });
    }
    skip_name(&mut rest)?;
    let daylight = if rest.starts_with(',') || rest.is_empty() {
        standard + 3600
    } else {
        -parse_time(&mut rest)?
    };
    // Without dates, POSIX leaves them to the implementation; tzcode uses the US rules.
    let (start, end) = match rest.strip_prefix(',') {
        Some(dates) => {
            rest = dates;
            let start = parse_transition(&mut rest)?;
            rest = rest.strip_prefix(',')?;
            (start, parse_transition(&mut rest)?)
        }
        None => (
            Transition {
                day: Day::Month(3, 2, 0),
                time: 7200,
            },
            Transition {
                day: Day::Month(11, 1, 0),
                time: 7200,
            },
        ),
    };
    rest.is_empty().then_some(Rule {
        standard,
        daylight: Some((daylight, start, end)),
    })
}

fn skip_name(rest: &mut &str) -> Option<()> {
    let length = if let Some(quoted) = rest.strip_prefix('<') {
        quoted.find('>')? + 2
    } else {
        rest.find(|character: char| !character.is_ascii_alphabetic())
            .unwrap_or(rest.len())
    };
    (length >= 3).then(|| *rest = &rest[length..])
}

fn parse_number(rest: &mut &str) -> Option<i64> {
    let end = rest
        .find(|character: char| !character.is_ascii_digit())
        .unwrap_or(rest.len());
    let number = rest[..end].parse().ok()?;
    *rest = &rest[end..];
    Some(number)
}

/// `[+-]hh[:mm[:ss]]`, in seconds.
fn parse_time(rest: &mut &str) -> Option<i64> {
    let sign = match rest.chars().next() {
        Some('-') => -1,
        _ => 1,
    };
    *rest = rest.trim_start_matches(['+', '-']);
    let mut seconds = parse_number(rest)? * 3600;
    for scale in [60, 1] {
        let Some(after) = rest.strip_prefix(':') else {
            break;
        };
        *rest = after;
        seconds += parse_number(rest)? * scale;
    }
    Some(sign * seconds)
}

fn parse_transition(rest: &mut &str) -> Option<Transition> {
    let day = if let Some(after) = rest.strip_prefix('J') {
        *rest = after;
        Day::Julian(parse_number(rest)?)
    } else if let Some(after) = rest.strip_prefix('M') {
        *rest = after;
        let month = parse_number(rest)?;
        *rest = rest.strip_prefix('.')?;
        let week = parse_number(rest)?;
        *rest = rest.strip_prefix('.')?;
        Day::Month(month, week, parse_number(rest)?)
    } else {
        Day::Zero(parse_number(rest)?)
    };
    let time = match rest.strip_prefix('/') {
        Some(after) => {
            *rest = after;
            parse_time(rest)?
        }
        None => 7200,
    };
    Some(Transition { day, time })
}

fn is_leap(year: i64) -> bool {
    year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
}

/// The day counted from 1970-01-01 of a proleptic Gregorian date (Howard Hinnant's algorithm).
pub fn days_from_civil(year: i64, month: i64, day: i64) -> i64 {
    let year = if month <= 2 { year - 1 } else { year };
    let era = year.div_euclid(400);
    let year_of_era = year.rem_euclid(400);
    let day_of_year = (153 * (if month > 2 { month - 3 } else { month + 9 }) + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    era * 146_097 + day_of_era - 719_468
}

impl Transition {
    /// The UTC second the transition happens in a year, its local time in the given offset.
    fn at(self, year: i64, offset: i64) -> i64 {
        let january = days_from_civil(year, 1, 1);
        let day = match self.day {
            Day::Julian(day) => january + day - 1 + i64::from(is_leap(year) && day >= 60),
            Day::Zero(day) => january + day,
            Day::Month(month, week, weekday) => {
                let first = days_from_civil(year, month, 1);
                // 1970-01-01 was a Thursday, weekday 4.
                let first_weekday = (first + 4).rem_euclid(7);
                let next_month = if month == 12 {
                    days_from_civil(year + 1, 1, 1)
                } else {
                    days_from_civil(year, month + 1, 1)
                };
                let mut day = first + (weekday - first_weekday).rem_euclid(7) + (week - 1) * 7;
                while day >= next_month {
                    day -= 7;
                }
                day
            }
        };
        day * 86_400 + self.time - offset
    }
}

impl Rule {
    fn offset(&self, utc: i64) -> i64 {
        let Some((daylight, start, end)) = self.daylight else {
            return self.standard;
        };
        let year = crate::time::civil_from_days((utc + self.standard).div_euclid(86_400)).0;
        let starts = start.at(year, self.standard);
        let ends = end.at(year, daylight);
        let is_daylight = if starts < ends {
            starts <= utc && utc < ends
        } else {
            utc < ends || starts <= utc
        };
        if is_daylight { daylight } else { self.standard }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn utc(year: i64, month: i64, day: i64, hour: i64) -> i64 {
        days_from_civil(year, month, day) * 86_400 + hour * 3600
    }

    #[test]
    fn follows_northern_and_southern_rules() {
        let new_york = parse_rule("EST5EDT,M3.2.0,M11.1.0").expect("a rule");
        assert_eq!(new_york.offset(utc(2026, 1, 15, 12)), -5 * 3600);
        assert_eq!(new_york.offset(utc(2026, 7, 15, 12)), -4 * 3600);
        // 2026-03-08 02:00 EST is 07:00 UTC; 2026-11-01 02:00 EDT is 06:00 UTC.
        assert_eq!(new_york.offset(utc(2026, 3, 8, 7) - 1), -5 * 3600);
        assert_eq!(new_york.offset(utc(2026, 3, 8, 7)), -4 * 3600);
        assert_eq!(new_york.offset(utc(2026, 11, 1, 6) - 1), -4 * 3600);
        assert_eq!(new_york.offset(utc(2026, 11, 1, 6)), -5 * 3600);
        let sydney = parse_rule("AEST-10AEDT,M10.1.0,M4.1.0/3").expect("a rule");
        assert_eq!(sydney.offset(utc(2026, 1, 15, 0)), 11 * 3600);
        assert_eq!(sydney.offset(utc(2026, 6, 15, 0)), 10 * 3600);
        assert_eq!(sydney.offset(utc(2026, 12, 31, 20)), 11 * 3600);
    }

    #[test]
    fn reads_fixed_and_quoted_offsets() {
        assert_eq!(parse_rule("UTC0").map(|rule| rule.offset(0)), Some(0));
        assert_eq!(
            parse_rule("<+0530>-5:30").map(|rule| rule.offset(0)),
            Some(5 * 3600 + 1800)
        );
        assert_eq!(parse_rule("America/New_York"), None);
        assert_eq!(parse_rule("X5"), None);
    }

    #[test]
    fn reads_a_tzif_file_and_its_footer() {
        // A version 2 file with one transition, in 1990 to +1h, and a footer rule after it.
        let mut bytes = b"TZif2".to_vec();
        bytes.resize(44, 0);
        bytes.extend(b"TZif2");
        bytes.resize(44 + 20, 0);
        for count in [0u32, 0, 0, 1, 2, 8] {
            bytes.extend(count.to_be_bytes());
        }
        bytes.extend(631_152_000i64.to_be_bytes());
        bytes.push(1);
        bytes.extend(0i32.to_be_bytes());
        bytes.extend([0, 0]);
        bytes.extend(3600i32.to_be_bytes());
        bytes.extend([0, 4]);
        bytes.extend(b"LMT\0ONE\0");
        bytes.extend(b"\nCET-1CEST,M3.5.0,M10.5.0/3\n");
        let zone = read_tzif(&bytes).expect("a zone");
        assert_eq!(zone.offset(0), 0);
        assert_eq!(zone.offset(631_152_000 - 1), 0);
        assert_eq!(zone.offset(utc(2026, 1, 1, 0)), 3600);
        assert_eq!(zone.offset(utc(2026, 7, 1, 0)), 7200);
    }
}
