//! TLC's dates and durations, as `src/tlc/messages.ts` formats them.

use std::time::{SystemTime, UNIX_EPOCH};

use crate::zone::Zone;

/// TLC's convertRuntimeToHumanReadable: a duration in its two largest units.
pub fn format_duration(milliseconds: u128) -> String {
    let seconds = milliseconds / 1000 % 60;
    let minutes = milliseconds / 60_000 % 60;
    let hours = milliseconds / 3_600_000;
    if milliseconds > 86_400_000 {
        format!("{}d {:02}h", hours / 24, hours % 24)
    } else if milliseconds > 3_600_000 {
        format!("{:02}h {minutes:02}min", hours % 24)
    } else if milliseconds > 60_000 {
        format!("{minutes:02}min {seconds:02}s")
    } else {
        format!("{seconds:02}s")
    }
}

/// TLC's SimpleDateFormat("yyyy-MM-dd HH:mm:ss"), in the zone.
pub fn format_date(time: SystemTime, zone: &Zone) -> String {
    let utc = time
        .duration_since(UNIX_EPOCH)
        .map_or(0, |duration| duration.as_secs() as i64);
    let seconds = utc + zone.offset(utc);
    let (days, second) = (seconds.div_euclid(86_400), seconds.rem_euclid(86_400));
    let (year, month, day) = civil_from_days(days);
    format!(
        "{year:04}-{month:02}-{day:02} {:02}:{:02}:{:02}",
        second / 3600,
        second / 60 % 60,
        second % 60
    )
}

/// `java.util.Date.toString` in UTC: `EEE MMM dd HH:mm:ss zzz yyyy`.
pub fn format_java_date(time: SystemTime) -> String {
    const WEEKDAYS: [&str; 7] = ["Thu", "Fri", "Sat", "Sun", "Mon", "Tue", "Wed"];
    const MONTHS: [&str; 12] = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    ];
    let seconds = time
        .duration_since(UNIX_EPOCH)
        .map_or(0, |duration| duration.as_secs() as i64);
    let (days, second) = (seconds.div_euclid(86_400), seconds.rem_euclid(86_400));
    let (year, month, day) = civil_from_days(days);
    format!(
        "{} {} {day:02} {:02}:{:02}:{:02} UTC {year}",
        WEEKDAYS[days.rem_euclid(7) as usize],
        MONTHS[(month - 1) as usize],
        second / 3600,
        second / 60 % 60,
        second % 60
    )
}

/// The proleptic Gregorian date of a day counted from 1970-01-01 (Howard Hinnant's algorithm).
pub fn civil_from_days(days: i64) -> (i64, i64, i64) {
    let shifted = days + 719_468;
    let era = shifted.div_euclid(146_097);
    let day_of_era = shifted.rem_euclid(146_097);
    let year_of_era =
        (day_of_era - day_of_era / 1460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_index = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_index + 2) / 5 + 1;
    let month = if month_index < 10 {
        month_index + 3
    } else {
        month_index - 9
    };
    let year = year_of_era + era * 400 + i64::from(month <= 2);
    (year, month, day)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zone::parse_rule;
    use std::time::Duration;

    #[test]
    fn formats_a_date_as_java_in_utc() {
        // The date TLC wrote at the end of a trace exploration spec.
        let time = UNIX_EPOCH + Duration::from_secs(1_794_362_816);
        assert_eq!(format_java_date(time), "Wed Nov 11 02:06:56 UTC 2026");
    }

    #[test]
    fn formats_durations_in_two_units() {
        assert_eq!(format_duration(88), "00s");
        assert_eq!(format_duration(5_000), "05s");
        assert_eq!(format_duration(60_000), "00s");
        assert_eq!(format_duration(125_000), "02min 05s");
        assert_eq!(format_duration(3_720_000), "01h 02min");
        assert_eq!(format_duration(90_000_000), "1d 01h");
    }

    #[test]
    fn formats_dates_in_utc() {
        let at = |seconds| UNIX_EPOCH + Duration::from_secs(seconds);
        assert_eq!(format_date(at(0), &Zone::UTC), "1970-01-01 00:00:00");
        assert_eq!(
            format_date(at(1_794_191_943), &Zone::UTC),
            "2026-11-09 02:39:03"
        );
        assert_eq!(
            format_date(at(951_782_400), &Zone::UTC),
            "2000-02-29 00:00:00"
        );
    }

    #[test]
    fn formats_dates_in_a_zone() {
        let zone = |rule| Zone::from_rule(parse_rule(rule).expect("a rule"));
        let at = UNIX_EPOCH + Duration::from_secs(1_794_191_943);
        assert_eq!(
            format_date(at, &zone("EST5EDT,M3.2.0,M11.1.0")),
            "2026-11-08 21:39:03"
        );
        assert_eq!(
            format_date(at, &zone("<+0530>-5:30")),
            "2026-11-09 08:09:03"
        );
    }
}
