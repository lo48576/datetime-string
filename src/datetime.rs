//! Datetime-related utilities.

use core::fmt;

/// Year-month-mday validation error.
#[derive(Debug, Clone, Copy)]
pub(crate) enum DateError {
    /// Month is out of range.
    MonthOutOfRange,
    /// Day of month is out of range.
    MdayOutOfRange,
}

impl fmt::Display for DateError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Self::MonthOutOfRange => "Month is out of range",
            Self::MdayOutOfRange => "Day of month is out of range",
        };
        f.write_str(msg)
    }
}

/// Returns true iff the given year is leap year.
#[inline]
pub(crate) fn is_leap_year(year: u16) -> bool {
    (year % 4 == 0) && ((year % 100 != 0) || (year % 400 == 0))
}

/// Validates the given year, month, and day of month.
///
/// Note that this function takes 0-based month value and 1-based year and mday.
pub(crate) fn validate_ym0d(year: u16, month0: u8, mday: u8) -> Result<(), DateError> {
    /// Maximum day of month value for normal (non-leap) year.
    const NORMAL_MDAY_MAX: [u8; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];

    if month0 >= 12 {
        return Err(DateError::MonthOutOfRange);
    }

    // Check if `mday` is 29 and return earily, rather than checking if `month1`
    // is 2, because `mday != 29` is much more likely than `month1 == 2`.
    if mday != 29 {
        return if mday <= NORMAL_MDAY_MAX[month0 as usize] {
            Ok(())
        } else {
            Err(DateError::MdayOutOfRange)
        };
    }

    // For 29th day of month, check if it is leap year.
    let mday_max = if is_leap_year(year) { 29 } else { 28 };

    if mday <= mday_max {
        Ok(())
    } else {
        Err(DateError::MdayOutOfRange)
    }
}

/// Validates the given year, month, and day of month.
///
/// Note that this function takes 1-based year, month, and mday.
#[inline]
pub(crate) fn validate_ym1d(year: u16, month1: u8, mday: u8) -> Result<(), DateError> {
    validate_ym0d(year, month1.wrapping_sub(1), mday)
}
