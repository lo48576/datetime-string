//! [RFC 3339] string types.
//!
//! [RFC 3339]: https://tools.ietf.org/html/rfc3339

mod full_date;
mod hhmmss;
mod num_offset;
mod partial_time;
mod secfrac;

use core::fmt;

use crate::datetime::DateError;

pub use self::{
    full_date::{FullDateStr, FullDateString},
    hhmmss::{HhmmssStr, HhmmssString},
    num_offset::{TimeNumOffsetStr, TimeNumOffsetString},
    partial_time::PartialTimeStr,
    secfrac::SecfracStr,
};
#[cfg(feature = "alloc")]
pub use self::{partial_time::PartialTimeString, secfrac::SecfracString};

/// Sign of a time offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TimeOffsetSign {
    /// Negative time offset.
    Negative,
    /// Positive time offset.
    Positive,
}

/// Component kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
enum ComponentKind {
    /// Year.
    Year,
    /// Month.
    Month,
    /// Day of month.
    Mday,
    /// Hour.
    Hour,
    /// Minute.
    Minute,
    /// Second.
    Second,
    /// Fraction part of a second.
    Secfrac,
    /// Hour of time offset.
    OffsetHour,
    /// Minute of time offset.
    OffsetMinute,
}

impl ComponentKind {
    /// Returns a name of the component.
    fn as_str(&self) -> &'static str {
        match self {
            Self::Year => "year",
            Self::Month => "month",
            Self::Mday => "day of month",
            Self::Hour => "hour",
            Self::Minute => "minute",
            Self::Second => "second",
            Self::Secfrac => "secfrac",
            Self::OffsetHour => "time offset hour",
            Self::OffsetMinute => "time offset minute",
        }
    }
}

/// Validation error kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
enum ErrorKind {
    /// Invalid separator.
    InvalidSeparator,
    /// Invalid component type.
    InvalidComponentType(ComponentKind),
    /// Component value is out of range.
    ComponentOutOfRange(ComponentKind),
    /// String is too short or lacks expected following components.
    TooShort,
    /// String is too long or contains unexpected suffix.
    TooLong,
}

/// Validation error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValidationError {
    /// Error kind.
    kind: ErrorKind,
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            ErrorKind::InvalidSeparator => write!(f, "Invalid separator"),
            ErrorKind::InvalidComponentType(component) => {
                write!(f, "Invalid component type for {}", component.as_str())
            }
            ErrorKind::ComponentOutOfRange(component) => {
                write!(f, "Out of range value for {}", component.as_str())
            }
            ErrorKind::TooShort => write!(f, "Too short"),
            ErrorKind::TooLong => write!(f, "Too long"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ValidationError {}

impl From<ErrorKind> for ValidationError {
    #[inline]
    fn from(kind: ErrorKind) -> Self {
        Self { kind }
    }
}

impl From<DateError> for ValidationError {
    #[inline]
    fn from(e: DateError) -> Self {
        match e {
            DateError::MonthOutOfRange => {
                ErrorKind::ComponentOutOfRange(ComponentKind::Month).into()
            }
            DateError::MdayOutOfRange => ErrorKind::ComponentOutOfRange(ComponentKind::Mday).into(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn time_offset_sign_ord() {
        assert!(
            TimeOffsetSign::Negative < TimeOffsetSign::Positive,
            "Negative time offset should be \"less than\" positive offset"
        );
    }
}
