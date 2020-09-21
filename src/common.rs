//! Common formats.
//!
//! This module contains types which may be commonly used for multiple specifications.

mod hms6_colon;
mod secfrac_digits;
mod time_num_offset_colon;
mod ymd8_hyphen;

#[cfg(feature = "alloc")]
pub use self::secfrac_digits::SecfracDigitsString;
pub use self::{
    hms6_colon::{Hms6ColonStr, Hms6ColonString},
    secfrac_digits::SecfracDigitsStr,
    time_num_offset_colon::{TimeNumOffsetColonStr, TimeNumOffsetColonString},
    ymd8_hyphen::{Ymd8HyphenStr, Ymd8HyphenString},
};

/// Sign of a time offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TimeOffsetSign {
    /// Negative time offset.
    Negative,
    /// Positive time offset.
    Positive,
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
