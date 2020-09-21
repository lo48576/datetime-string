//! Common formats.
//!
//! This module contains types which may be commonly used for multiple specifications.

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
