//! [RFC 3339] string types.
//!
//! [RFC 3339]: https://tools.ietf.org/html/rfc3339

mod date_time;
mod full_time;
mod num_offset;
mod offset;
mod partial_time;
mod secfrac;

pub use self::{
    date_time::DateTimeStr,
    full_time::FullTimeStr,
    num_offset::{TimeNumOffsetStr, TimeNumOffsetString},
    offset::TimeOffsetStr,
    partial_time::PartialTimeStr,
    secfrac::SecfracStr,
};
#[cfg(feature = "alloc")]
pub use self::{
    date_time::DateTimeString, full_time::FullTimeString, offset::TimeOffsetString,
    partial_time::PartialTimeString, secfrac::SecfracString,
};

/// RFC 3339 [`full-date`] string slice.
///
/// [`full-date`]: https://tools.ietf.org/html/rfc3339#section-5.6
pub type FullDateStr = crate::common::Ymd8HyphenStr;

/// RFC 3339 [`full-date`] owned string.
///
/// [`full-date`]: https://tools.ietf.org/html/rfc3339#section-5.6
pub type FullDateString = crate::common::Ymd8HyphenString;
