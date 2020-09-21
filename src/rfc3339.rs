//! [RFC 3339] string types.
//!
//! [RFC 3339]: https://tools.ietf.org/html/rfc3339

mod date_time;
mod full_time;
mod offset;
mod partial_time;
mod secfrac;

pub use self::{
    date_time::DateTimeStr, full_time::FullTimeStr, offset::TimeOffsetStr,
    partial_time::PartialTimeStr, secfrac::SecfracStr,
};
#[cfg(feature = "alloc")]
pub use self::{
    date_time::DateTimeString, full_time::FullTimeString, offset::TimeOffsetString,
    partial_time::PartialTimeString, secfrac::SecfracString,
};

/// RFC 3339 [`full-date`] string slice, such as `2001-12-31`.
///
/// [`full-date`]: https://tools.ietf.org/html/rfc3339#section-5.6
pub type FullDateStr = crate::common::Ymd8HyphenStr;

/// RFC 3339 [`full-date`] owned string, such as `2001-12-31`.
///
/// [`full-date`]: https://tools.ietf.org/html/rfc3339#section-5.6
pub type FullDateString = crate::common::Ymd8HyphenString;

/// RFC 3339 [`time-numoffset`] string slice, such as `+09:30` and `-00:00`.
///
/// [`time-numoffset`]: https://tools.ietf.org/html/rfc3339#section-5.6
pub type TimeNumOffsetStr = crate::common::TimeNumOffsetColonStr;

/// RFC 3339 [`time-numoffset`] owned string, such as `+09:30` and `-00:00`.
///
/// [`time-numoffset`]: https://tools.ietf.org/html/rfc3339#section-5.6
pub type TimeNumOffsetString = crate::common::TimeNumOffsetColonString;
