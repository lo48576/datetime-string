//! Datetime string types.
//!
//! This crate provides borrowed and owned string types for datetime.
//!
//! The types in this crate do:
//!
//! * guarantee that the content string is well-formatted in some specific
//!   datetime format, and
//! * provide convenient API for getting and setting components of datetime,
//!   for example getting the hour and setting the day of a month.
//!
//! # Feature flags
//!
//! * `alloc`
//!     + Enabled by default.
//!     + Provides types and functions which requires `alloc` crate.
//!       Examples of stuff in `alloc` is `String`, `ToOwned`, `Vec<u8>`, etc.
//! * `std`
//!     + Enabled by default.
//!     + Provides types and functions which requires `std` crate.
//!       Examples of stuff in `std` is `std::error::Error`.
//! * `chrono04`
//!     + Provides some conversions between types in `chrono` crate v0.4 and this crate.
//! * `serde`
//!     + Provides `serde::{Serilaize, Deserialize}` implementations for string types.
//! * `alloc_with_serde`
//!     + Enables `alloc` feature for this crate and `alloc` feature for `serde` crate.
//! * `std_with_serde`
//!     + Enables `std` feature for this crate and `std` feature for `serde` crate.
//!
//! # Values construction
//!
//! Borrowed string slice types can be constructed by:
//!
//! * `from_str()`, `from_mut_str()`,
//! * `from_bytes()`, `from_bytes_mut()`,
//! * `TryFrom<&[u8]>`, `TryFrom<&mut [u8]>`,
//! * `TryFrom<&str>`, and `TryFrom<&mut str>`.
//!
//! Owned string types can be constructed by:
//!
//! * `From<&{corresponding borrowed string type}>`,
//! * `TryFrom<&[u8]>`, `TryFrom<Vec<u8>>`,
//! * `TryFrom<&str>`, `TryFrom<String>`, and
//! * `FromStr` (i.e. [`str::parse`]).
//!
//! # Examples
//!
//! ```
//! // `Hms6ColonStr` guarantees that the string is valid `hh:mm:ss` time.
//! use datetime_string::common::Hms6ColonStr;
//!
//! let time = Hms6ColonStr::from_str("12:34:56")?;
//!
//! assert_eq!(time.hour(), 12);
//! assert_eq!(time.minute(), 34);
//! assert_eq!(time.second(), 56);
//! # Ok::<_, datetime_string::Error>(())
//! ```
//!
//! ```
//! use std::convert::TryFrom;
//! // `Ymd8HyphenString` guarantees that the string is valid `YYYY-MM-DD` date.
//! use datetime_string::common::Ymd8HyphenString;
//!
//! let mut date = Ymd8HyphenString::try_from("1999-12-31")?;
//!
//! assert_eq!(date.year(), 1999);
//! // 1-based month.
//! assert_eq!(date.month1(), 12);
//! // 0-based month.
//! assert_eq!(date.month0(), 11);
//! // Day of a month.
//! assert_eq!(date.mday(), 31);
//!
//! date.set_month1(1)?;
//! assert_eq!(date.as_str(), "1999-01-31");
//!
//! assert!(date.set_month1(11).is_err(), "This fails because 1999-11-31 is invalid date");
//! # Ok::<_, datetime_string::Error>(())
//! ```
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![warn(clippy::missing_docs_in_private_items)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[macro_use]
mod macros;

pub mod common;
pub(crate) mod datetime;
pub(crate) mod error;
pub(crate) mod parse;
pub mod rfc3339;
pub(crate) mod str;

pub use self::error::{ConversionError, Error};
