//! Datetime string types.
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
pub(crate) mod parse;
pub mod rfc3339;
pub(crate) mod str;
