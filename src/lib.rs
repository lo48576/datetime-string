//! Datetime string types.
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![warn(clippy::missing_docs_in_private_items)]
#![cfg_attr(not(feature = "std"), no_std)]

#[allow(unused_extern_crates)] // Remove once `alloc` is used.
#[cfg(feature = "alloc")]
extern crate alloc;

#[macro_use]
mod macros;

pub mod rfc3339;

pub(crate) mod datetime;
pub(crate) mod parse;
pub(crate) mod str;
