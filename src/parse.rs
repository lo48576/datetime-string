//! Utilities for parsing.

mod digits2;
mod digits4;
mod digits8;

pub(crate) use self::{digits2::parse_digits2, digits4::parse_digits4, digits8::parse_digits8};
