//! Utilities for parsing.

mod bcd2;
mod bcd4;
mod bcd8;

pub(crate) use self::{bcd2::parse_bcd2, bcd4::parse_bcd4, bcd8::parse_bcd8};
