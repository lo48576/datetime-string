//! String-related utilities.
//!
//! Serialization function takes `&mut [u8]` or similar types rather than
//! `&mut W where W: std::io::Write`, because `core` does not have an alternative
//! of `std::io::Write`, and `core::fmt::Write` is not implemented for `&mut [u8]`.

/// Writes 0-padded 4 digits string.
///
/// It is guaranteed that this does not panic and `buf` is filled with ASCII digits.
///
/// # Failures
///
/// Note that this function writes meaning less content for integer which is not
/// representable with 4 digits.
/// This is safe in a sense that this never cause UB for any integer input, but
/// callers should ensure that the integer value is less than 10000.
#[inline]
pub(crate) fn write_digit4(buf: &mut [u8; 4], v: u16) {
    buf[3] = (v % 10) as u8 + b'0';
    let v = v / 10;
    buf[2] = (v % 10) as u8 + b'0';
    let v = v / 10;
    buf[1] = (v % 10) as u8 + b'0';
    let v = v / 10;
    buf[0] = v as u8 + b'0';
}

/// Writes 0-padded 2 digits string.
///
/// It is guaranteed that this does not panic and `buf` is filled with ASCII digits.
///
/// # Failures
///
/// Note that this function writes meaning less content for integer which is not
/// representable with 4 digits.
/// This is safe in a sense that this never cause UB for any integer input, but
/// callers should ensure that the integer value is less than 10000.
#[inline]
pub(crate) fn write_digit2(buf: &mut [u8; 2], v: u8) {
    buf[0] = (v / 10) as u8 + b'0';
    buf[1] = (v % 10) as u8 + b'0';
}
