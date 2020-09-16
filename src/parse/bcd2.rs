//! Parser functions for a string with 2 digits.

/// Parses 2-digits BCD effectively in little endian.
///
/// # Failures
///
/// Note that this returns meaningless value for strings with non-digit characters.
/// This is safe in a sense that this never cause UB for any input, but callers
/// should ensure that the bytes consists of only ASCII digits.
#[cfg(any(not(target_endian = "big"), test))]
#[must_use]
fn parse_bcd2_le(bcd: [u8; 2]) -> u8 {
    // Sample: bcd == "12" (i.e. bcd == [0x31, 0x32]).

    // Sample: chunk == 0x32_31.
    let chunk = u16::from_le_bytes(bcd);

    // Sample: chunk & 0x00_0f == 1.
    // Sample: (chunk & 0x0f_00) == 0x02_00.
    // Sample: (chunk & 0x0f_00) >> 8 == 2.
    ((chunk & 0x00_0f) * 10 + ((chunk & 0x0f_00) >> 8)) as u8
}

/// Parses 2-digits BCD effectively in big endian.
///
/// # Failures
///
/// Note that this returns meaningless value for strings with non-digit characters.
/// This is safe in a sense that this never cause UB for any input, but callers
/// should ensure that the bytes consists of only ASCII digits.
#[cfg(any(target_endian = "big", test))]
#[must_use]
fn parse_bcd2_be(bcd: [u8; 2]) -> u8 {
    // Sample: bcd == "12" (i.e. bcd == [0x31, 0x32]).

    // Sample: chunk == 0x31_32.
    let chunk = u16::from_be_bytes(bcd);

    // Sample: (chunk & 0x0f_00) == 0x01_00.
    // Sample: (chunk & 0x0f_00) >> 8 == 1.
    // Sample: chunk & 0x00_0f == 2.
    (((chunk & 0x0f_00) >> 8) * 10 + (chunk & 0x00_0f)) as u8
}

/// Parses 2-digits BCD effectively.
///
/// # Failures
///
/// Note that this returns meaningless value for strings with non-digit characters.
/// This is safe in a sense that this never cause UB for any input, but callers
/// should ensure that the bytes consists of only ASCII digits.
#[inline]
#[must_use]
pub(crate) fn parse_bcd2(bcd: [u8; 2]) -> u8 {
    #[cfg(not(target_endian = "big"))]
    {
        parse_bcd2_le(bcd)
    }
    #[cfg(target_endian = "big")]
    {
        parse_bcd2_be(bcd)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use core::convert::TryFrom;

    #[cfg(feature = "alloc")]
    use alloc::format;

    fn as_digit2(s: &str) -> [u8; 2] {
        TryFrom::try_from(s.as_bytes()).unwrap()
    }

    #[test]
    fn bcd2_le() {
        #[cfg(not(feature = "alloc"))]
        {
            assert_eq!(parse_bcd2_le(as_digit2("00")), 0);
            assert_eq!(parse_bcd2_le(as_digit2("01")), 1);
            assert_eq!(parse_bcd2_le(as_digit2("10")), 10);
            assert_eq!(parse_bcd2_le(as_digit2("12")), 12);
            assert_eq!(parse_bcd2_le(as_digit2("55")), 55);
            assert_eq!(parse_bcd2_le(as_digit2("99")), 99);
        }
        #[cfg(feature = "alloc")]
        {
            for i in 0_u8..=99_u8 {
                let s = format!("{:02}", i);
                assert_eq!(parse_bcd2_le(as_digit2(&s)), i);
            }
        }
    }

    #[test]
    fn bcd2_be() {
        #[cfg(not(feature = "alloc"))]
        {
            assert_eq!(parse_bcd2_be(as_digit2("00")), 0);
            assert_eq!(parse_bcd2_be(as_digit2("01")), 1);
            assert_eq!(parse_bcd2_be(as_digit2("10")), 10);
            assert_eq!(parse_bcd2_be(as_digit2("12")), 12);
            assert_eq!(parse_bcd2_be(as_digit2("55")), 55);
            assert_eq!(parse_bcd2_be(as_digit2("99")), 99);
        }
        #[cfg(feature = "alloc")]
        {
            for i in 0_u8..=99_u8 {
                let s = format!("{:02}", i);
                assert_eq!(parse_bcd2_be(as_digit2(&s)), i);
            }
        }
    }

    #[test]
    fn bcd2() {
        #[cfg(not(feature = "alloc"))]
        {
            assert_eq!(parse_bcd2(as_digit2("00")), 0);
            assert_eq!(parse_bcd2(as_digit2("01")), 1);
            assert_eq!(parse_bcd2(as_digit2("10")), 10);
            assert_eq!(parse_bcd2(as_digit2("12")), 12);
            assert_eq!(parse_bcd2(as_digit2("55")), 55);
            assert_eq!(parse_bcd2(as_digit2("99")), 99);
        }
        #[cfg(feature = "alloc")]
        {
            for i in 0_u8..=99_u8 {
                let s = format!("{:02}", i);
                assert_eq!(parse_bcd2(as_digit2(&s)), i);
            }
        }
    }
}
