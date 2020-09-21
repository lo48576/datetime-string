//! Parser functions for a string with 4 digits.

/// Parses 4-digits BCD effectively in little endian.
///
/// # Failures
///
/// Note that this returns meaningless value for strings with non-digit characters.
/// This is safe in a sense that this never cause UB for any input, but callers
/// should ensure that the bytes consists of only ASCII digits.
#[cfg(any(not(target_endian = "big"), test))]
#[must_use]
fn parse_bcd4_le(bcd: [u8; 4]) -> u16 {
    // Sample: bcd == "1234" (i.e. bcd == [0x31, 0x32, 0x33, 0x34]).

    // Sample: chunk1 == 0x34_33_32_31.
    let chunk1 = u32::from_le_bytes(bcd);

    /// Mask for 2nd and 4th significant digits.
    const LOWER_MASK_1: u32 = 0x0f_00_0f_00;
    /// Mask for 1st and 3rd significant digits.
    const UPPER_MASK_1: u32 = 0x00_0f_00_0f;

    // Sample: (chunk1 & LOWER_MASK_1) == 0x04_00_02_00.
    // Sample: (chunk1 & LOWER_MASK_1) >> 8 == 0x00_04_00_02 (i.e. u32::from_be([0, 4, 0, 2]).
    let chunk1_lower = (chunk1 & LOWER_MASK_1) >> 8;
    // Sample: (chunk1 & UPPER_MASK_1) == 0x00_03_00_01 (i.e. u32::from_be([0x00, 0x03, 0x00, 0x01])).
    // Sample: (chunk1 & UPPER_MASK_1) * 10 == u32::from_be([0, 30, 0, 10]).
    let chunk1_upper = (chunk1 & UPPER_MASK_1) * 10;

    // Sample: chunk1_lower + chunk1_upper == (4 + 30) << 16 + (2 + 10).
    let chunk2: u32 = chunk1_lower + chunk1_upper;

    // Sample: (chunk2 >> 16) as u16 == 4 + 30.
    // Sample: chunk2 * 100 == (2 + 10) * 100 + (((4 + 30) << 16) * 100).
    // Sample: (chunk2 * 100) as u16 == (2 + 10) * 100.
    // Here `(chunk2 * 100) as u16` can be `chunk2 * 100`, because `99 * 100` is representable in
    // 16-bits.
    ((chunk2 >> 16) + (chunk2 * 100)) as u16
}

/// Parses 4-digits BCD effectively in big endian.
///
/// # Failures
///
/// Note that this returns meaningless value for strings with non-digit characters.
/// This is safe in a sense that this never cause UB for any input, but callers
/// should ensure that the bytes consists of only ASCII digits.
#[cfg(any(target_endian = "big", test))]
#[must_use]
fn parse_bcd4_be(bcd: [u8; 4]) -> u16 {
    // Sample: bcd == "1234" (i.e. bcd == [0x31, 0x32, 0x33, 0x34]).

    // Sample: chunk1 == 0x31_32_33_34.
    let chunk1 = u32::from_be_bytes(bcd);

    /// Mask for 2nd and 4th significant digits.
    const LOWER_MASK_1: u32 = 0x00_0f_00_0f;
    /// Mask for 1st and 3rd significant digits.
    const UPPER_MASK_1: u32 = 0x0f_00_0f_00;

    // Sample: (chunk1 & LOWER_MASK_1) == 0x00_02_00_04 (i.e. u32::from_be([0, 2, 0, 4]).
    let chunk1_lower = chunk1 & LOWER_MASK_1;
    // Sample: (chunk1 & UPPER_MASK_1) == 0x01_00_03_00.
    // Sample: (chunk1 & UPPER_MASK_1) >> 8 == 0x00_01_00_03.
    // Sample: ((chunk1 & UPPER_MASK_1) >> 8) * 10 == u32::from_be([0, 10, 0, 30]).
    let chunk1_upper = ((chunk1 & UPPER_MASK_1) >> 8) * 10;

    // Sample: chunk1_lower + chunk1_upper == (2 + 10) << 16 + (4 + 30).
    let chunk2: u32 = chunk1_lower + chunk1_upper;

    // Sample: chunk2 = (2 + 10) << 16 + (4 + 30).
    // Sample: (chunk2 >> 16) as u16 == 2 + 10.
    // Sample: (chunk2 >> 16) * 100 as u16 == (2 + 10) * 100.
    // Sample: chunk2 as u16 = 4 + 30.
    ((chunk2 >> 16) * 100 + chunk2) as u16
}

/// Parses 4-digits BCD effectively.
///
/// # Failures
///
/// Note that this returns meaningless value for strings with non-digit characters.
/// This is safe in a sense that this never cause UB for any input, but callers
/// should ensure that the bytes consists of only ASCII digits.
#[inline]
#[must_use]
pub(crate) fn parse_bcd4(bcd: [u8; 4]) -> u16 {
    #[cfg(not(target_endian = "big"))]
    {
        parse_bcd4_le(bcd)
    }
    #[cfg(target_endian = "big")]
    {
        parse_bcd4_be(bcd)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use core::convert::TryFrom;

    fn as_digit4(s: &str) -> [u8; 4] {
        TryFrom::try_from(s.as_bytes()).unwrap()
    }

    #[test]
    fn bcd4_le() {
        assert_eq!(parse_bcd4_le(as_digit4("0000")), 0000);
        assert_eq!(parse_bcd4_le(as_digit4("1234")), 1234);
        assert_eq!(parse_bcd4_le(as_digit4("8765")), 8765);
        assert_eq!(parse_bcd4_le(as_digit4("9999")), 9999);
    }

    #[test]
    fn bcd4_be() {
        assert_eq!(parse_bcd4_be(as_digit4("0000")), 0000);
        assert_eq!(parse_bcd4_be(as_digit4("1234")), 1234);
        assert_eq!(parse_bcd4_be(as_digit4("8765")), 8765);
        assert_eq!(parse_bcd4_be(as_digit4("9999")), 9999);
    }

    #[test]
    fn bcd4() {
        assert_eq!(parse_bcd4(as_digit4("0000")), 0000);
        assert_eq!(parse_bcd4(as_digit4("1234")), 1234);
        assert_eq!(parse_bcd4(as_digit4("8765")), 8765);
        assert_eq!(parse_bcd4(as_digit4("9999")), 9999);
    }
}
