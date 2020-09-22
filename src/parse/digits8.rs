//! Parser functions for a string with 8 digits.

/// Parses 8 digits effectively in little endian.
///
/// # Failures
///
/// Note that this returns meaningless value for strings with non-digit characters.
/// This is safe in a sense that this never cause UB for any input, but callers
/// should ensure that the bytes consists of only ASCII digits.
#[cfg(any(not(target_endian = "big"), test))]
#[must_use]
fn parse_digits8_le(digits: [u8; 8]) -> u32 {
    // Sample: digits == "12345678" (i.e. digits == [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38]).

    // Sample: chunk1 == 0x38_37_36_35_34_33_32_31.
    let chunk1 = u64::from_le_bytes(digits);

    /// Mask for 2nd, 4th, 6th, and 8th significant digits.
    const LOWER_MASK_1: u64 = 0x0f_00_0f_00_0f_00_0f_00;
    /// Mask for 1st, 3rd, 5th, and 7th significant digits.
    const UPPER_MASK_1: u64 = 0x00_0f_00_0f_00_0f_00_0f;

    // Sample: (chunk1 & LOWER_MASK_1) == 0x08_00_06_00_04_00_02_00.
    // Sample: (chunk1 & LOWER_MASK_1) >> 8 == 0x00_08_00_06_00_04_00_02
    // (i.e. u64::from_be([0, 8, 0, 6, 0, 4, 0, 2]).
    let chunk1_lower = (chunk1 & LOWER_MASK_1) >> 8;
    // Sample: (chunk1 & UPPER_MASK_1) == 0x00_07_00_05_00_03_00_01
    // (i.e. u64::from_be([0x00, 0x03, 0x00, 0x01])).
    // Sample: (chunk1 & UPPER_MASK_1) * 10 == u64::from_be([0, 70, 0, 50, 0, 30, 0, 10]).
    let chunk1_upper = (chunk1 & UPPER_MASK_1) * 10;

    // Sample: chunk1_lower + chunk1_upper
    //          == (8 + 70) << 48 + (6 + 50) << 24 + (4 + 30) << 16 + (2 + 10).
    let chunk2: u64 = chunk1_lower + chunk1_upper;

    // Doing essentially same things for sums of larger size.

    /// Mask for 2nd and 4th significant words.
    // This can be `0xffff_0000_...`, but `00ff` is enough because each word has
    // a value less than 100.
    const LOWER_MASK_2: u64 = 0x00ff_0000_00ff_0000;
    /// Mask for 1st and 3rd significant words.
    const UPPER_MASK_2: u64 = 0x0000_00ff_0000_00ff;

    let chunk2_lower = (chunk2 & LOWER_MASK_2) >> 16;
    // 100 == 10 * 10.
    let chunk2_upper = (chunk2 & UPPER_MASK_2) * 100;

    let chunk3 = chunk2_lower + chunk2_upper;

    // 10000 == 100 * 100.
    (chunk3 >> 32) as u32 + (chunk3 as u32) * 10000
}

/// Parses 8 digits effectively in big endian.
///
/// # Failures
///
/// Note that this returns meaningless value for strings with non-digit characters.
/// This is safe in a sense that this never cause UB for any input, but callers
/// should ensure that the bytes consists of only ASCII digits.
#[cfg(any(target_endian = "big", test))]
#[must_use]
fn parse_digits8_be(digits: [u8; 8]) -> u32 {
    // Sample: digits == "12345678" (i.e. digits == [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38]).

    // Sample: chunk1 == 0x31_32_33_34_35_36_37_38.
    let chunk1 = u64::from_be_bytes(digits);

    /// Mask for 2nd, 4th, 6th, and 8th significant digits.
    const LOWER_MASK_1: u64 = 0x00_0f_00_0f_00_0f_00_0f;
    /// Mask for 1st, 3rd, 5th, and 7th significant digits.
    const UPPER_MASK_1: u64 = 0x0f_00_0f_00_0f_00_0f_00;

    // Sample: (chunk1 & LOWER_MASK_1) == 0x00_02_00_04_00_06_00_08
    // (i.e. u64::from_be([0, 2, 0, 4, 0, 6, 0, 8]).
    let chunk1_lower = chunk1 & LOWER_MASK_1;
    // Sample: (chunk1 & UPPER_MASK_1) == 0x01_00_03_00_05_00_07_00.
    // Sample: (chunk1 & UPPER_MASK_1) >> 8 == 0x00_01_00_03_00_05_00_07.
    // Sample: ((chunk1 & UPPER_MASK_1) >> 8) * 10 == u64::from_be([0, 10, 0, 30, 0, 50, 0, 70]).
    let chunk1_upper = ((chunk1 & UPPER_MASK_1) >> 8) * 10;

    // Sample: chunk1_lower + chunk1_upper
    //          == (2 + 10) << 48 + (4 + 30) << 32 + (6 + 50) << 16 + (8 + 70).
    let chunk2: u64 = chunk1_lower + chunk1_upper;

    // Doing essentially same things for sums of larger size.

    /// Mask for 2nd and 4th significant words.
    // This can be `0x0000_ffff_...`, but `00ff` is enough because each word has
    // a value less than 100.
    const LOWER_MASK_2: u64 = 0x0000_00ff_0000_00ff;
    /// Mask for 1st and 3rd significant words.
    const UPPER_MASK_2: u64 = 0x00ff_0000_00ff_0000;

    let chunk2_lower = chunk2 & LOWER_MASK_2;
    // 100 == 10 * 10.
    let chunk2_upper = ((chunk2 & UPPER_MASK_2) >> 16) * 100;

    let chunk3 = chunk2_lower + chunk2_upper;

    // 10000 == 100 * 100.
    (chunk3 >> 32) as u32 * 10000 + chunk3 as u32
}

/// Parses 8 digits effectively.
///
/// # Failures
///
/// Note that this returns meaningless value for strings with non-digit characters.
/// This is safe in a sense that this never cause UB for any input, but callers
/// should ensure that the bytes consists of only ASCII digits.
#[inline]
#[must_use]
pub(crate) fn parse_digits8(digits: [u8; 8]) -> u32 {
    #[cfg(not(target_endian = "big"))]
    {
        parse_digits8_le(digits)
    }
    #[cfg(target_endian = "big")]
    {
        parse_digits8_be(digits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use core::convert::TryFrom;

    fn as_digit8(s: &str) -> [u8; 8] {
        TryFrom::try_from(s.as_bytes()).unwrap()
    }

    #[test]
    fn digits8_le() {
        assert_eq!(parse_digits8_le(as_digit8("00000000")), 00000000);
        assert_eq!(parse_digits8_le(as_digit8("12345678")), 12345678);
        assert_eq!(parse_digits8_le(as_digit8("87654321")), 87654321);
        assert_eq!(parse_digits8_le(as_digit8("99999999")), 99999999);
    }

    #[test]
    fn digits8_be() {
        assert_eq!(parse_digits8_be(as_digit8("00000000")), 00000000);
        assert_eq!(parse_digits8_be(as_digit8("12345678")), 12345678);
        assert_eq!(parse_digits8_be(as_digit8("87654321")), 87654321);
        assert_eq!(parse_digits8_be(as_digit8("99999999")), 99999999);
    }

    #[test]
    fn digits8() {
        assert_eq!(parse_digits8(as_digit8("00000000")), 00000000);
        assert_eq!(parse_digits8(as_digit8("12345678")), 12345678);
        assert_eq!(parse_digits8(as_digit8("87654321")), 87654321);
        assert_eq!(parse_digits8(as_digit8("99999999")), 99999999);
    }
}
