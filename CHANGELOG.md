# Change Log

## [Unreleased]

## [0.2.0]

* Now `TryFrom<Vec<u8>> for {OwnedString}` impls uses `ConversionError<Vec<u8>>`
  as an error type, instead of `Error` (4353b833860cbbf92e708cf9ddf55103ab059386).
* `TryFrom<String> for {VariableLengthOwnedString}` impls are added.
* Added `assign` method to fixed length string slice types
  (`common::{Hms6ColonStr, TimeNumOffsetColonStr, Ymd8HyphenStr}`)
  (d4de91e7abbad0cd13a45da48efe698c1b2e5d57).
* Added `Hms6ColonStr::to_seconds` method (66448be35bf51bc37589855dc2084cf706e69a03).
* Added `Ymd8HyphenStr::{days_since_epoch, yday0, yday1}` methods
  (66448be35bf51bc37589855dc2084cf706e69a03).
* Added value creation methods and trait impls (6feb20ae2c9efebb34ccf18a5ce333383fa768f0).
* Improve doc comments.

### Added

* `TryFrom<String> for {VariableLengthOwnedString}` impls are added.
* Added `assign` method to fixed length string slice types
  (`common::{Hms6ColonStr, TimeNumOffsetColonStr, Ymd8HyphenStr}`).
* Added `Hms6ColonStr::to_seconds` method.
* Added `Ymd8HyphenStr::{days_since_epoch, yday0, yday1}` methods.
* Added value creation methods and trait impls.
    + `common::Hms6ColonString`
        - `from_hms()`
    + `common::Ymd8HyphenString`
        - `from_ym0d()`, `from_ym1d()`
    + `common::TimeNumOffsetColonString`
        - `utc()`, `unknown_local_offset()`, `from_minutes()`,
          `from_sign_and_hm()`, `from_hm_signed()`
    + `rfc3339::TimeOffsetString`
        - `z()`, `unknown_local_offset()`, `from_minutes()`,
          `from_sign_and_hm()`, `from_hm_signed()`
        - `From<&common::TimeNumOffsetColonStr{,ing}> for rfc3339::TimeOffsetString`

### Breaking changes

* Now `TryFrom<Vec<u8>> for {OwnedString}` impls uses `ConversionError<Vec<u8>>`
  as an error type, instead of `Error`.
    + A pair of `Error` and `ConversionError<T>` is quite similar to
      `std::str::Utf8Error` and `std::string::FromUtf8Error`.
      `ConversionError<T>` allows users to get the value back without extra
      allocation overhead, when it is not convertible to the target type.

## [0.1.0]

Initial release.

Mainly RFC 3339 datetime types are supported.

[Unreleased]: <https://github.com/lo48576/fbxcel/compare/v0.2.0...develop>
[0.2.0]: <https://github.com/lo48576/fbxcel/releases/tag/v0.2.0>
[0.1.0]: <https://github.com/lo48576/fbxcel/releases/tag/v0.1.0>
