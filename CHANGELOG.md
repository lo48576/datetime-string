# Change Log

## [Unreleased]

* Now `TryFrom<Vec<u8>> for {OwnedString}` impls uses `ConversionError<Vec<u8>>`
  as an error type, instead of `Error`.
* `TryFrom<String> for {VariableLengthOwnedString}` impls are added.

### Added

* `TryFrom<String> for {VariableLengthOwnedString}` impls are added.

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

[Unreleased]: <https://github.com/lo48576/fbxcel/compare/v0.1.0...develop>
[0.1.0]: <https://github.com/lo48576/fbxcel/releases/tag/v0.1.0>
