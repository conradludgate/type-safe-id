# Changelog

## 0.3.4 - 2026-11-05

### Added

- A documented const type-prefix validation hook for eager validation by callers.
  It replaces the former doc-hidden validation constant.

### Fixed

- Return an error for overlong Unicode prefixes without panicking while building
  the error hint.
- Report the encoded length correctly for IDs with an empty prefix, which have
  no separator.

### Tests

- Refresh the upstream TypeID 0.3.0 invalid-input fixtures, including empty input.
