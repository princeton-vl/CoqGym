# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Fixed
- Examples use new generator combinators.
- Determine C source files with `*.c` rather than `*c`.
- Derive instances properly regardless of interpretation scope.
- Keep `Bullet Behavior` unchanged from "Strict Subproofs" (#142).
- Keep `Asymmetric Patterns` unset (#146).

### Deprecated
- `-exclude` option in `quickChickTool` is deprecated. Use `-include` instead.

## [1.0.2] - 2018-08-22
### Added
- Functor and Applicative instances for generators.
- Decidable equivalence between `unit`s.
- `-N` option to modify max success in `quickChickTool`.
- Collect labels for discarded tests.
- `quickChickTool` takes Python and Solidity files.

### Changed
- Rename `BasicInterface` to `QuickChickInterface`.
- Rename `Eq` to `Dec_Eq`.
- Separate generator interface from implementation.

### Deprecated
- `elements`  is deprecated in favor of `elems_`.
- `oneof`     is deprecated in favor of `oneOf_`.
- `frequency` is deprecated in favor of `freq_`.

### Fixed
- Show lists with elements separated by `;` rather than `,`.

## [1.0.1] - 2018-06-13
### Added
- Support Coq 8.8
- `-include` option for `quickChickTool`.
- Highlighted success message for `quickChickTool`.
- Checker combinator `whenFail'`.
- Tagged mutants.
- Line number information of mutants.

### Fixed
- OPAM dependencies.

### Removed
- No longer support Coq 8.7

## [1.0.0] - 2018-04-06
### Added
- OPAM package `coq-quickchick` on [coq-released](https://coq.inria.fr/opam/www/).

[Unreleased]: https://github.com/QuickChick/QuickChick/compare/v1.0.2...8.9
[1.0.2]: https://github.com/QuickChick/QuickChick/compare/v1.0.1...v1.0.2
[1.0.1]: https://github.com/QuickChick/QuickChick/compare/v1.0.0...v1.0.1
[1.0.0]: https://github.com/QuickChick/QuickChick/compare/itp-2015-final...v1.0.0
