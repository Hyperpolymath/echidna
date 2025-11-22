<!--
SPDX-License-Identifier: MIT AND Palimpsest-0.6
SPDX-FileCopyrightText: 2024-2025 ECHIDNA Project Contributors
-->

# Changelog

All notable changes to the ECHIDNA project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- RSR/CCCP compliance templates
- Dual licensing (MIT + Palimpsest v0.6)
- REUSE-compliant SPDX headers
- GitLab CI/CD pipeline with security scanning
- Podman containerization support
- Justfile build system
- Complete project documentation structure

### Changed
- Nothing yet

### Deprecated
- Nothing yet

### Removed
- Nothing yet

### Fixed
- Nothing yet

### Security
- Integrated Trivy security scanning
- Added cargo-audit for Rust dependencies
- Implemented Aqua.jl for Julia package security

## [0.1.0] - 2025-11-22

### Added
- Initial project structure
- Rust core implementation
- Julia ML components
- ReScript UI foundation
- Basic Agda prover support
- Project documentation (CLAUDE.md)
- Contribution guidelines
- Code of Conduct
- Security policy

### Infrastructure
- GitLab CI/CD pipeline
- Podman Containerfile
- REUSE license compliance
- EditorConfig for consistent formatting
- .gitignore for all languages

### Documentation
- Comprehensive README
- CONTRIBUTING guide
- CODE_OF_CONDUCT
- SECURITY policy
- CHANGELOG (this file)
- AUTHORS attribution

## Release Notes Format

Each release will include the following sections as applicable:

### Added
- New features and capabilities

### Changed
- Changes to existing functionality

### Deprecated
- Features that will be removed in future releases

### Removed
- Features that have been removed

### Fixed
- Bug fixes

### Security
- Security improvements and vulnerability fixes

## Version Numbering

ECHIDNA follows Semantic Versioning (SemVer):

- **MAJOR** version (X.0.0): Incompatible API changes
- **MINOR** version (0.X.0): New functionality, backwards compatible
- **PATCH** version (0.0.X): Bug fixes, backwards compatible

## Upcoming Releases

### [0.2.0] - Target: 2026-01-22
- Tier 1 prover implementations (Coq, Lean, Isabelle)
- Enhanced Z3 and CVC5 integration
- Neural proof synthesis improvements
- Python to Julia migration completion

### [0.3.0] - Target: 2026-04-22
- Tier 2 prover implementations (Metamath, HOL Light, Mizar)
- Aspect tagging system
- OpenCyc integration

### [0.4.0] - Target: 2026-07-22
- Tier 3 prover implementations (PVS, ACL2)
- DeepProbLog integration
- Performance optimizations

### [1.0.0] - Target: 2026-11-22
- Tier 4 prover implementation (HOL4)
- Complete 12-prover support
- Production-ready release
- Comprehensive documentation

## Migration Notes

### From Quill (Agda-only)

If you're migrating from the original Quill project:

1. Update import paths to use ECHIDNA modules
2. Replace Python ML code with Julia equivalents
3. Update prover selection to use new universal backend
4. Review aspect tagging configuration
5. Update build scripts to use Justfile

See migration guide in docs/ for detailed instructions.

---

**Maintained By**: ECHIDNA Project Team
**Last Updated**: 2025-11-22
