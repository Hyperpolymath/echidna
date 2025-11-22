<!--
SPDX-License-Identifier: MIT AND Palimpsest-0.6
SPDX-FileCopyrightText: 2024-2025 ECHIDNA Project Contributors
-->

# Contributing to ECHIDNA

Thank you for your interest in contributing to ECHIDNA (Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance)! We welcome contributions from the community.

## Table of Contents

- [Code of Conduct](#code-of-conduct)
- [Getting Started](#getting-started)
- [Development Setup](#development-setup)
- [How to Contribute](#how-to-contribute)
- [Coding Standards](#coding-standards)
- [Testing Guidelines](#testing-guidelines)
- [Commit Message Guidelines](#commit-message-guidelines)
- [Pull Request Process](#pull-request-process)
- [License](#license)

## Code of Conduct

This project adheres to a Code of Conduct that all contributors are expected to follow. Please read [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md) before contributing.

## Getting Started

1. **Fork the repository** on GitLab
2. **Clone your fork** locally:
   ```bash
   git clone https://gitlab.com/YOUR_USERNAME/rhodinised/quill.git
   cd quill
   ```
3. **Add upstream remote**:
   ```bash
   git remote add upstream https://gitlab.com/non-initiate/rhodinised/quill.git
   ```

## Development Setup

ECHIDNA uses a 4-language architecture. Follow these steps to set up your development environment:

### Prerequisites

- **Rust** 1.75+ (for core logic and FFI)
- **Julia** 1.10+ (for ML components - NO Python allowed)
- **Deno** 1.40+ (for ReScript UI)
- **Podman** (NOT Docker)
- **Just** command runner (PRIMARY build system)

### Installation

```bash
# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Install Julia
wget https://julialang-s3.julialang.org/bin/linux/x64/1.10/julia-1.10.0-linux-x86_64.tar.gz
tar -xvzf julia-1.10.0-linux-x86_64.tar.gz
sudo mv julia-1.10.0 /opt/
sudo ln -s /opt/julia-1.10.0/bin/julia /usr/local/bin/julia

# Install Deno
curl -fsSL https://deno.land/install.sh | sh

# Install Podman (Debian/Ubuntu)
sudo apt-get install podman

# Install Just
cargo install just
```

### Build the Project

```bash
# Build everything
just build

# Run tests
just test

# Run quality checks
just check
```

## How to Contribute

### Reporting Bugs

1. Check if the bug has already been reported in [GitLab Issues](https://gitlab.com/non-initiate/rhodinised/quill/-/issues)
2. If not, create a new issue using the bug report template
3. Include:
   - Clear description of the bug
   - Steps to reproduce
   - Expected vs actual behavior
   - Environment details (OS, versions, etc.)

### Suggesting Enhancements

1. Check existing [GitLab Issues](https://gitlab.com/non-initiate/rhodinised/quill/-/issues) for similar suggestions
2. Create a new issue using the feature request template
3. Clearly describe:
   - The enhancement and its benefits
   - Possible implementation approach
   - Any potential drawbacks

### Contributing Code

1. **Find or create an issue** to work on
2. **Create a feature branch**:
   ```bash
   git checkout -b feature/your-feature-name
   ```
3. **Make your changes** following our coding standards
4. **Write tests** for your changes
5. **Run quality checks**:
   ```bash
   just check
   just test
   ```
6. **Commit your changes** with clear commit messages
7. **Push to your fork**:
   ```bash
   git push origin feature/your-feature-name
   ```
8. **Create a Merge Request** on GitLab

## Coding Standards

### Rust

- Follow Rust naming conventions and idioms
- Use `rustfmt` for formatting: `cargo fmt`
- Use `clippy` for linting: `cargo clippy`
- Maximum line length: 100 characters
- Add documentation comments for public APIs

### Julia

- Follow Julia style guide
- Use 4 spaces for indentation
- Add docstrings for exported functions
- Run `JET.jl` for static analysis

### ReScript

- Follow ReScript conventions
- Use 2 spaces for indentation
- Add type annotations where helpful

### General

- Write clear, self-documenting code
- Add comments for complex logic
- Keep functions small and focused
- Use meaningful variable and function names
- Avoid global state where possible

## Testing Guidelines

### Rust Tests

```bash
# Run all tests
cargo test

# Run specific test
cargo test test_name

# Run with coverage
cargo tarpaulin --out Xml
```

### Julia Tests

```julia
# Run tests
julia --project=. -e 'using Pkg; Pkg.test()'

# With coverage
julia --project=. -e 'using Pkg; Pkg.test(coverage=true)'
```

### Integration Tests

- Write integration tests for multi-component features
- Test all 12 theorem prover backends
- Include error cases and edge conditions

## Commit Message Guidelines

We follow the Conventional Commits specification:

### Format

```
<type>(<scope>): <subject>

<body>

<footer>
```

### Types

- `feat:` New feature
- `fix:` Bug fix
- `docs:` Documentation changes
- `refactor:` Code refactoring
- `test:` Adding or updating tests
- `chore:` Maintenance tasks
- `perf:` Performance improvements
- `ci:` CI/CD changes

### Examples

```
feat(agda): add support for cubical type theory

Implements cubical type theory support in the Agda backend,
including path types and higher inductive types.

Closes #123
```

```
fix(lean): resolve parser error with implicit arguments

The Lean parser was incorrectly handling implicit arguments
in dependent function types. This fix ensures proper parsing.

Fixes #456
```

## Pull Request Process

1. **Ensure your MR**:
   - Passes all CI/CD checks
   - Includes tests for new functionality
   - Updates documentation as needed
   - Follows coding standards
   - Has a clear description

2. **MR Description Should Include**:
   - What changes were made and why
   - How to test the changes
   - Screenshots (if UI changes)
   - Related issues

3. **Review Process**:
   - At least one maintainer must approve
   - All discussions must be resolved
   - CI/CD pipeline must pass
   - No merge conflicts

4. **After Approval**:
   - Maintainer will merge your MR
   - Your contribution will be acknowledged in AUTHORS.md

## Development Priorities

Current development priorities (12-month timeline):

1. **Tier 1 Provers** (Months 2-4): Coq, Lean, Isabelle, Z3, CVC5
2. **Tier 2 Provers** (Months 5-7): Metamath (easiest, start here!), HOL Light, Mizar
3. **Tier 3 Provers** (Months 8-10): PVS, ACL2
4. **Tier 4 Provers** (Months 11-12): HOL4

## Critical Constraints

- ❌ **NO PYTHON** - All ML code must use Julia
- ✅ **RSR/CCCP Compliance** - Follow Rhodium Standard Repository guidelines
- ✅ **Justfile PRIMARY** - Use Just, not Make
- ✅ **GitLab-first** - This is a GitLab project
- ✅ **Podman not Docker** - Always use Podman for containers
- ✅ **Dual Licensing** - MIT + Palimpsest v0.6

## Resources

- [Project Documentation](docs/)
- [GitLab Issues](https://gitlab.com/non-initiate/rhodinised/quill/-/issues)
- [Merge Requests](https://gitlab.com/non-initiate/rhodinised/quill/-/merge_requests)
- [RSR/CCCP Guidelines](https://rhodium-standard.org)
- [Palimpsest License](https://palimpsest.license)

## Questions?

If you have questions about contributing, please:
- Check existing documentation
- Search GitLab Issues
- Open a new issue with the "question" label

## Recognition

All contributors will be acknowledged in [AUTHORS.md](AUTHORS.md). Thank you for helping make ECHIDNA better!

---

**Last Updated**: 2025-11-22
**Maintainer**: ECHIDNA Project Team
