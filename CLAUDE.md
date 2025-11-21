# CLAUDE.md

This document provides guidelines and context for working with Claude Code on the echidna project.

## Project Overview

**ECHIDNA** (Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance) is a neurosymbolic theorem proving platform that transforms Quill (Agda-only neural solver) into a universal multi-prover system supporting 12 theorem provers with aspect tagging, OpenCyc, and DeepProbLog integration.

**Target Repository**: https://gitlab.com/non-initiate/rhodinised/quill (GitLab)

**Timeline**: 12 months for complete 12-prover implementation

## Repository Structure

```
echidna/
├── .git/              # Git repository
├── CLAUDE.md          # This file
├── src/               # Source code
│   ├── rust/          # Rust core/FFI/WASM
│   ├── julia/         # Julia ML components
│   ├── rescript/      # ReScript+Deno UI
│   └── mercury/       # Mercury/Logtalk logic (optional)
├── templates/         # RSR/CCCP compliance templates
├── scripts/           # Automation scripts
├── docs/              # Documentation
└── Justfile           # Primary build system
```

## Working with Claude Code

### General Guidelines

1. **Code Quality**: Maintain high code quality standards with proper error handling, tests, and documentation
2. **Git Workflow**: Follow conventional commit messages and keep commits atomic
3. **Security**: Be vigilant about security vulnerabilities (XSS, SQL injection, command injection, etc.)
4. **Dependencies**: Document all dependencies and their purposes

### Development Workflow

When working on features or fixes:

1. Create feature branches with descriptive names (prefix with `claude/` for Claude Code branches)
2. Write clear, concise commit messages
3. Test changes thoroughly before committing
4. Update documentation as needed

### Commit Message Format

Follow conventional commit format:
- `feat:` - New features
- `fix:` - Bug fixes
- `docs:` - Documentation changes
- `refactor:` - Code refactoring
- `test:` - Adding or updating tests
- `chore:` - Maintenance tasks

Example: `feat: add user authentication module`

### Code Style

- Use consistent formatting throughout the codebase
- Include comments for complex logic
- Keep functions small and focused
- Use meaningful variable and function names

### Testing

- Write tests for new features
- Ensure existing tests pass before committing
- Include both unit and integration tests where appropriate

### Documentation

- Update README.md for user-facing changes
- Document API endpoints and interfaces
- Include inline comments for complex algorithms
- Keep this CLAUDE.md updated with project-specific guidelines

## Project-Specific Context

### Tech Stack

**4-Language Architecture** (use as few languages as necessary):
- **Julia**: Machine learning components (replaces Python - NO PYTHON ALLOWED)
- **Rust**: Core logic, FFI, WASM compilation (replaces Haskell/Zig/Ada)
- **ReScript + Deno**: User interface
- **Mercury/Logtalk**: Optional logic reservoir

**Prover Support** (12 Total):
- **Tier 1 (6)**: Agda, Coq/Rocq, Lean, Isabelle, Z3, CVC5
- **Tier 2 (3)**: Metamath (easiest!), HOL Light, Mizar
- **Tier 3 (2)**: PVS, ACL2
- **Tier 4 (1)**: HOL4

### Key Dependencies

**Development Tools**:
- Justfile (PRIMARY build system, not Make)
- Podman (not Docker)
- GitLab CI/CD
- Trivy (security scanning)

**Quality Checkers**:
- REUSE (license compliance)
- Aqua.jl (dependency security)
- JET.jl (static analysis)
- Coverage.jl (test coverage)

**Integrations**:
- OpenCyc ontology
- DeepProbLog probabilistic logic

### Architecture

**12-Prover Expansion**: Based on "Big Six" theorem provers covering >70% of standard theorems. Full implementation over 12 months.

**Key Components**:
- `echidna_provers.rs`: Complete Rust trait system (600+ lines)
- Aspect tagging system
- Neural solver integration from original Quill
- Universal prover abstraction layer

**Integration Complexity**:
- Metamath: 2/5 (easiest - plain text parser, start here!)
- HOL Light: 3/5
- Mizar: 3/5

### Known Issues

**Critical**: All work (35+ files) currently in wrong repository (zotero-voyant-export)

**Completed but Not Deployed**:
- ✅ 23 RSR/CCCP compliance templates
- ✅ 4 automation scripts
- ✅ 5 quality checkers integrated
- ✅ Complete Rust trait system
- ✅ Integration guides for Tier 2 provers
- ✅ 8 architecture/planning documents

**Not Done**: No code deployed to actual Quill repository yet

## Useful Commands

```bash
# Build System (Justfile is PRIMARY)
just build              # Build the project
just test               # Run tests
just check              # Run all quality checkers

# Deployment (when ready)
./scripts/deploy-templates.sh    # Deploy RSR/CCCP templates
./scripts/setup.sh                # Initial setup
./scripts/customize.sh            # Customize placeholders
./scripts/migrate-spdx.sh         # Migrate SPDX licenses

# Container Management (Podman, not Docker)
podman build -f Containerfile .   # Build container
podman run echidna                # Run container

# Quality Checks
reuse lint                        # License compliance
julia -e 'using Aqua; ...'       # Dependency security
trivy scan .                      # Security vulnerabilities
```

## Resources

- [Quill Original Repository](https://gitlab.com/non-initiate/rhodinised/quill)
- [RSR/CCCP Compliance](https://rhodium-standard.org) - Rhodium Standard Repository
- [Palimpsest License v0.6](https://palimpsest.license)
- Critical Files (to preserve from wrong repo):
  - `echidna_provers.rs` - Rust trait implementation
  - `TIER2_PROVER_INTEGRATION_GUIDES.md`
  - `ECHIDNA_PROVER_EXPANSION_ANALYSIS.md`
  - All `.quill-template` files

## Notes for Claude Code

### Priorities

1. Code correctness and security
2. Clear, maintainable code
3. Comprehensive testing
4. Thorough documentation

### Constraints

- Always verify file paths before operations
- Use parallel tool calls when operations are independent
- Prefer specialized tools over bash commands for file operations
- Use the Task tool for complex, multi-step operations

### Special Considerations

**Critical Constraints**:
- ❌ **ABSOLUTELY NO PYTHON** - migrate all Python code to Julia
- ✅ **RSR/CCCP Compliance Required** - follow Rhodium Standard Repository guidelines
- ✅ **Justfile PRIMARY** - never use Make or other build systems
- ✅ **GitLab-first** - not GitHub (target repo is on GitLab)
- ✅ **Podman not Docker** - always use Podman for containers
- ✅ **Dual Licensing**: MIT + Palimpsest v0.6

**Development Priority Order**:
1. Deploy templates to actual Quill repository (Priority 1)
2. Remove Python code → migrate to Julia (Priority 2 - user requirement)
3. Tier 1 implementation: Coq, Lean, Isabelle, Z3, CVC5 (Months 2-4)
4. Tier 2 "Big Six" completion: Metamath first (easiest!), then HOL Light, Mizar (Months 5-7)

**Key Insights**:
- Start Tier 2 with Metamath (2/5 complexity, plain text parser, 1.5 weeks)
- 12 provers provide >70% standard theorem coverage
- 4-language stack minimizes complexity while maintaining power

**Migration Status**:
- Current session branch: `claude/create-claude-md-01JJTxAXBb4bHzgpeRHXDLnW`
- Previous work branch: `claude/review-quill-rhodium-01AWCPRWZUY8mhjUZgC17tEc`
- All work needs migration from zotero-voyant-export repo

---

**Last Updated**: 2025-11-21
**Maintained By**: ECHIDNA Project Team
