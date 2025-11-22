<!--
SPDX-License-Identifier: MIT AND Palimpsest-0.6
SPDX-FileCopyrightText: 2024-2025 ECHIDNA Project Contributors
-->

# ECHIDNA

**E**xtensible **C**ognitive **H**ybrid **I**ntelligence for **D**eductive **N**eural **A**ssistance

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSES/MIT.txt)
[![License: Palimpsest-0.6](https://img.shields.io/badge/License-Palimpsest--0.6-green.svg)](LICENSES/Palimpsest-0.6.txt)
[![REUSE status](https://api.reuse.software/badge/gitlab.com/non-initiate/rhodinised/quill)](https://api.reuse.software/info/gitlab.com/non-initiate/rhodinised/quill)
[![Pipeline](https://gitlab.com/non-initiate/rhodinised/quill/badges/main/pipeline.svg)](https://gitlab.com/non-initiate/rhodinised/quill/-/pipelines)

A neurosymbolic theorem proving platform that transforms Quill (Agda-only neural solver) into a universal multi-prover system supporting 12 theorem provers with aspect tagging, OpenCyc integration, and DeepProbLog probabilistic logic.

## Features

- **12 Theorem Prover Support**: Universal backend supporting Agda, Coq/Rocq, Lean, Isabelle, Z3, CVC5, Metamath, HOL Light, Mizar, PVS, ACL2, and HOL4
- **Neurosymbolic AI**: Neural proof synthesis combined with symbolic verification
- **Aspect Tagging**: Intelligent proof categorization and analysis
- **OpenCyc Integration**: Common sense reasoning with ontological knowledge
- **DeepProbLog**: Probabilistic logic programming for uncertain reasoning
- **4-Language Architecture**: Rust (core), Julia (ML), ReScript (UI), Mercury/Logtalk (logic)

## Quick Start

### Prerequisites

- **Rust** 1.75 or later
- **Julia** 1.10 or later
- **Deno** 1.40 or later (for ReScript)
- **Podman** (NOT Docker)
- **Just** command runner

### Installation

```bash
# Clone the repository
git clone https://gitlab.com/non-initiate/rhodinised/quill.git
cd quill

# Build the project
just build

# Run tests
just test

# Run ECHIDNA
just run
```

### Using Podman Container

```bash
# Build container
podman build -f Containerfile -t echidna:latest .

# Run container
podman run -it echidna:latest
```

## Architecture

### Prover Tiers

**Tier 1** (6 provers - Months 2-4):
- Agda - Dependent type theory
- Coq/Rocq - Interactive theorem prover
- Lean - Functional programming and proving
- Isabelle - Higher-order logic
- Z3 - SMT solver
- CVC5 - SMT solver

**Tier 2** (3 provers - Months 5-7):
- Metamath - Plain text verifier (easiest, start here!)
- HOL Light - Classical higher-order logic
- Mizar - Mathematical vernacular

**Tier 3** (2 provers - Months 8-10):
- PVS - Specification and verification
- ACL2 - Applicative Common Lisp

**Tier 4** (1 prover - Months 11-12):
- HOL4 - Higher-order logic

### Technology Stack

- **Rust**: Core logic, FFI, WASM compilation
- **Julia**: Machine learning components (NO Python allowed!)
- **ReScript + Deno**: User interface
- **Mercury/Logtalk**: Optional logic reservoir

### Key Components

- **`echidna_provers.rs`**: Complete Rust trait system (600+ lines)
- **Aspect Tagging System**: Proof classification and analysis
- **Neural Solver**: Integration from original Quill project
- **Universal Prover Abstraction**: Unified interface for all 12 provers

## Usage

### Basic Theorem Proving

```rust
use echidna::prover::{Prover, AgdaProver};

let prover = AgdaProver::new();
let result = prover.prove("∀ (n : ℕ) → n + 0 ≡ n")?;
println!("Proof: {}", result);
```

### Using Multiple Provers

```rust
use echidna::prover::{ProverBackend, lean, coq, z3};

// Try multiple provers
let backends = vec![lean(), coq(), z3()];
for backend in backends {
    if let Ok(proof) = backend.prove(theorem) {
        println!("Proved with {}: {}", backend.name(), proof);
        break;
    }
}
```

### Neural Proof Synthesis

```julia
using ECHIDNA

# Train neural model
model = train_proof_synthesizer(training_data)

# Generate proof candidates
candidates = synthesize_proofs(model, theorem)

# Verify with symbolic prover
for candidate in candidates
    if verify_proof(candidate)
        return candidate
    end
end
```

## Development

### Building from Source

```bash
# Install dependencies
just deps

# Build all components
just build

# Build specific component
just build-rust
just build-julia
just build-rescript
```

### Running Tests

```bash
# Run all tests
just test

# Run specific language tests
just test-rust
just test-julia

# Run integration tests
just test-integration
```

### Quality Checks

```bash
# Run all quality checks
just check

# Individual checks
just lint          # REUSE, rustfmt, clippy
just security      # Trivy, cargo-audit
just coverage      # Test coverage
```

## Documentation

- [Contributing Guidelines](CONTRIBUTING.md)
- [Code of Conduct](CODE_OF_CONDUCT.md)
- [Security Policy](SECURITY.md)
- [Changelog](CHANGELOG.md)
- [API Documentation](docs/)
- [Prover Backend Guides](docs/)

## Roadmap

### 12-Month Implementation Plan

**Months 1-2**: Foundation
- Deploy RSR/CCCP compliance templates
- Migrate Python code to Julia
- Complete Tier 1 infrastructure

**Months 2-4**: Tier 1 Provers
- Coq/Rocq implementation
- Lean implementation
- Isabelle implementation
- Z3 and CVC5 integration

**Months 5-7**: Tier 2 Provers
- Metamath (start here - easiest!)
- HOL Light
- Mizar

**Months 8-10**: Tier 3 Provers
- PVS
- ACL2

**Months 11-12**: Tier 4 and Polish
- HOL4 implementation
- Performance optimization
- Documentation completion

## Contributing

We welcome contributions! Please see [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

### Critical Constraints

- ❌ **NO PYTHON** - Use Julia for all ML code
- ✅ **RSR/CCCP Compliance** - Follow Rhodium Standard Repository guidelines
- ✅ **Justfile PRIMARY** - Use Just, not Make
- ✅ **GitLab-first** - This is a GitLab project
- ✅ **Podman not Docker** - Always use Podman
- ✅ **Dual Licensing** - MIT + Palimpsest v0.6

## License

This project is dual-licensed under:

- [MIT License](LICENSES/MIT.txt)
- [Palimpsest License v0.6](LICENSES/Palimpsest-0.6.txt)

See [NOTICE](NOTICE) for complete license information.

## Citation

If you use ECHIDNA in your research, please cite:

```bibtex
@software{echidna2025,
  title = {ECHIDNA: Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance},
  author = {ECHIDNA Project Contributors},
  year = {2025},
  url = {https://gitlab.com/non-initiate/rhodinised/quill},
  license = {MIT AND Palimpsest-0.6}
}
```

## Acknowledgments

- Based on the Quill project (Agda neural solver)
- Built on the shoulders of the theorem proving community
- See [AUTHORS.md](AUTHORS.md) for contributor list

## Contact

- **GitLab Issues**: https://gitlab.com/non-initiate/rhodinised/quill/-/issues
- **Merge Requests**: https://gitlab.com/non-initiate/rhodinised/quill/-/merge_requests
- **Security**: security@echidna-project.org

---

**Version**: 0.1.0
**Status**: Active Development
**Last Updated**: 2025-11-22
