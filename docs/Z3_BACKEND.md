# Z3 SMT Solver Backend

Complete implementation of Z3 SMT solver integration for ECHIDNA.

## Overview

Z3 is a Tier 1 SMT (Satisfiability Modulo Theories) solver supporting multiple theories and SMT-LIB 2.0 format. This backend provides full integration including parsing, tactic application, and proof verification.

## Features

### 1. SMT-LIB 2.0 Parser

Complete parser supporting:
- **Declarations**: `declare-const`, `declare-fun`
- **Assertions**: `assert` statements
- **Commands**: `check-sat`, `get-model`, `set-logic`, `set-option`
- **Quantifiers**: `forall`, `exists` with typed bindings
- **Let bindings**: Local variable definitions
- **Comments**: Semicolon-based comments

### 2. Supported SMT Theories

- **QF_UF**: Uninterpreted functions with equality
- **QF_LIA**: Linear integer arithmetic
- **QF_NIA**: Nonlinear integer arithmetic  
- **QF_BV**: Fixed-size bitvectors
- **ALL**: All supported theories (for quantified formulas)
- Arrays, datatypes, and more

### 3. Process Management

- Asynchronous Z3 process spawning
- Configurable timeouts (default: 300 seconds)
- Proper stdin/stdout/stderr handling
- Clean process termination

### 4. Term Conversion

Bidirectional conversion between:
- SMT-LIB 2.0 terms (SmtTerm)
- ECHIDNA universal terms (Term)

Supports:
- Symbols and constants
- Function applications
- Quantified formulas
- Let expressions

### 5. Tactic Support

Built-in Z3 tactics:
- `simplify` - Term simplification
- `solve-eqs` - Equation solving
- `ctx-simplify` - Context-aware simplification
- `propagate-values` - Value propagation
- `normalize-bounds` - Bound normalization
- `lia2pb`, `pb2bv`, `bit-blast` - Arithmetic encoding

### 6. Proof Verification

Validates proofs by checking if goal negation is unsatisfiable.

## Usage Example

```rust
use echidna::{ProverBackend, ProverConfig};
use std::path::PathBuf;

let config = ProverConfig {
    executable: PathBuf::from("z3"),
    timeout: 60,
    ..Default::default()
};

let backend = z3::Z3Backend::new(config);
let state = backend.parse_file(
    PathBuf::from("examples/z3_simple.smt2")
).await?;

let is_valid = backend.verify_proof(&state).await?;
```

## Implementation Details

**File**: `/home/user/echidna/src/rust/provers/z3.rs`  
**Lines**: ~850 (including parser and tests)  
**Complexity**: 2/5  
**Tier**: 1

## Testing

```bash
cargo test --lib z3
```

## License

MIT OR Palimpsest-0.6
