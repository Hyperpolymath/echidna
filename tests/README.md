# ECHIDNA Test Infrastructure

Comprehensive testing framework for the ECHIDNA neurosymbolic theorem proving platform.

## Overview

This test suite provides:
- **Integration tests** - Full prover pipeline testing for all 12 supported provers
- **Property-based tests** - Automated invariant checking with proptest
- **Benchmarks** - Performance regression testing with criterion
- **Proof validation** - Automated verification of proof examples
- **Test utilities** - Mock backends, generators, and assertion helpers

## Directory Structure

```
tests/
├── README.md                 # This file
├── common/                   # Test utilities
│   ├── mod.rs               # Main utilities module
│   ├── mock_prover.rs       # Mock prover backend for testing
│   ├── generators.rs        # Property-based test generators
│   └── assertions.rs        # Custom assertion helpers
├── integration_tests.rs     # Integration tests for all provers
├── property_tests.rs        # Property-based tests with proptest
└── test_agda_backend.rs     # Agda-specific tests

benches/
├── parser_bench.rs          # Parser performance benchmarks
└── verification_bench.rs    # Verification performance benchmarks

scripts/
└── test-proofs.sh           # Proof validation script
```

## Running Tests

### Unit Tests

Run all tests (including integration tests):
```bash
cargo test
```

Run tests for a specific module:
```bash
cargo test integration_tests
cargo test property_tests
```

Run tests with output:
```bash
cargo test -- --nocapture
```

### Integration Tests

Integration tests cover all 12 theorem provers:

**Tier 1 (6 provers):**
- Agda
- Coq/Rocq
- Lean
- Isabelle
- Z3
- CVC5

**Tier 2 (3 provers):**
- Metamath
- HOL Light
- Mizar

**Tier 3 (2 provers):**
- PVS
- ACL2

**Tier 4 (1 prover):**
- HOL4

Run integration tests:
```bash
cargo test --test integration_tests
```

**Note:** Tests automatically skip provers that are not installed on your system.

### Property-Based Tests

Property-based tests use proptest to verify invariants:
- Term serialization roundtrips
- Parser invariants
- Tactic composition
- Type system properties

Run property tests:
```bash
cargo test --test property_tests
```

### Benchmarks

Performance benchmarks using criterion:

Run all benchmarks:
```bash
cargo bench
```

Run specific benchmark suite:
```bash
cargo bench parser_bench
cargo bench verification_bench
```

View benchmark reports:
```bash
open target/criterion/report/index.html
```

### Proof Validation

Validate all proof examples using the automated script:

```bash
# Test all provers
./scripts/test-proofs.sh

# Test specific prover
./scripts/test-proofs.sh agda
./scripts/test-proofs.sh coq
./scripts/test-proofs.sh z3
```

Available provers: `agda`, `coq`, `lean`, `isabelle`, `z3`, `cvc5`, `metamath`, `mizar`

## Test Utilities

### Mock Prover Backend

The `MockProver` allows testing without real prover installations:

```rust
use echidna::provers::ProverKind;
use crate::common::mock_prover::MockProver;

let mock = MockProver::new(ProverKind::Agda);
mock.add_verify_result(Ok(true));

let state = simple_proof_state();
let result = mock.verify_proof(&state).await;
assert!(result.unwrap());
```

### Test Generators

Property-based test generators for core types:

```rust
use crate::common::generators;
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_term_roundtrip(term in generators::arb_term()) {
        let json = serde_json::to_string(&term).unwrap();
        let deserialized: Term = serde_json::from_str(&json).unwrap();
        assert_eq!(term, deserialized);
    }
}
```

Available generators:
- `arb_term()` - Generate arbitrary terms
- `arb_goal()` - Generate proof goals
- `arb_proof_state()` - Generate proof states
- `arb_tactic()` - Generate tactics
- `arb_context()` - Generate contexts

### Custom Assertions

Specialized assertion helpers:

```rust
use crate::common::assertions::*;

// Alpha-equivalence
assert_alpha_equivalent(&lambda1, &lambda2);

// Proof state validity
assert_valid_proof_state(&state);

// Proof progress
assert_progress(&before_state, &after_state);

// Well-formed terms
assert_well_formed_term(&term);

// Serialization roundtrip
assert_serialization_roundtrip(&value);
```

### Helper Functions

Common test utilities:

```rust
use crate::common::*;

// Create test configurations
let config = test_prover_config(ProverKind::Agda);

// Find proof files
let files = find_proof_files(ProverKind::Coq);

// Check prover availability
if is_prover_available(ProverKind::Z3) {
    // Run test
}

// Create test terms
let simple = simple_term();
let lambda = lambda_term();
let pi = pi_term();
let complex = complex_term();

// Create test proof states
let state = simple_proof_state();
let multi = multi_goal_proof_state();
```

## Test Categories

### 1. Parser Tests

Test proof parsing for each prover:
- Valid syntax parsing
- Error handling for invalid syntax
- File I/O operations
- Performance benchmarks

### 2. Verification Tests

Test proof verification:
- Valid proof verification
- Invalid proof rejection
- Timeout handling
- Cross-prover verification

### 3. Tactic Tests

Test interactive proof tactics:
- Basic tactics (intro, reflexivity, assumption)
- Advanced tactics (apply, rewrite, induction)
- Tactic composition
- Error handling

### 4. Translation Tests

Test cross-prover term translation:
- Agda ↔ Coq
- Z3 ↔ CVC5
- Lean ↔ Isabelle
- Term equivalence preservation

### 5. Export Tests

Test proof export to different formats:
- Export to native prover syntax
- Roundtrip conversions
- Format validation

### 6. Error Handling Tests

Test error conditions:
- Invalid syntax
- Type errors
- Timeout errors
- Missing dependencies

## Writing New Tests

### Integration Test Template

```rust
#[tokio::test]
async fn test_new_feature() {
    if !common::is_prover_available(ProverKind::Agda) {
        eprintln!("Skipping: Agda not available");
        return;
    }

    let config = common::test_prover_config(ProverKind::Agda);
    let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

    let content = r#"
    module Test where
    -- Your test content
    "#;

    let result = backend.parse_string(content).await;
    assert!(result.is_ok());
}
```

### Property Test Template

```rust
proptest! {
    #[test]
    fn test_invariant(term in generators::arb_term()) {
        // Test your invariant
        prop_assert!(some_property(&term));
    }
}
```

### Benchmark Template

```rust
fn bench_operation(c: &mut Criterion) {
    c.bench_function("operation_name", |b| {
        b.iter(|| {
            // Operation to benchmark
            black_box(expensive_operation());
        });
    });
}
```

## Continuous Integration

Tests are designed to work in CI environments:
- Automatic prover detection
- Graceful skipping of unavailable provers
- Parallel test execution
- HTML benchmark reports

Example CI configuration:
```yaml
test:
  script:
    - cargo test --all
    - cargo bench --no-run
    - ./scripts/test-proofs.sh
```

## Dependencies

Test dependencies (from Cargo.toml):
- `tokio-test` - Async test utilities
- `proptest` - Property-based testing
- `criterion` - Benchmarking framework
- `mockall` - Mock object generation
- `tempfile` - Temporary file creation
- `pretty_assertions` - Better assertion output
- `quickcheck` - Alternative property testing
- `which` - Executable detection

## Coverage

Generate test coverage reports:
```bash
# Install tarpaulin
cargo install cargo-tarpaulin

# Generate coverage
cargo tarpaulin --out Html
```

## Performance

Benchmark results are saved to:
- `target/criterion/` - Detailed benchmark data
- `target/criterion/report/` - HTML reports

Track performance regressions by comparing benchmark results across commits.

## Best Practices

1. **Test Isolation** - Each test should be independent
2. **Prover Detection** - Always check if prover is available
3. **Timeout Handling** - Use reasonable timeouts (10-30s for tests)
4. **Error Messages** - Provide clear failure messages
5. **Property Tests** - Test invariants, not specific values
6. **Benchmarks** - Use `black_box` to prevent optimization
7. **Mock Backends** - Use for unit tests, real backends for integration

## Troubleshooting

### Tests Failing

1. Check prover installation:
   ```bash
   which agda coqc lean isabelle z3 cvc5
   ```

2. Check prover versions:
   ```bash
   agda --version
   coqc --version
   ```

3. Run with verbose output:
   ```bash
   cargo test -- --nocapture --test-threads=1
   ```

### Benchmarks Not Running

1. Build in release mode:
   ```bash
   cargo bench
   ```

2. Check benchmark configuration in Cargo.toml

### Proof Validation Failing

1. Check proof file syntax
2. Verify prover can compile file directly
3. Check environment variables (e.g., `MIZAR_HOME`)

## Contributing

When adding new tests:
1. Add to appropriate test file (integration, property, or unit)
2. Use common test utilities where possible
3. Add documentation for new test patterns
4. Update this README if adding new test categories
5. Ensure tests work with and without provers installed

---

**Last Updated:** 2025-11-22
**Maintained By:** ECHIDNA Project Team
