# CVC5 Backend Quick Reference

**File**: `/home/user/echidna/src/rust/provers/cvc5.rs` (719 lines)

## Quick Start

```rust
use echidna::provers::{ProverFactory, ProverKind, ProverConfig};
use std::path::PathBuf;

// Create CVC5 backend
let config = ProverConfig {
    executable: PathBuf::from("cvc5"),
    timeout: 60,
    ..Default::default()
};
let backend = ProverFactory::create(ProverKind::CVC5, config)?;

// Parse SMT-LIB file
let state = backend.parse_file(PathBuf::from("problem.smt2")).await?;

// Verify proof
let valid = backend.verify_proof(&state).await?;
```

## Key Types

### CVC5Config
```rust
pub struct CVC5Config {
    pub base: ProverConfig,
    pub produce_proofs: bool,         // default: true
    pub produce_models: bool,         // default: true
    pub produce_unsat_cores: bool,    // default: false
    pub incremental: bool,            // default: true
    pub cvc5_options: HashMap<String, String>,
}
```

### SmtResult
```rust
pub enum SmtResult {
    Sat,      // Satisfiable
    Unsat,    // Unsatisfiable (valid theorem)
    Unknown,  // Solver couldn't determine
}
```

## Core Methods

| Method | Purpose | Example |
|--------|---------|---------|
| `new(config)` | Create backend | `CVC5Backend::new(config)` |
| `version()` | Get CVC5 version | `backend.version().await?` |
| `parse_file(path)` | Parse SMT-LIB file | `backend.parse_file(path).await?` |
| `parse_string(s)` | Parse SMT-LIB string | `backend.parse_string(smt).await?` |
| `verify_proof(state)` | Check validity | `backend.verify_proof(&state).await?` |
| `export(state)` | Generate SMT-LIB | `backend.export(&state).await?` |
| `apply_tactic(state, t)` | Execute tactic | `backend.apply_tactic(&s, &t).await?` |

## Custom Tactics

```rust
use echidna::core::Tactic;

// Check satisfiability
Tactic::Custom {
    prover: "cvc5".to_string(),
    command: "check-sat".to_string(),
    args: vec![],
}

// Get model
Tactic::Custom {
    prover: "cvc5".to_string(),
    command: "get-model".to_string(),
    args: vec![],
}

// Get proof
Tactic::Custom {
    prover: "cvc5".to_string(),
    command: "get-proof".to_string(),
    args: vec![],
}
```

## String Theory Examples

```rust
use echidna::provers::cvc5::string_examples;

// String concatenation
let ex1 = string_examples::string_concat_length();

// Substring
let ex2 = string_examples::string_substring();

// Contains
let ex3 = string_examples::string_contains();

// Regex (email validation)
let ex4 = string_examples::regex_match();
```

### Example SMT-LIB (String Contains)
```smt2
(set-logic QF_SLIA)
(declare-const s String)
(assert (str.contains s "abc"))
(assert (not (str.contains s "xyz")))
(assert (< (str.len s) 10))
(check-sat)
(get-model)
```

## Sequence Theory Examples

```rust
use echidna::provers::cvc5::sequence_examples;

// Sequence operations
let ex1 = sequence_examples::sequence_ops();

// Subsequence containment
let ex2 = sequence_examples::sequence_contains();
```

### Example SMT-LIB (Sequences)
```smt2
(set-logic QF_SLIA)
(declare-const s (Seq Int))
(assert (= (seq.len s) 5))
(assert (= (seq.nth s 0) 1))
(assert (= (seq.nth s 4) 5))
(check-sat)
(get-model)
```

## Sets and Relations Examples

```rust
use echidna::provers::cvc5::sets_examples;

// Set operations
let ex1 = sets_examples::set_ops();

// Transitive closure
let ex2 = sets_examples::relation_ops();
```

### Example SMT-LIB (Relations)
```smt2
(set-logic QF_ALL)
(declare-const R (Relation Int Int))
(assert (set.member (tuple 1 2) R))
(assert (set.member (tuple 2 3) R))
(assert (set.member (tuple 1 3) (rel.tclosure R)))
(check-sat)
```

## Separation Logic Examples

```rust
use echidna::provers::cvc5::separation_logic_examples;

// Heap separation
let ex = separation_logic_examples::sep_logic_basic();
```

### Example SMT-LIB (Separation Logic)
```smt2
(set-logic QF_ALL)
(declare-const x Int)
(declare-const y Int)
(assert (sep (pto x 1) (pto y 2)))
(assert (distinct x y))
(check-sat)
```

## Common SMT-LIB Operations

### String Operations
| Operation | SMT-LIB | Description |
|-----------|---------|-------------|
| Concatenation | `(str.++ s1 s2)` | Concatenate strings |
| Length | `(str.len s)` | String length |
| Substring | `(str.substr s i n)` | Extract substring |
| Contains | `(str.contains s sub)` | Check substring |
| At | `(str.at s i)` | Character at index |
| Index of | `(str.indexof s sub i)` | Find substring |
| Replace | `(str.replace s old new)` | Replace substring |
| Regex | `(str.in.re s r)` | Regex matching |

### Sequence Operations
| Operation | SMT-LIB | Description |
|-----------|---------|-------------|
| Concatenation | `(seq.++ s1 s2)` | Concatenate sequences |
| Length | `(seq.len s)` | Sequence length |
| Nth | `(seq.nth s i)` | Element at index |
| Contains | `(seq.contains s sub)` | Check subsequence |
| Extract | `(seq.extract s i n)` | Extract subsequence |
| Unit | `(seq.unit x)` | Single-element sequence |

### Set Operations
| Operation | SMT-LIB | Description |
|-----------|---------|-------------|
| Member | `(set.member x s)` | Element membership |
| Union | `(set.union s1 s2)` | Set union |
| Intersection | `(set.inter s1 s2)` | Set intersection |
| Difference | `(set.minus s1 s2)` | Set difference |
| Subset | `(set.subset s1 s2)` | Subset test |
| Cardinality | `(set.card s)` | Set size |
| Empty | `(as set.empty (Set Int))` | Empty set |

### Relation Operations
| Operation | SMT-LIB | Description |
|-----------|---------|-------------|
| Tuple | `(tuple x y)` | Create tuple |
| Transpose | `(rel.transpose R)` | Swap tuple elements |
| Join | `(rel.join R S)` | Relational join |
| Closure | `(rel.tclosure R)` | Transitive closure |

## Configuration Examples

### Enable Finite Model Finding
```rust
let mut config = CVC5Config::default();
config.cvc5_options.insert(
    "finite-model-find".to_string(),
    "true".to_string()
);
```

### Enable Quantifier Instantiation
```rust
config.cvc5_options.insert(
    "full-saturate-quant".to_string(),
    "true".to_string()
);
```

### Set Time Limit
```rust
config.base.timeout = 30; // seconds
```

### Enable Unsat Cores
```rust
config.produce_unsat_cores = true;
```

## Error Handling

```rust
use anyhow::Result;

async fn solve_problem(path: PathBuf) -> Result<bool> {
    let backend = CVC5Backend::new(config);

    // Parse file (may fail if file doesn't exist or invalid SMT-LIB)
    let state = backend.parse_file(path).await?;

    // Verify (may fail if CVC5 process crashes or timeout)
    let valid = backend.verify_proof(&state).await?;

    Ok(valid)
}

// Handle errors
match solve_problem(path).await {
    Ok(true) => println!("Valid theorem!"),
    Ok(false) => println!("Not valid"),
    Err(e) => eprintln!("Error: {:?}", e),
}
```

## Testing

```bash
# Run unit tests (no CVC5 binary needed)
cargo test --package echidna --lib provers::cvc5

# Run integration tests (requires CVC5 binary)
cargo test --package echidna cvc5 -- --ignored

# Run all tests
cargo test
```

## Performance Tips

1. **Reuse Backend** - Create once, use for multiple queries
2. **Incremental Mode** - Use push/pop for related queries
3. **Simplify First** - Simplify formulas before solving
4. **Set Timeouts** - Prevent infinite solving
5. **Choose Logic** - Use specific logic (QF_SLIA) for better performance

## Common Patterns

### Batch Verification
```rust
let backend = CVC5Backend::new(config);

for file in problem_files {
    let state = backend.parse_file(file).await?;
    let valid = backend.verify_proof(&state).await?;
    results.push((file, valid));
}
```

### Counterexample Extraction
```rust
let tactic = Tactic::Custom {
    prover: "cvc5".to_string(),
    command: "check-sat".to_string(),
    args: vec![],
};

match backend.apply_tactic(&state, &tactic).await? {
    TacticResult::QED => println!("Valid!"),
    TacticResult::Error(msg) => {
        // Check metadata for counterexample
        if let Some(ce) = state.metadata.get("counterexample") {
            println!("Counterexample: {}", ce);
        }
    }
    _ => {}
}
```

### Custom Options
```rust
let mut config = CVC5Config::default();
config.cvc5_options.insert("strings-exp".to_string(), "true".to_string());
config.cvc5_options.insert("strings-fmf".to_string(), "true".to_string());
let backend = CVC5Backend::with_config(config);
```

## Debugging

### Enable Verbose Output
Add to `cvc5_options`:
```rust
config.cvc5_options.insert("verbose".to_string(), "true".to_string());
```

### Dump SMT-LIB
```rust
let smtlib = backend.export(&state).await?;
std::fs::write("debug.smt2", smtlib)?;
```

### Check CVC5 Version
```bash
cvc5 --version
```

### Test CVC5 Directly
```bash
cvc5 problem.smt2
```

## When to Use CVC5

✅ **Use CVC5 for**:
- String constraint solving
- Sequence reasoning
- Regular expression matching
- Set theory with transitive closure
- Separation logic
- Problems involving strings/sequences

⚠️ **Consider Z3 instead for**:
- General SMT solving
- Bit-vector reasoning
- Floating-point arithmetic
- More mature ecosystem

💡 **Use Both**:
- ECHIDNA supports portfolio solving
- Run both solvers in parallel
- Use fastest result

## Links

- [Full Implementation Details](/home/user/echidna/docs/CVC5_IMPLEMENTATION.md)
- [Implementation Summary](/home/user/echidna/CVC5_IMPLEMENTATION_SUMMARY.md)
- [CVC5 Documentation](https://cvc5.github.io/docs/latest/)
- [SMT-LIB Standard](https://smtlib.cs.uiowa.edu/)

---

**Quick Reference v1.0** | ECHIDNA Project | 2025-11-22
