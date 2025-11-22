# Aspect Tagging - Quick Start Guide

## TL;DR

ECHIDNA's aspect tagging system classifies theorems into 60 mathematical/logical domains for better premise selection.

## Usage in 30 Seconds

```rust
use echidna::aspect::{Aspect, AspectTagger, RuleBasedTagger};
use echidna::core::Term;

// Create tagger
let tagger = RuleBasedTagger::new();

// Tag theorem
let aspects = tagger.tag("nat_add_comm", &statement);

// Get confidence scores
let scores = tagger.tag_with_confidence("theorem_name", &statement);
```

## Key Files

| File | Purpose | Size |
|------|---------|------|
| `/home/user/echidna/src/rust/aspect.rs` | Core implementation | 1,156 lines |
| `/home/user/echidna/docs/ASPECT_TAGGING.md` | Full documentation | 11 KB |
| `/home/user/echidna/examples/aspect_tagging_demo.rs` | Examples | 6.5 KB |
| `/home/user/echidna/docs/ASPECT_IMPLEMENTATION_SUMMARY.md` | Implementation details | 14 KB |

## Key Components

### 1. Aspects (60 total)

```rust
Aspect::PropositionalLogic    // Logic
Aspect::NaturalNumbers         // Arithmetic
Aspect::Groups                 // Algebra
Aspect::Limits                 // Analysis
Aspect::TopologicalSpaces     // Topology
Aspect::DependentTypes        // Type Theory
Aspect::Algorithms            // Computer Science
Aspect::Induction             // Proof Techniques
```

### 2. Taggers

```rust
// Rule-based (keyword/symbol matching)
let rule_tagger = RuleBasedTagger::new();

// Neural (Julia ML integration - stub)
let neural_tagger = NeuralTagger::new();

// OpenCyc (ontology - stub)
let cyc_tagger = OpenCycTagger::new("http://localhost:3601");

// Composite (combine multiple)
let composite = CompositeTagger::new(AggregationStrategy::WeightedVoting)
    .add_tagger(Box::new(rule_tagger), 0.7)
    .add_tagger(Box::new(neural_tagger), 0.3);
```

### 3. Features

```rust
let features = tagger.extract_features(&statement);
println!("Lambda depth: {}", features.lambda_depth);
println!("Quantifiers: {}", features.quantifier_count);
println!("Symbols: {:?}", features.symbols);
```

## Common Patterns

### Tag All Theorems in Context

```rust
for theorem in &mut context.theorems {
    theorem.aspects = tagger.tag(&theorem.name, &theorem.statement)
        .into_iter()
        .map(|a| a.to_string())
        .collect();
}
```

### Filter by Aspect

```rust
let arithmetic_theorems: Vec<_> = theorems.iter()
    .filter(|t| t.aspects.contains(&"Arithmetic".to_string()))
    .collect();
```

### Custom Rules

```rust
let mut tagger = RuleBasedTagger::new();
tagger.add_keyword_rule("banach", vec![
    Aspect::FunctionalAnalysis,
    Aspect::MetricSpaces,
]);
```

## Run Examples

```bash
# Build
cargo build

# Run demo
cargo run --example aspect_tagging_demo

# Run tests
cargo test --lib aspect
```

## Status

✅ **Production Ready**:
- RuleBasedTagger (100+ rules)
- CompositeTagger (4 strategies)
- 60 aspects, 10 categories
- 12 comprehensive tests

⏳ **Stub (needs integration)**:
- NeuralTagger (Julia ML)
- OpenCycTagger (OpenCyc API)

## Quick Reference: Aspect Categories

| Category | Count | Examples |
|----------|-------|----------|
| Logic | 7 | Propositional, Predicate, Modal |
| Arithmetic | 7 | Natural Numbers, Integers, Reals |
| Algebra | 8 | Groups, Rings, Fields |
| Analysis | 7 | Limits, Continuity, Derivatives |
| Topology | 5 | Metric Spaces, Compactness |
| Set Theory | 5 | Set Operations, Cardinality |
| Type Theory | 6 | Dependent Types, Universes |
| Computer Science | 8 | Algorithms, Complexity |
| Proof Techniques | 6 | Induction, Recursion |
| Other | 6 | Combinatorics, Graph Theory |

## Integration Checklist

- [ ] Tag theorems during proof parsing
- [ ] Use aspects for premise selection
- [ ] Integrate with neural models (Julia)
- [ ] Add aspect-based search/filtering
- [ ] Export aspects to prover formats
- [ ] Track aspect statistics
- [ ] Build aspect-based recommendations

## Learn More

- **Full Documentation**: `/home/user/echidna/docs/ASPECT_TAGGING.md`
- **Implementation Details**: `/home/user/echidna/docs/ASPECT_IMPLEMENTATION_SUMMARY.md`
- **Examples**: `/home/user/echidna/examples/aspect_tagging_demo.rs`
- **Source Code**: `/home/user/echidna/src/rust/aspect.rs`

## License

SPDX-License-Identifier: MIT OR Palimpsest-0.6
