# Aspect Tagging System

## Overview

The ECHIDNA aspect tagging system classifies theorems by mathematical domain and logical structure to improve premise selection and neural learning. This system provides comprehensive multi-label classification with confidence scores.

## Architecture

### Components

1. **Aspect Enum** - 60+ mathematical/logical aspects organized into categories:
   - Logic (7 aspects): Propositional, Predicate, Modal, Temporal, Higher-Order, Intuitionistic, Classical
   - Arithmetic (7 aspects): Natural Numbers, Integers, Rationals, Reals, Complex, Number Theory, Arithmetic
   - Algebra (8 aspects): Groups, Rings, Fields, Vector Spaces, Modules, Lattices, Category Theory, Universal Algebra
   - Analysis (7 aspects): Limits, Continuity, Derivatives, Integrals, Sequences, Measure Theory, Functional Analysis
   - Topology (5 aspects): Metric Spaces, Topological Spaces, Compactness, Connectedness, Topological Continuity
   - Set Theory (5 aspects): Set Operations, Cardinality, Ordinals, Axiom of Choice, ZFC
   - Type Theory (6 aspects): Dependent Types, Universes, Inductive Types, Coinductive Types, Polymorphism, Type Equivalence
   - Computer Science (8 aspects): Algorithms, Complexity, Formal Verification, Program Semantics, Concurrency, Cryptography, Automata, Lambda Calculus
   - Proof Techniques (6 aspects): Induction, Coinduction, Recursion, Case Analysis, Contradiction, Direct Proof
   - Other (6 aspects): Combinatorics, Graph Theory, Probability, Game Theory, Geometry, Abstract Nonsense

2. **AspectTagger Trait** - Interface for tagging strategies:
   - `tag()` - Tag theorem with aspects
   - `extract_features()` - Extract structural features
   - `tag_with_confidence()` - Get confidence scores (0.0-1.0)

3. **RuleBasedTagger** - Heuristic keyword and pattern matching:
   - 100+ keyword rules (e.g., "nat" → NaturalNumbers, "group" → Groups)
   - 20+ symbol rules (e.g., "∀" → PredicateLogic, "ℕ" → NaturalNumbers)
   - Structural analysis (quantifiers, lambda depth, Pi types, universes)
   - Configurable confidence threshold

4. **NeuralTagger** - ML-based classification (Julia integration):
   - Embeddings from theorem statements
   - Multi-label classification
   - Julia ML service integration (HTTP or FFI)
   - Trained on tagged theorem corpus

5. **OpenCycTagger** - Ontology-based semantic tagging:
   - Maps concepts to OpenCyc ontology
   - Uses semantic relationships
   - Cached concept mappings

6. **CompositeTagger** - Combines multiple strategies:
   - Union: All aspects from all taggers
   - Intersection: Only common aspects
   - WeightedVoting: Weighted confidence scores
   - Majority: Aspects with >50% vote

## Usage

### Basic Usage

```rust
use echidna::aspect::{Aspect, AspectTagger, RuleBasedTagger};
use echidna::core::Term;

// Create tagger
let tagger = RuleBasedTagger::new();

// Tag a theorem
let theorem_name = "nat_add_comm";
let statement = Term::App {
    func: Box::new(Term::Const("add".to_string())),
    args: vec![
        Term::Var("n".to_string()),
        Term::Var("m".to_string()),
    ],
};

let aspects = tagger.tag(theorem_name, &statement);
// aspects = [Aspect::Arithmetic, Aspect::NaturalNumbers]
```

### Confidence Scores

```rust
let scores = tagger.tag_with_confidence(theorem_name, &statement);
for (aspect, score) in scores {
    println!("{}: {:.2}", aspect.name(), score);
}
// Output:
// Arithmetic: 0.50
// Natural Numbers: 0.50
```

### Feature Extraction

```rust
let features = tagger.extract_features(&statement);
println!("Lambda depth: {}", features.lambda_depth);
println!("Quantifiers: {}", features.quantifier_count);
println!("Pi types: {}", features.pi_count);
println!("Symbols: {:?}", features.symbols);
```

### Custom Threshold

```rust
// Only tag with high-confidence aspects (≥0.8)
let tagger = RuleBasedTagger::with_threshold(0.8);
let aspects = tagger.tag(theorem_name, &statement);
```

### Composite Tagging

```rust
use echidna::aspect::{CompositeTagger, AggregationStrategy, NeuralTagger};

let composite = CompositeTagger::new(AggregationStrategy::WeightedVoting)
    .add_tagger(Box::new(RuleBasedTagger::new()), 0.7)
    .add_tagger(Box::new(NeuralTagger::new()), 0.3);

let aspects = composite.tag(theorem_name, &statement);
```

### Custom Rules

```rust
let mut tagger = RuleBasedTagger::new();

// Add custom keyword rule
tagger.add_keyword_rule("banach", vec![
    Aspect::FunctionalAnalysis,
    Aspect::MetricSpaces,
]);

// Add custom symbol rule
tagger.add_symbol_rule("⊗", vec![Aspect::VectorSpaces]);
```

## Integration with ECHIDNA

### Premise Selection

Aspects improve premise selection by filtering relevant theorems:

```rust
fn select_premises(goal: &Goal, theorems: &[Theorem], tagger: &dyn AspectTagger) -> Vec<Theorem> {
    // Tag the goal
    let goal_aspects = tagger.tag(&goal.id, &goal.target);

    // Filter theorems with matching aspects
    theorems.iter()
        .filter(|thm| {
            let thm_aspects = &thm.aspects;
            goal_aspects.iter().any(|a| thm_aspects.contains(&a.to_string()))
        })
        .cloned()
        .collect()
}
```

### Neural Learning

Aspects provide additional features for neural models:

```rust
struct TheoremEmbedding {
    syntactic_embedding: Vec<f64>,     // From term structure
    aspect_embedding: Vec<f64>,        // From aspect tags
}

fn embed_theorem(theorem: &Theorem, tagger: &dyn AspectTagger) -> TheoremEmbedding {
    let aspects = tagger.tag(&theorem.name, &theorem.statement);

    // Convert aspects to one-hot encoding
    let aspect_embedding = aspects_to_vector(&aspects);

    TheoremEmbedding {
        syntactic_embedding: term_to_embedding(&theorem.statement),
        aspect_embedding,
    }
}
```

### Prover Integration

Tag theorems during proof state construction:

```rust
impl ProverBackend for MyProver {
    async fn parse_file(&self, path: &Path) -> Result<ProofState> {
        let mut state = self.parse_proof(path).await?;

        // Tag all theorems with aspects
        let tagger = RuleBasedTagger::new();
        for theorem in &mut state.context.theorems {
            theorem.aspects = tagger.tag(&theorem.name, &theorem.statement)
                .into_iter()
                .map(|a| a.to_string())
                .collect();
        }

        Ok(state)
    }
}
```

## Neural Tagger Integration (Julia)

The `NeuralTagger` integrates with Julia ML components for advanced classification.

### Julia Service Setup

```julia
# julia/aspect_classifier.jl
using Flux, BSON

struct AspectClassifier
    model::Chain
    aspects::Vector{String}
end

function predict_aspects(classifier::AspectClassifier, embedding::Vector{Float64})
    scores = classifier.model(embedding)
    [(classifier.aspects[i], scores[i]) for i in 1:length(scores) if scores[i] > 0.5]
end

# Start HTTP service
using HTTP, JSON

function serve_classifier(classifier, port=8080)
    HTTP.serve(port) do request
        embedding = JSON.parse(String(request.body))["embedding"]
        aspects = predict_aspects(classifier, embedding)
        HTTP.Response(200, JSON.json(aspects))
    end
end
```

### Rust Integration

```rust
impl NeuralTagger {
    pub async fn tag_async(&self, theorem_name: &str, statement: &Term) -> Vec<Aspect> {
        // Get embeddings
        let embeddings = self.get_embeddings(statement).await;

        // Call Julia service
        if let Some(url) = &self.service_url {
            let client = reqwest::Client::new();
            let response = client.post(url)
                .json(&json!({ "embedding": embeddings }))
                .send()
                .await?;

            let aspects: Vec<(String, f64)> = response.json().await?;
            aspects.into_iter()
                .filter(|(_, score)| *score >= self.threshold)
                .map(|(name, _)| Aspect::from_string(&name))
                .collect()
        } else {
            Vec::new()
        }
    }
}
```

## OpenCyc Integration

The `OpenCycTagger` uses OpenCyc ontology for semantic tagging.

### Concept Mappings

```
OpenCyc Concept                    → ECHIDNA Aspects
=====================================
#$MathematicalObject               → [SetOperations]
#$Group-Mathematical               → [Groups, Algebra]
#$TopologicalSpace                 → [TopologicalSpaces, Topology]
#$RealNumber                       → [Reals, Arithmetic]
#$NaturalNumber                    → [NaturalNumbers, Arithmetic]
#$Predicate                        → [PredicateLogic]
#$PropositionalFormula            → [PropositionalLogic]
```

### Query Example

```rust
impl OpenCycTagger {
    async fn query_concept(&self, concept: &str) -> Option<Vec<Aspect>> {
        let query = format!(
            "(isa {} ?type)",
            concept
        );

        // Query OpenCyc API
        let response = self.query_cyc(&query).await?;

        // Map Cyc types to aspects
        self.map_types_to_aspects(&response)
    }
}
```

## Performance Considerations

### Rule-Based Tagger
- **Speed**: Very fast (microseconds per theorem)
- **Accuracy**: 70-80% for well-named theorems
- **Best for**: Real-time tagging, initial classification

### Neural Tagger
- **Speed**: Slower (milliseconds per theorem, depends on Julia service)
- **Accuracy**: 85-95% with good training data
- **Best for**: High-quality classification, large batches

### OpenCyc Tagger
- **Speed**: Medium (depends on OpenCyc query speed)
- **Accuracy**: 75-85% for concepts in ontology
- **Best for**: Semantic relationships, domain-specific knowledge

### Composite Strategy
- **WeightedVoting**: Balanced accuracy and coverage
- **Union**: Maximum recall, may have false positives
- **Intersection**: High precision, may miss relevant aspects
- **Majority**: Good compromise between precision and recall

## Testing

Run the test suite:

```bash
cargo test --lib aspect
```

Run the demo:

```bash
cargo run --example aspect_tagging_demo
```

## Future Enhancements

1. **Active Learning**: Use confidence scores to identify theorems needing manual tagging
2. **Transfer Learning**: Fine-tune neural tagger on new prover corpora
3. **Hierarchical Classification**: Multi-level aspect taxonomy
4. **Cross-Prover Alignment**: Map aspects across different theorem provers
5. **Temporal Tracking**: Track aspect usage over time for recommendation
6. **User Feedback**: Incorporate user corrections to improve tagging

## References

- **ECHIDNA Architecture**: See `docs/ARCHITECTURE.md`
- **Core Types**: See `src/rust/core.rs`
- **Prover Integration**: See `docs/PROVER_INTEGRATION.md`
- **Neural Components**: See `src/julia/README.md`

## License

SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
SPDX-License-Identifier: MIT OR Palimpsest-0.6
