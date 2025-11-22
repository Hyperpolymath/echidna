# SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
# SPDX-License-Identifier: MIT AND Palimpsest-0.6

# ECHIDNA Julia ML Components

**Neural Premise Selection for Universal Theorem Proving**

This directory contains the complete Julia-based machine learning system for ECHIDNA (Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance). It generalizes Quill's Agda-specific neural architecture to support all 12 theorem provers.

## Overview

**NO PYTHON** - Pure Julia implementation using Flux.jl for deep learning.

### Supported Provers (12 Total)

- **Tier 1 (7)**: Agda, Coq/Rocq, Lean, Isabelle, Z3, CVC5
- **Tier 2 (3)**: Metamath (easiest!), HOL Light, Mizar
- **Tier 3 (2)**: PVS, ACL2
- **Tier 4 (1)**: HOL4

### Architecture

1. **Text Encoding**: Transformer-based encoding of proof states and premises
2. **Graph Neural Networks**: Model theorem dependencies and relationships
3. **Premise Ranking**: Cross-attention between goals and candidate premises
4. **Multi-Prover**: Unified architecture handling prover-specific syntax

## Directory Structure

```
julia/
├── Project.toml           # Julia package dependencies
├── EchidnaML.jl          # Main module entry point
├── models/
│   ├── encoder.jl        # Multi-prover proof state encoding
│   └── neural_solver.jl  # GNN + Transformer architecture
├── training/
│   └── train.jl          # Training pipeline and loss functions
├── inference/
│   └── predict.jl        # Inference engine and caching
└── api/
    └── server.jl         # HTTP API server (Oxygen.jl)
```

## Installation

### Prerequisites

- Julia 1.9 or higher
- CUDA-compatible GPU (optional, but recommended)
- Podman (for containerized deployment)

### Setup

```bash
cd /home/user/echidna/src/julia

# Install dependencies
julia --project=. -e 'using Pkg; Pkg.instantiate()'

# Optional: Precompile for faster startup
julia --project=. -e 'using Pkg; Pkg.precompile()'
```

### GPU Support

If you have CUDA available:

```julia
using CUDA
CUDA.functional()  # Should return true
```

The system will automatically use GPU acceleration if available.

## Quick Start

### 1. Basic Usage

```julia
using EchidnaML

# Create vocabulary from training corpus
corpus = ["theorem example : ∀ x, P x → Q x", "lemma test : A ∧ B → C", ...]
vocab = create_vocabulary(corpus, min_freq=2, max_vocab=50000)

# Create neural solver
solver = create_solver(vocab)

# Define proof state
goal = ProofState(
    LEAN,  # Prover type
    "∀ x, P x → Q x",  # Goal
    ["P : Type", "Q : Type"],  # Context
    ["h1 : ∀ x, P x"],  # Hypotheses
    String[],
    0,
    Dict{String, Any}()
)

# Available premises
premises = [
    Premise("modus_ponens", "∀ P Q, (P → Q) → P → Q", LEAN, nothing, 0.8f0, 0.0f0),
    Premise("forall_intro", "∀ P, (∀ x, P x) → P a", LEAN, nothing, 0.6f0, 0.0f0),
    # ... more premises
]

# Predict relevant premises
ranking = predict_premises(solver, goal, premises, top_k=10)

# Display results
for (premise, score) in zip(ranking.premises, ranking.scores)
    println("$(premise.name): $(score)")
end
```

### 2. Training

```julia
using EchidnaML

# Load training data
train_data, val_data = load_training_data("path/to/data", train_split=0.8)

# Create solver
vocab = create_vocabulary(training_corpus)
solver = create_solver(vocab)

# Configure training
config = TrainingConfig(
    num_epochs=100,
    learning_rate=1f-4,
    lr_schedule=:cosine,
    early_stopping_patience=10,
    checkpoint_every=5,
    save_dir="checkpoints"
)

# Train
metrics = train_solver!(solver, train_data, val_data, config=config)

# Save model
save_solver(solver, "trained_models/echidna_v1")
```

### 3. Inference

```julia
using EchidnaML

# Load trained model
solver = load_solver("trained_models/echidna_v1")

# Create inference cache
cache = InferenceCache(1000)

# Interactive suggestion with diversity
ranking = suggest_next_step(
    solver,
    current_proof_state,
    available_premises,
    top_k=5,
    use_diversity=true,
    estimate_uncertainty=true
)

# Beam search for proof exploration
beam = beam_search_premises(
    solver,
    initial_state,
    available_premises,
    beam_width=5,
    max_depth=10
)

# Extract proof path from best beam node
proof_path = extract_proof_path(beam[1])
```

### 4. HTTP API Server

```julia
using EchidnaML

# Start server
start_api_server(
    "trained_models/echidna_v1",
    port=8080,
    host="0.0.0.0",
    cache_size=1000,
    async=true
)

# Server runs at http://localhost:8080
```

#### API Endpoints

**Health Check**
```bash
curl http://localhost:8080/health
```

**Predict Premises**
```bash
curl -X POST http://localhost:8080/predict \
  -H "Content-Type: application/json" \
  -d '{
    "goal": "∀ x, P x → Q x",
    "context": ["P : Type", "Q : Type"],
    "hypotheses": ["h1 : ∀ x, P x"],
    "available_premises": [
      {"name": "mp", "statement": "P → Q → (P → Q)"},
      {"name": "ax1", "statement": "P → (Q → P)"}
    ],
    "prover": "lean",
    "top_k": 10,
    "min_confidence": 0.1,
    "use_cache": true
  }'
```

**Interactive Suggestion**
```bash
curl -X POST http://localhost:8080/suggest \
  -H "Content-Type: application/json" \
  -d '{
    "goal": "theorem_statement",
    "context": ["context"],
    "hypotheses": ["hyps"],
    "available_premises": [...],
    "prover": "coq",
    "top_k": 5,
    "use_diversity": true,
    "estimate_uncertainty": true
  }'
```

**List Provers**
```bash
curl http://localhost:8080/provers
```

**Metrics**
```bash
curl http://localhost:8080/metrics
```

## Architecture Details

### Text Encoder

- **Embeddings**: Learned token embeddings with positional encoding
- **Transformer**: Multi-head self-attention (8 heads, 6 layers)
- **Dimensions**: 512-dim embeddings, 1024-dim hidden states
- **Prover-Specific**: Custom tokenizers for each prover's syntax

### Graph Neural Network

- **Node Types**: Premises, theorems, goals
- **Edge Types**: Dependencies, implications, similarities
- **Layers**: 4 Graph Attention (GAT) layers with residual connections
- **Aggregation**: Neighborhood aggregation with learned attention weights

### Premise Ranking

- **Cross-Attention**: Goal queries premise candidates
- **Scoring**: MLP combines goal and premise features
- **Loss**: Combined ranking loss + contrastive learning (InfoNCE)
- **Output**: Scores in [0, 1] indicating premise relevance

### Diversity & Confidence

- **Diversity**: Maximum Marginal Relevance (MMR) for varied suggestions
- **Confidence**: Monte Carlo dropout for uncertainty estimation
- **Caching**: LRU cache for repeated queries

## Performance Optimization

### GPU Acceleration

Automatically uses CUDA if available:

```julia
# Check GPU status
using CUDA
CUDA.functional()  # true if GPU available

# Move model to GPU (automatic in create_solver if GPU detected)
solver = gpu(solver)
```

### Batch Processing

Process multiple requests efficiently:

```julia
requests = BatchInferenceRequest(goals, premises, top_k)
results = predict_premises_batch(solver, requests)
```

### Inference Caching

```julia
cache = InferenceCache(1000)  # Cache 1000 most recent queries

ranking = predict_premises(
    solver, goal, premises,
    use_cache=true,
    cache=cache
)

# Check cache stats
stats = cache_stats(cache)
println("Hit rate: $(stats.hit_rate)")
```

## Quality Assurance

### Running Tests

```julia
# From Julia REPL
using Pkg
Pkg.test("EchidnaML")
```

### Static Analysis

```julia
using JET
@report_opt create_solver(vocab)
```

### Dependency Security

```julia
using Aqua
Aqua.test_all(EchidnaML)
```

### Coverage

```julia
using Coverage
coverage = process_folder()
```

## Prover-Specific Features

### Metamath (Tier 2 - Easiest!)

```julia
# Metamath uses plain text RPN notation
goal = ProofState(METAMATH, "|- ( ph -> ph )", ...)
premises = [Premise("ax-1", "|- ( ph -> ( ps -> ph ) )", METAMATH, ...)]
```

### Lean 4

```julia
# Modern dependent type theory
goal = ProofState(LEAN, "∀ x, P x → Q x", ...)
```

### Isabelle/HOL

```julia
# Higher-order logic
goal = ProofState(ISABELLE, "⟦ P; Q ⟧ ⟹ P ∧ Q", ...)
```

### SMT Solvers (Z3, CVC5)

```julia
# SMT-LIB format
goal = ProofState(Z3, "(assert (forall ((x Int)) (> x 0)))", ...)
```

## Integration with ECHIDNA

### Rust FFI

The Julia components integrate with ECHIDNA's Rust core via FFI:

```rust
// In Rust (echidna_provers.rs)
use echidna_julia_ffi::predict_premises;

let ranking = predict_premises(goal, premises, top_k)?;
```

### ReScript UI

The HTTP API serves the ReScript+Deno frontend:

```rescript
// In ReScript
let response = await fetch("/predict", {
  method: "POST",
  body: JSON.stringify(request)
})
```

## Deployment

### Podman Container

```bash
# Build container
podman build -t echidna-ml -f Containerfile.julia .

# Run server
podman run -p 8080:8080 \
  -v ./trained_models:/models:ro \
  echidna-ml \
  julia --project=/app -e 'using EchidnaML; start_api_server("/models/echidna_v1")'
```

### Justfile Integration

```bash
# From project root
just julia-train      # Train model
just julia-serve      # Start API server
just julia-test       # Run tests
just julia-check      # Quality checks
```

## Roadmap

### Current Status (v0.1.0)

✅ Complete architecture implementation
✅ All 12 prover encoders
✅ Training pipeline
✅ Inference engine
✅ HTTP API server

### Next Steps

- [ ] Implement actual data loaders for each prover
- [ ] Train initial models on theorem datasets
- [ ] Add prover-specific optimizations
- [ ] Implement proof state updates after premise application
- [ ] Add streaming inference for long proofs
- [ ] Multi-GPU distributed training
- [ ] Model compression for edge deployment

## Contributing

See `/home/user/echidna/CLAUDE.md` for contribution guidelines.

### Code Style

- Use descriptive variable names
- Add docstrings to all public functions
- Include type annotations
- Write tests for new features
- Run quality checks before committing

### Testing New Provers

To add support for a new prover:

1. Add enum variant to `ProverType` in `EchidnaML.jl`
2. Implement `ProverEncoder` subtype in `encoder.jl`
3. Add tokenization rules
4. Add test cases
5. Update documentation

## License

Dual licensed under:
- MIT License
- Palimpsest v0.6

See LICENSE files for details.

## Support

- Issues: GitLab issue tracker at https://gitlab.com/non-initiate/rhodinised/quill
- Documentation: See `/home/user/echidna/docs/`
- ECHIDNA Project: https://gitlab.com/non-initiate/rhodinised/quill

## References

- Quill (original Agda-only system): https://gitlab.com/non-initiate/rhodinised/quill
- Flux.jl: https://fluxml.ai/
- GraphNeuralNetworks.jl: https://github.com/CarloLucibello/GraphNeuralNetworks.jl
- Oxygen.jl: https://github.com/ndortega/Oxygen.jl

---

**Built with Julia. No Python. Pure power.**
