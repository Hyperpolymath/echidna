# ECHIDNA Agentic Features

## Overview

ECHIDNA's agentic theorem proving system provides autonomous, self-improving proof search with multi-agent collaboration, neural guidance, and symbolic verification. This document describes the architecture, components, and usage of the agentic features.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         Agent Core                              │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐         │
│  │ Goal Queue   │  │   Planner    │  │    Router    │         │
│  │  (Priority)  │  │ (HTN-based)  │  │ (Learning)   │         │
│  └──────────────┘  └──────────────┘  └──────────────┘         │
│         ↓                 ↓                  ↓                  │
│  ┌──────────────────────────────────────────────────┐          │
│  │            Proof Memory (SQLite)                 │          │
│  │  - Successful proofs (cached)                    │          │
│  │  - Failed attempts (reflection)                  │          │
│  │  - Aspect-based similarity search                │          │
│  └──────────────────────────────────────────────────┘          │
└─────────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────────┐
│                   Multi-Agent System (Actix)                    │
│  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐   │
│  │ ProverAgent(s) │  │ ContextAgent   │  │  LemmaAgent    │   │
│  │ - Z3           │  │ - ConceptNet   │  │ - Generates    │   │
│  │ - Lean         │  │ - Common-sense │  │   auxiliary    │   │
│  │ - Coq          │  │   knowledge    │  │   lemmas       │   │
│  │ - ...          │  └────────────────┘  └────────────────┘   │
│  └────────────────┘                                            │
│         ↓                     ↓                     ↓           │
│  ┌─────────────────────────────────────────────────────────┐  │
│  │            CoordinatorAgent                             │  │
│  │  - Parallel proof search                               │  │
│  │  - Message passing between agents                      │  │
│  └─────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────────┐
│              Neural-Symbolic Feedback Loop (Julia)              │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  Reinforcement Learning (ReinforcementLearning.jl)       │  │
│  │  - State: Proof state + aspects                          │  │
│  │  - Action: Tactic selection                              │  │
│  │  - Reward: Success (+1.0) / Failure (-0.1) / Time        │  │
│  └──────────────────────────────────────────────────────────┘  │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  Probabilistic Reasoning (Gen.jl)                        │  │
│  │  - Generative models for proof synthesis                 │  │
│  │  - Tactic probability distributions                      │  │
│  │  - Confidence estimation                                 │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

## Core Components

### 1. Agent Core (`src/rust/agent/mod.rs`)

The central autonomous agent that coordinates theorem proving.

**Key Features:**
- **Priority Queue**: Goals are processed by priority (Critical > High > Medium > Low)
- **Autonomous Loop**: Continuously processes goals without human intervention
- **Reflection**: Learns from successes and failures
- **Decomposition**: Breaks complex goals into simpler sub-goals
- **Memory Integration**: Caches successful proofs for reuse

**Configuration:**
```rust
AgentConfig {
    max_concurrent: 4,        // Parallel goals
    max_attempts: 3,          // Retry limit
    timeout_secs: 300,        // 5 minute timeout
    neural_enabled: true,     // Use ML guidance
    reflection_enabled: true, // Learn from failures
    planning_enabled: true,   // Decompose goals
}
```

**Usage:**
```rust
use echidna::agent::{AgentCore, AgentConfig, AgenticGoal, Priority};

let agent = AgentCore::new(
    memory,
    planner,
    router,
    provers,
    AgentConfig::default(),
);

// Add a goal
agent.add_goal(AgenticGoal {
    goal: Goal { /* ... */ },
    priority: Priority::High,
    attempts: 0,
    max_attempts: 3,
    preferred_prover: Some(ProverKind::Lean),
    aspects: vec!["algebra".to_string()],
    parent: None,
}).await?;

// Run autonomous loop (non-blocking)
tokio::spawn(async move {
    agent.run().await
});
```

### 2. Proof Memory (`src/rust/agent/memory.rs`)

SQLite-based storage for successful proofs and failures.

**Key Features:**
- **Success Caching**: Store proofs for instant retrieval
- **Failure Tracking**: Remember what didn't work
- **Similarity Search**: Find similar proofs by aspect overlap
- **Statistics**: Success rates, average times, total proofs

**Schema:**
```sql
CREATE TABLE successes (
    id INTEGER PRIMARY KEY,
    goal_id TEXT,
    target_term TEXT,
    aspects TEXT,
    prover TEXT,
    proof_script TEXT,
    time_ms INTEGER,
    timestamp TEXT
);

CREATE TABLE failures (
    id INTEGER PRIMARY KEY,
    goal_id TEXT,
    target_term TEXT,
    aspects TEXT,
    prover TEXT,
    reason TEXT,
    timestamp TEXT
);
```

**Usage:**
```rust
use echidna::agent::memory::SqliteMemory;

let memory = SqliteMemory::new("proofs.db").await?;

// Store success
memory.store_success(&goal, &proof, ProverKind::Lean).await?;

// Find similar proof
if let Some(cached) = memory.find_similar(&goal).await? {
    println!("Found cached proof from {:?}", cached.prover);
}

// Get stats
let stats = memory.stats().await?;
println!("Success rate: {:.2}%", stats.success_rate * 100.0);
```

### 3. Dynamic Prover Router (`src/rust/agent/router.rs`)

Learns which provers work best for different types of goals.

**Key Features:**
- **Aspect-Based Scoring**: Matches goal aspects to prover strengths
- **Success/Failure Tracking**: Per-prover, per-aspect statistics
- **Dynamic Selection**: Adapts based on historical performance
- **Score Formula**: `score = success_rate * (1 / log(avg_time))`

**Usage:**
```rust
use echidna::agent::router::ProverRouter;

let router = ProverRouter::new();

// Record outcomes
router.record_success(&goal, ProverKind::Lean).await;
router.record_failure(&goal, ProverKind::Z3).await;

// Select best prover
let prover = router.select_async(&goal).await;
println!("Selected {:?} for goal with aspects {:?}", prover, goal.aspects);
```

**Aspect Examples:**
- `algebra`, `group_theory`, `ring_theory`
- `logic`, `propositional`, `first_order`
- `type_theory`, `dependent_types`
- `analysis`, `calculus`, `topology`
- `category_theory`, `functors`, `monads`

### 4. Hierarchical Planner (`src/rust/agent/planner.rs`)

Decomposes complex goals into manageable sub-goals.

**Decomposition Rules:**
1. **Implication (A → B)**: Decompose into "Prove B assuming A"
2. **Conjunction (A ∧ B)**: Decompose into "Prove A" + "Prove B"
3. **Universal (∀x. P(x))**: Introduce variable, prove P(x)

**Usage:**
```rust
use echidna::agent::planner::RulePlanner;

let planner = RulePlanner::new();

// Decompose complex goal
let sub_goals = planner.decompose(&goal).await?;

for sub_goal in sub_goals {
    println!("Sub-goal: {}", sub_goal.goal.id);
}
```

### 5. Multi-Agent System (`src/rust/agent/actors.rs`)

Actix-based actor system for parallel proof search.

**Actors:**
- **ProverAgent**: Wraps a prover backend, handles `ProveGoal` messages
- **ContextAgent**: Queries ConceptNet for common-sense knowledge
- **LemmaAgent**: Generates auxiliary lemmas
- **CoordinatorAgent**: Orchestrates parallel proof attempts

**Usage:**
```rust
use echidna::agent::actors::MultiAgentSystem;

let system = MultiAgentSystem::new(vec![
    (ProverKind::Z3, z3_backend),
    (ProverKind::Lean, lean_backend),
    (ProverKind::Coq, coq_backend),
]);

// Parallel proof search
let (proof, prover) = system.prove(goal, true).await?;
println!("Proved with {:?}", prover);
```

### 6. Explanations (`src/rust/agent/explanations.rs`)

Template-based human-readable explanations.

**Explanation Types:**
- **Proof Failure**: Why a proof attempt failed + suggestions
- **Prover Selection**: Why a particular prover was chosen
- **Goal Decomposition**: How a goal was broken down
- **Tactic Selection**: Why a specific tactic was chosen
- **Proof Success**: Summary of successful proof

**Usage:**
```rust
use echidna::agent::explanations::ExplanationGenerator;

let generator = ExplanationGenerator::new();

// Explain failure
let exp = generator.explain_failure(&goal, "timeout", Some(ProverKind::Coq));
println!("{}", exp.format());

// Explain success
let exp = generator.explain_success(&goal, ProverKind::Lean, 150);
println!("{}", exp.format());
```

**Example Output:**
```
# Proof Attempt Failed

The proof attempt for 'goal_123' failed using prover Coq. timeout

## Details

- **Goal ID**: goal_123
- **Target**: ∀x:A. P(x)
- **Attempts**: 2
- **Priority**: High
- **Prover**: Coq

## Suggestions

- Try decomposing the goal into smaller sub-goals
- Use a faster prover (Z3 or CVC5)
- Simplify the goal using lemmas
```

## Julia ML Components

### 7. Reinforcement Learning (`src/julia/rl/training.jl`)

Trains neural models from symbolic feedback.

**Environment:**
- **State**: Proof state + aspect vector
- **Action**: Tactic selection
- **Reward**: +1.0 (success), -0.1 (failure), -time_penalty

**Training Loop:**
```julia
using EchidnaML.RLTraining

env = RLEnvironment(
    db_path="proofs.db",
    model_path="models/rl_agent.bson",
    aspects=["algebra", "logic", "type_theory"]
)

# Train from proof history
train_agent!(env, epochs=100, batch_size=32)

# Save model
save_model(env, "models/rl_agent_v2.bson")
```

### 8. Probabilistic Reasoning (`src/julia/probabilistic/gen_reasoning.jl`)

Gen.jl-based probabilistic models for proof synthesis.

**Generative Model:**
```julia
@gen function theorem_proving_model(goal::String, context::Vector{String})
    num_tactics = @trace(geometric(0.3), :num_tactics) + 1
    tactics = String[]

    for i in 1:num_tactics
        tactic_idx = @trace(categorical([0.3, 0.2, 0.15, 0.15, 0.1, 0.1]),
                            Symbol("tactic_", i))
        push!(tactics, tactic_names[tactic_idx])
    end

    success = @trace(bernoulli(success_prob), :success)
    (tactics, success)
end
```

**Usage:**
```julia
using EchidnaML.ProbabilisticReasoning

# Infer likely proof steps
candidates = infer_proof_steps(
    "∀x. P(x) → Q(x)",
    ["hypothesis: P(a)", "hypothesis: a : A"],
    num_samples=100
)

# Rank candidates
ranked = rank_candidates_probabilistic(
    [["intro", "apply"], ["assumption"]],
    goal,
    context
)

# Estimate confidence
(mean_prob, std_prob) = estimate_confidence(
    ["intro", "apply", "reflexivity"],
    goal,
    context,
    num_samples=1000
)
```

## Integration with ConceptNet

The `ContextAgent` queries ConceptNet for common-sense knowledge to augment theorem proving.

**Example:**
```rust
// Goal: "Prove every group has an identity element"
// ConceptNet query: "group", "identity", "element"
// Returns: ["inverse", "associativity", "closure", "binary_operation", ...]
```

**API Usage:**
```rust
use echidna::integrations::ConceptNetClient;

let client = ConceptNetClient::new();

// Get related concepts
let edges = client.related_concepts("group").await?;
for edge in edges {
    println!("{} --({})-> {}",
             edge.start.label,
             edge.rel.label,
             edge.end.label);
}

// Augment theorem
let related = client.augment_theorem(
    "Prove that every group has an identity element"
).await?;
println!("Related concepts: {:?}", related);
```

## Workflow

### Typical Agentic Proof Workflow

```
1. User submits goal
   ↓
2. Agent Core adds to priority queue
   ↓
3. Agent checks memory for similar proofs
   ├─ Found → Return cached proof ✓
   └─ Not found → Continue
   ↓
4. Planner evaluates goal complexity
   ├─ Simple → Continue
   └─ Complex → Decompose into sub-goals → Go to step 2
   ↓
5. Router selects best prover based on aspects
   ↓
6. Multi-Agent System coordinates parallel search
   ├─ ProverAgents attempt proof
   ├─ ContextAgent queries ConceptNet
   └─ LemmaAgent generates auxiliary lemmas
   ↓
7. Symbolic verification
   ├─ Success → Store in memory, update router (+) ✓
   └─ Failure → Store failure, update router (-), retry
   ↓
8. Reflection & Learning
   ├─ Update router statistics
   ├─ Train RL model (Julia)
   └─ Update probabilistic models (Gen.jl)
   ↓
9. Generate human explanation
```

## Testing

Run integration tests:
```bash
cargo test --test agentic_integration
```

Tests cover:
- Proof memory storage/retrieval
- Router aspect-based learning
- Goal decomposition
- Priority queue ordering
- Explanation generation
- Failure tracking
- Multi-prover coordination

## Configuration

### Environment Variables

```bash
# Database path
export ECHIDNA_PROOF_DB="proofs.db"

# ConceptNet API
export CONCEPTNET_API_BASE="https://api.conceptnet.io"

# Model paths
export ECHIDNA_RL_MODEL="models/rl_agent.bson"
export ECHIDNA_GEN_MODEL="models/gen_model.bson"

# Agent config
export ECHIDNA_MAX_ATTEMPTS=3
export ECHIDNA_TIMEOUT_SECS=300
export ECHIDNA_MAX_CONCURRENT=4
```

### Config File (TOML)

```toml
[agent]
max_concurrent = 4
max_attempts = 3
timeout_secs = 300
neural_enabled = true
reflection_enabled = true
planning_enabled = true

[memory]
database_path = "proofs.db"
cache_size = 1000

[router]
default_prover = "Lean"
aspect_weight = 0.7
time_weight = 0.3

[multiagent]
parallel_search = true
context_augmentation = true
lemma_generation = false  # Experimental

[rl]
model_path = "models/rl_agent.bson"
training_epochs = 100
batch_size = 32

[gen]
model_path = "models/gen_model.bson"
num_samples = 100
confidence_threshold = 0.7
```

## Performance Optimization

### Memory Optimization
- **Limit cache size**: Set `cache_size` to prevent unbounded memory growth
- **Periodic cleanup**: Remove old failures after threshold

### Speed Optimization
- **Parallel mode**: Enable parallel proof search for independent goals
- **Fast provers first**: Z3 and CVC5 for decidable sub-problems
- **Early termination**: Stop on first success in parallel mode

### Learning Optimization
- **Batch training**: Train RL model periodically, not per-proof
- **Aspect granularity**: Use specific aspects for better router accuracy
- **Prune statistics**: Remove low-confidence prover-aspect pairs

## Troubleshooting

### "No prover succeeded"
- Check aspect tags are descriptive
- Increase `max_attempts`
- Enable `planning_enabled` for decomposition
- Review goal formulation

### "Timeout on all attempts"
- Decompose goal manually
- Use faster provers (Z3, CVC5)
- Increase `timeout_secs`
- Simplify goal or add lemmas

### "Memory growing unbounded"
- Set `cache_size` limit
- Run periodic cleanup
- Archive old proofs to separate database

### "Router always selects same prover"
- Need more training data
- Check aspect distribution
- Reset router statistics if biased

## Future Enhancements

### Planned Features
1. **Human-in-the-Loop**: Interactive proof repair
2. **Proof Sketching**: Partial proofs with holes
3. **Multi-Objective RL**: Optimize for speed + correctness + readability
4. **Distributed Agents**: Proof search across multiple machines
5. **Proof Compression**: Minimize proof script length
6. **Explanation Refinement**: NLG for more detailed explanations

### Research Directions
1. **Neural Theorem Proving**: Full end-to-end neural models
2. **Transfer Learning**: Cross-domain proof transfer
3. **Meta-Learning**: Few-shot adaptation to new domains
4. **Causal Reasoning**: Why proofs succeed or fail
5. **Adversarial Training**: Robustness to malformed goals

## References

1. **ConceptNet**: https://conceptnet.io/
2. **Gen.jl**: https://www.gen.dev/
3. **ReinforcementLearning.jl**: https://github.com/JuliaReinforcementLearning/ReinforcementLearning.jl
4. **Actix**: https://actix.rs/
5. **Neurosymbolic AI**: [Combining Logic and Learning (Survey)](https://arxiv.org/abs/2202.01364)

## License

MIT AND Palimpsest-0.6

---

**ECHIDNA Project Team**
Last Updated: 2025-11-22
