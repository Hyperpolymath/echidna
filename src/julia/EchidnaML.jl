# SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
# SPDX-License-Identifier: MIT AND Palimpsest-0.6

"""
    EchidnaML

ECHIDNA (Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance)
Machine Learning Module - Universal Neural Solver for 12 Theorem Provers

Generalizes Quill's Agda-specific neural architecture to support:
- Tier 1 (6): Agda, Coq/Rocq, Lean, Isabelle, Z3, CVC5
- Tier 2 (3): Metamath, HOL Light, Mizar
- Tier 3 (2): PVS, ACL2
- Tier 4 (1): HOL4

Architecture:
- Graph Neural Networks for theorem embeddings
- Transformer-based premise selection
- Multi-prover encoder/decoder
- Async HTTP API for inference

NO PYTHON - Pure Julia implementation with Flux.jl
"""
module EchidnaML

using Flux
using Zygote
using CUDA
using GraphNeuralNetworks
using Graphs
using Transformers
using NNlib
using Statistics
using LinearAlgebra
using Random
using Logging
using JSON3
using BSON
using Distributions
using Optimisers

# Export core functionality
export ProverType, ProofState, Premise, PremiseRanking
export encode_proof_state, decode_prediction
export NeuralSolver, create_solver, train_solver!, predict_premises
export start_api_server

# Prover enumeration - all 12 supported provers
@enum ProverType begin
    # Tier 1 - Primary targets (6)
    AGDA = 1
    COQ = 2
    ROCQ = 3  # Coq rebrand
    LEAN = 4
    ISABELLE = 5
    Z3 = 6
    CVC5 = 7

    # Tier 2 - "Big Six" completion (3)
    METAMATH = 8   # Easiest - start here!
    HOL_LIGHT = 9
    MIZAR = 10

    # Tier 3 - Advanced (2)
    PVS = 11
    ACL2 = 12

    # Tier 4 - Complex (1)
    HOL4 = 13
end

# Core data structures
"""
    ProofState

Represents the current state of a proof across any supported prover.
Contains prover-agnostic representation of goals, context, and available premises.
"""
struct ProofState
    prover::ProverType
    goal::String
    context::Vector{String}
    hypotheses::Vector{String}
    available_premises::Vector{String}
    proof_depth::Int
    metadata::Dict{String, Any}
end

"""
    Premise

Represents a theorem, lemma, or axiom available for use in a proof.
"""
struct Premise
    name::String
    statement::String
    prover::ProverType
    embedding::Union{Nothing, Vector{Float32}}
    frequency_score::Float32
    relevance_score::Float32
end

"""
    PremiseRanking

Result of neural premise selection - ranked list of relevant premises.
"""
struct PremiseRanking
    premises::Vector{Premise}
    scores::Vector{Float32}
    confidence::Float32
    prover::ProverType
end

# Configuration
"""
    EchidnaConfig

Global configuration for ECHIDNA ML system.
"""
mutable struct EchidnaConfig
    embedding_dim::Int
    hidden_dim::Int
    num_attention_heads::Int
    num_transformer_layers::Int
    gnn_num_layers::Int
    dropout_rate::Float32
    learning_rate::Float32
    batch_size::Int
    max_premises::Int
    device::Function  # cpu or gpu
    checkpoint_dir::String
    log_level::Logging.LogLevel
end

# Default configuration
const DEFAULT_CONFIG = EchidnaConfig(
    512,      # embedding_dim
    1024,     # hidden_dim
    8,        # num_attention_heads
    6,        # num_transformer_layers
    4,        # gnn_num_layers
    0.1f0,    # dropout_rate
    1f-4,     # learning_rate
    32,       # batch_size
    100,      # max_premises
    CUDA.functional() ? gpu : cpu,
    "checkpoints",
    Logging.Info
)

# Global config instance
const CONFIG = Ref{EchidnaConfig}(DEFAULT_CONFIG)

"""
    set_config!(; kwargs...)

Update global configuration with keyword arguments.
"""
function set_config!(; kwargs...)
    for (key, value) in kwargs
        if hasfield(EchidnaConfig, key)
            setfield!(CONFIG[], key, value)
        else
            @warn "Unknown configuration key: $key"
        end
    end
end

"""
    get_config()

Get current configuration.
"""
get_config() = CONFIG[]

# Include submodules
include("models/encoder.jl")
include("models/neural_solver.jl")
include("training/train.jl")
include("inference/predict.jl")
include("api/server.jl")

# Initialization
function __init__()
    # Set up logging
    global_logger(ConsoleLogger(stderr, CONFIG[].log_level))

    # Check CUDA availability
    if CUDA.functional()
        @info "CUDA available - using GPU acceleration"
        @info "CUDA version: $(CUDA.version())"
        @info "Device: $(CUDA.device())"
    else
        @info "CUDA not available - using CPU"
    end

    # Create checkpoint directory if it doesn't exist
    mkpath(CONFIG[].checkpoint_dir)

    @info "EchidnaML initialized - Universal Neural Solver for 12 Theorem Provers"
    @info "Architecture: GNN + Transformer | Framework: Flux.jl | Device: $(CUDA.functional() ? "GPU" : "CPU")"
end

end # module EchidnaML
