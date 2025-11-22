# SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
# SPDX-License-Identifier: MIT AND Palimpsest-0.6

"""
    models/neural_solver.jl

Universal Neural Premise Selector

Combines Graph Neural Networks (GNN) and Transformer architecture
to rank premises for theorem proving across all 12 supported provers.

Architecture:
1. GNN: Models relationships between premises, theorems, and proof states
2. Transformer: Captures sequential dependencies in proof search
3. Attention: Cross-attention between goal and premise candidates
4. Ranking: Scores premises by relevance to current proof state

Generalizes Quill's Agda-specific architecture to universal multi-prover system.
"""

using Flux
using GraphNeuralNetworks
using Graphs
using SimpleWeightedGraphs
using NNlib
using Statistics
using LinearAlgebra
using Random

# ============================================================================
# Graph Construction
# ============================================================================

"""
    TheoremGraph

Graph representation of theorem dependencies and relationships.
Nodes: Theorems, premises, proof states
Edges: Dependencies, implications, similarity
"""
struct TheoremGraph
    graph::SimpleWeightedDiGraph{Int, Float32}
    node_features::Matrix{Float32}  # (feature_dim, num_nodes)
    node_types::Vector{Symbol}       # :theorem, :premise, :goal
    node_names::Vector{String}
    prover::ProverType
end

"""
    build_theorem_graph(premises::Vector{Premise}, goal::ProofState)

Construct a graph from premises and current proof goal.
"""
function build_theorem_graph(premises::Vector{Premise}, goal::ProofState, embeddings::Matrix{Float32})
    num_premises = length(premises)
    num_nodes = num_premises + 1  # premises + goal

    # Create weighted directed graph
    g = SimpleWeightedDiGraph(num_nodes)

    # Add edges based on premise relationships
    # 1. Goal -> Premise edges (potential applications)
    for i in 1:num_premises
        add_edge!(g, num_nodes, i, 1.0f0)  # Goal is last node
    end

    # 2. Premise -> Premise edges (dependencies)
    # Use embedding similarity to determine relationships
    for i in 1:num_premises
        for j in 1:num_premises
            if i != j
                # Compute cosine similarity between embeddings
                sim = dot(embeddings[:, i], embeddings[:, j]) /
                      (norm(embeddings[:, i]) * norm(embeddings[:, j]))
                if sim > 0.5f0  # Threshold for creating edge
                    add_edge!(g, i, j, Float32(sim))
                end
            end
        end
    end

    # Node features from embeddings
    node_features = embeddings

    # Node types
    node_types = vcat(fill(:premise, num_premises), [:goal])

    # Node names
    node_names = vcat([p.name for p in premises], ["__GOAL__"])

    return TheoremGraph(g, node_features, node_types, node_names, goal.prover)
end

# ============================================================================
# Graph Neural Network Layers
# ============================================================================

"""
    GCNLayer

Graph Convolutional Network layer for message passing on theorem graphs.
"""
struct GCNLayer
    weight::Dense
    bias::Bool
    activation::Function
end

Flux.@functor GCNLayer

function GCNLayer(in_dim::Int, out_dim::Int; bias::Bool=true, activation=relu)
    weight = Dense(in_dim, out_dim, bias=bias)
    return GCNLayer(weight, bias, activation)
end

function (layer::GCNLayer)(g::TheoremGraph, x::AbstractMatrix)
    # Graph convolution: aggregate neighbor features
    adj = adjacency_matrix(g.graph)

    # Add self-loops
    adj_with_self = adj + I(size(adj, 1))

    # Symmetric normalization: D^(-1/2) * A * D^(-1/2)
    d = vec(sum(adj_with_self, dims=2))
    d_inv_sqrt = 1.0f0 ./ sqrt.(d .+ 1f-10)
    d_mat_inv_sqrt = Diagonal(d_inv_sqrt)

    adj_normalized = d_mat_inv_sqrt * adj_with_self * d_mat_inv_sqrt

    # Apply convolution
    x_agg = adj_normalized * x'  # (num_nodes, feature_dim)
    x_agg = x_agg'  # (feature_dim, num_nodes)

    # Apply weight transformation
    out = layer.weight(x_agg)

    return layer.activation.(out)
end

"""
    GraphAttentionLayer

Graph Attention Network (GAT) layer with multi-head attention.
"""
struct GraphAttentionLayer
    num_heads::Int
    head_dim::Int
    query_proj::Dense
    key_proj::Dense
    value_proj::Dense
    output_proj::Dense
    attention_weights::Vector{Dense}
    dropout::Dropout
end

Flux.@functor GraphAttentionLayer

function GraphAttentionLayer(in_dim::Int, out_dim::Int, num_heads::Int=4; dropout::Float32=0.1f0)
    head_dim = out_dim ÷ num_heads

    query_proj = Dense(in_dim, out_dim)
    key_proj = Dense(in_dim, out_dim)
    value_proj = Dense(in_dim, out_dim)
    output_proj = Dense(out_dim, out_dim)

    # Attention weight computation for each head
    attention_weights = [Dense(2 * head_dim, 1) for _ in 1:num_heads]

    dropout_layer = Dropout(dropout)

    return GraphAttentionLayer(
        num_heads, head_dim, query_proj, key_proj, value_proj,
        output_proj, attention_weights, dropout_layer
    )
end

function (layer::GraphAttentionLayer)(g::TheoremGraph, x::AbstractMatrix)
    num_nodes = size(x, 2)

    # Project to Q, K, V
    Q = layer.query_proj(x)  # (out_dim, num_nodes)
    K = layer.key_proj(x)
    V = layer.value_proj(x)

    # Reshape for multi-head attention
    Q_heads = reshape(Q, layer.head_dim, layer.num_heads, num_nodes)
    K_heads = reshape(K, layer.head_dim, layer.num_heads, num_nodes)
    V_heads = reshape(V, layer.head_dim, layer.num_heads, num_nodes)

    # Compute attention for each head
    outputs = []
    for h in 1:layer.num_heads
        q = Q_heads[:, h, :]  # (head_dim, num_nodes)
        k = K_heads[:, h, :]
        v = V_heads[:, h, :]

        # Attention scores
        scores = q' * k  # (num_nodes, num_nodes)
        scores = scores ./ sqrt(Float32(layer.head_dim))

        # Mask based on graph edges
        edge_mask = adjacency_matrix(g.graph) .> 0
        scores = scores .* edge_mask .+ (1.0f0 .- edge_mask) .* (-1f10)

        # Softmax attention
        attn = softmax(scores, dims=2)
        attn = layer.dropout(attn)

        # Apply attention to values
        out = v * attn'  # (head_dim, num_nodes)
        push!(outputs, out)
    end

    # Concatenate heads
    concat_out = vcat(outputs...)  # (out_dim, num_nodes)

    # Output projection
    final_out = layer.output_proj(concat_out)

    return final_out
end

"""
    GNNEncoder

Multi-layer Graph Neural Network for encoding theorem graphs.
"""
struct GNNEncoder
    layers::Vector{Union{GCNLayer, GraphAttentionLayer}}
    layer_norms::Vector{LayerNorm}
    dropout::Dropout
end

Flux.@functor GNNEncoder

function GNNEncoder(in_dim::Int, hidden_dim::Int, num_layers::Int;
                    use_attention::Bool=true, dropout::Float32=0.1f0)
    layers = []
    layer_norms = []

    # First layer
    if use_attention
        push!(layers, GraphAttentionLayer(in_dim, hidden_dim, 4, dropout=dropout))
    else
        push!(layers, GCNLayer(in_dim, hidden_dim))
    end
    push!(layer_norms, LayerNorm(hidden_dim))

    # Hidden layers
    for _ in 2:num_layers
        if use_attention
            push!(layers, GraphAttentionLayer(hidden_dim, hidden_dim, 4, dropout=dropout))
        else
            push!(layers, GCNLayer(hidden_dim, hidden_dim))
        end
        push!(layer_norms, LayerNorm(hidden_dim))
    end

    return GNNEncoder(layers, layer_norms, Dropout(dropout))
end

function (encoder::GNNEncoder)(g::TheoremGraph)
    x = g.node_features

    for (layer, norm) in zip(encoder.layers, encoder.layer_norms)
        # Apply GNN layer with residual connection
        x_new = layer(g, x)
        x_new = norm(x_new)
        x = x .+ encoder.dropout(x_new)  # Residual
    end

    return x
end

# ============================================================================
# Premise Ranking Network
# ============================================================================

"""
    PremiseRanker

Neural network that ranks premises based on relevance to proof goal.
Combines GNN-encoded graph features with cross-attention.
"""
struct PremiseRanker
    gnn_encoder::GNNEncoder
    goal_encoder::Dense
    premise_encoder::Dense
    cross_attention::MultiHeadAttention
    score_mlp::Chain
end

Flux.@functor PremiseRanker

function PremiseRanker(feature_dim::Int, hidden_dim::Int, num_gnn_layers::Int=4)
    gnn_encoder = GNNEncoder(feature_dim, hidden_dim, num_gnn_layers, use_attention=true)

    goal_encoder = Dense(hidden_dim, hidden_dim)
    premise_encoder = Dense(hidden_dim, hidden_dim)

    cross_attention = MultiHeadAttention(hidden_dim, 8)

    score_mlp = Chain(
        Dense(hidden_dim * 2, hidden_dim, relu),
        Dropout(0.1f0),
        Dense(hidden_dim, hidden_dim ÷ 2, relu),
        Dense(hidden_dim ÷ 2, 1),
        x -> sigmoid.(x)
    )

    return PremiseRanker(gnn_encoder, goal_encoder, premise_encoder, cross_attention, score_mlp)
end

function (ranker::PremiseRanker)(g::TheoremGraph)
    # Encode graph with GNN
    node_embeddings = ranker.gnn_encoder(g)  # (hidden_dim, num_nodes)

    # Split into premise and goal embeddings
    num_premises = length(node_embeddings[1, :]) - 1
    premise_embeds = node_embeddings[:, 1:num_premises]  # (hidden_dim, num_premises)
    goal_embed = node_embeddings[:, end:end]  # (hidden_dim, 1)

    # Encode goal and premises
    goal_enc = ranker.goal_encoder(goal_embed)
    premise_enc = ranker.premise_encoder(premise_embeds)

    # Cross-attention: goal queries premise candidates
    attn_out = ranker.cross_attention(goal_enc, premise_enc, premise_enc)  # (hidden_dim, 1)

    # Combine goal and attended premises for scoring
    # Broadcast goal to match premise dimensions
    goal_broadcast = repeat(goal_enc, 1, num_premises)
    combined = vcat(goal_broadcast, premise_enc)  # (2*hidden_dim, num_premises)

    # Score each premise
    scores = ranker.score_mlp(combined)  # (1, num_premises)

    return vec(scores)  # (num_premises,)
end

"""
    MultiHeadAttention

Standard multi-head attention mechanism.
"""
struct MultiHeadAttention
    num_heads::Int
    head_dim::Int
    qkv_proj::Dense
    out_proj::Dense
    dropout::Dropout
end

Flux.@functor MultiHeadAttention

function MultiHeadAttention(d_model::Int, num_heads::Int; dropout::Float32=0.1f0)
    head_dim = d_model ÷ num_heads
    qkv_proj = Dense(d_model, 3 * d_model)
    out_proj = Dense(d_model, d_model)
    dropout_layer = Dropout(dropout)

    return MultiHeadAttention(num_heads, head_dim, qkv_proj, out_proj, dropout_layer)
end

function (mha::MultiHeadAttention)(Q::AbstractMatrix, K::AbstractMatrix, V::AbstractMatrix)
    # Q, K, V: (d_model, seq_len)
    seq_len_q = size(Q, 2)
    seq_len_kv = size(K, 2)

    # Project and reshape
    Q_proj = reshape(mha.qkv_proj(Q)[1:end÷3, :], mha.head_dim, mha.num_heads, seq_len_q)
    K_proj = reshape(mha.qkv_proj(K)[1:end÷3, :], mha.head_dim, mha.num_heads, seq_len_kv)
    V_proj = reshape(mha.qkv_proj(V)[end÷3+1:end, :], mha.head_dim, mha.num_heads, seq_len_kv)

    # Compute attention scores
    scores = zeros(Float32, seq_len_q, seq_len_kv, mha.num_heads)
    for h in 1:mha.num_heads
        scores[:, :, h] = (Q_proj[:, h, :]' * K_proj[:, h, :]) ./ sqrt(Float32(mha.head_dim))
    end

    # Softmax and apply to values
    attn_weights = softmax(scores, dims=2)
    attn_weights = mha.dropout(attn_weights)

    # Apply attention to values
    outputs = zeros(Float32, mha.head_dim, mha.num_heads, seq_len_q)
    for h in 1:mha.num_heads
        outputs[:, h, :] = V_proj[:, h, :] * attn_weights[:, :, h]'
    end

    # Concatenate heads and project
    concat_out = reshape(outputs, mha.head_dim * mha.num_heads, seq_len_q)
    final_out = mha.out_proj(concat_out)

    return final_out
end

# ============================================================================
# Complete Neural Solver
# ============================================================================

"""
    NeuralSolver

Complete neural solver combining text encoding, graph modeling, and premise ranking.
"""
struct NeuralSolver
    text_encoder::TextEncoder
    premise_ranker::PremiseRanker
    vocabulary::ProverVocabulary
    config::EchidnaConfig
end

Flux.@functor NeuralSolver

"""
    create_solver(vocab::ProverVocabulary; config::EchidnaConfig=get_config())

Create a new neural solver with specified configuration.
"""
function create_solver(vocab::ProverVocabulary; config::EchidnaConfig=get_config())
    text_encoder = TextEncoder(
        vocab.vocab_size,
        config.embedding_dim,
        config.hidden_dim,
        config.num_transformer_layers,
        config.dropout_rate
    )

    premise_ranker = PremiseRanker(
        config.embedding_dim,
        config.hidden_dim,
        config.gnn_num_layers
    )

    solver = NeuralSolver(text_encoder, premise_ranker, vocab, config)

    # Move to GPU if available
    if config.device === gpu
        solver = config.device(solver)
    end

    return solver
end

"""
    (solver::NeuralSolver)(goal::ProofState, premises::Vector{Premise})

Rank premises for a given proof goal.
Returns scores for each premise (higher = more relevant).
"""
function (solver::NeuralSolver)(goal::ProofState, premises::Vector{Premise})
    # Encode proof state
    goal_embedding = encode_proof_state(goal, solver.vocabulary, solver.text_encoder)

    # Encode all premises
    premise_embeddings = zeros(Float32, solver.config.embedding_dim, length(premises))
    for (i, premise) in enumerate(premises)
        # Create temporary proof state for premise
        premise_state = ProofState(
            premise.prover,
            premise.statement,
            String[],
            String[],
            String[],
            0,
            Dict{String, Any}()
        )
        premise_embeddings[:, i] = encode_proof_state(premise_state, solver.vocabulary, solver.text_encoder)
    end

    # Combine goal and premise embeddings
    all_embeddings = hcat(premise_embeddings, goal_embedding)

    # Build theorem graph
    graph = build_theorem_graph(premises, goal, all_embeddings)

    # Rank premises
    scores = solver.premise_ranker(graph)

    return scores
end

"""
    save_solver(solver::NeuralSolver, path::String)

Save trained solver to disk.
"""
function save_solver(solver::NeuralSolver, path::String)
    # Save model weights
    weights = Flux.state(solver)
    BSON.@save joinpath(path, "model.bson") weights

    # Save vocabulary
    BSON.@save joinpath(path, "vocabulary.bson") solver.vocabulary

    # Save config
    BSON.@save joinpath(path, "config.bson") solver.config

    @info "Solver saved to $path"
end

"""
    load_solver(path::String)

Load trained solver from disk.
"""
function load_solver(path::String)
    # Load vocabulary
    BSON.@load joinpath(path, "vocabulary.bson") vocabulary

    # Load config
    BSON.@load joinpath(path, "config.bson") config

    # Create solver
    solver = create_solver(vocabulary, config=config)

    # Load weights
    BSON.@load joinpath(path, "model.bson") weights
    Flux.loadmodel!(solver, weights)

    @info "Solver loaded from $path"
    return solver
end

export TheoremGraph, build_theorem_graph
export GCNLayer, GraphAttentionLayer, GNNEncoder
export PremiseRanker, MultiHeadAttention
export NeuralSolver, create_solver, save_solver, load_solver
