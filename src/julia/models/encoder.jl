# SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
# SPDX-License-Identifier: MIT AND Palimpsest-0.6

"""
    models/encoder.jl

Multi-Prover Proof State Encoder

Encodes proof states from all 12 supported theorem provers into a unified
vector representation for neural processing. Handles prover-specific syntax
and semantics while producing consistent embeddings.

Supported Provers:
- Tier 1: Agda, Coq/Rocq, Lean, Isabelle, Z3, CVC5
- Tier 2: Metamath, HOL Light, Mizar
- Tier 3: PVS, ACL2
- Tier 4: HOL4
"""

using Flux
using NNlib
using Transformers
using Statistics
using LinearAlgebra

# ============================================================================
# Tokenization & Vocabulary
# ============================================================================

"""
    ProverVocabulary

Unified vocabulary across all provers with prover-specific token mappings.
"""
mutable struct ProverVocabulary
    # Core vocabulary
    token_to_id::Dict{String, Int}
    id_to_token::Dict{Int, String}
    vocab_size::Int

    # Prover-specific vocabularies
    prover_tokens::Dict{ProverType, Set{String}}

    # Special tokens
    pad_token::String
    unk_token::String
    cls_token::String
    sep_token::String
    mask_token::String
end

"""
    create_vocabulary(corpus::Vector{String}; min_freq=2, max_vocab=50000)

Build vocabulary from training corpus with prover-specific tokens.
"""
function create_vocabulary(corpus::Vector{String}; min_freq=2, max_vocab=50000)
    # Initialize with special tokens
    special_tokens = ["<PAD>", "<UNK>", "<CLS>", "<SEP>", "<MASK>"]

    # Count token frequencies
    token_counts = Dict{String, Int}()
    for text in corpus
        for token in tokenize_text(text)
            token_counts[token] = get(token_counts, token, 0) + 1
        end
    end

    # Filter by frequency and limit size
    filtered_tokens = [t for (t, c) in token_counts if c >= min_freq]
    sort!(filtered_tokens, by=t -> token_counts[t], rev=true)
    filtered_tokens = filtered_tokens[1:min(length(filtered_tokens), max_vocab - length(special_tokens))]

    # Build vocabulary
    all_tokens = vcat(special_tokens, filtered_tokens)
    token_to_id = Dict(t => i for (i, t) in enumerate(all_tokens))
    id_to_token = Dict(i => t for (i, t) in enumerate(all_tokens))

    # Initialize prover-specific tokens (populated during encoding)
    prover_tokens = Dict{ProverType, Set{String}}()
    for prover in instances(ProverType)
        prover_tokens[prover] = Set{String}()
    end

    ProverVocabulary(
        token_to_id,
        id_to_token,
        length(all_tokens),
        prover_tokens,
        "<PAD>", "<UNK>", "<CLS>", "<SEP>", "<MASK>"
    )
end

"""
    tokenize_text(text::String)

Basic tokenization - splits on whitespace and symbols.
Can be extended with prover-specific tokenizers.
"""
function tokenize_text(text::String)
    # Simple whitespace + symbol splitting
    # TODO: Add prover-specific tokenization rules
    tokens = split(text, r"[\s\(\)\[\]\{\},;:.]+", keepempty=false)
    return String.(tokens)
end

"""
    encode_tokens(vocab::ProverVocabulary, tokens::Vector{String})

Convert tokens to integer IDs using vocabulary.
"""
function encode_tokens(vocab::ProverVocabulary, tokens::Vector{String})
    unk_id = vocab.token_to_id[vocab.unk_token]
    return [get(vocab.token_to_id, token, unk_id) for token in tokens]
end

# ============================================================================
# Prover-Specific Encoders
# ============================================================================

"""
    ProverEncoder

Abstract base for prover-specific encoders.
Each prover can override parsing and feature extraction.
"""
abstract type ProverEncoder end

"""
    encode_goal(encoder::ProverEncoder, goal::String)

Parse and encode a goal statement (prover-specific).
"""
function encode_goal end

"""
    encode_context(encoder::ProverEncoder, context::Vector{String})

Parse and encode proof context (prover-specific).
"""
function encode_context end

"""
    encode_hypothesis(encoder::ProverEncoder, hyp::String)

Parse and encode a hypothesis (prover-specific).
"""
function encode_hypothesis end

# --- Agda Encoder ---
struct AgdaEncoder <: ProverEncoder end

function encode_goal(::AgdaEncoder, goal::String)
    # Agda-specific parsing
    # Extract type signatures, hole context, etc.
    tokens = tokenize_text(goal)
    features = Dict(
        "has_hole" => occursin("?", goal),
        "has_lambda" => occursin("λ", goal) || occursin("\\", goal),
        "has_forall" => occursin("∀", goal) || occursin("forall", goal),
        "num_arrows" => count("→", goal) + count("->", goal)
    )
    return (tokens, features)
end

# --- Coq/Rocq Encoder ---
struct CoqEncoder <: ProverEncoder end

function encode_goal(::CoqEncoder, goal::String)
    tokens = tokenize_text(goal)
    features = Dict(
        "has_forall" => occursin("forall", goal),
        "has_exists" => occursin("exists", goal),
        "has_match" => occursin("match", goal),
        "num_implications" => count("->", goal)
    )
    return (tokens, features)
end

# --- Lean Encoder ---
struct LeanEncoder <: ProverEncoder end

function encode_goal(::LeanEncoder, goal::String)
    tokens = tokenize_text(goal)
    features = Dict(
        "has_sorry" => occursin("sorry", goal),
        "has_calc" => occursin("calc", goal),
        "has_by" => occursin("by", goal),
        "num_arrows" => count("→", goal) + count("->", goal)
    )
    return (tokens, features)
end

# --- Isabelle Encoder ---
struct IsabelleEncoder <: ProverEncoder end

function encode_goal(::IsabelleEncoder, goal::String)
    tokens = tokenize_text(goal)
    features = Dict(
        "has_assume" => occursin("assume", goal),
        "has_show" => occursin("show", goal),
        "has_obtain" => occursin("obtain", goal),
        "num_implications" => count("⟹", goal) + count("==>", goal)
    )
    return (tokens, features)
end

# --- Z3 Encoder (SMT-LIB format) ---
struct Z3Encoder <: ProverEncoder end

function encode_goal(::Z3Encoder, goal::String)
    tokens = tokenize_text(goal)
    features = Dict(
        "has_assert" => occursin("assert", goal),
        "has_declare" => occursin("declare-fun", goal) || occursin("declare-const", goal),
        "has_forall" => occursin("forall", goal),
        "num_quantifiers" => count("forall", goal) + count("exists", goal)
    )
    return (tokens, features)
end

# --- CVC5 Encoder (SMT-LIB format) ---
struct CVC5Encoder <: ProverEncoder end

function encode_goal(::CVC5Encoder, goal::String)
    # Similar to Z3 (both use SMT-LIB)
    tokens = tokenize_text(goal)
    features = Dict(
        "has_assert" => occursin("assert", goal),
        "has_set_logic" => occursin("set-logic", goal),
        "has_forall" => occursin("forall", goal),
        "num_quantifiers" => count("forall", goal) + count("exists", goal)
    )
    return (tokens, features)
end

# --- Metamath Encoder (Easiest - plain text!) ---
struct MetamathEncoder <: ProverEncoder end

function encode_goal(::MetamathEncoder, goal::String)
    # Metamath uses RPN notation - straightforward parsing
    tokens = tokenize_text(goal)
    features = Dict(
        "has_turnstile" => occursin("|-", goal),
        "has_wff" => occursin("wff", goal),
        "has_class" => occursin("class", goal),
        "num_symbols" => length(tokens)
    )
    return (tokens, features)
end

# --- HOL Light Encoder ---
struct HOLLightEncoder <: ProverEncoder end

function encode_goal(::HOLLightEncoder, goal::String)
    tokens = tokenize_text(goal)
    features = Dict(
        "has_forall" => occursin("!", goal),
        "has_exists" => occursin("?", goal),
        "has_lambda" => occursin("\\", goal),
        "num_implications" => count("==>", goal)
    )
    return (tokens, features)
end

# --- Mizar Encoder ---
struct MizarEncoder <: ProverEncoder end

function encode_goal(::MizarEncoder, goal::String)
    tokens = tokenize_text(goal)
    features = Dict(
        "has_for" => occursin("for", goal),
        "has_holds" => occursin("holds", goal),
        "has_being" => occursin("being", goal),
        "num_st" => count(" st ", goal)
    )
    return (tokens, features)
end

# --- PVS Encoder ---
struct PVSEncoder <: ProverEncoder end

function encode_goal(::PVSEncoder, goal::String)
    tokens = tokenize_text(goal)
    features = Dict(
        "has_forall" => occursin("FORALL", goal),
        "has_exists" => occursin("EXISTS", goal),
        "has_lambda" => occursin("LAMBDA", goal),
        "num_implications" => count("=>", goal)
    )
    return (tokens, features)
end

# --- ACL2 Encoder ---
struct ACL2Encoder <: ProverEncoder end

function encode_goal(::ACL2Encoder, goal::String)
    tokens = tokenize_text(goal)
    features = Dict(
        "has_defthm" => occursin("defthm", goal),
        "has_implies" => occursin("implies", goal),
        "has_equal" => occursin("equal", goal),
        "num_parens" => count("(", goal)
    )
    return (tokens, features)
end

# --- HOL4 Encoder ---
struct HOL4Encoder <: ProverEncoder end

function encode_goal(::HOL4Encoder, goal::String)
    tokens = tokenize_text(goal)
    features = Dict(
        "has_forall" => occursin("!", goal),
        "has_exists" => occursin("?", goal),
        "has_lambda" => occursin("\\", goal),
        "num_implications" => count("==>", goal)
    )
    return (tokens, features)
end

# Factory function for encoder selection
"""
    get_prover_encoder(prover::ProverType)

Get the appropriate encoder for a given prover.
"""
function get_prover_encoder(prover::ProverType)
    encoders = Dict(
        AGDA => AgdaEncoder(),
        COQ => CoqEncoder(),
        ROCQ => CoqEncoder(),  # Rocq uses same encoder as Coq
        LEAN => LeanEncoder(),
        ISABELLE => IsabelleEncoder(),
        Z3 => Z3Encoder(),
        CVC5 => CVC5Encoder(),
        METAMATH => MetamathEncoder(),
        HOL_LIGHT => HOLLightEncoder(),
        MIZAR => MizarEncoder(),
        PVS => PVSEncoder(),
        ACL2 => ACL2Encoder(),
        HOL4 => HOL4Encoder()
    )
    return encoders[prover]
end

# ============================================================================
# Neural Encoder Network
# ============================================================================

"""
    TextEncoder

Neural network for encoding tokenized text into embeddings.
Uses embeddings + positional encoding + transformer layers.
"""
struct TextEncoder
    embedding::Embedding
    positional_encoding::PositionalEncoding
    transformer_layers::Chain
    output_projection::Dense
end

Flux.@functor TextEncoder

"""
    TextEncoder(vocab_size, embed_dim, hidden_dim, num_layers, dropout)

Create a text encoder network.
"""
function TextEncoder(vocab_size::Int, embed_dim::Int, hidden_dim::Int, num_layers::Int, dropout::Float32)
    embedding = Embedding(vocab_size, embed_dim)
    pos_enc = PositionalEncoding(embed_dim, dropout=dropout)

    # Transformer encoder layers
    transformer_layers = Chain([
        TransformerEncoderLayer(embed_dim, hidden_dim, dropout=dropout)
        for _ in 1:num_layers
    ]...)

    output_projection = Dense(embed_dim, embed_dim)

    return TextEncoder(embedding, pos_enc, transformer_layers, output_projection)
end

"""
    (encoder::TextEncoder)(token_ids::AbstractMatrix)

Forward pass through text encoder.
Input: token_ids of shape (seq_len, batch_size)
Output: embeddings of shape (embed_dim, seq_len, batch_size)
"""
function (encoder::TextEncoder)(token_ids::AbstractMatrix)
    # Embed tokens
    x = encoder.embedding(token_ids)  # (embed_dim, seq_len, batch)

    # Add positional encoding
    x = encoder.positional_encoding(x)

    # Apply transformer layers
    x = encoder.transformer_layers(x)

    # Output projection
    x = encoder.output_projection(x)

    return x
end

"""
    PositionalEncoding

Sinusoidal positional encoding for transformers.
"""
struct PositionalEncoding
    dropout::Dropout
    pe::Matrix{Float32}
end

Flux.@functor PositionalEncoding

function PositionalEncoding(d_model::Int, max_len::Int=5000; dropout::Float32=0.1f0)
    pe = zeros(Float32, d_model, max_len)

    position = collect(0:max_len-1)
    div_term = exp.(collect(0:2:d_model-1) .* -(log(10000.0) / d_model))

    pe[1:2:end, :] = sin.(position' .* div_term)
    pe[2:2:end, :] = cos.(position' .* div_term)

    PositionalEncoding(Dropout(dropout), pe)
end

function (pe::PositionalEncoding)(x::AbstractArray)
    seq_len = size(x, 2)
    x .+ pe.pe[:, 1:seq_len]
    return pe.dropout(x)
end

"""
    TransformerEncoderLayer

Single transformer encoder layer with multi-head attention and FFN.
"""
struct TransformerEncoderLayer
    attention::MultiHeadAttention
    norm1::LayerNorm
    ffn::Chain
    norm2::LayerNorm
    dropout::Dropout
end

Flux.@functor TransformerEncoderLayer

function TransformerEncoderLayer(d_model::Int, d_ff::Int; num_heads::Int=8, dropout::Float32=0.1f0)
    attention = MultiHeadAttention(d_model, num_heads)
    norm1 = LayerNorm(d_model)

    ffn = Chain(
        Dense(d_model, d_ff, gelu),
        Dropout(dropout),
        Dense(d_ff, d_model)
    )
    norm2 = LayerNorm(d_model)

    dropout_layer = Dropout(dropout)

    return TransformerEncoderLayer(attention, norm1, ffn, norm2, dropout_layer)
end

function (layer::TransformerEncoderLayer)(x::AbstractArray)
    # Self-attention with residual
    attn_out = layer.attention(x, x, x)
    x = layer.norm1(x .+ layer.dropout(attn_out))

    # FFN with residual
    ffn_out = layer.ffn(x)
    x = layer.norm2(x .+ layer.dropout(ffn_out))

    return x
end

# ============================================================================
# Main Encoding Functions
# ============================================================================

"""
    encode_proof_state(state::ProofState, vocab::ProverVocabulary, encoder::TextEncoder)

Encode a complete proof state into a vector representation.
"""
function encode_proof_state(state::ProofState, vocab::ProverVocabulary, encoder::TextEncoder)
    # Get prover-specific encoder
    prover_enc = get_prover_encoder(state.prover)

    # Encode goal
    goal_tokens, goal_features = encode_goal(prover_enc, state.goal)
    goal_ids = encode_tokens(vocab, goal_tokens)

    # Encode context
    context_tokens = reduce(vcat, [tokenize_text(c) for c in state.context])
    context_ids = encode_tokens(vocab, context_tokens)

    # Encode hypotheses
    hyp_tokens = reduce(vcat, [tokenize_text(h) for h in state.hypotheses])
    hyp_ids = encode_tokens(vocab, hyp_tokens)

    # Combine all tokens with separator
    sep_id = vocab.token_to_id[vocab.sep_token]
    all_ids = vcat(goal_ids, [sep_id], context_ids, [sep_id], hyp_ids)

    # Convert to matrix (seq_len, 1) for batch dimension
    token_matrix = reshape(all_ids, length(all_ids), 1)

    # Encode through neural network
    embeddings = encoder(token_matrix)  # (embed_dim, seq_len, 1)

    # Pool to single vector (mean pooling)
    state_embedding = mean(embeddings, dims=2)[:, 1, 1]

    return state_embedding
end

"""
    decode_prediction(embedding::Vector{Float32}, prover::ProverType)

Decode a prediction embedding back to prover-specific format.
(Used for autoencoder training and validation)
"""
function decode_prediction(embedding::Vector{Float32}, prover::ProverType)
    # Placeholder for decoder implementation
    # In practice, this would use a separate decoder network
    # For now, return the embedding itself
    return embedding
end

export ProverVocabulary, create_vocabulary, tokenize_text, encode_tokens
export ProverEncoder, get_prover_encoder
export TextEncoder, PositionalEncoding, TransformerEncoderLayer
export encode_proof_state, decode_prediction
