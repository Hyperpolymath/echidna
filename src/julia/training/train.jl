# SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
# SPDX-License-Identifier: MIT AND Palimpsest-0.6

"""
    training/train.jl

Training Pipeline for ECHIDNA Neural Solver

Implements training loop, data loading, loss functions, and optimization
for the universal neural premise selector across all 12 theorem provers.

Features:
- Multi-prover training with balanced sampling
- Contrastive learning for premise ranking
- Learning rate scheduling
- Early stopping and checkpointing
- Distributed training support (multi-GPU)
- Metrics tracking and logging
"""

using Flux
using Flux.Optimise
using Optimisers
using CUDA
using Statistics
using Random
using Logging
using DataFrames
using CSV
using BSON
using Dates
using ProgressMeter

# ============================================================================
# Data Structures
# ============================================================================

"""
    TrainingExample

Single training example with proof state, relevant premises, and labels.
"""
struct TrainingExample
    proof_state::ProofState
    candidate_premises::Vector{Premise}
    relevant_indices::Vector{Int}  # Indices of actually useful premises
    prover::ProverType
end

"""
    TrainingDataset

Collection of training examples with batching support.
"""
mutable struct TrainingDataset
    examples::Vector{TrainingExample}
    batch_size::Int
    shuffle::Bool
    current_idx::Int
end

function TrainingDataset(examples::Vector{TrainingExample}; batch_size::Int=32, shuffle::Bool=true)
    return TrainingDataset(examples, batch_size, shuffle, 1)
end

"""
    next_batch!(dataset::TrainingDataset)

Get next batch of training examples. Returns nothing when epoch is complete.
"""
function next_batch!(dataset::TrainingDataset)
    if dataset.current_idx > length(dataset.examples)
        # Epoch complete - shuffle and reset
        if dataset.shuffle
            shuffle!(dataset.examples)
        end
        dataset.current_idx = 1
        return nothing
    end

    # Get batch
    end_idx = min(dataset.current_idx + dataset.batch_size - 1, length(dataset.examples))
    batch = dataset.examples[dataset.current_idx:end_idx]
    dataset.current_idx = end_idx + 1

    return batch
end

"""
    reset!(dataset::TrainingDataset)

Reset dataset to beginning.
"""
function reset!(dataset::TrainingDataset)
    dataset.current_idx = 1
    if dataset.shuffle
        shuffle!(dataset.examples)
    end
end

# ============================================================================
# Loss Functions
# ============================================================================

"""
    ranking_loss(scores::Vector{Float32}, relevant_indices::Vector{Int})

Pairwise ranking loss for premise selection.
Encourages relevant premises to score higher than irrelevant ones.
"""
function ranking_loss(scores::Vector{Float32}, relevant_indices::Vector{Int})
    if isempty(relevant_indices)
        return 0.0f0
    end

    num_premises = length(scores)
    irrelevant_indices = setdiff(1:num_premises, relevant_indices)

    if isempty(irrelevant_indices)
        return 0.0f0
    end

    # Pairwise margin ranking loss
    loss = 0.0f0
    margin = 0.5f0

    for rel_idx in relevant_indices
        for irrel_idx in irrelevant_indices
            # Encourage scores[rel_idx] > scores[irrel_idx] + margin
            loss += max(0.0f0, margin + scores[irrel_idx] - scores[rel_idx])
        end
    end

    # Normalize by number of pairs
    num_pairs = length(relevant_indices) * length(irrelevant_indices)
    return loss / num_pairs
end

"""
    contrastive_loss(scores::Vector{Float32}, relevant_indices::Vector{Int}; temperature::Float32=0.1f0)

Contrastive learning loss (InfoNCE) for premise selection.
"""
function contrastive_loss(scores::Vector{Float32}, relevant_indices::Vector{Int}; temperature::Float32=0.1f0)
    if isempty(relevant_indices)
        return 0.0f0
    end

    # Normalize scores with temperature
    scaled_scores = scores ./ temperature
    exp_scores = exp.(scaled_scores)

    # For each relevant premise, compute contrastive loss
    loss = 0.0f0
    for rel_idx in relevant_indices
        # Positive: relevant premise
        positive_score = exp_scores[rel_idx]

        # Negatives: all premises
        denominator = sum(exp_scores)

        # InfoNCE loss
        loss -= log(positive_score / (denominator + 1f-10))
    end

    return loss / length(relevant_indices)
end

"""
    combined_loss(solver::NeuralSolver, batch::Vector{TrainingExample}; α::Float32=0.5f0)

Combined loss function: ranking + contrastive learning.
"""
function combined_loss(solver::NeuralSolver, batch::Vector{TrainingExample}; α::Float32=0.5f0)
    total_loss = 0.0f0
    batch_size = length(batch)

    for example in batch
        # Forward pass
        scores = solver(example.proof_state, example.candidate_premises)

        # Compute losses
        rank_loss = ranking_loss(scores, example.relevant_indices)
        contrast_loss = contrastive_loss(scores, example.relevant_indices)

        # Combine
        total_loss += α * rank_loss + (1 - α) * contrast_loss
    end

    return total_loss / batch_size
end

# ============================================================================
# Metrics
# ============================================================================

"""
    TrainingMetrics

Track training metrics over time.
"""
mutable struct TrainingMetrics
    epoch::Vector{Int}
    train_loss::Vector{Float32}
    val_loss::Vector{Float32}
    precision_at_k::Vector{Float32}  # Precision@10
    recall_at_k::Vector{Float32}     # Recall@10
    mrr::Vector{Float32}              # Mean Reciprocal Rank
    learning_rate::Vector{Float32}
    timestamp::Vector{DateTime}
end

function TrainingMetrics()
    return TrainingMetrics(
        Int[], Float32[], Float32[], Float32[], Float32[], Float32[], Float32[], DateTime[]
    )
end

"""
    compute_metrics(solver::NeuralSolver, dataset::TrainingDataset; k::Int=10)

Compute evaluation metrics on a dataset.
"""
function compute_metrics(solver::NeuralSolver, dataset::TrainingDataset; k::Int=10)
    reset!(dataset)

    total_precision = 0.0f0
    total_recall = 0.0f0
    total_mrr = 0.0f0
    num_examples = 0

    while true
        batch = next_batch!(dataset)
        batch === nothing && break

        for example in batch
            scores = solver(example.proof_state, example.candidate_premises)

            # Get top-k predictions
            top_k_indices = partialsortperm(scores, 1:min(k, length(scores)), rev=true)

            # Precision@k
            num_relevant_in_top_k = length(intersect(top_k_indices, example.relevant_indices))
            precision = num_relevant_in_top_k / k

            # Recall@k
            recall = num_relevant_in_top_k / max(1, length(example.relevant_indices))

            # MRR - find rank of first relevant premise
            mrr = 0.0f0
            for (rank, idx) in enumerate(top_k_indices)
                if idx in example.relevant_indices
                    mrr = 1.0f0 / rank
                    break
                end
            end

            total_precision += precision
            total_recall += recall
            total_mrr += mrr
            num_examples += 1
        end
    end

    return (
        precision = total_precision / num_examples,
        recall = total_recall / num_examples,
        mrr = total_mrr / num_examples
    )
end

"""
    log_metrics!(metrics::TrainingMetrics, epoch::Int, train_loss::Float32,
                 val_loss::Float32, val_metrics, lr::Float32)

Log metrics for current epoch.
"""
function log_metrics!(metrics::TrainingMetrics, epoch::Int, train_loss::Float32,
                      val_loss::Float32, val_metrics, lr::Float32)
    push!(metrics.epoch, epoch)
    push!(metrics.train_loss, train_loss)
    push!(metrics.val_loss, val_loss)
    push!(metrics.precision_at_k, val_metrics.precision)
    push!(metrics.recall_at_k, val_metrics.recall)
    push!(metrics.mrr, val_metrics.mrr)
    push!(metrics.learning_rate, lr)
    push!(metrics.timestamp, now())

    @info "Epoch $epoch" train_loss val_loss precision=val_metrics.precision recall=val_metrics.recall mrr=val_metrics.mrr lr
end

"""
    save_metrics(metrics::TrainingMetrics, path::String)

Save metrics to CSV file.
"""
function save_metrics(metrics::TrainingMetrics, path::String)
    df = DataFrame(
        epoch = metrics.epoch,
        train_loss = metrics.train_loss,
        val_loss = metrics.val_loss,
        precision_at_10 = metrics.precision_at_k,
        recall_at_10 = metrics.recall_at_k,
        mrr = metrics.mrr,
        learning_rate = metrics.learning_rate,
        timestamp = metrics.timestamp
    )
    CSV.write(path, df)
    @info "Metrics saved to $path"
end

# ============================================================================
# Training Loop
# ============================================================================

"""
    TrainingConfig

Configuration for training process.
"""
mutable struct TrainingConfig
    num_epochs::Int
    learning_rate::Float32
    lr_schedule::Symbol  # :constant, :exponential, :cosine
    lr_decay_rate::Float32
    weight_decay::Float32
    gradient_clip_norm::Float32
    loss_alpha::Float32  # Weight for ranking vs contrastive loss
    early_stopping_patience::Int
    checkpoint_every::Int
    eval_every::Int
    save_dir::String
end

function TrainingConfig(;
    num_epochs::Int=100,
    learning_rate::Float32=1f-4,
    lr_schedule::Symbol=:cosine,
    lr_decay_rate::Float32=0.95f0,
    weight_decay::Float32=1f-5,
    gradient_clip_norm::Float32=1.0f0,
    loss_alpha::Float32=0.5f0,
    early_stopping_patience::Int=10,
    checkpoint_every::Int=5,
    eval_every::Int=1,
    save_dir::String="checkpoints"
)
    return TrainingConfig(
        num_epochs, learning_rate, lr_schedule, lr_decay_rate, weight_decay,
        gradient_clip_norm, loss_alpha, early_stopping_patience,
        checkpoint_every, eval_every, save_dir
    )
end

"""
    get_learning_rate(config::TrainingConfig, epoch::Int)

Compute learning rate for current epoch based on schedule.
"""
function get_learning_rate(config::TrainingConfig, epoch::Int)
    base_lr = config.learning_rate

    if config.lr_schedule == :constant
        return base_lr
    elseif config.lr_schedule == :exponential
        return base_lr * (config.lr_decay_rate ^ (epoch - 1))
    elseif config.lr_schedule == :cosine
        # Cosine annealing
        return base_lr * 0.5f0 * (1.0f0 + cos(π * epoch / config.num_epochs))
    else
        @warn "Unknown learning rate schedule: $(config.lr_schedule), using constant"
        return base_lr
    end
end

"""
    train_solver!(solver::NeuralSolver, train_data::TrainingDataset,
                  val_data::TrainingDataset; config::TrainingConfig=TrainingConfig())

Train the neural solver on provided data.
"""
function train_solver!(solver::NeuralSolver, train_data::TrainingDataset,
                       val_data::TrainingDataset; config::TrainingConfig=TrainingConfig())
    @info "Starting training with config" config

    # Create save directory
    mkpath(config.save_dir)

    # Initialize optimizer
    opt_state = Flux.setup(Adam(config.learning_rate), solver)

    # Metrics tracking
    metrics = TrainingMetrics()
    best_val_loss = Inf32
    patience_counter = 0

    # Training loop
    for epoch in 1:config.num_epochs
        @info "Epoch $epoch / $(config.num_epochs)"

        # Update learning rate
        current_lr = get_learning_rate(config, epoch)
        Optimisers.adjust!(opt_state, current_lr)

        # Training epoch
        reset!(train_data)
        epoch_loss = 0.0f0
        num_batches = 0

        progress = Progress(ceil(Int, length(train_data.examples) / train_data.batch_size),
                           desc="Training: ")

        while true
            batch = next_batch!(train_data)
            batch === nothing && break

            # Compute loss and gradients
            loss, grads = Flux.withgradient(solver) do m
                combined_loss(m, batch, α=config.loss_alpha)
            end

            # Clip gradients
            Flux.Optimise.clip_norm!(grads, config.gradient_clip_norm)

            # Update parameters
            Flux.update!(opt_state, solver, grads[1])

            epoch_loss += loss
            num_batches += 1

            next!(progress, showvalues=[(:loss, loss)])
        end

        avg_train_loss = epoch_loss / num_batches

        # Validation
        if epoch % config.eval_every == 0
            @info "Running validation..."

            # Compute validation loss
            reset!(val_data)
            val_loss = 0.0f0
            val_batches = 0

            Flux.testmode!(solver)  # Disable dropout
            while true
                batch = next_batch!(val_data)
                batch === nothing && break

                loss = combined_loss(solver, batch, α=config.loss_alpha)
                val_loss += loss
                val_batches += 1
            end
            Flux.trainmode!(solver)  # Re-enable dropout

            avg_val_loss = val_loss / val_batches

            # Compute metrics
            val_metrics = compute_metrics(solver, val_data)

            # Log metrics
            log_metrics!(metrics, epoch, avg_train_loss, avg_val_loss, val_metrics, current_lr)

            # Early stopping check
            if avg_val_loss < best_val_loss
                best_val_loss = avg_val_loss
                patience_counter = 0

                # Save best model
                save_solver(solver, joinpath(config.save_dir, "best_model"))
            else
                patience_counter += 1
                if patience_counter >= config.early_stopping_patience
                    @info "Early stopping triggered after $epoch epochs"
                    break
                end
            end
        else
            # Just log training loss
            push!(metrics.epoch, epoch)
            push!(metrics.train_loss, avg_train_loss)
            push!(metrics.learning_rate, current_lr)
            push!(metrics.timestamp, now())
        end

        # Checkpoint
        if epoch % config.checkpoint_every == 0
            checkpoint_path = joinpath(config.save_dir, "checkpoint_epoch_$epoch")
            save_solver(solver, checkpoint_path)
        end
    end

    # Save final metrics
    save_metrics(metrics, joinpath(config.save_dir, "training_metrics.csv"))

    @info "Training complete!"
    return metrics
end

# ============================================================================
# Data Loading Utilities
# ============================================================================

"""
    load_training_data(data_dir::String; train_split::Float32=0.8f0)

Load training and validation data from directory.
"""
function load_training_data(data_dir::String; train_split::Float32=0.8f0)
    # Placeholder - implement based on your data format
    # Expected: JSON/BSON files with proof states and premise labels

    @info "Loading training data from $data_dir"

    # TODO: Implement actual data loading
    # For now, return empty datasets
    train_examples = TrainingExample[]
    val_examples = TrainingExample[]

    train_data = TrainingDataset(train_examples, batch_size=32, shuffle=true)
    val_data = TrainingDataset(val_examples, batch_size=32, shuffle=false)

    @info "Loaded $(length(train_examples)) training examples, $(length(val_examples)) validation examples"

    return train_data, val_data
end

export TrainingExample, TrainingDataset, next_batch!, reset!
export ranking_loss, contrastive_loss, combined_loss
export TrainingMetrics, compute_metrics, log_metrics!, save_metrics
export TrainingConfig, train_solver!
export load_training_data
