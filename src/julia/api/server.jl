# SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
# SPDX-License-Identifier: MIT AND Palimpsest-0.6

"""
    api/server.jl

HTTP API Server for ECHIDNA Neural Solver

Provides RESTful API for neural premise selection using Oxygen.jl.
Supports async requests, batching, and streaming responses.

Endpoints:
- POST /predict - Single premise prediction
- POST /predict/batch - Batch prediction
- POST /suggest - Interactive suggestion with diversity
- GET /health - Health check
- GET /metrics - Server metrics
- GET /provers - List supported provers
"""

using Oxygen
using HTTP
using JSON3
using Logging
using Dates
using Statistics
using Base.Threads

# ============================================================================
# Global State
# ============================================================================

"""
    ServerState

Global server state including loaded models and caches.
"""
mutable struct ServerState
    solver::Union{Nothing, NeuralSolver}
    vocabulary::Union{Nothing, ProverVocabulary}
    cache::InferenceCache
    request_count::Int
    start_time::DateTime
    model_path::String
    port::Int
    host::String
end

# Global server state
const SERVER_STATE = Ref{ServerState}()

"""
    init_server_state(model_path::String; cache_size::Int=1000,
                      port::Int=8080, host::String="0.0.0.0")

Initialize server state and load model.
"""
function init_server_state(model_path::String; cache_size::Int=1000,
                           port::Int=8080, host::String="0.0.0.0")
    @info "Initializing server state..."

    # Load solver
    @info "Loading model from $model_path"
    solver = load_solver(model_path)
    vocabulary = solver.vocabulary

    # Initialize cache
    cache = InferenceCache(cache_size)

    # Create state
    state = ServerState(
        solver,
        vocabulary,
        cache,
        0,
        now(),
        model_path,
        port,
        host
    )

    SERVER_STATE[] = state

    @info "Server initialized successfully"
    return state
end

"""
    get_state()

Get current server state.
"""
function get_state()
    if !isassigned(SERVER_STATE)
        error("Server not initialized. Call init_server_state() first.")
    end
    return SERVER_STATE[]
end

# ============================================================================
# Request/Response DTOs
# ============================================================================

"""
    PredictRequest

Request for single premise prediction.
"""
struct PredictRequest
    goal::String
    context::Vector{String}
    hypotheses::Vector{String}
    available_premises::Vector{Dict{String, Any}}
    prover::String
    top_k::Int
    min_confidence::Float32
    use_cache::Bool
end

# JSON3 struct mapping
JSON3.StructType(::Type{PredictRequest}) = JSON3.Struct()

"""
    PredictResponse

Response with ranked premises.
"""
struct PredictResponse
    success::Bool
    premises::Vector{Dict{String, Any}}
    scores::Vector{Float32}
    confidence::Float32
    prover::String
    cached::Bool
    inference_time_ms::Float32
end

JSON3.StructType(::Type{PredictResponse}) = JSON3.Struct()

"""
    BatchPredictRequest

Request for batch prediction.
"""
struct BatchPredictRequest
    requests::Vector{PredictRequest}
end

JSON3.StructType(::Type{BatchPredictRequest}) = JSON3.Struct()

"""
    SuggestRequest

Request for interactive suggestion with options.
"""
struct SuggestRequest
    goal::String
    context::Vector{String}
    hypotheses::Vector{String}
    available_premises::Vector{Dict{String, Any}}
    prover::String
    top_k::Int
    use_diversity::Bool
    estimate_uncertainty::Bool
end

JSON3.StructType(::Type{SuggestRequest}) = JSON3.Struct()

"""
    ErrorResponse

Error response.
"""
struct ErrorResponse
    success::Bool
    error::String
    error_type::String
end

JSON3.StructType(::Type{ErrorResponse}) = JSON3.Struct()

# ============================================================================
# Helper Functions
# ============================================================================

"""
    parse_prover(prover_str::String)

Parse prover string to ProverType enum.
"""
function parse_prover(prover_str::String)
    prover_map = Dict(
        "agda" => AGDA,
        "coq" => COQ,
        "rocq" => ROCQ,
        "lean" => LEAN,
        "isabelle" => ISABELLE,
        "z3" => Z3,
        "cvc5" => CVC5,
        "metamath" => METAMATH,
        "hol_light" => HOL_LIGHT,
        "hollight" => HOL_LIGHT,
        "mizar" => MIZAR,
        "pvs" => PVS,
        "acl2" => ACL2,
        "hol4" => HOL4
    )

    prover_lower = lowercase(prover_str)
    if haskey(prover_map, prover_lower)
        return prover_map[prover_lower]
    else
        error("Unknown prover: $prover_str")
    end
end

"""
    request_to_proof_state(req::PredictRequest)

Convert API request to ProofState.
"""
function request_to_proof_state(req::PredictRequest)
    prover = parse_prover(req.prover)

    return ProofState(
        prover,
        req.goal,
        req.context,
        req.hypotheses,
        String[],  # available_premises stored separately
        0,         # proof_depth
        Dict{String, Any}()
    )
end

"""
    dict_to_premise(d::Dict{String, Any}, prover::ProverType)

Convert dictionary to Premise.
"""
function dict_to_premise(d::Dict{String, Any}, prover::ProverType)
    return Premise(
        get(d, "name", ""),
        get(d, "statement", ""),
        prover,
        nothing,  # embedding computed during inference
        Float32(get(d, "frequency_score", 0.0)),
        Float32(get(d, "relevance_score", 0.0))
    )
end

"""
    premise_to_dict(p::Premise, score::Float32)

Convert Premise to dictionary for response.
"""
function premise_to_dict(p::Premise, score::Float32)
    return Dict{String, Any}(
        "name" => p.name,
        "statement" => p.statement,
        "score" => score,
        "frequency_score" => p.frequency_score,
        "relevance_score" => p.relevance_score
    )
end

# ============================================================================
# API Endpoints
# ============================================================================

"""
    @get /health

Health check endpoint.
"""
@get "/health" function(req::HTTP.Request)
    state = get_state()

    health_status = Dict(
        "status" => "healthy",
        "model_loaded" => state.solver !== nothing,
        "uptime_seconds" => (now() - state.start_time).value / 1000,
        "request_count" => state.request_count,
        "cache_stats" => cache_stats(state.cache)
    )

    return JSON3.write(health_status)
end

"""
    @get /metrics

Server metrics endpoint.
"""
@get "/metrics" function(req::HTTP.Request)
    state = get_state()
    cache_stats_data = cache_stats(state.cache)

    uptime_seconds = (now() - state.start_time).value / 1000
    requests_per_second = state.request_count / max(uptime_seconds, 1)

    metrics = Dict(
        "uptime_seconds" => uptime_seconds,
        "total_requests" => state.request_count,
        "requests_per_second" => requests_per_second,
        "cache_hits" => cache_stats_data.hits,
        "cache_misses" => cache_stats_data.misses,
        "cache_hit_rate" => cache_stats_data.hit_rate,
        "cache_size" => cache_stats_data.size,
        "model_path" => state.model_path,
        "gpu_available" => CUDA.functional(),
        "num_threads" => Threads.nthreads()
    )

    return JSON3.write(metrics)
end

"""
    @get /provers

List supported provers.
"""
@get "/provers" function(req::HTTP.Request)
    provers = Dict(
        "tier1" => ["agda", "coq", "rocq", "lean", "isabelle", "z3", "cvc5"],
        "tier2" => ["metamath", "hol_light", "mizar"],
        "tier3" => ["pvs", "acl2"],
        "tier4" => ["hol4"],
        "total" => 13
    )

    return JSON3.write(provers)
end

"""
    @post /predict

Single premise prediction endpoint.
"""
@post "/predict" function(req::HTTP.Request)
    state = get_state()
    state.request_count += 1

    try
        # Parse request
        body = JSON3.read(req.body, PredictRequest)

        # Convert to internal types
        proof_state = request_to_proof_state(body)
        prover = parse_prover(body.prover)
        premises = [dict_to_premise(d, prover) for d in body.available_premises]

        # Run inference
        start_time = time()
        ranking = predict_premises(
            state.solver,
            proof_state,
            premises,
            top_k=body.top_k,
            min_confidence=body.min_confidence,
            use_cache=body.use_cache,
            cache=state.cache
        )
        inference_time = (time() - start_time) * 1000  # Convert to ms

        # Build response
        response = PredictResponse(
            true,
            [premise_to_dict(p, s) for (p, s) in zip(ranking.premises, ranking.scores)],
            ranking.scores,
            ranking.confidence,
            body.prover,
            body.use_cache,  # Simplified - would need to track actual cache hit
            Float32(inference_time)
        )

        return JSON3.write(response)

    catch e
        @error "Error processing predict request" exception=(e, catch_backtrace())

        error_response = ErrorResponse(
            false,
            string(e),
            string(typeof(e))
        )

        return HTTP.Response(500, JSON3.write(error_response))
    end
end

"""
    @post /predict/batch

Batch premise prediction endpoint.
"""
@post "/predict/batch" function(req::HTTP.Request)
    state = get_state()
    state.request_count += length(req.body)

    try
        # Parse batch request
        body = JSON3.read(req.body, BatchPredictRequest)

        # Process each request
        responses = []

        for pred_req in body.requests
            proof_state = request_to_proof_state(pred_req)
            prover = parse_prover(pred_req.prover)
            premises = [dict_to_premise(d, prover) for d in pred_req.available_premises]

            start_time = time()
            ranking = predict_premises(
                state.solver,
                proof_state,
                premises,
                top_k=pred_req.top_k,
                min_confidence=pred_req.min_confidence,
                use_cache=pred_req.use_cache,
                cache=state.cache
            )
            inference_time = (time() - start_time) * 1000

            response = PredictResponse(
                true,
                [premise_to_dict(p, s) for (p, s) in zip(ranking.premises, ranking.scores)],
                ranking.scores,
                ranking.confidence,
                pred_req.prover,
                pred_req.use_cache,
                Float32(inference_time)
            )

            push!(responses, response)
        end

        return JSON3.write(Dict("success" => true, "results" => responses))

    catch e
        @error "Error processing batch predict request" exception=(e, catch_backtrace())

        error_response = ErrorResponse(
            false,
            string(e),
            string(typeof(e))
        )

        return HTTP.Response(500, JSON3.write(error_response))
    end
end

"""
    @post /suggest

Interactive suggestion endpoint with diversity and confidence estimation.
"""
@post "/suggest" function(req::HTTP.Request)
    state = get_state()
    state.request_count += 1

    try
        # Parse request
        body = JSON3.read(req.body, SuggestRequest)

        # Convert to internal types
        proof_state = request_to_proof_state(PredictRequest(
            body.goal,
            body.context,
            body.hypotheses,
            body.available_premises,
            body.prover,
            body.top_k,
            0.0f0,
            false
        ))
        prover = parse_prover(body.prover)
        premises = [dict_to_premise(d, prover) for d in body.available_premises]

        # Run suggestion with options
        start_time = time()
        ranking = suggest_next_step(
            state.solver,
            proof_state,
            premises,
            top_k=body.top_k,
            use_diversity=body.use_diversity,
            estimate_uncertainty=body.estimate_uncertainty
        )
        inference_time = (time() - start_time) * 1000

        # Build response
        response = Dict(
            "success" => true,
            "premises" => [premise_to_dict(p, s) for (p, s) in zip(ranking.premises, ranking.scores)],
            "scores" => ranking.scores,
            "confidence" => ranking.confidence,
            "prover" => body.prover,
            "inference_time_ms" => Float32(inference_time),
            "diversity_applied" => body.use_diversity,
            "uncertainty_estimated" => body.estimate_uncertainty
        )

        return JSON3.write(response)

    catch e
        @error "Error processing suggest request" exception=(e, catch_backtrace())

        error_response = ErrorResponse(
            false,
            string(e),
            string(typeof(e))
        )

        return HTTP.Response(500, JSON3.write(error_response))
    end
end

# ============================================================================
# Server Management
# ============================================================================

"""
    start_api_server(model_path::String;
                     port::Int=8080,
                     host::String="0.0.0.0",
                     cache_size::Int=1000,
                     async::Bool=true)

Start the HTTP API server.

# Arguments
- `model_path`: Path to trained model directory
- `port`: Server port (default: 8080)
- `host`: Server host (default: "0.0.0.0")
- `cache_size`: Inference cache size (default: 1000)
- `async`: Run server asynchronously (default: true)
"""
function start_api_server(model_path::String;
                          port::Int=8080,
                          host::String="0.0.0.0",
                          cache_size::Int=1000,
                          async::Bool=true)
    @info "Starting ECHIDNA Neural Solver API Server"
    @info "Model: $model_path"
    @info "Host: $host:$port"
    @info "Cache size: $cache_size"

    # Initialize server state
    init_server_state(model_path, cache_size=cache_size, port=port, host=host)

    @info "Server ready - listening on http://$host:$port"
    @info "Endpoints:"
    @info "  GET  /health        - Health check"
    @info "  GET  /metrics       - Server metrics"
    @info "  GET  /provers       - List supported provers"
    @info "  POST /predict       - Single premise prediction"
    @info "  POST /predict/batch - Batch prediction"
    @info "  POST /suggest       - Interactive suggestion"

    # Start Oxygen server
    if async
        serve(host=host, port=port, async=true)
        @info "Server started asynchronously"
    else
        serve(host=host, port=port)
    end
end

"""
    stop_api_server()

Stop the API server.
"""
function stop_api_server()
    @info "Stopping ECHIDNA API server..."
    terminate()
    @info "Server stopped"
end

# ============================================================================
# Exports
# ============================================================================

export ServerState, init_server_state, get_state
export PredictRequest, PredictResponse, BatchPredictRequest, SuggestRequest, ErrorResponse
export start_api_server, stop_api_server
