// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! HTTP API server for ECHIDNA
//!
//! Provides REST API and WebSocket endpoints for theorem proving

use anyhow::Result;
use axum::{
    extract::{
        ws::{Message, WebSocket, WebSocketUpgrade},
        Path, Query, State,
    },
    http::StatusCode,
    response::{IntoResponse, Response},
    routing::{get, post},
    Json, Router,
};
use colored::Colorize;
use echidna::core::{ProofState, Tactic, TacticResult};
use echidna::{ProverBackend, ProverConfig, ProverKind};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock};
use tower_http::cors::CorsLayer;
use tracing::info;

/// Application state shared across handlers
#[derive(Clone)]
struct AppState {
    /// Active proof sessions (session_id -> ProofSession)
    sessions: Arc<RwLock<HashMap<String, Arc<Mutex<ProofSession>>>>>,
}

/// A proof session
struct ProofSession {
    prover: Box<dyn ProverBackend>,
    state: Option<ProofState>,
    history: Vec<String>,
}

/// Start the HTTP server
pub async fn start_server(port: u16, host: String, enable_cors: bool) -> Result<()> {
    let state = AppState {
        sessions: Arc::new(RwLock::new(HashMap::new())),
    };

    // Build router
    let mut app = Router::new()
        // REST API endpoints
        .route("/api/health", get(health_check))
        .route("/api/provers", get(list_provers))
        .route("/api/prove", post(prove_handler))
        .route("/api/verify", post(verify_handler))
        .route("/api/suggest", post(suggest_handler))
        .route("/api/search", get(search_handler))
        .route("/api/session/create", post(create_session))
        .route("/api/session/:id/state", get(get_session_state))
        .route("/api/session/:id/apply", post(apply_tactic_handler))
        // WebSocket endpoint
        .route("/ws/interactive", get(websocket_handler))
        .with_state(state);

    // Add CORS if enabled
    if enable_cors {
        app = app.layer(CorsLayer::permissive());
    }

    // Bind server
    let addr: SocketAddr = format!("{}:{}", host, port).parse()?;

    println!("{}", "╔═══════════════════════════════════════════════════════════╗".cyan());
    println!("{}", "║  ECHIDNA HTTP API Server                                  ║".cyan().bold());
    println!("{}", "╚═══════════════════════════════════════════════════════════╝".cyan());
    println!();
    println!("Server listening on: {}", format!("http://{}", addr).green().bold());
    println!();
    println!("{}", "Endpoints:".yellow().bold());
    println!("  GET  /api/health              - Health check");
    println!("  GET  /api/provers             - List available provers");
    println!("  POST /api/prove               - Prove a theorem");
    println!("  POST /api/verify              - Verify a proof");
    println!("  POST /api/suggest             - Get tactic suggestions");
    println!("  GET  /api/search?q=<pattern>  - Search theorems");
    println!("  POST /api/session/create      - Create proof session");
    println!("  GET  /api/session/:id/state   - Get session state");
    println!("  POST /api/session/:id/apply   - Apply tactic to session");
    println!("  WS   /ws/interactive          - WebSocket live proof session");
    println!();
    println!("Press Ctrl+C to stop the server");
    println!();

    // Start server
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app)
        .await?;

    Ok(())
}

// ========== REST API Handlers ==========

/// Health check endpoint
async fn health_check() -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "ok".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
    })
}

/// List available provers
async fn list_provers() -> Json<ProversResponse> {
    let provers = vec![
        ProverInfo {
            name: "Agda".to_string(),
            tier: 1,
            complexity: 3,
        },
        ProverInfo {
            name: "Coq".to_string(),
            tier: 1,
            complexity: 3,
        },
        ProverInfo {
            name: "Lean".to_string(),
            tier: 1,
            complexity: 3,
        },
        ProverInfo {
            name: "Isabelle".to_string(),
            tier: 1,
            complexity: 4,
        },
        ProverInfo {
            name: "Z3".to_string(),
            tier: 1,
            complexity: 2,
        },
        ProverInfo {
            name: "CVC5".to_string(),
            tier: 1,
            complexity: 2,
        },
        ProverInfo {
            name: "Metamath".to_string(),
            tier: 2,
            complexity: 2,
        },
        ProverInfo {
            name: "HolLight".to_string(),
            tier: 2,
            complexity: 3,
        },
        ProverInfo {
            name: "Mizar".to_string(),
            tier: 2,
            complexity: 3,
        },
        ProverInfo {
            name: "PVS".to_string(),
            tier: 3,
            complexity: 4,
        },
        ProverInfo {
            name: "ACL2".to_string(),
            tier: 3,
            complexity: 4,
        },
        ProverInfo {
            name: "Hol4".to_string(),
            tier: 4,
            complexity: 5,
        },
    ];

    Json(ProversResponse { provers })
}

/// Prove theorem endpoint
async fn prove_handler(
    Json(req): Json<ProveRequest>,
) -> Result<Json<ProveResponse>, AppError> {
    info!("Prove request for prover: {:?}", req.prover);

    // Create prover
    let mut config = ProverConfig::default();
    config.timeout = req.timeout.unwrap_or(300);
    config.neural_enabled = req.neural.unwrap_or(true);

    let prover = echidna::provers::ProverFactory::create(req.prover, config)
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    // Parse proof
    let state = prover
        .parse_string(&req.content)
        .await
        .map_err(|e| AppError::ParseError(e.to_string()))?;

    // Verify proof
    let valid = prover
        .verify_proof(&state)
        .await
        .map_err(|e| AppError::VerificationError(e.to_string()))?;

    Ok(Json(ProveResponse {
        success: valid,
        goals: state.goals.len(),
        message: if valid {
            "Proof verified successfully".to_string()
        } else {
            "Proof verification failed".to_string()
        },
    }))
}

/// Verify proof endpoint
async fn verify_handler(
    Json(req): Json<VerifyRequest>,
) -> Result<Json<VerifyResponse>, AppError> {
    info!("Verify request for prover: {:?}", req.prover);

    // Create prover
    let config = ProverConfig::default();
    let prover = echidna::provers::ProverFactory::create(req.prover, config)
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    // Parse proof
    let state = prover
        .parse_string(&req.content)
        .await
        .map_err(|e| AppError::ParseError(e.to_string()))?;

    // Verify
    let valid = prover
        .verify_proof(&state)
        .await
        .map_err(|e| AppError::VerificationError(e.to_string()))?;

    Ok(Json(VerifyResponse {
        valid,
        goals_remaining: state.goals.len(),
        tactics_used: state.proof_script.len(),
    }))
}

/// Get tactic suggestions
async fn suggest_handler(
    Json(req): Json<SuggestRequest>,
) -> Result<Json<SuggestResponse>, AppError> {
    info!("Suggest request for prover: {:?}", req.prover);

    // Create prover
    let config = ProverConfig::default();
    let prover = echidna::provers::ProverFactory::create(req.prover, config)
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    // Parse current state
    let state = prover
        .parse_string(&req.content)
        .await
        .map_err(|e| AppError::ParseError(e.to_string()))?;

    // Get suggestions
    let tactics = prover
        .suggest_tactics(&state, req.limit.unwrap_or(5))
        .await
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    let suggestions = tactics
        .iter()
        .map(|t| format!("{:?}", t))
        .collect();

    Ok(Json(SuggestResponse { suggestions }))
}

/// Search theorems
async fn search_handler(
    Query(params): Query<HashMap<String, String>>,
) -> Result<Json<SearchResponse>, AppError> {
    let pattern = params
        .get("q")
        .ok_or_else(|| AppError::BadRequest("Missing query parameter 'q'".to_string()))?;

    let prover_name = params.get("prover");

    info!("Search request: pattern={}, prover={:?}", pattern, prover_name);

    let mut all_results = Vec::new();

    // Determine which provers to search
    let provers: Vec<ProverKind> = if let Some(name) = prover_name {
        vec![parse_prover_kind(name)?]
    } else {
        vec![
            ProverKind::Agda,
            ProverKind::Coq,
            ProverKind::Lean,
            ProverKind::Isabelle,
        ]
    };

    // Search each prover
    for prover_kind in provers {
        let config = ProverConfig::default();

        if let Ok(prover) = echidna::provers::ProverFactory::create(prover_kind, config) {
            if let Ok(results) = prover.search_theorems(pattern).await {
                all_results.extend(results);
            }
        }
    }

    let count = all_results.len();
    Ok(Json(SearchResponse {
        results: all_results,
        count,
    }))
}

/// Create a new proof session
async fn create_session(
    State(state): State<AppState>,
    Json(req): Json<CreateSessionRequest>,
) -> Result<Json<CreateSessionResponse>, AppError> {
    info!("Creating session for prover: {:?}", req.prover);

    // Create prover
    let config = ProverConfig::default();
    let prover = echidna::provers::ProverFactory::create(req.prover, config)
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    // Create session
    let session_id = uuid::Uuid::new_v4().to_string();
    let session = ProofSession {
        prover,
        state: None,
        history: Vec::new(),
    };

    // Store session
    state
        .sessions
        .write()
        .await
        .insert(session_id.clone(), Arc::new(Mutex::new(session)));

    Ok(Json(CreateSessionResponse { session_id }))
}

/// Get session state
async fn get_session_state(
    State(state): State<AppState>,
    Path(session_id): Path<String>,
) -> Result<Json<SessionStateResponse>, AppError> {
    let sessions = state.sessions.read().await;
    let session = sessions
        .get(&session_id)
        .ok_or_else(|| AppError::NotFound(format!("Session not found: {}", session_id)))?;

    let session = session.lock().await;

    Ok(Json(SessionStateResponse {
        goals: session.state.as_ref().map(|s| s.goals.len()).unwrap_or(0),
        complete: session.state.as_ref().map(|s| s.is_complete()).unwrap_or(false),
        tactics_applied: session.history.len(),
    }))
}

/// Apply tactic to session
async fn apply_tactic_handler(
    State(state): State<AppState>,
    Path(session_id): Path<String>,
    Json(req): Json<ApplyTacticRequest>,
) -> Result<Json<ApplyTacticResponse>, AppError> {
    let sessions = state.sessions.read().await;
    let session_arc = sessions
        .get(&session_id)
        .ok_or_else(|| AppError::NotFound(format!("Session not found: {}", session_id)))?
        .clone();

    drop(sessions);

    let mut session = session_arc.lock().await;

    // Ensure we have a state
    if session.state.is_none() {
        return Err(AppError::BadRequest("No proof loaded in session".to_string()));
    }

    // Parse tactic (simplified)
    let tactic = parse_tactic_from_json(&req.tactic)?;

    // Apply tactic
    let proof_state = session.state.as_ref().unwrap();
    let result = session.prover.apply_tactic(proof_state, &tactic).await
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    match result {
        TacticResult::Success(new_state) => {
            let complete = new_state.is_complete();
            session.state = Some(new_state);
            session.history.push(req.tactic.clone());

            Ok(Json(ApplyTacticResponse {
                success: true,
                complete,
                goals_remaining: session.state.as_ref().unwrap().goals.len(),
                message: "Tactic applied successfully".to_string(),
            }))
        }

        TacticResult::Error(msg) => {
            Ok(Json(ApplyTacticResponse {
                success: false,
                complete: false,
                goals_remaining: session.state.as_ref().unwrap().goals.len(),
                message: msg,
            }))
        }

        TacticResult::QED => {
            session.state.as_mut().unwrap().goals.clear();

            Ok(Json(ApplyTacticResponse {
                success: true,
                complete: true,
                goals_remaining: 0,
                message: "Proof complete!".to_string(),
            }))
        }
    }
}

// ========== WebSocket Handler ==========

/// WebSocket handler for interactive proof sessions
async fn websocket_handler(
    ws: WebSocketUpgrade,
    State(state): State<AppState>,
) -> Response {
    ws.on_upgrade(|socket| handle_websocket(socket, state))
}

/// Handle WebSocket connection
async fn handle_websocket(socket: WebSocket, _state: AppState) {
    info!("WebSocket connection established");

    let (mut sender, mut receiver) = socket.split();

    // For this example, we'll just echo messages
    // In production, this would handle proof session commands
    while let Some(msg) = receiver.next().await {
        match msg {
            Ok(Message::Text(text)) => {
                info!("Received: {}", text);

                // Echo back
                if sender
                    .send(Message::Text(format!("Echo: {}", text)))
                    .await
                    .is_err()
                {
                    break;
                }
            }
            Ok(Message::Close(_)) => {
                info!("WebSocket closed");
                break;
            }
            _ => {}
        }
    }
}

// ========== Helper Functions ==========

/// Parse prover kind from string
fn parse_prover_kind(s: &str) -> Result<ProverKind, AppError> {
    match s.to_lowercase().as_str() {
        "agda" => Ok(ProverKind::Agda),
        "coq" => Ok(ProverKind::Coq),
        "lean" => Ok(ProverKind::Lean),
        "isabelle" => Ok(ProverKind::Isabelle),
        "z3" => Ok(ProverKind::Z3),
        "cvc5" => Ok(ProverKind::CVC5),
        "metamath" => Ok(ProverKind::Metamath),
        "hollight" => Ok(ProverKind::HolLight),
        "mizar" => Ok(ProverKind::Mizar),
        "pvs" => Ok(ProverKind::PVS),
        "acl2" => Ok(ProverKind::ACL2),
        "hol4" => Ok(ProverKind::Hol4),
        _ => Err(AppError::BadRequest(format!("Unknown prover: {}", s))),
    }
}

/// Parse tactic from JSON string (simplified)
fn parse_tactic_from_json(s: &str) -> Result<Tactic, AppError> {
    // Simplified parsing - in production, use proper JSON parsing
    let parts: Vec<&str> = s.split_whitespace().collect();

    if parts.is_empty() {
        return Err(AppError::BadRequest("Empty tactic".to_string()));
    }

    match parts[0].to_lowercase().as_str() {
        "apply" => Ok(Tactic::Apply(parts[1..].join(" "))),
        "intro" => Ok(Tactic::Intro(parts.get(1).map(|s| s.to_string()))),
        "rewrite" => Ok(Tactic::Rewrite(parts[1..].join(" "))),
        "simplify" => Ok(Tactic::Simplify),
        "reflexivity" => Ok(Tactic::Reflexivity),
        "assumption" => Ok(Tactic::Assumption),
        _ => Ok(Tactic::Custom {
            prover: "unknown".to_string(),
            command: parts[0].to_string(),
            args: parts[1..].iter().map(|s| s.to_string()).collect(),
        }),
    }
}

// ========== Request/Response Types ==========

#[derive(Deserialize)]
struct ProveRequest {
    prover: ProverKind,
    content: String,
    timeout: Option<u64>,
    neural: Option<bool>,
}

#[derive(Serialize)]
struct ProveResponse {
    success: bool,
    goals: usize,
    message: String,
}

#[derive(Deserialize)]
struct VerifyRequest {
    prover: ProverKind,
    content: String,
}

#[derive(Serialize)]
struct VerifyResponse {
    valid: bool,
    goals_remaining: usize,
    tactics_used: usize,
}

#[derive(Deserialize)]
struct SuggestRequest {
    prover: ProverKind,
    content: String,
    limit: Option<usize>,
}

#[derive(Serialize)]
struct SuggestResponse {
    suggestions: Vec<String>,
}

#[derive(Serialize)]
struct SearchResponse {
    results: Vec<String>,
    count: usize,
}

#[derive(Deserialize)]
struct CreateSessionRequest {
    prover: ProverKind,
}

#[derive(Serialize)]
struct CreateSessionResponse {
    session_id: String,
}

#[derive(Serialize)]
struct SessionStateResponse {
    goals: usize,
    complete: bool,
    tactics_applied: usize,
}

#[derive(Deserialize)]
struct ApplyTacticRequest {
    tactic: String,
}

#[derive(Serialize)]
struct ApplyTacticResponse {
    success: bool,
    complete: bool,
    goals_remaining: usize,
    message: String,
}

#[derive(Serialize)]
struct HealthResponse {
    status: String,
    version: String,
}

#[derive(Serialize)]
struct ProversResponse {
    provers: Vec<ProverInfo>,
}

#[derive(Serialize)]
struct ProverInfo {
    name: String,
    tier: u8,
    complexity: u8,
}

// ========== Error Handling ==========

#[derive(Debug)]
enum AppError {
    BadRequest(String),
    NotFound(String),
    ParseError(String),
    VerificationError(String),
    InternalError(String),
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let (status, message) = match self {
            AppError::BadRequest(msg) => (StatusCode::BAD_REQUEST, msg),
            AppError::NotFound(msg) => (StatusCode::NOT_FOUND, msg),
            AppError::ParseError(msg) => (StatusCode::BAD_REQUEST, format!("Parse error: {}", msg)),
            AppError::VerificationError(msg) => {
                (StatusCode::UNPROCESSABLE_ENTITY, format!("Verification error: {}", msg))
            }
            AppError::InternalError(msg) => {
                (StatusCode::INTERNAL_SERVER_ERROR, format!("Internal error: {}", msg))
            }
        };

        let body = Json(serde_json::json!({
            "error": message,
        }));

        (status, body).into_response()
    }
}

// Import for WebSocket stream splitting
use futures::stream::StreamExt;
use futures::SinkExt;
