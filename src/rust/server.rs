// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: AGPL-3.0-or-later

//! HTTP API server for ECHIDNA
//!
//! Provides REST API and WebSocket endpoints for theorem proving

use anyhow::Result;
use axum::{
    extract::{Path, Query, State},
    http::StatusCode,
    response::{IntoResponse, Response},
    routing::{get, post},
    Json, Router,
};
use colored::Colorize;
use echidna::agent::meta_controller::{MetaController, Plan};
use echidna::agent::AgenticGoal;
use echidna::core::{Goal, ProofState, Tactic, TacticResult, Term};
use echidna::diagnostics::HealthStatus;
use echidna::dispatch::ProverDispatcher;
use echidna::provers::ProverOutcome;
use echidna::verification::StatisticsTracker;
use echidna::{ProverBackend, ProverConfig, ProverKind};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock};
use tower_http::cors::CorsLayer;
use tracing::{debug, info, instrument};

/// Application state shared across handlers
#[derive(Clone)]
struct AppState {
    /// Active proof sessions (session_id -> ProofSession)
    sessions: Arc<RwLock<HashMap<String, Arc<Mutex<ProofSession>>>>>,
    /// HTTP client for Julia ML API
    ml_client: Client,
    /// Julia ML API base URL
    ml_api_url: String,
    /// MetaController — shared (prover × coprocessor) planner with persistent
    /// StatisticsTracker.  Survives request boundaries so the Bayesian routing
    /// state accumulates across the server's lifetime.  All handlers that
    /// perform goal-aware dispatch share this single instance.
    meta_controller: Arc<MetaController>,
    /// Shared proof-outcome statistics used by MetaController for Bayesian
    /// routing and exported to Julia for GNN online learning.
    stats: Arc<RwLock<StatisticsTracker>>,
    /// Prover dispatcher for trust-hardening pipeline and health monitoring
    dispatcher: Arc<ProverDispatcher>,
}

/// A proof session
struct ProofSession {
    prover: Box<dyn ProverBackend>,
    state: Option<ProofState>,
    history: Vec<String>,
}

const DEFAULT_ML_API_URL: &str = "http://127.0.0.1:8090";

/// Start the HTTP server
pub async fn start_server(port: u16, host: String, enable_cors: bool) -> Result<()> {
    // Create HTTP client for Julia ML API
    let ml_client = Client::builder().timeout(Duration::from_secs(10)).build()?;

    let ml_api_url =
        std::env::var("ECHIDNA_ML_API_URL").unwrap_or_else(|_| DEFAULT_ML_API_URL.to_string());

    // Security: Validate that the ML API URL is either local or explicitly allowed
    if !ml_api_url.starts_with("http://127.0.0.1") && !ml_api_url.starts_with("http://localhost") {
        info!("⚠ Untrusted ML API URL detected: {}. Baseline security policy requires local or trusted endpoint.", ml_api_url);
    }

    // Test Julia ML connection
    match ml_client.get(format!("{}/health", ml_api_url)).send().await {
        Ok(resp) if resp.status().is_success() => {
            info!("✓ Connected to Julia ML API at {}", ml_api_url);
        },
        _ => {
            info!(
                "⚠ Julia ML API not available at {} (will use fallback)",
                ml_api_url
            );
        },
    }

    // Shared stats tracker — MetaController uses it for Bayesian routing;
    // the background GNN sync task pushes snapshots to Julia for online learning.
    let stats = Arc::new(RwLock::new(StatisticsTracker::new()));
    let meta_controller = Arc::new(MetaController::new().with_stats(stats.clone()));

    // Create prover dispatcher with default configuration.
    // When compiled with --features verisim, attach the VeriSimDB writer so
    // every HTTP proof attempt (including parse failures) feeds the S4 learning
    // loop.  The writer runs fire-and-forget; a VeriSimDB outage never blocks
    // or alters a dispatch result.
    let dispatcher = {
        let d = ProverDispatcher::new();
        #[cfg(feature = "verisim")]
        let d = {
            let url = std::env::var("VERISIM_URL")
                .unwrap_or_else(|_| "http://localhost:8080".to_string());
            info!("✓ VeriSim writer attached at {}", url);
            d.with_verisim_writer(&url)
        };
        Arc::new(d)
    };
    info!("✓ Initialized prover dispatcher for trust-hardening pipeline");

    let state = AppState {
        sessions: Arc::new(RwLock::new(HashMap::new())),
        ml_client,
        ml_api_url,
        meta_controller,
        stats,
        dispatcher,
    };

    // GNN training sync — background task that pushes accumulated proof-outcome
    // stats to Julia's /training/update endpoint every 60 seconds.
    // Only fires when >= 10 new outcomes have accumulated since the last push,
    // so idle servers incur no traffic.  Errors are logged at debug level and
    // do not affect the main server loop (fire-and-forget).
    {
        let sync_stats = state.stats.clone();
        let sync_client = state.ml_client.clone();
        let sync_url = state.ml_api_url.clone();
        tokio::spawn(async move {
            let mut last_push_count: u64 = 0;
            let mut interval = tokio::time::interval(Duration::from_secs(60));
            interval.tick().await; // consume the immediate first tick; wait 60s before first push
            loop {
                interval.tick().await;
                let (total, records) = {
                    let guard = sync_stats.read().await;
                    (guard.total_attempts(), guard.export_records())
                };
                if total < last_push_count + 10 || records.is_empty() {
                    continue;
                }
                last_push_count = total;
                let url = format!("{}/training/update", sync_url);
                let payload = json!({ "records": records });
                match sync_client.post(&url).json(&payload).send().await {
                    Ok(resp) if resp.status().is_success() => {
                        info!(
                            "GNN training sync: {} records pushed to Julia",
                            records.len()
                        );
                    },
                    Ok(resp) => {
                        debug!("GNN training sync: Julia returned {}", resp.status());
                    },
                    Err(e) => {
                        debug!("GNN training sync: Julia unavailable ({})", e);
                    },
                }
            }
        });
    }

    // Build router
    let mut app = Router::new()
        // Groove discovery endpoint — returns capability manifest for service mesh.
        // See Groove.idr echidnaManifest for the canonical ABI definition.
        .route("/.well-known/groove", get(groove_manifest))
        // REST API endpoints
        .route("/api/health", get(health_check))
        .route("/api/diagnostics/health", get(diagnostics_health_handler))
        .route("/api/provers", get(list_provers))
        .route("/api/prove", post(prove_handler))
        .route("/api/verify", post(verify_handler))
        .route("/api/verify_parallel", post(verify_parallel_handler))
        .route("/api/verify_raw", post(verify_raw_handler))
        .route("/api/suggest", post(suggest_handler))
        .route("/api/search", get(search_handler))
        .route("/api/session/create", post(create_session))
        .route("/api/session/{id}/state", get(get_session_state))
        .route("/api/session/{id}/apply", post(apply_tactic_handler))
        .route("/api/session/{id}/tree", get(get_proof_tree))
        // Additional UI-specific endpoints
        .route("/api/agent/plan", post(agent_plan_handler))
        .route("/api/aspect-tags", get(get_aspect_tags))
        .route("/api/tactics/suggest", post(suggest_tactics_ui))
        .route("/api/theorems/search", get(search_theorems_ui))
        // WebSocket endpoint (disabled - requires axum ws feature)
        // .route("/ws/interactive", get(websocket_handler))
        .with_state(state);

    // Add CORS if enabled
    if enable_cors {
        app = app.layer(CorsLayer::permissive());
    }

    // Bind server
    let addr: SocketAddr = format!("{}:{}", host, port).parse()?;

    println!(
        "{}",
        "╔═══════════════════════════════════════════════════════════╗".cyan()
    );
    println!(
        "{}",
        "║  ECHIDNA HTTP API Server                                  ║"
            .cyan()
            .bold()
    );
    println!(
        "{}",
        "╚═══════════════════════════════════════════════════════════╝".cyan()
    );
    println!();
    println!(
        "Server listening on: {}",
        format!("https://{}", addr).green().bold()
    );
    println!();
    println!("{}", "Endpoints:".yellow().bold());
    println!("  GET  /.well-known/groove       - Groove discovery manifest");
    println!("  GET  /api/health              - Health check");
    println!("  GET  /api/provers             - List available provers");
    println!("  POST /api/prove               - Prove a theorem");
    println!("  POST /api/verify              - Verify a proof");
    println!("  POST /api/suggest             - Get tactic suggestions");
    println!("  GET  /api/search?q=<pattern>  - Search theorems");
    println!("  POST /api/session/create      - Create proof session");
    println!("  GET  /api/session/{{id}}/state   - Get session state");
    println!("  POST /api/session/{{id}}/apply   - Apply tactic to session");
    println!("  WS   /ws/interactive          - WebSocket live proof session");
    println!();
    println!("Press Ctrl+C to stop the server");
    println!();

    // Start server
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;

    Ok(())
}

// ========== Agent Planning ==========

/// Request to `POST /api/agent/plan`.
///
/// Asks the MetaController to plan a proof attempt: which prover to use,
/// which coprocessor preconditions to run first, and the Bayesian-estimated
/// timeout.  The response is a `Plan` that callers can inspect before
/// deciding whether to submit a full `/api/verify` or `/api/prove` request.
///
/// `aspects` drive the coprocessor routing (e.g. `"arithmetic.factorisation"`
/// triggers a Math precondition; `"algebra.groebner.basis"` triggers Singular).
/// `preferred_prover` and `candidates` are both optional — omitting both lets
/// the Pareto ranker pick freely from Z3 as the default.
#[derive(Debug, Deserialize)]
struct AgentPlanRequest {
    /// Goal aspect tags (e.g. `["arithmetic.factorisation", "crypto.hash.sha256"]`).
    #[serde(default)]
    aspects: Vec<String>,

    /// Client's preferred prover, if any.  Overridden by Pareto ranking when
    /// `candidates` is non-empty.
    preferred_prover: Option<ProverKind>,

    /// Candidate provers to rank.  When empty, `preferred_prover` (or Z3)
    /// is selected directly without Pareto scoring.
    #[serde(default)]
    candidates: Vec<ProverKind>,

    /// Default timeout hint (ms) used when no historical data is available.
    #[serde(default = "default_timeout_ms")]
    default_timeout_ms: u64,
}

fn default_timeout_ms() -> u64 {
    30_000
}

/// `POST /api/agent/plan` — return a MetaController plan for the given goal aspects.
///
/// Does not execute any provers or coprocessors; it only plans.  Callers use
/// the returned `coprocessor_preconditions` to understand what computational
/// preparation the system recommends before submitting the proof content.
async fn agent_plan_handler(
    State(state): State<AppState>,
    Json(req): Json<AgentPlanRequest>,
) -> impl IntoResponse {
    // Build a minimal AgenticGoal from the request metadata.  The goal target
    // is a placeholder (`Term::Const("?")`) because planning doesn't inspect
    // the proof content — only the aspects and prover preferences matter here.
    use echidna::agent::Priority;
    let goal = AgenticGoal {
        goal: Goal {
            id: uuid::Uuid::new_v4().to_string(),
            target: Term::Const("?".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::Medium,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: req.preferred_prover,
        aspects: req.aspects,
        parent: None,
    };

    let plan: Plan = if req.candidates.is_empty() {
        state.meta_controller.plan(&goal).await
    } else {
        use echidna::verification::confidence::TrustLevel;
        state
            .meta_controller
            .plan_with_pareto(
                &goal,
                &req.candidates,
                req.default_timeout_ms,
                TrustLevel::Level2,
            )
            .await
    };

    Json(json!({
        "prover": format!("{:?}", plan.prover),
        "estimated_timeout_ms": plan.estimated_timeout_ms,
        "rationale": plan.rationale,
        "coprocessor_preconditions": plan.coprocessor_preconditions
            .iter()
            .map(|p| json!({
                "kind": format!("{:?}", p.kind),
                "aspect": p.aspect,
            }))
            .collect::<Vec<_>>(),
    }))
}

// ========== Groove Discovery ==========

/// Groove capability manifest for ECHIDNA.
///
/// Returns the service's capabilities in the standard Groove format so that
/// Gossamer, PanLL, and other groove-aware systems can discover ECHIDNA by
/// probing GET /.well-known/groove. See Groove.idr echidnaManifest for the
/// canonical ABI definition.
///
/// Capabilities offered:
///   - theorem-proving: Multi-backend theorem proving (48 provers)
///
/// Capabilities consumed:
///   - octad-storage (VeriSimDB): Persist proof artifacts as octad entities
///   - scanning (Hypatia): Trigger re-verification after codebase changes
async fn groove_manifest() -> Json<serde_json::Value> {
    let core_count = echidna::ProverKind::all_core().len();
    let advertised_count = echidna::ProverKind::all().len();
    Json(json!({
        "groove_version": "1",
        "service_id": "echidna",
        "service_version": env!("CARGO_PKG_VERSION"),
        "capabilities": {
            "theorem_proving": {
                "type": "theorem-proving",
                "description": format!(
                    "Neurosymbolic theorem proving — {} core / {} advertised prover backends",
                    core_count, advertised_count
                ),
                "protocol": "http",
                "endpoint": "/api/prove",
                "requires_auth": false,
                "panel_compatible": true
            }
        },
        "consumes": ["octad-storage", "scanning"],
        "endpoints": {
            "provers": "/api/provers",
            "prove":   "/api/prove",
            "verify":  "/api/verify",
            "health":  "/api/health"
        },
        "health": "/api/health",
        "applicability": ["individual", "team"]
    }))
}

// ========== REST API Handlers ==========

/// Health check endpoint
async fn health_check() -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "ok".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
    })
}

/// Detailed diagnostics health endpoint
/// Returns full HealthStatus snapshot from dispatcher with prover metrics and degradation mode
async fn diagnostics_health_handler(State(app_state): State<AppState>) -> Json<HealthStatus> {
    let health = app_state.dispatcher.health_status();
    Json(health)
}

/// List available provers
async fn list_provers() -> Json<ProversResponse> {
    let provers = ProverKind::all_core()
        .into_iter()
        .map(|prover| ProverInfo {
            name: format!("{:?}", prover),
            tier: prover.tier(),
            complexity: prover.complexity(),
        })
        .collect();

    Json(ProversResponse { provers })
}

/// Prove theorem endpoint
async fn prove_handler(
    State(app_state): State<AppState>,
    Json(req): Json<ProveRequest>,
) -> Result<Json<ProveResponse>, AppError> {
    info!("Prove request for prover: {:?}", req.prover);

    // Route through the full dispatch pipeline when the verisim feature is
    // active.  This fires the VeriSimDB writer for every HTTP proof (parse
    // failures and final results), closing the S4 learning loop.  The writer
    // runs fire-and-forget — a VeriSimDB outage never blocks or alters a
    // result.  Response shape (success/goals/message) is preserved.
    #[cfg(feature = "verisim")]
    {
        let result = app_state
            .dispatcher
            .verify_proof(req.prover, &req.content)
            .await
            .map_err(|e| AppError::VerificationError(e.to_string()))?;
        return Ok(Json(ProveResponse {
            success: result.verified,
            goals: result.goals_remaining,
            message: result.message,
        }));
    }

    // Non-verisim path: direct factory + prover call (existing behaviour).
    #[cfg(not(feature = "verisim"))]
    {
        // Create prover
        let config = ProverConfig {
            timeout: req.timeout.unwrap_or(300),
            neural_enabled: req.neural.unwrap_or(true),
            ..ProverConfig::default()
        };

        let prover = echidna::provers::ProverFactory::create(req.prover, config)
            .map_err(|e| AppError::InternalError(e.to_string()))?;

        // Parse proof
        let state = prover
            .parse_string(&req.content)
            .await
            .map_err(|e| AppError::ParseError(e.to_string()))?;

        // Fail-fast on empty parse results (fixes false-positive: unrecognised
        // content produced an empty ProofState that re-exported to an empty file
        // which the backend prover then happily accepted).
        if is_empty_state(&state) && !req.content.trim().is_empty() {
            let outcome = ProverOutcome::InvalidInput {
                reason: "Parse produced no goals, theorems, definitions, or axioms — \
                         content not recognised by the selected prover backend"
                    .to_string(),
                location: None,
            };
            app_state
                .dispatcher
                .record_prover_result(req.prover, &outcome, 0);
            return Ok(Json(ProveResponse {
                success: false,
                goals: 0,
                message: "Parse produced no goals, theorems, definitions, or axioms — \
                         content not recognised by the selected prover backend"
                    .to_string(),
            }));
        }

        // Verify proof and record health metrics
        let verify_start = Instant::now();
        let valid = prover
            .verify_proof(&state)
            .await
            .map_err(|e| AppError::VerificationError(e.to_string()))?;
        let verify_elapsed_ms = verify_start.elapsed().as_millis() as u64;

        let outcome = if valid {
            ProverOutcome::Proved {
                elapsed_ms: verify_elapsed_ms,
            }
        } else {
            ProverOutcome::NoProofFound {
                elapsed_ms: verify_elapsed_ms,
                reason: Some("Proof verification failed".to_string()),
            }
        };
        app_state
            .dispatcher
            .record_prover_result(req.prover, &outcome, verify_elapsed_ms);

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
}

/// Verify proof endpoint
async fn verify_handler(Json(req): Json<VerifyRequest>) -> Result<Json<VerifyResponse>, AppError> {
    info!("Verify request for prover: {:?}", req.prover);

    // SMT query mode: when users send raw SMT-LIB with (check-sat) to Z3/CVC5,
    // run passthrough evaluation instead of proof-obligation negation semantics.
    if should_passthrough_smt_eval(&req) {
        let Json(raw) = verify_raw_handler(Json(req.clone())).await?;
        let smt_status =
            extract_smt_status(&raw.stdout).or_else(|| extract_smt_status(&raw.stderr));
        let goals_remaining = if matches!(smt_status.as_deref(), Some("unsat")) {
            0
        } else {
            1
        };

        // A completed SMT query is not necessarily a discharged obligation.
        // Only unsat closes a query interpreted as the negated obligation.
        let verified = raw.valid && matches!(smt_status.as_deref(), Some("unsat"));
        let outcome_str = if verified {
            "PROVED"
        } else {
            "NO_PROOF_FOUND"
        };
        return Ok(Json(VerifyResponse {
            valid: verified,
            outcome: outcome_str.to_string(),
            goals_remaining,
            tactics_used: 0,
            mode: Some("smt-query".to_string()),
            smt_status,
        }));
    }

    // Create prover
    let config = ProverConfig::default();
    let prover = echidna::provers::ProverFactory::create(req.prover, config)
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    // Parse proof — parse errors surface as INVALID_INPUT in the outcome.
    // We intentionally don't forward the raw error message to the response
    // body (it may leak internal paths or prover internals).
    let state = match prover.parse_string(&req.content).await {
        Ok(s) => s,
        Err(_) => {
            return Ok(Json(VerifyResponse {
                valid: false,
                outcome: "INVALID_INPUT".to_string(),
                goals_remaining: 0,
                tactics_used: 0,
                mode: None,
                smt_status: None,
            }));
        },
    };

    // Fail-fast on empty parse results (see prove_handler comment).
    if is_empty_state(&state) && !req.content.trim().is_empty() {
        return Ok(Json(VerifyResponse {
            valid: false,
            outcome: "INVALID_INPUT".to_string(),
            goals_remaining: 0,
            tactics_used: 0,
            mode: None,
            smt_status: None,
        }));
    }

    // NOTE: a richer `.check()` call returning a `ProverOutcome` taxonomy
    // lived here until 2026-04-17 but the typed-outcome module was never
    // committed (see z3.rs note). Reverted to `verify_proof()` so the HTTP
    // API is no worse than it was before the dropped refactor; the outcome
    // string is a two-valued approximation of the planned taxonomy.
    // Tracked in AI-WORK-todo.md phase-2 followups.
    let valid = prover
        .verify_proof(&state)
        .await
        .map_err(|e| AppError::VerificationError(e.to_string()))?;

    Ok(Json(VerifyResponse {
        valid,
        outcome: if valid {
            "PROVED".to_string()
        } else {
            "NO_PROOF_FOUND".to_string()
        },
        goals_remaining: if valid { 0 } else { state.goals.len() },
        tactics_used: state.proof_script.len(),
        mode: None,
        smt_status: None,
    }))
}

/// `/api/verify_parallel` — L2 Chapel parallel dispatch.
///
/// Fans out to multiple prover backends simultaneously (when the `chapel`
/// Cargo feature is compiled in and the Chapel runtime is available).
/// Returns the first successful result through the standard trust pipeline.
/// Falls back to sequential `select_prover` heuristic when Chapel is
/// unavailable. Callers that want a specific prover should use `/api/verify`.
async fn verify_parallel_handler(
    Json(req): Json<serde_json::Value>,
) -> Result<Json<serde_json::Value>, AppError> {
    let content = req
        .get("content")
        .and_then(|v| v.as_str())
        .ok_or_else(|| AppError::BadRequest("Missing 'content' field".to_string()))?;

    info!("verify_parallel request ({} bytes)", content.len());

    let dispatcher = ProverDispatcher::new();
    let result = dispatcher
        .verify_proof_parallel(content)
        .await
        .map_err(|e| AppError::VerificationError(e.to_string()))?;

    Ok(Json(serde_json::json!({
        "valid": result.verified,
        "outcome": result.outcome.status_str(),
        "provers_used": result.provers_used,
        "trust_level": result.trust_level as u8,
        "proof_time_ms": result.proof_time_ms,
        "goals_remaining": result.goals_remaining,
        "cross_checked": result.cross_checked,
        "message": result.message,
    })))
}

/// `/api/verify_raw` — writes the original `content` to a temp file with
/// the right extension for the prover, then invokes the backend binary
/// directly. Bypasses `parse_string`/`export` round-trip entirely — the
/// content you send is the content the prover sees.
///
/// This is the real fix for the parse+export round-trip bug: no
/// information is lost between the wire and the prover binary.
/// Currently supports: z3, cvc5, coq, lean, agda, idris2, vampire,
/// eprover. Other provers fall through to the legacy verify_handler path.
#[instrument(skip(req))]
async fn verify_raw_handler(
    Json(req): Json<VerifyRequest>,
) -> Result<Json<VerifyRawResponse>, AppError> {
    use tokio::process::Command;

    info!("Verify_raw request for prover: {:?}", req.prover);

    if req.content.trim().is_empty() {
        return Ok(Json(VerifyRawResponse {
            valid: false,
            exit_code: -1,
            stdout: String::new(),
            stderr: String::new(),
            message: "empty content".to_string(),
        }));
    }

    type Interpret = fn(i32, &str, &str) -> (bool, String);
    let (ext, program, args, interpret): (&str, &str, Vec<String>, Interpret) = match req.prover {
        echidna::provers::ProverKind::Z3 => (
            "smt2",
            "z3",
            vec!["-smt2".to_string()],
            |rc, stdout, _stderr| {
                let produced = stdout.contains("sat")
                    || stdout.contains("unsat")
                    || stdout.contains("unknown");
                (rc == 0 && produced, format!("exit={} smt-output", rc))
            },
        ),
        echidna::provers::ProverKind::CVC5 => ("smt2", "cvc5", vec![], |rc, stdout, _stderr| {
            let produced =
                stdout.contains("sat") || stdout.contains("unsat") || stdout.contains("unknown");
            (rc == 0 && produced, format!("exit={} smt-output", rc))
        }),
        echidna::provers::ProverKind::Coq => (
            "v",
            "coqc",
            vec!["-q".to_string()],
            |rc, _stdout, _stderr| (rc == 0, format!("exit={}", rc)),
        ),
        echidna::provers::ProverKind::Lean => ("lean", "lean", vec![], |rc, _stdout, _stderr| {
            (rc == 0, format!("exit={}", rc))
        }),
        echidna::provers::ProverKind::Agda => ("agda", "agda", vec![], |rc, _stdout, _stderr| {
            (rc == 0, format!("exit={}", rc))
        }),
        echidna::provers::ProverKind::Idris2 => (
            "idr",
            "idris2",
            vec!["--check".to_string()],
            |rc, _stdout, _stderr| (rc == 0, format!("exit={}", rc)),
        ),
        echidna::provers::ProverKind::Vampire => (
            "p",
            "vampire",
            vec!["--mode".to_string(), "casc".to_string()],
            |rc, stdout, _stderr| {
                let theorem = stdout.contains("SZS status Theorem")
                    || stdout.contains("SZS status Unsatisfiable");
                (rc == 0 || theorem, "szs-status".to_string())
            },
        ),
        echidna::provers::ProverKind::EProver => (
            "p",
            "eprover",
            vec!["--auto-schedule".to_string()],
            |rc, stdout, _stderr| {
                let theorem = stdout.contains("SZS status Theorem")
                    || stdout.contains("SZS status Unsatisfiable")
                    || stdout.contains("SZS status ContradictoryAxioms");
                (rc == 0 && theorem, "szs-status".to_string())
            },
        ),
        _ => {
            return Ok(Json(VerifyRawResponse {
                valid: false,
                exit_code: -1,
                stdout: String::new(),
                stderr: String::new(),
                message: format!(
                    "verify_raw not yet implemented for {:?} — use /api/verify",
                    req.prover
                ),
            }));
        },
    };

    // Write content to a unique temp file with the right extension.
    let tmpdir = std::env::temp_dir().join(format!("echidna_verify_raw_{}", std::process::id()));
    if let Err(e) = tokio::fs::create_dir_all(&tmpdir).await {
        return Ok(Json(VerifyRawResponse {
            valid: false,
            exit_code: -1,
            stdout: String::new(),
            stderr: String::new(),
            message: format!("tmpdir create failed: {}", e),
        }));
    }
    let filename = format!("Input.{}", ext);
    let path = tmpdir.join(&filename);
    if let Err(e) = tokio::fs::write(&path, req.content.as_bytes()).await {
        return Ok(Json(VerifyRawResponse {
            valid: false,
            exit_code: -1,
            stdout: String::new(),
            stderr: String::new(),
            message: format!("write failed: {}", e),
        }));
    }

    // Run the prover. cd to tmpdir for provers that care about module
    // name = filename (agda, coq, idris2, lean).
    let mut cmd = Command::new(program);
    cmd.current_dir(&tmpdir);
    for arg in &args {
        cmd.arg(arg);
    }
    cmd.arg(&filename);

    let output_result = cmd.output().await;
    // Best-effort cleanup; ignore errors.
    let _ = tokio::fs::remove_dir_all(&tmpdir).await;

    match output_result {
        Ok(output) => {
            let exit_code = output.status.code().unwrap_or(-1);
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            let (valid, message) = interpret(exit_code, &stdout, &stderr);
            Ok(Json(VerifyRawResponse {
                valid,
                exit_code,
                stdout: stdout.chars().take(1024).collect(),
                stderr: stderr.chars().take(1024).collect(),
                message,
            }))
        },
        Err(e) => Ok(Json(VerifyRawResponse {
            valid: false,
            exit_code: -1,
            stdout: String::new(),
            stderr: String::new(),
            message: format!("spawn failed: {} (is the '{}' binary on PATH?)", e, program),
        })),
    }
}

/// Return true if the parsed ProofState contains no meaningful structure.
/// Used to detect the parse+export round-trip bug: a prover backend's
/// `parse_string` returns an empty state on unrecognised input, then
/// `verify_proof` regenerates an empty file which the real backend binary
/// then accepts vacuously (false positive).
fn is_empty_state(state: &echidna::core::ProofState) -> bool {
    state.goals.is_empty()
        && state.context.theorems.is_empty()
        && state.context.axioms.is_empty()
        && state.context.definitions.is_empty()
        && state.context.variables.is_empty()
}

fn should_passthrough_smt_eval(req: &VerifyRequest) -> bool {
    matches!(req.prover, ProverKind::Z3 | ProverKind::CVC5)
        && req.content.to_ascii_lowercase().contains("(check-sat")
}

fn extract_smt_status(text: &str) -> Option<String> {
    let lower = text.to_ascii_lowercase();
    if lower.contains("unsat") {
        Some("unsat".to_string())
    } else if lower.contains("sat") {
        Some("sat".to_string())
    } else if lower.contains("unknown") {
        Some("unknown".to_string())
    } else {
        None
    }
}

/// Get tactic suggestions
async fn suggest_handler(
    State(state): State<AppState>,
    Json(req): Json<SuggestRequest>,
) -> Result<Json<SuggestResponse>, AppError> {
    info!("Suggest request for prover: {:?}", req.prover);

    // Try Julia ML API first
    let julia_req = json!({
        "goal": req.content,
        "prover": format!("{:?}", req.prover),
        "top_k": req.limit.unwrap_or(5)
    });

    match state
        .ml_client
        .post(format!("{}/suggest", state.ml_api_url))
        .json(&julia_req)
        .send()
        .await
    {
        Ok(resp) if resp.status().is_success() => {
            if let Ok(ml_resp) = resp.json::<serde_json::Value>().await {
                if let Some(suggestions_arr) = ml_resp["suggestions"].as_array() {
                    let suggestions: Vec<String> = suggestions_arr
                        .iter()
                        .filter_map(|s| s["tactic"].as_str().map(|t| t.to_string()))
                        .collect();

                    if !suggestions.is_empty() {
                        info!("✓ Got {} ML suggestions", suggestions.len());
                        return Ok(Json(SuggestResponse { suggestions }));
                    }
                }
            }
        },
        _ => {
            info!("ML API unavailable, using prover fallback");
        },
    }

    // Fallback: Use prover's built-in suggestions
    let config = ProverConfig::default();
    let prover = echidna::provers::ProverFactory::create(req.prover, config)
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    let state = prover
        .parse_string(&req.content)
        .await
        .map_err(|e| AppError::ParseError(e.to_string()))?;

    let tactics = prover
        .suggest_tactics(&state, req.limit.unwrap_or(5))
        .await
        .map_err(|e| AppError::InternalError(e.to_string()))?;

    let suggestions = tactics.iter().map(|t| format!("{:?}", t)).collect();

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

    info!(
        "Search request: pattern={}, prover={:?}",
        pattern, prover_name
    );

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

    // Cross-prover layer (see main.rs::search_command for rationale).
    // Folds VeriSimDB matches into the same response so REST clients
    // see results from backends without native search commands too.
    let verisim_url =
        std::env::var("VERISIM_URL").unwrap_or_else(|_| "http://localhost:8080".to_string());
    if let Ok(cross) = echidna::vcl_ut::cross_prover_search_names(&verisim_url, pattern, 50).await {
        all_results.extend(cross);
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
        goals: session
            .state
            .as_ref()
            .map(|s| s.goals.len())
            .unwrap_or_else(|| 0),
        complete: session
            .state
            .as_ref()
            .map(|s| s.is_complete())
            .unwrap_or(false),
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
        return Err(AppError::BadRequest(
            "No proof loaded in session".to_string(),
        ));
    }

    // Parse tactic (simplified)
    let tactic = parse_tactic_from_json(&req.tactic)?;

    // Apply tactic
    let proof_state = session.state.as_ref().unwrap();
    let result = session
        .prover
        .apply_tactic(proof_state, &tactic)
        .await
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
        },

        TacticResult::Error(msg) => Ok(Json(ApplyTacticResponse {
            success: false,
            complete: false,
            goals_remaining: session.state.as_ref().unwrap().goals.len(),
            message: msg,
        })),

        TacticResult::QED => {
            session.state.as_mut().unwrap().goals.clear();

            Ok(Json(ApplyTacticResponse {
                success: true,
                complete: true,
                goals_remaining: 0,
                message: "Proof complete!".to_string(),
            }))
        },
    }
}

/// Get aspect tags for filtering.
///
/// The tag vocabulary is intentionally hard-coded here — it's the UI's
/// facet list, not live-verified data, and needs to stay stable across
/// releases so saved filters keep working.
async fn get_aspect_tags() -> Json<AspectTagsResponse> {
    let tags = vec![
        AspectTag {
            name: "algebraic".to_string(),
            category: "domain".to_string(),
            active: false,
        },
        AspectTag {
            name: "geometric".to_string(),
            category: "domain".to_string(),
            active: false,
        },
        AspectTag {
            name: "logical".to_string(),
            category: "domain".to_string(),
            active: false,
        },
        AspectTag {
            name: "inductive".to_string(),
            category: "technique".to_string(),
            active: false,
        },
        AspectTag {
            name: "deductive".to_string(),
            category: "technique".to_string(),
            active: false,
        },
        AspectTag {
            name: "automated".to_string(),
            category: "technique".to_string(),
            active: false,
        },
    ];

    Json(AspectTagsResponse { tags })
}

/// Get proof tree for a session
async fn get_proof_tree(
    State(state): State<AppState>,
    Path(session_id): Path<String>,
) -> Result<Json<ProofTreeResponse>, AppError> {
    let sessions = state.sessions.read().await;
    let session = sessions
        .get(&session_id)
        .ok_or_else(|| AppError::NotFound(format!("Session not found: {}", session_id)))?;

    let session = session.lock().await;

    // Build proof tree from session state
    let tree = if let Some(proof_state) = &session.state {
        serde_json::json!({
            "id": "root",
            "type": "goal",
            "label": proof_state.goals.first()
                .map(|g| format!("{:?}", g.target))
                .unwrap_or_else(|| "No goals".to_string()),
            "children": []
        })
    } else {
        serde_json::json!({
            "id": "root",
            "type": "goal",
            "label": "No proof state",
            "children": []
        })
    };

    Ok(Json(ProofTreeResponse { tree }))
}

/// UI-specific tactic suggestion endpoint
async fn suggest_tactics_ui(
    Json(req): Json<SuggestTacticsUIRequest>,
) -> Result<Json<SuggestTacticsUIResponse>, AppError> {
    let prover = req.prover.as_deref().unwrap_or("Coq");
    let top_k = req.top_k.unwrap_or(5);

    info!(
        "UI tactic suggestion request - prover: {}, goal: {}",
        prover, req.goal
    );

    // Call Julia ML API for real AI predictions
    let client = reqwest::Client::new();
    let julia_url = "http://127.0.0.1:8090/suggest";

    let julia_request = serde_json::json!({
        "goal": req.goal,
        "prover": prover,
        "top_k": top_k
    });

    match client.post(julia_url).json(&julia_request).send().await {
        Ok(response) => {
            if response.status().is_success() {
                match response.json::<serde_json::Value>().await {
                    Ok(json) => {
                        let empty_vec = vec![];
                        let suggestions_json = json["suggestions"].as_array().unwrap_or(&empty_vec);
                        let suggestions: Vec<TacticSuggestion> = suggestions_json
                            .iter()
                            .map(|s| {
                                let confidence = s["confidence"].as_f64().unwrap_or(0.0);
                                let tactic = s["tactic"].as_str().unwrap_or("auto").to_string();
                                let premise = s
                                    .get("premises")
                                    .and_then(|p| p.as_array())
                                    .and_then(|arr| arr.first())
                                    .and_then(|v| v.as_str())
                                    .map(String::from);

                                // Infer aspect tags from confidence and tactic
                                let aspect_tags = if confidence > 0.8 {
                                    vec!["automated".to_string()]
                                } else if tactic.contains("intro") {
                                    vec!["deductive".to_string()]
                                } else {
                                    vec!["algebraic".to_string(), "deductive".to_string()]
                                };

                                TacticSuggestion {
                                    tactic,
                                    confidence,
                                    premise,
                                    aspect_tags,
                                }
                            })
                            .collect();

                        Ok(Json(SuggestTacticsUIResponse { suggestions }))
                    },
                    Err(e) => {
                        info!("Failed to parse Julia response: {}", e);
                        // Fall back to mock data
                        Ok(Json(SuggestTacticsUIResponse {
                            suggestions: vec![TacticSuggestion {
                                tactic: "auto".to_string(),
                                confidence: 0.5,
                                premise: None,
                                aspect_tags: vec!["automated".to_string()],
                            }],
                        }))
                    },
                }
            } else {
                info!("Julia API returned error status: {}", response.status());
                // Fall back to mock data
                Ok(Json(SuggestTacticsUIResponse {
                    suggestions: vec![TacticSuggestion {
                        tactic: "auto".to_string(),
                        confidence: 0.5,
                        premise: None,
                        aspect_tags: vec!["automated".to_string()],
                    }],
                }))
            }
        },
        Err(e) => {
            info!("Failed to connect to Julia ML API: {}", e);
            // Fall back to mock data if Julia service is down
            Ok(Json(SuggestTacticsUIResponse {
                suggestions: vec![TacticSuggestion {
                    tactic: "auto".to_string(),
                    confidence: 0.5,
                    premise: None,
                    aspect_tags: vec!["automated".to_string()],
                }],
            }))
        },
    }
}

/// UI-specific theorem search endpoint
async fn search_theorems_ui(
    Query(params): Query<HashMap<String, String>>,
) -> Result<Json<SearchTheoremsUIResponse>, AppError> {
    let query = params
        .get("query")
        .or_else(|| params.get("q"))
        .ok_or_else(|| AppError::BadRequest("Missing query parameter".to_string()))?;

    let _tags = params
        .get("tags")
        .map(|t| t.split(',').map(String::from).collect::<Vec<_>>())
        .unwrap_or_default();

    info!("UI theorem search: query={}", query);

    // Full-corpus search lives behind the REST interface
    // (`/api/search/theorems`) which indexes training_data/*.jsonl.
    // This UI endpoint is the keep-alive shim for the old ReScript
    // autocomplete — it returns canned exemplars so the UI has a
    // stable shape, and the real query goes through the search
    // workspace member.
    let results = vec![
        format!("Theorem: associativity_add (a + b) + c = a + (b + c)"),
        format!("Theorem: commutativity_mul a * b = b * a"),
        format!("Lemma: distributivity a * (b + c) = a * b + a * c"),
    ];

    Ok(Json(SearchTheoremsUIResponse { results }))
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
        "hollight" => Ok(ProverKind::HOLLight),
        "mizar" => Ok(ProverKind::Mizar),
        "pvs" => Ok(ProverKind::PVS),
        "acl2" => Ok(ProverKind::ACL2),
        "hol4" => Ok(ProverKind::HOL4),
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

#[derive(Clone, Deserialize)]
struct VerifyRequest {
    prover: ProverKind,
    content: String,
}

#[derive(Serialize)]
struct VerifyResponse {
    valid: bool,
    /// Typed outcome from the prover — one of PROVED, NO_PROOF_FOUND,
    /// INVALID_INPUT, UNSUPPORTED_FEATURE, TIMEOUT, INCONSISTENT_PREMISES,
    /// PROVER_ERROR, SYSTEM_ERROR.
    ///
    /// This is the primary result field; `valid` is a backward-compatible bool
    /// summary derived from it (true iff outcome == PROVED).
    outcome: String,
    goals_remaining: usize,
    tactics_used: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    mode: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    smt_status: Option<String>,
}

/// Raw-content verification response. Skips `parse_string`/`export` round
/// trip and invokes the prover binary directly on the supplied content.
#[derive(Serialize)]
struct VerifyRawResponse {
    valid: bool,
    exit_code: i32,
    stdout: String,
    stderr: String,
    message: String,
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

#[derive(Serialize)]
struct AspectTag {
    name: String,
    category: String,
    active: bool,
}

#[derive(Serialize)]
struct AspectTagsResponse {
    tags: Vec<AspectTag>,
}

#[derive(Serialize)]
struct ProofTreeResponse {
    tree: serde_json::Value,
}

#[derive(Deserialize)]
struct SuggestTacticsUIRequest {
    goal: String, // Changed from goal_id to accept goal text directly
    prover: Option<String>,
    #[allow(dead_code)] // Reserved for future aspect-tag filtering
    active_tags: Option<Vec<String>>,
    top_k: Option<usize>,
}

#[derive(Serialize)]
struct SuggestTacticsUIResponse {
    suggestions: Vec<TacticSuggestion>,
}

#[derive(Serialize)]
struct TacticSuggestion {
    tactic: String,
    confidence: f64,
    premise: Option<String>,
    aspect_tags: Vec<String>,
}

#[derive(Serialize)]
struct SearchTheoremsUIResponse {
    results: Vec<String>,
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
            AppError::VerificationError(msg) => (
                StatusCode::UNPROCESSABLE_ENTITY,
                format!("Verification error: {}", msg),
            ),
            AppError::InternalError(msg) => (
                StatusCode::INTERNAL_SERVER_ERROR,
                format!("Internal error: {}", msg),
            ),
        };

        let body = Json(serde_json::json!({
            "error": message,
        }));

        (status, body).into_response()
    }
}
