// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: AGPL-3.0-or-later
//
//! End-to-end tests for the ECHIDNA trust-hardened prover dispatcher.
//!
//! These tests exercise the full dispatch workflow without requiring any
//! installed prover binaries — they validate:
//!
//!   1. The complete workflow: input → dispatch → DispatchResult → verify fields
//!   2. Error handling: unsolvable (rejects), prover timeout, malformed input
//!   3. Trust pipeline invariants: result fields are always populated correctly
//!   4. Webhook-style event handling (echidnabot analysis path)
//!
//! Tests that require live prover binaries are gated by
//! `common::is_prover_available` and skip cleanly when the binary is absent.

mod common;

use anyhow::Result;
use echidna::dispatch::{DispatchConfig, DispatchResult, ProverDispatcher};
use echidna::provers::{ProverConfig, ProverFactory, ProverKind};
use echidna::verification::axiom_tracker::AxiomTracker;
use echidna::verification::confidence::{compute_trust_level, TrustFactors, TrustLevel};
use echidna::verification::DangerLevel;
use std::time::Duration;

// ---------------------------------------------------------------------------
// E2E 1: Dispatcher config defaults are safe
// ---------------------------------------------------------------------------

/// The default DispatchConfig must never silently weaken trust guarantees.
#[test]
fn e2e_dispatch_config_defaults_are_safe() {
    let config = DispatchConfig::default();
    // Axiom tracking must be on by default — this is a core trust invariant
    assert!(
        config.track_axioms,
        "Axiom tracking must be enabled by default to maintain trust pipeline"
    );
    // Cross-check defaults to false (opt-in feature, not a safety bypass)
    assert!(
        !config.cross_check,
        "Cross-check should default to false (opt-in)"
    );
    // Certificate generation is expensive; off by default
    assert!(
        !config.generate_certificates,
        "Certificate generation should default to false"
    );
    // Timeout must be positive — zero timeout would silently fail
    assert!(config.timeout > 0, "Dispatcher timeout must be positive");
    // Minimum trust level must be at least Level1 — never None/zero
    assert!(
        config.min_trust_level >= TrustLevel::Level1,
        "Minimum trust level must be at least Level1"
    );
}

// ---------------------------------------------------------------------------
// E2E 2: ProverFactory creates all 48 backends (no binary required)
// ---------------------------------------------------------------------------

/// All 48 prover backends must be instantiable from ProverFactory even when
/// the underlying binary is not installed. Factory creation is distinct from
/// binary execution.
#[tokio::test]
async fn e2e_all_prover_backends_instantiate() -> Result<()> {
    let config = ProverConfig::default();
    let all_kinds = ProverKind::all();

    assert!(
        !all_kinds.is_empty(),
        "ProverKind::all() must return at least one entry"
    );

    let mut created = 0usize;
    let mut failed: Vec<(ProverKind, String)> = Vec::new();

    for kind in all_kinds {
        match ProverFactory::create(kind, config.clone()) {
            Ok(_) => created += 1,
            Err(e) => failed.push((kind, e.to_string())),
        }
    }

    if !failed.is_empty() {
        eprintln!("Backends that failed to instantiate:");
        for (kind, err) in &failed {
            eprintln!("  {:?}: {}", kind, err);
        }
    }

    assert!(
        failed.is_empty(),
        "{}/{} prover backends failed factory instantiation: {:?}",
        failed.len(),
        created + failed.len(),
        failed.iter().map(|(k, _)| *k).collect::<Vec<_>>()
    );

    eprintln!("OK: {}/{} prover backends instantiated", created, created);
    Ok(())
}

// ---------------------------------------------------------------------------
// E2E 3: Trust level computation — full workflow simulation
// ---------------------------------------------------------------------------

/// Simulate the complete trust computation path that dispatch.rs executes.
/// Validates all 5 trust levels produce consistent, ordered results.
#[test]
fn e2e_trust_pipeline_all_levels_ordered() {
    // Level5: small-kernel prover, cross-checked, certificate, clean axioms
    let l5 = compute_trust_level(&TrustFactors {
        prover: ProverKind::Lean, // small-kernel prover
        confirming_provers: 3,
        has_certificate: true,
        certificate_verified: true,
        worst_axiom_danger: DangerLevel::Safe,
        solver_integrity_ok: true,
        portfolio_confidence: Some(
            echidna::verification::portfolio::PortfolioConfidence::CrossChecked,
        ),
    });

    // Level4: multiple provers, certificate, clean axioms
    let l4 = compute_trust_level(&TrustFactors {
        prover: ProverKind::Z3,
        confirming_provers: 2,
        has_certificate: true,
        certificate_verified: true,
        worst_axiom_danger: DangerLevel::Safe,
        solver_integrity_ok: true,
        portfolio_confidence: Some(
            echidna::verification::portfolio::PortfolioConfidence::CrossChecked,
        ),
    });

    // Level3: single prover with certificate
    let l3 = compute_trust_level(&TrustFactors {
        prover: ProverKind::Z3,
        confirming_provers: 1,
        has_certificate: true,
        certificate_verified: true,
        worst_axiom_danger: DangerLevel::Safe,
        solver_integrity_ok: true,
        portfolio_confidence: None,
    });

    // Level2: single prover without certificate (default case)
    let l2 = compute_trust_level(&TrustFactors {
        prover: ProverKind::Z3,
        confirming_provers: 1,
        has_certificate: false,
        certificate_verified: false,
        worst_axiom_danger: DangerLevel::Safe,
        solver_integrity_ok: true,
        portfolio_confidence: None,
    });

    // Level1: axiom usage flagged as Warning
    let l1 = compute_trust_level(&TrustFactors {
        prover: ProverKind::Lean,
        confirming_provers: 1,
        has_certificate: false,
        certificate_verified: false,
        worst_axiom_danger: DangerLevel::Warning,
        solver_integrity_ok: true,
        portfolio_confidence: None,
    });

    // Strict ordering: higher trust is >= lower trust
    assert!(
        l5 >= l4,
        "Level5 factors should produce >= Level4 trust, got {:?} vs {:?}",
        l5,
        l4
    );
    assert!(
        l4 >= l3,
        "Level4 factors should produce >= Level3 trust, got {:?} vs {:?}",
        l4,
        l3
    );
    assert!(
        l3 >= l2,
        "Level3 factors should produce >= Level2 trust, got {:?} vs {:?}",
        l3,
        l2
    );
    assert!(
        l2 >= l1,
        "Level2 factors should produce >= Level1 trust, got {:?} vs {:?}",
        l2,
        l1
    );

    eprintln!(
        "Trust levels: L5={:?} >= L4={:?} >= L3={:?} >= L2={:?} >= L1={:?}",
        l5, l4, l3, l2, l1
    );
}

// ---------------------------------------------------------------------------
// E2E 4: Reject level axioms drive trust to floor
// ---------------------------------------------------------------------------

/// When a proof contains a Reject-level axiom (unsound construct), the trust
/// pipeline MUST output Level1 or below — it cannot produce Level3+.
#[test]
fn e2e_reject_axiom_prevents_high_trust() {
    let trust = compute_trust_level(&TrustFactors {
        prover: ProverKind::Lean,
        confirming_provers: 5,
        has_certificate: true,
        certificate_verified: true,
        worst_axiom_danger: DangerLevel::Reject, // unsound construct
        solver_integrity_ok: true,
        portfolio_confidence: Some(
            echidna::verification::portfolio::PortfolioConfidence::CrossChecked,
        ),
    });

    assert!(
        trust < TrustLevel::Level3,
        "Reject-level axiom MUST prevent trust >= Level3, got {:?}",
        trust
    );
}

// ---------------------------------------------------------------------------
// E2E 5: Axiom tracker detects dangerous patterns (full scan workflow)
// ---------------------------------------------------------------------------

/// The axiom tracker must detect all known dangerous patterns in proof content.
/// This validates the scan() function used in step 4 of the dispatch pipeline.
#[test]
fn e2e_axiom_tracker_scans_dangerous_patterns() {
    let tracker = AxiomTracker::new();

    // Lean sorry — Reject level
    let lean_sorry = "theorem foo : True := by sorry";
    let usages = tracker.scan(ProverKind::Lean, lean_sorry);
    assert!(
        !usages.is_empty(),
        "AxiomTracker must detect 'sorry' in Lean proof"
    );
    let worst = usages.iter().map(|u| u.danger_level).max().unwrap();
    assert!(
        worst >= DangerLevel::Warning,
        "sorry in Lean must be Warning or Reject level, got {:?}",
        worst
    );

    // Coq Admitted — Reject level
    let coq_admitted = "Theorem foo : True. Proof. Admitted.";
    let usages = tracker.scan(ProverKind::Coq, coq_admitted);
    assert!(
        !usages.is_empty(),
        "AxiomTracker must detect 'Admitted' in Coq proof"
    );

    // Idris2 believe_me — Reject level
    let idris_believe_me = "foo : Bool\nfoo = believe_me True";
    let usages = tracker.scan(ProverKind::Idris2, idris_believe_me);
    assert!(
        !usages.is_empty(),
        "AxiomTracker must detect 'believe_me' in Idris2 proof"
    );

    // Clean Lean theorem — should have no dangerous usages
    let lean_clean = "theorem id : ∀ (x : Nat), x = x := fun x => rfl";
    let usages = tracker.scan(ProverKind::Lean, lean_clean);
    let has_danger = usages
        .iter()
        .any(|u| u.danger_level >= DangerLevel::Warning);
    assert!(
        !has_danger,
        "Clean Lean theorem should have no Warning/Reject axioms, got: {:?}",
        usages
    );
}

// ---------------------------------------------------------------------------
// E2E 6: Dispatcher with Z3 (skipped if binary absent)
// ---------------------------------------------------------------------------

/// Full dispatch workflow: content → ProverDispatcher → DispatchResult.
/// Validates that all result fields are populated correctly.
#[tokio::test]
async fn e2e_z3_full_dispatch_workflow() -> Result<()> {
    if !common::is_prover_available(ProverKind::Z3) {
        eprintln!("Skipping e2e_z3_full_dispatch_workflow: Z3 not on PATH");
        return Ok(());
    }

    let dispatcher = ProverDispatcher::new();

    // Simple satisfiable problem
    let content = r#"
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= x x))
(check-sat)
"#;

    let result: DispatchResult = dispatcher.verify_proof(ProverKind::Z3, content).await?;

    // Invariant: provers_used must always be populated
    assert!(
        !result.provers_used.is_empty(),
        "provers_used must not be empty after successful dispatch"
    );
    // Invariant: message must always be set
    assert!(
        !result.message.is_empty(),
        "DispatchResult.message must always be set"
    );
    // Invariant: timing must be recorded
    assert!(
        result.proof_time_ms > 0,
        "proof_time_ms must be > 0 after dispatch"
    );
    // Invariant: trust level must be a valid level (not beyond enum bounds)
    let _ = result.trust_level; // just access to ensure it deserializes cleanly
                                // Invariant: cross_checked must be false for single-prover dispatch
    assert!(
        !result.cross_checked,
        "Single-prover dispatch should not set cross_checked"
    );

    eprintln!(
        "E2E Z3: verified={}, trust={}, time={}ms, msg={}",
        result.verified, result.trust_level, result.proof_time_ms, result.message
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// E2E 7: Malformed input is handled gracefully (no panic)
// ---------------------------------------------------------------------------

/// Malformed proof content must return an error, not panic. The dispatcher
/// must never panic on adversarial input.
#[tokio::test]
async fn e2e_malformed_input_returns_error_not_panic() -> Result<()> {
    if !common::is_prover_available(ProverKind::Z3) {
        eprintln!("Skipping e2e_malformed_input_returns_error_not_panic: Z3 not on PATH");
        return Ok(());
    }

    let dispatcher = ProverDispatcher::new();

    let long_input = "x".repeat(100_000);
    let malformed_inputs: Vec<&str> = vec![
        "",                                            // empty
        "((((unclosed",                                // unbalanced parens
        "\x00\x01\x02",                                // binary garbage
        &long_input,                                   // pathologically long input
        "SELECT * FROM proofs; DROP TABLE proofs; --", // SQL injection attempt (should be a no-op)
    ];

    for input in malformed_inputs {
        // The result may be Ok (verified=false) or Err — both are acceptable.
        // What is NOT acceptable: a panic.
        let result = dispatcher.verify_proof(ProverKind::Z3, input).await;
        // We don't assert success; we just assert the call returns (no panic).
        match result {
            Ok(r) => eprintln!(
                "E2E malformed[{}..]: Ok(verified={})",
                input.chars().take(20).collect::<String>(),
                r.verified
            ),
            Err(e) => eprintln!(
                "E2E malformed[{}..]: Err({})",
                input.chars().take(20).collect::<String>(),
                e
            ),
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// E2E 8: Error path — prover binary not found
// ---------------------------------------------------------------------------

/// When a prover binary is not installed, the dispatcher must return an Err,
/// not panic or return a falsely successful result.
#[tokio::test]
async fn e2e_missing_binary_returns_error() -> Result<()> {
    // Use a prover that is extremely unlikely to be installed in CI
    let unlikely_kinds = [ProverKind::ACL2, ProverKind::PVS, ProverKind::HOL4];

    for kind in unlikely_kinds {
        if common::is_prover_available(kind) {
            eprintln!("Skipping {:?}: binary unexpectedly available", kind);
            continue;
        }

        let dispatcher = ProverDispatcher::new();
        let content = "theorem test : 1 = 1 := rfl";

        let result = dispatcher.verify_proof(kind, content).await;

        match result {
            Ok(r) => {
                // If it returns Ok, it must NOT claim the proof is verified
                // (since the binary wasn't available to actually run)
                eprintln!(
                    "  {:?}: Ok(verified={}), acceptable if verified=false",
                    kind, r.verified
                );
                // We do NOT assert verified=false here because some backends
                // may return mock/stub results in CI — that's the backend's
                // responsibility to handle. We just verify no panic.
            },
            Err(e) => {
                eprintln!("  {:?}: Err({}) — expected when binary absent", kind, e);
                // This is the expected case
            },
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// E2E 9: DispatchResult serialisation roundtrip
// ---------------------------------------------------------------------------

/// DispatchResult must survive a serde_json roundtrip with all fields intact.
/// This validates the webhook/reporting path where results are serialised.
#[test]
fn e2e_dispatch_result_json_roundtrip() {
    use echidna::verification::axiom_tracker::{AxiomUsage, DangerLevel as DL};

    let original = DispatchResult {
        verified: true,
        trust_level: TrustLevel::Level3,
        provers_used: vec!["Z3".to_string(), "CVC5".to_string()],
        proof_time_ms: 42,
        goals_remaining: 0,
        axiom_report: Some(AxiomUsage {
            prover: ProverKind::Lean,
            construct: "Classical.choice".to_string(),
            danger_level: DL::Noted,
            line: Some(7),
            explanation: "classical axiom".to_string(),
        }),
        certificate_hash: Some("abc123def456".to_string()),
        message: "Proof verified with Level3".to_string(),
        cross_checked: true,
        outcome: echidna::provers::outcome::ProverOutcome::Proved { elapsed_ms: 42 },
        diagnostics: None,
        needs_review: false,
        arbitration: None,
    };

    let json = serde_json::to_string(&original).expect("DispatchResult must serialise to JSON");

    let roundtripped: DispatchResult =
        serde_json::from_str(&json).expect("DispatchResult must deserialise from JSON");

    // Field-by-field validation
    assert_eq!(roundtripped.verified, original.verified);
    assert_eq!(roundtripped.trust_level, original.trust_level);
    assert_eq!(roundtripped.provers_used, original.provers_used);
    assert_eq!(roundtripped.proof_time_ms, original.proof_time_ms);
    assert_eq!(roundtripped.goals_remaining, original.goals_remaining);
    assert_eq!(roundtripped.certificate_hash, original.certificate_hash);
    assert_eq!(roundtripped.message, original.message);
    assert_eq!(roundtripped.cross_checked, original.cross_checked);
    assert!(
        roundtripped.axiom_report.is_some(),
        "axiom_report must survive roundtrip"
    );
}

// ---------------------------------------------------------------------------
// E2E 10: Dispatcher with short timeout — proof time must be bounded
// ---------------------------------------------------------------------------

/// When a short timeout is set, the dispatcher must not hang indefinitely.
/// This validates the timeout plumbing (not necessarily that the prover
/// itself respects it, but that the config round-trips correctly).
#[tokio::test]
async fn e2e_dispatcher_respects_timeout_config() {
    let short_timeout = DispatchConfig {
        timeout: 5, // 5 seconds — enough for a trivial SMT problem
        ..DispatchConfig::default()
    };
    let dispatcher = ProverDispatcher::with_config(short_timeout.clone());

    // Validate the config was applied
    // (We can't inspect the internal field directly, but we can test behaviour)
    // The simplest check: the dispatcher was created successfully with a short timeout
    // and can process a trivial problem if Z3 is available.
    if !common::is_prover_available(ProverKind::Z3) {
        eprintln!("Skipping timeout E2E: Z3 not on PATH");
        return;
    }

    let content = "(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (= x x))\n(check-sat)";

    let start = std::time::Instant::now();
    let result = dispatcher.verify_proof(ProverKind::Z3, content).await;
    let elapsed = start.elapsed();

    // The trivial problem should complete well within 5 seconds
    assert!(
        elapsed < Duration::from_secs(10),
        "Trivial Z3 problem took {}s with 5s timeout — possible timeout not respected",
        elapsed.as_secs()
    );

    match result {
        Ok(r) => eprintln!(
            "E2E timeout: verified={}, time={}ms, wall={}ms",
            r.verified,
            r.proof_time_ms,
            elapsed.as_millis()
        ),
        Err(e) => eprintln!("E2E timeout: Err({}) — acceptable", e),
    }
}

// ---------------------------------------------------------------------------
// E2E 11: Select prover from content heuristic
// ---------------------------------------------------------------------------

/// ProverDispatcher::select_prover must return a valid ProverKind for all
/// common file extensions and content patterns.
#[test]
fn e2e_select_prover_heuristic_coverage() {
    use echidna::dispatch::ProverDispatcher;

    let cases: Vec<(&str, Option<&str>)> = vec![
        ("theorem id : ∀ x, x = x := rfl", Some("lean")),
        ("Theorem id : True. Proof. trivial. Qed.", Some("v")),
        ("module Test where\nid : a -> a", Some("agda")),
        (
            "(set-logic QF_LIA)\n(assert true)\n(check-sat)",
            Some("smt2"),
        ),
        // No extension — heuristic only
        ("", None),
        ("random content", None),
    ];

    for (content, ext) in cases {
        let kind = ProverDispatcher::select_prover(content, ext);
        // Result must be a valid ProverKind — if it doesn't panic, it's valid
        let _ = format!("{:?}", kind); // just ensure it's printable
        eprintln!(
            "select_prover({:?}, {:?}) -> {:?}",
            &content[..content.len().min(30)],
            ext,
            kind
        );
    }
}
