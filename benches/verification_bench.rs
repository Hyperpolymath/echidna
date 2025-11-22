// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Verification benchmarks for ECHIDNA theorem provers

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use echidna::core::{ProofState, Tactic, Term};
use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind};
use std::path::PathBuf;

/// Benchmark proof verification
fn bench_proof_verification(c: &mut Criterion) {
    let mut group = c.benchmark_group("proof_verification");

    // Agda proof verification
    let agda_proof = r#"
module ProofTest where

open import Relation.Binary.PropositionalEquality

id-proof : {A : Set} (x : A) → x ≡ x
id-proof x = refl

sym-proof : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym-proof refl = refl
    "#;

    group.bench_with_input(
        BenchmarkId::new("agda", "simple"),
        &agda_proof,
        |b, proof| {
            let runtime = tokio::runtime::Runtime::new().unwrap();
            let config = ProverConfig {
                executable: PathBuf::from("agda"),
                timeout: 30,
                neural_enabled: false,
                ..Default::default()
            };
            let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

            b.to_async(&runtime).iter(|| async {
                let state = backend.parse_string(black_box(proof)).await.unwrap();
                let _ = backend.verify_proof(black_box(&state)).await;
            });
        },
    );

    // Z3 SMT verification
    let z3_proof = r#"
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0))
(assert (>= y 0))
(assert (= (+ x y) (+ y x)))
(check-sat)
    "#;

    group.bench_with_input(
        BenchmarkId::new("z3", "smt"),
        &z3_proof,
        |b, proof| {
            let runtime = tokio::runtime::Runtime::new().unwrap();
            let config = ProverConfig {
                executable: PathBuf::from("z3"),
                timeout: 30,
                neural_enabled: false,
                ..Default::default()
            };
            let backend = ProverFactory::create(ProverKind::Z3, config).unwrap();

            b.to_async(&runtime).iter(|| async {
                let state = backend.parse_string(black_box(proof)).await.unwrap();
                let _ = backend.verify_proof(black_box(&state)).await;
            });
        },
    );

    group.finish();
}

/// Benchmark tactic execution
fn bench_tactic_execution(c: &mut Criterion) {
    let mut group = c.benchmark_group("tactic_execution");

    // Intro tactic
    group.bench_function("intro", |b| {
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let config = ProverConfig::default();
        let backend = ProverFactory::create(ProverKind::Coq, config).unwrap();
        let state = runtime
            .block_on(backend.parse_string("Theorem t : forall x, x = x."))
            .unwrap();

        b.to_async(&runtime).iter(|| async {
            let _ = backend
                .apply_tactic(black_box(&state), black_box(&Tactic::Intro))
                .await;
        });
    });

    // Reflexivity tactic
    group.bench_function("reflexivity", |b| {
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let config = ProverConfig::default();
        let backend = ProverFactory::create(ProverKind::Coq, config).unwrap();
        let state = runtime
            .block_on(backend.parse_string("Theorem t : 1 = 1."))
            .unwrap();

        b.to_async(&runtime).iter(|| async {
            let _ = backend
                .apply_tactic(black_box(&state), black_box(&Tactic::Reflexivity))
                .await;
        });
    });

    // Apply tactic
    group.bench_function("apply", |b| {
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let config = ProverConfig::default();
        let backend = ProverFactory::create(ProverKind::Coq, config).unwrap();
        let state = runtime
            .block_on(backend.parse_string("Theorem t : forall x, x = x."))
            .unwrap();
        let term = Term::Const("refl".to_string());

        b.to_async(&runtime).iter(|| async {
            let _ = backend
                .apply_tactic(black_box(&state), &Tactic::Apply { term: term.clone() })
                .await;
        });
    });

    group.finish();
}

/// Benchmark term translation between provers
fn bench_term_translation(c: &mut Criterion) {
    let mut group = c.benchmark_group("term_translation");

    let simple_term = Term::App {
        func: Box::new(Term::Const("eq".to_string())),
        args: vec![
            Term::Var("x".to_string()),
            Term::Var("x".to_string()),
        ],
    };

    // Agda to Coq translation
    group.bench_function("agda_to_coq", |b| {
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let config = ProverConfig::default();
        let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

        b.to_async(&runtime).iter(|| async {
            let _ = backend
                .translate_term(black_box(&simple_term), ProverKind::Coq)
                .await;
        });
    });

    // Z3 to CVC5 translation
    group.bench_function("z3_to_cvc5", |b| {
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let config = ProverConfig::default();
        let backend = ProverFactory::create(ProverKind::Z3, config).unwrap();

        b.to_async(&runtime).iter(|| async {
            let _ = backend
                .translate_term(black_box(&simple_term), ProverKind::CVC5)
                .await;
        });
    });

    group.finish();
}

/// Benchmark type checking
fn bench_type_checking(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_checking");

    // Simple term
    let simple = Term::Lambda {
        param: "x".to_string(),
        param_type: Some(Box::new(Term::Universe(0))),
        body: Box::new(Term::Var("x".to_string())),
    };

    group.bench_function("simple_lambda", |b| {
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let config = ProverConfig::default();
        let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

        b.to_async(&runtime).iter(|| async {
            let _ = backend.check_type(black_box(&simple)).await;
        });
    });

    // Complex nested term
    let complex = Term::App {
        func: Box::new(Term::Lambda {
            param: "f".to_string(),
            param_type: None,
            body: Box::new(Term::Lambda {
                param: "x".to_string(),
                param_type: None,
                body: Box::new(Term::App {
                    func: Box::new(Term::Var("f".to_string())),
                    args: vec![Term::Var("x".to_string())],
                }),
            }),
        }),
        args: vec![Term::Const("id".to_string())],
    };

    group.bench_function("complex_application", |b| {
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let config = ProverConfig::default();
        let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

        b.to_async(&runtime).iter(|| async {
            let _ = backend.check_type(black_box(&complex)).await;
        });
    });

    group.finish();
}

/// Benchmark term normalization
fn bench_normalization(c: &mut Criterion) {
    let mut group = c.benchmark_group("normalization");

    // Beta reduction
    let beta_term = Term::App {
        func: Box::new(Term::Lambda {
            param: "x".to_string(),
            param_type: None,
            body: Box::new(Term::Var("x".to_string())),
        }),
        args: vec![Term::Const("42".to_string())],
    };

    group.bench_function("beta_reduction", |b| {
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let config = ProverConfig::default();
        let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

        b.to_async(&runtime).iter(|| async {
            let _ = backend.normalize(black_box(&beta_term)).await;
        });
    });

    // Nested applications
    let nested = Term::App {
        func: Box::new(Term::App {
            func: Box::new(Term::Const("compose".to_string())),
            args: vec![
                Term::Const("f".to_string()),
                Term::Const("g".to_string()),
            ],
        }),
        args: vec![Term::Const("x".to_string())],
    };

    group.bench_function("nested_application", |b| {
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let config = ProverConfig::default();
        let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

        b.to_async(&runtime).iter(|| async {
            let _ = backend.normalize(black_box(&nested)).await;
        });
    });

    group.finish();
}

/// Benchmark proof export to different formats
fn bench_proof_export(c: &mut Criterion) {
    let mut group = c.benchmark_group("proof_export");

    // Create a simple proof state
    let state = ProofState {
        goals: vec![],
        context: echidna::core::Context {
            definitions: std::collections::HashMap::new(),
            theorems: vec![],
        },
        proof_script: vec![Tactic::Intro, Tactic::Reflexivity],
        metadata: std::collections::HashMap::new(),
    };

    // Export to Agda
    group.bench_function("export_agda", |b| {
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let config = ProverConfig::default();
        let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

        b.to_async(&runtime).iter(|| async {
            let _ = backend.export(black_box(&state)).await;
        });
    });

    // Export to Coq
    group.bench_function("export_coq", |b| {
        let runtime = tokio::runtime::Runtime::new().unwrap();
        let config = ProverConfig::default();
        let backend = ProverFactory::create(ProverKind::Coq, config).unwrap();

        b.to_async(&runtime).iter(|| async {
            let _ = backend.export(black_box(&state)).await;
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_proof_verification,
    bench_tactic_execution,
    bench_term_translation,
    bench_type_checking,
    bench_normalization,
    bench_proof_export
);
criterion_main!(benches);
