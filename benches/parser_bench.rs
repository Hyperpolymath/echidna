// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Parser benchmarks for ECHIDNA theorem provers

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind};
use std::path::PathBuf;

/// Benchmark parsing simple proofs for all provers
fn bench_simple_parse(c: &mut Criterion) {
    let mut group = c.benchmark_group("simple_parse");

    // Agda
    let agda_content = r#"
module Test where

id : {A : Set} → A → A
id x = x

comp : {A B C : Set} → (B → C) → (A → B) → A → C
comp g f x = g (f x)
    "#;

    group.bench_with_input(
        BenchmarkId::new("agda", "simple"),
        &agda_content,
        |b, content| {
            let runtime = tokio::runtime::Runtime::new().unwrap();
            let config = ProverConfig {
                executable: PathBuf::from("agda"),
                timeout: 30,
                neural_enabled: false,
                ..Default::default()
            };
            let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

            b.to_async(&runtime).iter(|| async {
                let _ = backend.parse_string(black_box(content)).await;
            });
        },
    );

    // Coq
    let coq_content = r#"
Theorem id_nat : forall n : nat, n = n.
Proof.
  intros.
  reflexivity.
Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.
    "#;

    group.bench_with_input(
        BenchmarkId::new("coq", "simple"),
        &coq_content,
        |b, content| {
            let runtime = tokio::runtime::Runtime::new().unwrap();
            let config = ProverConfig {
                executable: PathBuf::from("coqc"),
                timeout: 30,
                neural_enabled: false,
                ..Default::default()
            };
            let backend = ProverFactory::create(ProverKind::Coq, config).unwrap();

            b.to_async(&runtime).iter(|| async {
                let _ = backend.parse_string(black_box(content)).await;
            });
        },
    );

    // Z3 (SMT solver)
    let z3_content = r#"
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) (+ y x)))
(assert (>= x 0))
(assert (>= y 0))
(check-sat)
    "#;

    group.bench_with_input(
        BenchmarkId::new("z3", "simple"),
        &z3_content,
        |b, content| {
            let runtime = tokio::runtime::Runtime::new().unwrap();
            let config = ProverConfig {
                executable: PathBuf::from("z3"),
                timeout: 30,
                neural_enabled: false,
                ..Default::default()
            };
            let backend = ProverFactory::create(ProverKind::Z3, config).unwrap();

            b.to_async(&runtime).iter(|| async {
                let _ = backend.parse_string(black_box(content)).await;
            });
        },
    );

    group.finish();
}

/// Benchmark parsing complex proofs
fn bench_complex_parse(c: &mut Criterion) {
    let mut group = c.benchmark_group("complex_parse");

    // Complex Agda proof
    let complex_agda = r#"
module Complex where

open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality

map-compose : {A B C : Set} (f : A → B) (g : B → C) (xs : List A) →
              map g (map f xs) ≡ map (λ x → g (f x)) xs
map-compose f g [] = refl
map-compose f g (x ∷ xs) = cong (g (f x) ∷_) (map-compose f g xs)
    "#;

    group.throughput(Throughput::Bytes(complex_agda.len() as u64));
    group.bench_with_input(
        BenchmarkId::new("agda", "complex"),
        &complex_agda,
        |b, content| {
            let runtime = tokio::runtime::Runtime::new().unwrap();
            let config = ProverConfig {
                executable: PathBuf::from("agda"),
                timeout: 60,
                neural_enabled: false,
                ..Default::default()
            };
            let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

            b.to_async(&runtime).iter(|| async {
                let _ = backend.parse_string(black_box(content)).await;
            });
        },
    );

    group.finish();
}

/// Benchmark serialization/deserialization
fn bench_serialization(c: &mut Criterion) {
    use echidna::core::Term;

    let mut group = c.benchmark_group("serialization");

    // Create a moderately complex term
    let term = Term::App {
        func: Box::new(Term::Lambda {
            param: "x".to_string(),
            param_type: Some(Box::new(Term::Universe(0))),
            body: Box::new(Term::Var("x".to_string())),
        }),
        args: vec![
            Term::Const("42".to_string()),
            Term::App {
                func: Box::new(Term::Const("add".to_string())),
                args: vec![
                    Term::Const("1".to_string()),
                    Term::Const("2".to_string()),
                ],
            },
        ],
    };

    group.bench_function("serialize_json", |b| {
        b.iter(|| {
            let _ = serde_json::to_string(black_box(&term)).unwrap();
        });
    });

    let json = serde_json::to_string(&term).unwrap();
    group.bench_function("deserialize_json", |b| {
        b.iter(|| {
            let _: Term = serde_json::from_str(black_box(&json)).unwrap();
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_simple_parse,
    bench_complex_parse,
    bench_serialization
);
criterion_main!(benches);
