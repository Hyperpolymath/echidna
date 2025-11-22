// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Integration tests for Agda backend

use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind};
use std::path::PathBuf;

#[tokio::test]
async fn test_parse_basic_agda() {
    let config = ProverConfig {
        executable: PathBuf::from("agda"),
        ..Default::default()
    };

    let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

    let content = r#"
module Test where

id : {A : Set} → A → A
id x = x

postulate
  extensionality : {A B : Set} {f g : A → B}
                 → ((x : A) → f x ≡ g x)
                 → f ≡ g
    "#;

    let result = backend.parse_string(content).await;
    assert!(result.is_ok(), "Failed to parse Agda file: {:?}", result.err());

    let state = result.unwrap();
    assert!(!state.context.theorems.is_empty(), "No theorems parsed");
}

#[tokio::test]
async fn test_agda_export() {
    let config = ProverConfig::default();
    let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

    let content = r#"
module Test where

id : {A : Set} → A → A
id x = x
    "#;

    let state = backend.parse_string(content).await.unwrap();
    let exported = backend.export(&state).await;
    
    assert!(exported.is_ok());
    let code = exported.unwrap();
    
    // Should generate valid Agda code
    assert!(code.contains("module Generated where"));
    assert!(code.contains("open import"));
}
