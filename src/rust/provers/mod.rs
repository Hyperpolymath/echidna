// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Theorem prover backend implementations
//!
//! Supports 12 theorem provers across 4 tiers

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

use crate::core::{ProofState, Tactic, TacticResult, Term};

pub mod agda;
pub mod coq;
pub mod lean;
pub mod isabelle;
pub mod z3;
pub mod cvc5;
pub mod metamath;
pub mod hol_light;
pub mod mizar;
pub mod pvs;
pub mod acl2;
pub mod hol4;

/// Enumeration of all supported provers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProverKind {
    // Tier 1: Original + SMT solvers
    Agda,
    Coq,
    Lean,
    Isabelle,
    Z3,
    CVC5,

    // Tier 2: "Big Six" completion
    Metamath,
    HolLight,
    Mizar,

    // Tier 3: Additional coverage
    PVS,
    ACL2,

    // Tier 4: Advanced
    Hol4,
}

impl std::str::FromStr for ProverKind {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "agda" => Ok(ProverKind::Agda),
            "coq" => Ok(ProverKind::Coq),
            "lean" => Ok(ProverKind::Lean),
            "isabelle" => Ok(ProverKind::Isabelle),
            "z3" => Ok(ProverKind::Z3),
            "cvc5" => Ok(ProverKind::CVC5),
            "metamath" => Ok(ProverKind::Metamath),
            "hollight" | "hol-light" => Ok(ProverKind::HolLight),
            "mizar" => Ok(ProverKind::Mizar),
            "pvs" => Ok(ProverKind::PVS),
            "acl2" => Ok(ProverKind::ACL2),
            "hol4" => Ok(ProverKind::Hol4),
            _ => Err(anyhow::anyhow!("Unknown prover: {}", s)),
        }
    }
}

impl std::fmt::Display for ProverKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl ProverKind {
    /// Get complexity rating (1-5, lower is easier)
    pub fn complexity(&self) -> u8 {
        match self {
            ProverKind::Metamath => 2,
            ProverKind::Agda => 3,
            ProverKind::HolLight => 3,
            ProverKind::Mizar => 3,
            ProverKind::Lean => 3,
            ProverKind::Coq => 3,
            ProverKind::Isabelle => 4,
            ProverKind::Z3 => 2,
            ProverKind::CVC5 => 2,
            ProverKind::PVS => 4,
            ProverKind::ACL2 => 4,
            ProverKind::Hol4 => 5,
        }
    }

    /// Get tier (1-4)
    pub fn tier(&self) -> u8 {
        match self {
            ProverKind::Agda | ProverKind::Coq | ProverKind::Lean |
            ProverKind::Isabelle | ProverKind::Z3 | ProverKind::CVC5 => 1,

            ProverKind::Metamath | ProverKind::HolLight | ProverKind::Mizar => 2,

            ProverKind::PVS | ProverKind::ACL2 => 3,

            ProverKind::Hol4 => 4,
        }
    }

    /// Get expected implementation time in weeks
    pub fn implementation_time(&self) -> f32 {
        match self {
            ProverKind::Metamath => 1.5,
            ProverKind::Z3 | ProverKind::CVC5 => 1.0,
            ProverKind::HolLight | ProverKind::Mizar => 2.0,
            ProverKind::Agda | ProverKind::Lean | ProverKind::Coq => 2.5,
            ProverKind::Isabelle => 3.0,
            ProverKind::PVS | ProverKind::ACL2 => 3.5,
            ProverKind::Hol4 => 4.0,
        }
    }
}

/// Configuration for a prover backend
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProverConfig {
    /// Path to prover executable
    pub executable: PathBuf,

    /// Library/standard library paths
    pub library_paths: Vec<PathBuf>,

    /// Additional arguments
    pub args: Vec<String>,

    /// Timeout in seconds
    pub timeout: u64,

    /// Enable neural premise selection
    pub neural_enabled: bool,
}

impl Default for ProverConfig {
    fn default() -> Self {
        ProverConfig {
            executable: PathBuf::new(),
            library_paths: vec![],
            args: vec![],
            timeout: 300,  // 5 minutes
            neural_enabled: true,
        }
    }
}

/// Universal trait for theorem prover backends
#[async_trait]
pub trait ProverBackend: Send + Sync {
    /// Get prover kind
    fn kind(&self) -> ProverKind;

    /// Get prover version
    async fn version(&self) -> anyhow::Result<String>;

    /// Parse a proof file into ProofState
    async fn parse_file(&self, path: PathBuf) -> anyhow::Result<ProofState>;

    /// Parse a proof from string
    async fn parse_string(&self, content: &str) -> anyhow::Result<ProofState>;

    /// Apply a tactic to current proof state
    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic)
        -> anyhow::Result<TacticResult>;

    /// Check if a proof is valid
    async fn verify_proof(&self, state: &ProofState) -> anyhow::Result<bool>;

    /// Export proof to prover-specific format
    async fn export(&self, state: &ProofState) -> anyhow::Result<String>;

    /// Get suggested tactics using neural premise selection
    async fn suggest_tactics(&self, state: &ProofState, limit: usize)
        -> anyhow::Result<Vec<Tactic>>;

    /// Search for theorems matching a pattern
    async fn search_theorems(&self, pattern: &str) -> anyhow::Result<Vec<String>>;

    /// Get configuration
    fn config(&self) -> &ProverConfig;

    /// Set configuration
    fn set_config(&mut self, config: ProverConfig);
}

/// Factory for creating prover backends
pub struct ProverFactory;

impl ProverFactory {
    pub fn create(kind: ProverKind, config: ProverConfig) -> anyhow::Result<Box<dyn ProverBackend>> {
        match kind {
            ProverKind::Agda => Ok(Box::new(agda::AgdaBackend::new(config))),
            ProverKind::Coq => Ok(Box::new(coq::CoqBackend::new(config))),
            ProverKind::Lean => Ok(Box::new(lean::LeanBackend::new(config))),
            ProverKind::Isabelle => Ok(Box::new(isabelle::IsabelleBackend::new(config))),
            ProverKind::Z3 => Ok(Box::new(z3::Z3Backend::new(config))),
            ProverKind::CVC5 => Ok(Box::new(cvc5::CVC5Backend::new(config))),
            ProverKind::Metamath => Ok(Box::new(metamath::MetamathBackend::new(config))),
            ProverKind::HolLight => Ok(Box::new(hol_light::HolLightBackend::new(config))),
            ProverKind::Mizar => Ok(Box::new(mizar::MizarBackend::new(config))),
            ProverKind::PVS => Ok(Box::new(pvs::PVSBackend::new(config))),
            ProverKind::ACL2 => Ok(Box::new(acl2::ACL2Backend::new(config))),
            ProverKind::Hol4 => Ok(Box::new(hol4::Hol4Backend::new(config))),
        }
    }

    /// Detect prover from file extension
    pub fn detect_from_file(path: &PathBuf) -> Option<ProverKind> {
        path.extension()?.to_str().and_then(|ext| match ext {
            "agda" => Some(ProverKind::Agda),
            "v" => Some(ProverKind::Coq),
            "lean" => Some(ProverKind::Lean),
            "thy" => Some(ProverKind::Isabelle),
            "smt2" => Some(ProverKind::Z3),  // Could be CVC5 too
            "mm" => Some(ProverKind::Metamath),
            "ml" => Some(ProverKind::HolLight),
            "miz" => Some(ProverKind::Mizar),
            "pvs" => Some(ProverKind::PVS),
            "lisp" => Some(ProverKind::ACL2),
            "sml" => Some(ProverKind::Hol4),
            _ => None,
        })
    }
}
