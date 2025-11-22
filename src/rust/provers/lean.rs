// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6
//! Lean backend implementation (stub)
use async_trait::async_trait;
use anyhow::{anyhow, Result};
use std::path::PathBuf;
use crate::core::{ProofState, Tactic, TacticResult};
use crate::provers::{ProverBackend, ProverConfig, ProverKind};

pub struct LeanBackend { config: ProverConfig }
impl LeanBackend { pub fn new(config: ProverConfig) -> Self { LeanBackend { config } } }

#[async_trait]
impl ProverBackend for LeanBackend {
    fn kind(&self) -> ProverKind { ProverKind::Lean }
    async fn version(&self) -> Result<String> { Err(anyhow!("Not implemented")) }
    async fn parse_file(&self, _path: PathBuf) -> Result<ProofState> { Err(anyhow!("Not implemented")) }
    async fn parse_string(&self, _content: &str) -> Result<ProofState> { Err(anyhow!("Not implemented")) }
    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> { Err(anyhow!("Not implemented")) }
    async fn verify_proof(&self, _state: &ProofState) -> Result<bool> { Err(anyhow!("Not implemented")) }
    async fn export(&self, _state: &ProofState) -> Result<String> { Err(anyhow!("Not implemented")) }
    async fn suggest_tactics(&self, _state: &ProofState, _limit: usize) -> Result<Vec<Tactic>> { Err(anyhow!("Not implemented")) }
    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> { Err(anyhow!("Not implemented")) }
    fn config(&self) -> &ProverConfig { &self.config }
    fn set_config(&mut self, config: ProverConfig) { self.config = config; }
}
