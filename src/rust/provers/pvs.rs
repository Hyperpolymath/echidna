// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

use async_trait::async_trait;
use anyhow::Result;
use std::path::PathBuf;
use crate::core::{ProofState, Tactic, TacticResult};
use super::{ProverBackend, ProverConfig, ProverKind};

pub struct PVSBackend { config: ProverConfig }
impl PVSBackend { pub fn new(config: ProverConfig) -> Self { PVSBackend { config } } }

#[async_trait]
impl ProverBackend for PVSBackend {
    fn kind(&self) -> ProverKind { ProverKind::PVS }
    async fn version(&self) -> Result<String> { anyhow::bail!("Not implemented") }
    async fn parse_file(&self, _path: PathBuf) -> Result<ProofState> { anyhow::bail!("Not implemented") }
    async fn parse_string(&self, _content: &str) -> Result<ProofState> { anyhow::bail!("Not implemented") }
    async fn apply_tactic(&self, _state: &ProofState, _tactic: &Tactic) -> Result<TacticResult> { anyhow::bail!("Not implemented") }
    async fn verify_proof(&self, _state: &ProofState) -> Result<bool> { anyhow::bail!("Not implemented") }
    async fn export(&self, _state: &ProofState) -> Result<String> { anyhow::bail!("Not implemented") }
    async fn suggest_tactics(&self, _state: &ProofState, _limit: usize) -> Result<Vec<Tactic>> { Ok(vec![]) }
    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> { Ok(vec![]) }
    fn config(&self) -> &ProverConfig { &self.config }
    fn set_config(&mut self, config: ProverConfig) { self.config = config; }
}
