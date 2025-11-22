// SPDX-FileCopyrightText: 2025 ECHIDNA Project Contributors
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Proof Memory - stores successful proofs and failures for learning
//!
//! Uses SQLite for structured storage and optionally LanceDB for vector similarity search.

use anyhow::Result;
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use tokio::sync::RwLock;
use tracing::{debug, info};

use crate::core::ProofState;
use crate::provers::ProverKind;
use super::AgenticGoal;

/// A cached proof entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CachedProof {
    /// Goal that was proved
    pub goal_id: String,

    /// The proof
    pub proof: ProofState,

    /// Prover used
    pub prover: ProverKind,

    /// Time taken (milliseconds)
    pub time_ms: u64,

    /// Timestamp
    pub timestamp: i64,

    /// Aspect tags
    pub aspects: Vec<String>,
}

/// A failed proof attempt
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FailedAttempt {
    /// Goal that failed
    pub goal_id: String,

    /// Prover used (if any)
    pub prover: Option<ProverKind>,

    /// Reason for failure
    pub reason: String,

    /// Timestamp
    pub timestamp: i64,

    /// Aspect tags
    pub aspects: Vec<String>,
}

/// Trait for proof memory implementations
#[async_trait]
pub trait ProofMemory: Send + Sync {
    /// Store a successful proof
    async fn store_success(&self, goal: &AgenticGoal, proof: &ProofState, prover: ProverKind) -> Result<()>;

    /// Store a failed attempt
    async fn store_failure(&self, goal: &AgenticGoal, reason: String) -> Result<()>;

    /// Find a similar proof in memory
    async fn find_similar(&self, goal: &AgenticGoal) -> Result<Option<CachedProof>>;

    /// Get all successful proofs
    async fn get_successes(&self) -> Result<Vec<CachedProof>>;

    /// Get all failed attempts
    async fn get_failures(&self) -> Result<Vec<FailedAttempt>>;

    /// Get statistics
    async fn stats(&self) -> Result<MemoryStats>;
}

/// Memory statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryStats {
    pub total_proofs: usize,
    pub total_failures: usize,
    pub success_rate: f64,
    pub avg_proof_time_ms: f64,
}

/// SQLite-based proof memory
pub struct SqliteMemory {
    db_path: PathBuf,
    successes: RwLock<Vec<CachedProof>>,
    failures: RwLock<Vec<FailedAttempt>>,
}

impl SqliteMemory {
    /// Create a new SQLite memory
    pub fn new(db_path: PathBuf) -> Self {
        SqliteMemory {
            db_path,
            successes: RwLock::new(Vec::new()),
            failures: RwLock::new(Vec::new()),
        }
    }

    /// Initialize the database
    pub async fn init(&self) -> Result<()> {
        // TODO: Create SQLite tables
        // For now, use in-memory storage
        info!("Initialized proof memory at {:?}", self.db_path);
        Ok(())
    }
}

#[async_trait]
impl ProofMemory for SqliteMemory {
    async fn store_success(&self, goal: &AgenticGoal, proof: &ProofState, prover: ProverKind) -> Result<()> {
        let cached = CachedProof {
            goal_id: goal.goal.id.clone(),
            proof: proof.clone(),
            prover,
            time_ms: 0, // TODO: Track actual time
            timestamp: chrono::Utc::now().timestamp(),
            aspects: goal.aspects.clone(),
        };

        let mut successes = self.successes.write().await;
        successes.push(cached);

        debug!("Stored successful proof for goal {}", goal.goal.id);
        Ok(())
    }

    async fn store_failure(&self, goal: &AgenticGoal, reason: String) -> Result<()> {
        let failed = FailedAttempt {
            goal_id: goal.goal.id.clone(),
            prover: goal.preferred_prover,
            reason,
            timestamp: chrono::Utc::now().timestamp(),
            aspects: goal.aspects.clone(),
        };

        let mut failures = self.failures.write().await;
        failures.push(failed);

        debug!("Stored failed attempt for goal {}", goal.goal.id);
        Ok(())
    }

    async fn find_similar(&self, goal: &AgenticGoal) -> Result<Option<CachedProof>> {
        let successes = self.successes.read().await;

        // Simple similarity: check if aspects overlap
        for cached in successes.iter() {
            let overlap = goal.aspects.iter()
                .filter(|a| cached.aspects.contains(a))
                .count();

            if overlap > 0 {
                debug!("Found similar proof: {} aspects overlap", overlap);
                return Ok(Some(cached.clone()));
            }
        }

        Ok(None)
    }

    async fn get_successes(&self) -> Result<Vec<CachedProof>> {
        Ok(self.successes.read().await.clone())
    }

    async fn get_failures(&self) -> Result<Vec<FailedAttempt>> {
        Ok(self.failures.read().await.clone())
    }

    async fn stats(&self) -> Result<MemoryStats> {
        let successes = self.successes.read().await;
        let failures = self.failures.read().await;

        let total_proofs = successes.len();
        let total_failures = failures.len();
        let total = total_proofs + total_failures;

        let success_rate = if total > 0 {
            total_proofs as f64 / total as f64
        } else {
            0.0
        };

        let avg_proof_time_ms = if !successes.is_empty() {
            successes.iter().map(|s| s.time_ms).sum::<u64>() as f64 / successes.len() as f64
        } else {
            0.0
        };

        Ok(MemoryStats {
            total_proofs,
            total_failures,
            success_rate,
            avg_proof_time_ms,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Goal, Term};
    use super::super::{AgenticGoal, Priority};

    #[tokio::test]
    async fn test_memory_store_and_retrieve() {
        let memory = SqliteMemory::new(PathBuf::from(":memory:"));
        memory.init().await.unwrap();

        let goal = AgenticGoal {
            goal: Goal {
                id: "test_goal".to_string(),
                target: Term::Var("A".to_string()),
                hypotheses: vec![],
            },
            priority: Priority::Medium,
            attempts: 0,
            max_attempts: 3,
            preferred_prover: None,
            aspects: vec!["logic".to_string()],
            parent: None,
        };

        let proof = ProofState::new(Term::Var("A".to_string()));

        // Store success
        memory.store_success(&goal, &proof, ProverKind::Agda).await.unwrap();

        // Retrieve
        let successes = memory.get_successes().await.unwrap();
        assert_eq!(successes.len(), 1);
        assert_eq!(successes[0].goal_id, "test_goal");

        // Stats
        let stats = memory.stats().await.unwrap();
        assert_eq!(stats.total_proofs, 1);
        assert_eq!(stats.total_failures, 0);
        assert_eq!(stats.success_rate, 1.0);
    }
}
