// SPDX-FileCopyrightText: 2025 ECHIDNA Project Contributors
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Prover Router - dynamically selects best prover for a goal
//!
//! Uses aspect tags and success/failure history to score provers.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::sync::RwLock;
use tracing::{debug, info};

use crate::provers::ProverKind;
use super::AgenticGoal;

/// Prover performance statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ProverStats {
    /// Total attempts
    attempts: u32,

    /// Successful proofs
    successes: u32,

    /// Failures
    failures: u32,

    /// Total time (milliseconds)
    total_time_ms: u64,
}

impl ProverStats {
    fn new() -> Self {
        ProverStats {
            attempts: 0,
            successes: 0,
            failures: 0,
            total_time_ms: 0,
        }
    }

    /// Success rate (0.0 - 1.0)
    fn success_rate(&self) -> f64 {
        if self.attempts == 0 {
            0.5 // No data, assume 50%
        } else {
            self.successes as f64 / self.attempts as f64
        }
    }

    /// Average time per proof (milliseconds)
    fn avg_time_ms(&self) -> f64 {
        if self.successes == 0 {
            1000.0 // No data, assume 1 second
        } else {
            self.total_time_ms as f64 / self.successes as f64
        }
    }

    /// Combined score (higher is better)
    fn score(&self) -> f64 {
        // Score = success_rate * (1 / log(avg_time))
        // This favors both high success rate and fast provers
        let sr = self.success_rate();
        let time_factor = 1.0 / (self.avg_time_ms() / 1000.0).log10().max(1.0);
        sr * time_factor
    }
}

/// Aspect-based prover routing
pub struct ProverRouter {
    /// Statistics per (prover, aspect)
    stats: RwLock<HashMap<(ProverKind, String), ProverStats>>,

    /// Global prover preferences (fallback when no aspect data)
    global_stats: RwLock<HashMap<ProverKind, ProverStats>>,
}

impl ProverRouter {
    /// Create a new router
    pub fn new() -> Self {
        ProverRouter {
            stats: RwLock::new(HashMap::new()),
            global_stats: RwLock::new(HashMap::new()),
        }
    }

    /// Select the best prover for a goal
    pub fn select(&self, goal: &AgenticGoal) -> ProverKind {
        // For now, use a simple heuristic
        // TODO: Implement actual scoring based on aspects and history

        // If goal has aspects, try to match
        if !goal.aspects.is_empty() {
            // SMT solvers for arithmetic
            if goal.aspects.contains(&"arithmetic".to_string()) {
                return ProverKind::Z3;
            }

            // Coq for inductive proofs
            if goal.aspects.contains(&"inductive".to_string()) {
                return ProverKind::Coq;
            }

            // Lean for type theory
            if goal.aspects.contains(&"type_theory".to_string()) {
                return ProverKind::Lean;
            }
        }

        // Default: use Metamath (easiest)
        ProverKind::Metamath
    }

    /// Select the best prover with async access to stats
    pub async fn select_async(&self, goal: &AgenticGoal) -> ProverKind {
        // Get primary aspect
        let primary_aspect = goal.aspects.first()
            .cloned()
            .unwrap_or_else(|| "unknown".to_string());

        // Get stats for all provers for this aspect
        let stats = self.stats.read().await;
        let global_stats = self.global_stats.read().await;

        let provers = vec![
            ProverKind::Agda,
            ProverKind::Coq,
            ProverKind::Lean,
            ProverKind::Isabelle,
            ProverKind::Z3,
            ProverKind::CVC5,
            ProverKind::Metamath,
            ProverKind::HolLight,
            ProverKind::Mizar,
        ];

        let mut best_prover = ProverKind::Metamath;
        let mut best_score = 0.0;

        for prover in provers {
            // Get aspect-specific stats
            let aspect_stats = stats.get(&(prover, primary_aspect.clone()))
                .or_else(|| global_stats.get(&prover))
                .cloned()
                .unwrap_or_else(ProverStats::new);

            let score = aspect_stats.score();

            debug!("Prover {:?} score for aspect '{}': {}", prover, primary_aspect, score);

            if score > best_score {
                best_score = score;
                best_prover = prover;
            }
        }

        info!("Selected prover {:?} (score: {}) for goal {}", best_prover, best_score, goal.goal.id);

        best_prover
    }

    /// Record a successful proof
    pub async fn record_success(&self, goal: &AgenticGoal, prover: ProverKind) {
        let mut stats = self.stats.write().await;
        let mut global_stats = self.global_stats.write().await;

        // Update aspect-specific stats
        for aspect in &goal.aspects {
            let key = (prover, aspect.clone());
            let entry = stats.entry(key).or_insert_with(ProverStats::new);
            entry.attempts += 1;
            entry.successes += 1;
        }

        // Update global stats
        let global_entry = global_stats.entry(prover).or_insert_with(ProverStats::new);
        global_entry.attempts += 1;
        global_entry.successes += 1;

        debug!("Recorded success for {:?} on aspects {:?}", prover, goal.aspects);
    }

    /// Record a failed proof
    pub async fn record_failure(&self, goal: &AgenticGoal, prover: ProverKind) {
        let mut stats = self.stats.write().await;
        let mut global_stats = self.global_stats.write().await;

        // Update aspect-specific stats
        for aspect in &goal.aspects {
            let key = (prover, aspect.clone());
            let entry = stats.entry(key).or_insert_with(ProverStats::new);
            entry.attempts += 1;
            entry.failures += 1;
        }

        // Update global stats
        let global_entry = global_stats.entry(prover).or_insert_with(ProverStats::new);
        global_entry.attempts += 1;
        global_entry.failures += 1;

        debug!("Recorded failure for {:?} on aspects {:?}", prover, goal.aspects);
    }

    /// Get statistics for all provers
    pub async fn get_all_stats(&self) -> HashMap<ProverKind, ProverStats> {
        self.global_stats.read().await.clone()
    }
}

impl Default for ProverRouter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Goal, Term};
    use super::super::{AgenticGoal, Priority};

    #[tokio::test]
    async fn test_router_learning() {
        let router = ProverRouter::new();

        let goal = AgenticGoal {
            goal: Goal {
                id: "test".to_string(),
                target: Term::Var("A".to_string()),
                hypotheses: vec![],
            },
            priority: Priority::Medium,
            attempts: 0,
            max_attempts: 3,
            preferred_prover: None,
            aspects: vec!["arithmetic".to_string()],
            parent: None,
        };

        // Record multiple successes for Z3 on arithmetic
        for _ in 0..10 {
            router.record_success(&goal, ProverKind::Z3).await;
        }

        // Record failures for Coq on arithmetic
        for _ in 0..5 {
            router.record_failure(&goal, ProverKind::Coq).await;
        }

        // Router should now prefer Z3 for arithmetic
        let selected = router.select_async(&goal).await;
        assert_eq!(selected, ProverKind::Z3);

        // Check stats
        let stats = router.get_all_stats().await;
        assert!(stats.contains_key(&ProverKind::Z3));
        assert_eq!(stats[&ProverKind::Z3].successes, 10);
    }
}
