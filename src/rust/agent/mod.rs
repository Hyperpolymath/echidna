// SPDX-FileCopyrightText: 2025 ECHIDNA Project Contributors
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Agent Core - Agentic theorem proving with goal selection, planning, and reflection
//!
//! This module implements the autonomous agent that coordinates theorem proving
//! across multiple provers with neural guidance and symbolic verification.

use anyhow::Result;
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::VecDeque;
use tokio::sync::RwLock;
use tracing::{debug, info, warn};

use crate::core::{Goal, ProofState, Tactic, TacticResult, Term, Theorem};
use crate::provers::{ProverBackend, ProverKind};

pub mod memory;
pub mod planner;
pub mod router;
pub mod actors;
pub mod explanations;

use memory::ProofMemory;
use planner::Planner;
use router::ProverRouter;

pub use actors::{MultiAgentSystem, CoordinatorAgent, ProverAgent, ContextAgent, LemmaAgent};
pub use explanations::{Explanation, ExplanationGenerator};

/// Priority level for goals
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Priority {
    Low = 0,
    Medium = 1,
    High = 2,
    Critical = 3,
}

/// A goal with metadata for agentic processing
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgenticGoal {
    /// The underlying proof goal
    pub goal: Goal,

    /// Priority level
    pub priority: Priority,

    /// Number of attempts so far
    pub attempts: u32,

    /// Maximum attempts before giving up
    pub max_attempts: u32,

    /// Preferred prover (if any)
    pub preferred_prover: Option<ProverKind>,

    /// Aspect tags for this goal
    pub aspects: Vec<String>,

    /// Parent goal ID (for sub-goals)
    pub parent: Option<String>,
}

/// Strategy for achieving a goal
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Strategy {
    /// Try a single prover
    SingleProver(ProverKind),

    /// Try multiple provers in sequence
    Sequential(Vec<ProverKind>),

    /// Try multiple provers in parallel
    Parallel(Vec<ProverKind>),

    /// Decompose into sub-goals
    Decompose,

    /// Use neural guidance
    NeuralGuided,

    /// Custom strategy
    Custom(String),
}

/// Result of a goal attempt
#[derive(Debug, Clone)]
pub enum GoalResult {
    /// Goal was proved
    Proved {
        proof: ProofState,
        prover: ProverKind,
        time_ms: u64,
    },

    /// Goal failed
    Failed {
        reason: String,
        prover: Option<ProverKind>,
    },

    /// Goal was decomposed into sub-goals
    Decomposed {
        sub_goals: Vec<AgenticGoal>,
    },

    /// Goal is pending (needs more work)
    Pending,
}

/// The Agent Core - coordinates autonomous theorem proving
pub struct AgentCore {
    /// Queue of goals to prove (priority queue)
    goal_queue: RwLock<VecDeque<AgenticGoal>>,

    /// Proof memory (stores successful proofs and failures)
    memory: Box<dyn ProofMemory>,

    /// Planner (decomposes goals into sub-goals)
    planner: Box<dyn Planner>,

    /// Prover router (selects best prover for a goal)
    router: ProverRouter,

    /// Available provers
    provers: Vec<Box<dyn ProverBackend>>,

    /// Configuration
    config: AgentConfig,
}

/// Configuration for the agent
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentConfig {
    /// Maximum concurrent goals
    pub max_concurrent: usize,

    /// Maximum attempts per goal
    pub max_attempts: u32,

    /// Timeout per goal (seconds)
    pub timeout_secs: u64,

    /// Enable neural guidance
    pub neural_enabled: bool,

    /// Enable reflection (learning from failures)
    pub reflection_enabled: bool,

    /// Enable planning (goal decomposition)
    pub planning_enabled: bool,
}

impl Default for AgentConfig {
    fn default() -> Self {
        AgentConfig {
            max_concurrent: 4,
            max_attempts: 3,
            timeout_secs: 300,
            neural_enabled: true,
            reflection_enabled: true,
            planning_enabled: true,
        }
    }
}

impl AgentCore {
    /// Create a new agent core
    pub fn new(
        memory: Box<dyn ProofMemory>,
        planner: Box<dyn Planner>,
        router: ProverRouter,
        provers: Vec<Box<dyn ProverBackend>>,
        config: AgentConfig,
    ) -> Self {
        AgentCore {
            goal_queue: RwLock::new(VecDeque::new()),
            memory,
            planner,
            router,
            provers,
            config,
        }
    }

    /// Add a goal to the queue
    pub async fn add_goal(&self, goal: AgenticGoal) -> Result<()> {
        let mut queue = self.goal_queue.write().await;

        // Insert based on priority (higher priority first)
        let pos = queue.iter().position(|g| g.priority < goal.priority)
            .unwrap_or(queue.len());
        queue.insert(pos, goal);

        Ok(())
    }

    /// Get the next goal from the queue
    async fn next_goal(&self) -> Option<AgenticGoal> {
        let mut queue = self.goal_queue.write().await;
        queue.pop_front()
    }

    /// Main agent loop - processes goals autonomously
    pub async fn run(&mut self) -> Result<()> {
        info!("Agent core starting autonomous theorem proving");

        loop {
            // Get next goal
            let goal = match self.next_goal().await {
                Some(g) => g,
                None => {
                    debug!("No goals in queue, waiting...");
                    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
                    continue;
                }
            };

            info!("Processing goal: {}", goal.goal.id);

            // Check if we've exceeded max attempts
            if goal.attempts >= self.config.max_attempts {
                warn!("Goal {} exceeded max attempts ({}), giving up",
                    goal.goal.id, self.config.max_attempts);

                // Store failure
                self.memory.store_failure(&goal, "Max attempts exceeded".to_string()).await?;
                continue;
            }

            // Process the goal
            match self.process_goal(goal.clone()).await {
                Ok(GoalResult::Proved { proof, prover, time_ms }) => {
                    info!("Goal {} proved with {} in {}ms",
                        goal.goal.id, prover, time_ms);

                    // Store success
                    self.memory.store_success(&goal, &proof, prover).await?;

                    // Reflect on success (update router scores)
                    if self.config.reflection_enabled {
                        self.reflect_on_success(&goal, prover).await?;
                    }
                },

                Ok(GoalResult::Failed { reason, prover }) => {
                    warn!("Goal {} failed: {}", goal.goal.id, reason);

                    // Store failure
                    self.memory.store_failure(&goal, reason.clone()).await?;

                    // Reflect on failure
                    if self.config.reflection_enabled {
                        self.reflect_on_failure(&goal, prover).await?;
                    }

                    // Retry with different strategy
                    let mut retry_goal = goal.clone();
                    retry_goal.attempts += 1;
                    self.add_goal(retry_goal).await?;
                },

                Ok(GoalResult::Decomposed { sub_goals }) => {
                    info!("Goal {} decomposed into {} sub-goals",
                        goal.goal.id, sub_goals.len());

                    // Add sub-goals to queue
                    for sub_goal in sub_goals {
                        self.add_goal(sub_goal).await?;
                    }
                },

                Ok(GoalResult::Pending) => {
                    debug!("Goal {} is pending, re-queuing", goal.goal.id);
                    self.add_goal(goal).await?;
                },

                Err(e) => {
                    warn!("Error processing goal {}: {}", goal.goal.id, e);

                    // Store failure
                    self.memory.store_failure(&goal, e.to_string()).await?;
                }
            }
        }
    }

    /// Process a single goal
    async fn process_goal(&self, mut goal: AgenticGoal) -> Result<GoalResult> {
        // Step 1: Check memory for similar proofs
        if let Some(cached) = self.memory.find_similar(&goal).await? {
            info!("Found similar proof in memory for goal {}", goal.goal.id);
            return Ok(GoalResult::Proved {
                proof: cached.proof,
                prover: cached.prover,
                time_ms: 0, // Cached, instant
            });
        }

        // Step 2: Should we decompose this goal?
        if self.config.planning_enabled && self.should_decompose(&goal) {
            info!("Decomposing goal {}", goal.goal.id);
            let sub_goals = self.planner.decompose(&goal).await?;
            return Ok(GoalResult::Decomposed { sub_goals });
        }

        // Step 3: Select prover
        let prover_kind = goal.preferred_prover.unwrap_or_else(|| {
            self.router.select(&goal)
        });

        let prover = self.provers.iter()
            .find(|p| p.kind() == prover_kind)
            .ok_or_else(|| anyhow::anyhow!("Prover {:?} not available", prover_kind))?;

        // Step 4: Get tactic suggestions (neural guidance)
        let tactics = if self.config.neural_enabled {
            prover.suggest_tactics(&ProofState {
                goals: vec![goal.goal.clone()],
                context: Default::default(),
                proof_script: vec![],
                metadata: Default::default(),
            }, 5).await?
        } else {
            vec![Tactic::Assumption] // Fallback
        };

        // Step 5: Try tactics
        let start = std::time::Instant::now();

        for tactic in tactics {
            debug!("Trying tactic {:?} for goal {}", tactic, goal.goal.id);

            // TODO: Actually apply tactic and check result
            // For now, this is a stub that returns failure
        }

        Ok(GoalResult::Failed {
            reason: "No tactic succeeded".to_string(),
            prover: Some(prover_kind),
        })
    }

    /// Decide if a goal should be decomposed
    fn should_decompose(&self, goal: &AgenticGoal) -> bool {
        // Heuristics for decomposition:
        // 1. Goal has "and" or "forall" in it
        // 2. Goal is complex (based on term depth)
        // 3. Goal has failed multiple times already

        goal.attempts > 0 || self.is_compound_goal(&goal.goal)
    }

    /// Check if a goal is compound (can be decomposed)
    fn is_compound_goal(&self, goal: &Goal) -> bool {
        // Simple heuristic: check if target has Pi or App structure
        matches!(goal.target, Term::Pi { .. } | Term::App { .. })
    }

    /// Reflect on successful proof (update router)
    async fn reflect_on_success(&mut self, goal: &AgenticGoal, prover: ProverKind) -> Result<()> {
        info!("Reflecting on success: goal {} with {:?}", goal.goal.id, prover);

        // Update router to prefer this prover for similar goals
        self.router.record_success(goal, prover).await;

        Ok(())
    }

    /// Reflect on failed proof (update router)
    async fn reflect_on_failure(&mut self, goal: &AgenticGoal, prover: Option<ProverKind>) -> Result<()> {
        if let Some(prover) = prover {
            info!("Reflecting on failure: goal {} with {:?}", goal.goal.id, prover);

            // Update router to avoid this prover for similar goals
            self.router.record_failure(goal, prover).await;
        }

        Ok(())
    }

    /// Get statistics about the agent's performance
    pub async fn stats(&self) -> AgentStats {
        let queue_len = self.goal_queue.read().await.len();

        AgentStats {
            queue_length: queue_len,
            total_proved: 0, // TODO: Get from memory
            total_failed: 0, // TODO: Get from memory
            success_rate: 0.0, // TODO: Calculate
        }
    }
}

/// Agent statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentStats {
    pub queue_length: usize,
    pub total_proved: usize,
    pub total_failed: usize,
    pub success_rate: f64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_priority_ordering() {
        assert!(Priority::Critical > Priority::High);
        assert!(Priority::High > Priority::Medium);
        assert!(Priority::Medium > Priority::Low);
    }
}
