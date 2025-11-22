// SPDX-FileCopyrightText: 2025 ECHIDNA Project Contributors
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Planner - decomposes goals into sub-goals
//!
//! Uses hierarchical task network planning to break complex goals into manageable pieces.

use anyhow::Result;
use async_trait::async_trait;
use tracing::{debug, info};

use crate::core::{Goal, Term};
use super::{AgenticGoal, Priority};

/// Trait for goal planning/decomposition
#[async_trait]
pub trait Planner: Send + Sync {
    /// Decompose a goal into sub-goals
    async fn decompose(&self, goal: &AgenticGoal) -> Result<Vec<AgenticGoal>>;
}

/// Simple rule-based planner
pub struct RulePlanner {
    /// Maximum depth of decomposition
    max_depth: usize,
}

impl RulePlanner {
    pub fn new() -> Self {
        RulePlanner {
            max_depth: 3,
        }
    }

    /// Check if term is a conjunction (A ∧ B)
    fn is_conjunction(&self, term: &Term) -> Option<(Term, Term)> {
        // TODO: Implement proper pattern matching for conjunction
        None
    }

    /// Check if term is an implication (A → B)
    fn is_implication(&self, term: &Term) -> Option<(Term, Term)> {
        if let Term::Pi { param_type, body, .. } = term {
            Some((*param_type.clone(), *body.clone()))
        } else {
            None
        }
    }

    /// Check if term is a universal quantification (∀ x. P(x))
    fn is_universal(&self, term: &Term) -> bool {
        matches!(term, Term::Pi { .. })
    }
}

impl Default for RulePlanner {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Planner for RulePlanner {
    async fn decompose(&self, goal: &AgenticGoal) -> Result<Vec<AgenticGoal>> {
        info!("Decomposing goal: {}", goal.goal.id);

        let mut sub_goals = Vec::new();

        // Rule 1: Decompose implication (A → B) into:
        //   - Assume A
        //   - Prove B
        if let Some((premise, conclusion)) = self.is_implication(&goal.goal.target) {
            debug!("Decomposing implication");

            // Sub-goal 1: Assume premise (this becomes a hypothesis)
            // Sub-goal 2: Prove conclusion
            sub_goals.push(AgenticGoal {
                goal: Goal {
                    id: format!("{}_conclusion", goal.goal.id),
                    target: conclusion.clone(),
                    hypotheses: goal.goal.hypotheses.clone(),
                },
                priority: goal.priority,
                attempts: 0,
                max_attempts: goal.max_attempts,
                preferred_prover: goal.preferred_prover,
                aspects: goal.aspects.clone(),
                parent: Some(goal.goal.id.clone()),
            });

            return Ok(sub_goals);
        }

        // Rule 2: Decompose conjunction (A ∧ B) into:
        //   - Prove A
        //   - Prove B
        if let Some((left, right)) = self.is_conjunction(&goal.goal.target) {
            debug!("Decomposing conjunction");

            sub_goals.push(AgenticGoal {
                goal: Goal {
                    id: format!("{}_left", goal.goal.id),
                    target: left.clone(),
                    hypotheses: goal.goal.hypotheses.clone(),
                },
                priority: goal.priority,
                attempts: 0,
                max_attempts: goal.max_attempts,
                preferred_prover: goal.preferred_prover,
                aspects: goal.aspects.clone(),
                parent: Some(goal.goal.id.clone()),
            });

            sub_goals.push(AgenticGoal {
                goal: Goal {
                    id: format!("{}_right", goal.goal.id),
                    target: right.clone(),
                    hypotheses: goal.goal.hypotheses.clone(),
                },
                priority: goal.priority,
                attempts: 0,
                max_attempts: goal.max_attempts,
                preferred_prover: goal.preferred_prover,
                aspects: goal.aspects.clone(),
                parent: Some(goal.goal.id.clone()),
            });

            return Ok(sub_goals);
        }

        // Rule 3: If goal is complex but we can't decompose, return it as-is
        debug!("Cannot decompose goal, returning unchanged");
        Ok(vec![goal.clone()])
    }
}

/// Lean-based planner (stub for future implementation)
pub struct LeanPlanner;

#[async_trait]
impl Planner for LeanPlanner {
    async fn decompose(&self, _goal: &AgenticGoal) -> Result<Vec<AgenticGoal>> {
        // TODO: Use Lean's meta-programming to decompose goals
        Ok(vec![])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Goal, Term};

    #[tokio::test]
    async fn test_implication_decomposition() {
        let planner = RulePlanner::new();

        let goal = AgenticGoal {
            goal: Goal {
                id: "impl_test".to_string(),
                target: Term::Pi {
                    param: "x".to_string(),
                    param_type: Box::new(Term::Var("A".to_string())),
                    body: Box::new(Term::Var("B".to_string())),
                },
                hypotheses: vec![],
            },
            priority: Priority::Medium,
            attempts: 0,
            max_attempts: 3,
            preferred_prover: None,
            aspects: vec![],
            parent: None,
        };

        let sub_goals = planner.decompose(&goal).await.unwrap();
        assert!(!sub_goals.is_empty());
        // Should decompose implication into conclusion
    }
}
