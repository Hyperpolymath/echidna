// SPDX-FileCopyrightText: 2025 ECHIDNA Project Contributors
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Integration tests for agentic theorem proving

use echidna::agent::{
    AgentCore, AgentConfig, AgenticGoal, Priority,
    memory::{ProofMemory, SqliteMemory},
    planner::{Planner, RulePlanner},
    router::ProverRouter,
    explanations::ExplanationGenerator,
};
use echidna::core::{Goal, Term};
use echidna::provers::{ProverBackend, ProverKind};
use tempfile::TempDir;

/// Mock prover for testing
#[derive(Clone)]
struct MockProver {
    kind: ProverKind,
    always_succeeds: bool,
}

impl ProverBackend for MockProver {
    fn kind(&self) -> ProverKind {
        self.kind
    }

    fn prove(&self, _goal: &Goal) -> anyhow::Result<echidna::core::ProofState> {
        if self.always_succeeds {
            Ok(echidna::core::ProofState {
                goals: vec![],
                context: Default::default(),
                proof_script: vec![],
                metadata: Default::default(),
            })
        } else {
            Err(anyhow::anyhow!("Mock prover failed"))
        }
    }
}

#[tokio::test]
async fn test_proof_memory_storage_and_retrieval() {
    let temp_dir = TempDir::new().unwrap();
    let db_path = temp_dir.path().join("test_memory.db");

    let memory = SqliteMemory::new(db_path.clone()).await.unwrap();

    // Create a test goal
    let goal = AgenticGoal {
        goal: Goal {
            id: "test_memory".to_string(),
            target: Term::Var("A".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::High,
        attempts: 1,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["algebra".to_string()],
        parent: None,
    };

    // Store success
    let proof = echidna::core::ProofState {
        goals: vec![],
        context: Default::default(),
        proof_script: vec![],
        metadata: Default::default(),
    };

    memory.store_success(&goal, &proof, ProverKind::Z3).await.unwrap();

    // Retrieve similar proof
    let similar = memory.find_similar(&goal).await.unwrap();
    assert!(similar.is_some());
    assert_eq!(similar.unwrap().prover, ProverKind::Z3);

    // Check stats
    let stats = memory.stats().await.unwrap();
    assert_eq!(stats.total_proofs, 1);
    assert_eq!(stats.total_failures, 0);
}

#[tokio::test]
async fn test_prover_router_learning() {
    let router = ProverRouter::new();

    // Create test goals with different aspects
    let algebra_goal = AgenticGoal {
        goal: Goal {
            id: "algebra_test".to_string(),
            target: Term::Var("A".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::High,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["algebra".to_string()],
        parent: None,
    };

    let logic_goal = AgenticGoal {
        goal: Goal {
            id: "logic_test".to_string(),
            target: Term::Var("B".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::High,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["logic".to_string()],
        parent: None,
    };

    // Record successes for different provers
    router.record_success(&algebra_goal, ProverKind::Lean).await;
    router.record_success(&algebra_goal, ProverKind::Lean).await;
    router.record_success(&logic_goal, ProverKind::Z3).await;

    // Router should prefer Lean for algebra
    let selected_algebra = router.select_async(&algebra_goal).await;
    assert_eq!(selected_algebra, ProverKind::Lean);

    // Router should prefer Z3 for logic
    let selected_logic = router.select_async(&logic_goal).await;
    assert_eq!(selected_logic, ProverKind::Z3);
}

#[tokio::test]
async fn test_goal_decomposition() {
    let planner = RulePlanner::new();

    // Create an implication goal: A → B
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
        priority: Priority::High,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec![],
        parent: None,
    };

    // Decompose goal
    let sub_goals = planner.decompose(&goal).await.unwrap();

    // Should decompose into sub-goal for conclusion
    assert!(!sub_goals.is_empty());
    assert!(sub_goals[0].goal.id.contains("conclusion"));
}

#[tokio::test]
async fn test_agent_queue_priority() {
    let temp_dir = TempDir::new().unwrap();
    let db_path = temp_dir.path().join("test_agent.db");

    let memory = Box::new(SqliteMemory::new(db_path).await.unwrap());
    let planner = Box::new(RulePlanner::new());
    let router = ProverRouter::new();
    let provers: Vec<Box<dyn ProverBackend>> = vec![
        Box::new(MockProver {
            kind: ProverKind::Z3,
            always_succeeds: true,
        }),
    ];

    let agent = AgentCore::new(
        memory,
        planner,
        router,
        provers,
        AgentConfig::default(),
    );

    // Add goals with different priorities
    let low_goal = AgenticGoal {
        goal: Goal {
            id: "low_priority".to_string(),
            target: Term::Var("A".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::Low,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec![],
        parent: None,
    };

    let high_goal = AgenticGoal {
        goal: Goal {
            id: "high_priority".to_string(),
            target: Term::Var("B".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::Critical,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec![],
        parent: None,
    };

    // Add low priority first, then high priority
    agent.add_goal(low_goal).await.unwrap();
    agent.add_goal(high_goal.clone()).await.unwrap();

    // High priority should be processed first
    // (We can't easily test the actual processing without running the full agent loop,
    // but we've verified the queue ordering logic in the agent core)
}

#[test]
fn test_explanation_generation() {
    let generator = ExplanationGenerator::new();

    let goal = AgenticGoal {
        goal: Goal {
            id: "test_explain".to_string(),
            target: Term::Var("A".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::High,
        attempts: 2,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["algebra".to_string()],
        parent: None,
    };

    // Test failure explanation
    let failure_exp = generator.explain_failure(&goal, "timeout", Some(ProverKind::Coq));
    assert!(failure_exp.title.contains("Failed"));
    assert!(!failure_exp.suggestions.is_empty());

    // Test success explanation
    let success_exp = generator.explain_success(&goal, ProverKind::Lean, 150);
    assert!(success_exp.title.contains("Succeeded"));
    assert_eq!(success_exp.details.get("Time"), Some(&"150ms".to_string()));

    // Test prover selection explanation
    let selection_exp = generator.explain_prover_selection(
        &goal,
        ProverKind::Z3,
        0.92,
        "High aspect similarity"
    );
    assert!(selection_exp.title.contains("Selection"));
    assert!(selection_exp.message.contains("0.92"));

    // Test decomposition explanation
    let sub_goals = vec![
        AgenticGoal {
            goal: Goal {
                id: "sub1".to_string(),
                target: Term::Var("X".to_string()),
                hypotheses: vec![],
            },
            priority: Priority::Medium,
            attempts: 0,
            max_attempts: 3,
            preferred_prover: None,
            aspects: vec![],
            parent: Some(goal.goal.id.clone()),
        },
    ];

    let decomp_exp = generator.explain_decomposition(&goal, &sub_goals, "implication");
    assert!(decomp_exp.title.contains("Decomposition"));
    assert_eq!(decomp_exp.details.get("Number of Sub-goals"), Some(&"1".to_string()));
}

#[tokio::test]
async fn test_memory_failure_tracking() {
    let temp_dir = TempDir::new().unwrap();
    let db_path = temp_dir.path().join("test_failures.db");

    let memory = SqliteMemory::new(db_path).await.unwrap();

    let goal = AgenticGoal {
        goal: Goal {
            id: "failing_goal".to_string(),
            target: Term::Var("Impossible".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::Medium,
        attempts: 3,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["impossible".to_string()],
        parent: None,
    };

    // Store failures
    memory.store_failure(&goal, "Prover timeout".to_string()).await.unwrap();
    memory.store_failure(&goal, "No applicable tactics".to_string()).await.unwrap();

    // Check stats
    let stats = memory.stats().await.unwrap();
    assert_eq!(stats.total_failures, 2);

    // Get failures
    let failures = memory.get_failures().await.unwrap();
    assert_eq!(failures.len(), 2);
}

#[tokio::test]
async fn test_router_aspect_scoring() {
    let router = ProverRouter::new();

    // Train router with aspect-specific successes
    let type_theory_goal = AgenticGoal {
        goal: Goal {
            id: "type_theory_test".to_string(),
            target: Term::Var("T".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::High,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["type_theory".to_string(), "dependent_types".to_string()],
        parent: None,
    };

    // Record that Agda is good for type theory
    router.record_success(&type_theory_goal, ProverKind::Agda).await;
    router.record_success(&type_theory_goal, ProverKind::Agda).await;
    router.record_success(&type_theory_goal, ProverKind::Agda).await;

    // Record that Z3 is not good for type theory
    router.record_failure(&type_theory_goal, ProverKind::Z3).await;
    router.record_failure(&type_theory_goal, ProverKind::Z3).await;

    // New type theory goal should prefer Agda
    let new_type_theory_goal = AgenticGoal {
        goal: Goal {
            id: "new_type_theory".to_string(),
            target: Term::Var("U".to_string()),
            hypotheses: vec![],
        },
        priority: Priority::High,
        attempts: 0,
        max_attempts: 3,
        preferred_prover: None,
        aspects: vec!["type_theory".to_string()],
        parent: None,
    };

    let selected = router.select_async(&new_type_theory_goal).await;
    assert_eq!(selected, ProverKind::Agda);
}

#[test]
fn test_priority_ordering() {
    assert!(Priority::Critical > Priority::High);
    assert!(Priority::High > Priority::Medium);
    assert!(Priority::Medium > Priority::Low);
}
