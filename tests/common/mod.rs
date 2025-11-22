// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Common test utilities for ECHIDNA test suite

use echidna::core::{Context, Goal, ProofState, Tactic, TacticResult, Term, Theorem};
use echidna::provers::{ProverBackend, ProverConfig, ProverKind};
use std::collections::HashMap;
use std::path::PathBuf;

pub mod mock_prover;
pub mod generators;
pub mod assertions;

/// Create a simple test proof state with one goal
pub fn simple_proof_state() -> ProofState {
    ProofState {
        goals: vec![Goal {
            id: "goal1".to_string(),
            hypotheses: vec![],
            conclusion: Term::Const("true".to_string()),
        }],
        context: Context {
            definitions: HashMap::new(),
            theorems: vec![],
        },
        proof_script: vec![],
        metadata: HashMap::new(),
    }
}

/// Create a proof state with multiple goals
pub fn multi_goal_proof_state() -> ProofState {
    ProofState {
        goals: vec![
            Goal {
                id: "goal1".to_string(),
                hypotheses: vec![],
                conclusion: Term::App {
                    func: Box::new(Term::Const("eq".to_string())),
                    args: vec![
                        Term::Var("x".to_string()),
                        Term::Var("x".to_string()),
                    ],
                },
            },
            Goal {
                id: "goal2".to_string(),
                hypotheses: vec![Term::Const("P".to_string())],
                conclusion: Term::Const("Q".to_string()),
            },
        ],
        context: Context {
            definitions: HashMap::new(),
            theorems: vec![],
        },
        proof_script: vec![],
        metadata: HashMap::new(),
    }
}

/// Create a test configuration for a prover
pub fn test_prover_config(kind: ProverKind) -> ProverConfig {
    let executable = match kind {
        ProverKind::Agda => "agda",
        ProverKind::Coq => "coqc",
        ProverKind::Lean => "lean",
        ProverKind::Isabelle => "isabelle",
        ProverKind::Z3 => "z3",
        ProverKind::CVC5 => "cvc5",
        ProverKind::Metamath => "metamath",
        ProverKind::HolLight => "ocaml",
        ProverKind::Mizar => "mizf",
        ProverKind::PVS => "pvs",
        ProverKind::ACL2 => "acl2",
        ProverKind::Hol4 => "hol",
    };

    ProverConfig {
        executable: PathBuf::from(executable),
        library_paths: vec![],
        args: vec![],
        timeout: 10, // 10 seconds for tests
        neural_enabled: false, // Disable neural for basic tests
    }
}

/// Get path to proof examples for a prover
pub fn proof_examples_dir(kind: ProverKind) -> PathBuf {
    let subdir = match kind {
        ProverKind::Agda => "agda",
        ProverKind::Coq => "coq",
        ProverKind::Lean => "lean",
        ProverKind::Isabelle => "isabelle",
        ProverKind::Z3 => "z3",
        ProverKind::CVC5 => "cvc5",
        ProverKind::Metamath => "metamath",
        ProverKind::HolLight => "hol_light",
        ProverKind::Mizar => "mizar",
        ProverKind::PVS => "pvs",
        ProverKind::ACL2 => "acl2",
        ProverKind::Hol4 => "hol4",
    };

    PathBuf::from("/home/user/echidna/proofs").join(subdir)
}

/// Find all proof files for a prover
pub fn find_proof_files(kind: ProverKind) -> Vec<PathBuf> {
    let dir = proof_examples_dir(kind);
    if !dir.exists() {
        return vec![];
    }

    let extensions = match kind {
        ProverKind::Agda => vec!["agda"],
        ProverKind::Coq => vec!["v"],
        ProverKind::Lean => vec!["lean"],
        ProverKind::Isabelle => vec!["thy"],
        ProverKind::Z3 | ProverKind::CVC5 => vec!["smt2"],
        ProverKind::Metamath => vec!["mm"],
        ProverKind::HolLight => vec!["ml"],
        ProverKind::Mizar => vec!["miz"],
        ProverKind::PVS => vec!["pvs"],
        ProverKind::ACL2 => vec!["lisp"],
        ProverKind::Hol4 => vec!["sml"],
    };

    let mut files = vec![];
    if let Ok(entries) = std::fs::read_dir(&dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if let Some(ext) = path.extension() {
                if extensions.iter().any(|e| ext == *e) {
                    files.push(path);
                }
            }
        }
    }
    files
}

/// Create a simple term for testing
pub fn simple_term() -> Term {
    Term::App {
        func: Box::new(Term::Const("add".to_string())),
        args: vec![
            Term::Const("1".to_string()),
            Term::Const("2".to_string()),
        ],
    }
}

/// Create a lambda term for testing
pub fn lambda_term() -> Term {
    Term::Lambda {
        param: "x".to_string(),
        param_type: Some(Box::new(Term::Universe(0))),
        body: Box::new(Term::Var("x".to_string())),
    }
}

/// Create a pi type for testing
pub fn pi_term() -> Term {
    Term::Pi {
        param: "A".to_string(),
        param_type: Box::new(Term::Universe(0)),
        body: Box::new(Term::App {
            func: Box::new(Term::Const("List".to_string())),
            args: vec![Term::Var("A".to_string())],
        }),
    }
}

/// Create a complex nested term for testing
pub fn complex_term() -> Term {
    Term::App {
        func: Box::new(Term::Const("forall".to_string())),
        args: vec![
            Term::Lambda {
                param: "x".to_string(),
                param_type: Some(Box::new(Term::Universe(0))),
                body: Box::new(Term::App {
                    func: Box::new(Term::Const("eq".to_string())),
                    args: vec![
                        Term::Var("x".to_string()),
                        Term::Var("x".to_string()),
                    ],
                }),
            },
        ],
    }
}

/// Check if a prover executable is available
pub fn is_prover_available(kind: ProverKind) -> bool {
    let config = test_prover_config(kind);
    which::which(&config.executable).is_ok()
}

/// Skip test if prover is not available
#[macro_export]
macro_rules! require_prover {
    ($kind:expr) => {
        if !$crate::common::is_prover_available($kind) {
            eprintln!("Skipping test: {} not available", stringify!($kind));
            return;
        }
    };
}

/// Assert that two terms are structurally equal
pub fn assert_term_eq(left: &Term, right: &Term) {
    pretty_assertions::assert_eq!(left, right);
}

/// Assert that a proof state has no goals (is complete)
pub fn assert_proof_complete(state: &ProofState) {
    assert!(
        state.goals.is_empty(),
        "Expected proof to be complete, but {} goals remain",
        state.goals.len()
    );
}

/// Assert that a proof state has exactly n goals
pub fn assert_goal_count(state: &ProofState, expected: usize) {
    assert_eq!(
        state.goals.len(),
        expected,
        "Expected {} goals, but found {}",
        expected,
        state.goals.len()
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_proof_state() {
        let state = simple_proof_state();
        assert_eq!(state.goals.len(), 1);
        assert_eq!(state.goals[0].id, "goal1");
    }

    #[test]
    fn test_multi_goal_proof_state() {
        let state = multi_goal_proof_state();
        assert_eq!(state.goals.len(), 2);
    }

    #[test]
    fn test_proof_examples_dir() {
        let dir = proof_examples_dir(ProverKind::Agda);
        assert!(dir.to_str().unwrap().contains("agda"));
    }

    #[test]
    fn test_simple_term() {
        let term = simple_term();
        assert!(matches!(term, Term::App { .. }));
    }

    #[test]
    fn test_lambda_term() {
        let term = lambda_term();
        assert!(matches!(term, Term::Lambda { .. }));
    }

    #[test]
    fn test_pi_term() {
        let term = pi_term();
        assert!(matches!(term, Term::Pi { .. }));
    }
}
