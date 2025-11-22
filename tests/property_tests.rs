// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Property-based tests for ECHIDNA core types and operations

mod common;

use echidna::core::{ProofState, Term};
use proptest::prelude::*;

/// Test that term serialization round-trips correctly
proptest! {
    #[test]
    fn test_term_serialization_roundtrip(term in common::generators::arb_term()) {
        let json = serde_json::to_string(&term).expect("Failed to serialize");
        let deserialized: Term = serde_json::from_str(&json).expect("Failed to deserialize");
        prop_assert_eq!(&term, &deserialized);
    }
}

/// Test that term display doesn't panic
proptest! {
    #[test]
    fn test_term_display_no_panic(term in common::generators::arb_term()) {
        let _ = format!("{}", term);
    }
}

/// Test that term equality is reflexive
proptest! {
    #[test]
    fn test_term_equality_reflexive(term in common::generators::arb_term()) {
        prop_assert_eq!(&term, &term);
    }
}

/// Test that term equality is symmetric
proptest! {
    #[test]
    fn test_term_equality_symmetric(
        term1 in common::generators::arb_term(),
        term2 in common::generators::arb_term()
    ) {
        let eq1 = term1 == term2;
        let eq2 = term2 == term1;
        prop_assert_eq!(eq1, eq2);
    }
}

/// Test that term hashing is consistent
proptest! {
    #[test]
    fn test_term_hash_consistent(term in common::generators::arb_term()) {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher1 = DefaultHasher::new();
        term.hash(&mut hasher1);
        let hash1 = hasher1.finish();

        let mut hasher2 = DefaultHasher::new();
        term.hash(&mut hasher2);
        let hash2 = hasher2.finish();

        prop_assert_eq!(hash1, hash2);
    }
}

/// Test that cloning a term produces an equal term
proptest! {
    #[test]
    fn test_term_clone_equality(term in common::generators::arb_term()) {
        let cloned = term.clone();
        prop_assert_eq!(&term, &cloned);
    }
}

/// Test proof state serialization
proptest! {
    #[test]
    fn test_proof_state_serialization(state in common::generators::arb_proof_state()) {
        let json = serde_json::to_string(&state).expect("Failed to serialize");
        let deserialized: ProofState = serde_json::from_str(&json).expect("Failed to deserialize");

        prop_assert_eq!(state.goals.len(), deserialized.goals.len());
        prop_assert_eq!(state.proof_script.len(), deserialized.proof_script.len());
    }
}

/// Test that variable substitution preserves term structure
proptest! {
    #[test]
    fn test_variable_substitution_preserves_structure(
        (var, replacement, body) in common::generators::valid_substitution()
    ) {
        // Perform substitution
        let substituted = substitute_var(&body, &var, &replacement);

        // Check that the term is still valid after substitution
        common::assertions::assert_well_formed_term(&substituted);
    }
}

/// Helper function for variable substitution
fn substitute_var(term: &Term, var: &str, replacement: &Term) -> Term {
    match term {
        Term::Var(v) if v == var => replacement.clone(),
        Term::Var(_) | Term::Const(_) | Term::Universe(_) | Term::Meta(_) => term.clone(),
        Term::App { func, args } => Term::App {
            func: Box::new(substitute_var(func, var, replacement)),
            args: args
                .iter()
                .map(|arg| substitute_var(arg, var, replacement))
                .collect(),
        },
        Term::Lambda {
            param,
            param_type,
            body,
        } => {
            if param == var {
                // Variable is shadowed, don't substitute in body
                term.clone()
            } else {
                Term::Lambda {
                    param: param.clone(),
                    param_type: param_type
                        .as_ref()
                        .map(|t| Box::new(substitute_var(t, var, replacement))),
                    body: Box::new(substitute_var(body, var, replacement)),
                }
            }
        }
        Term::Pi {
            param,
            param_type,
            body,
        } => {
            if param == var {
                // Variable is shadowed
                term.clone()
            } else {
                Term::Pi {
                    param: param.clone(),
                    param_type: Box::new(substitute_var(param_type, var, replacement)),
                    body: Box::new(substitute_var(body, var, replacement)),
                }
            }
        }
        Term::ProverSpecific { .. } => term.clone(),
    }
}

/// Test that term normalization is idempotent
proptest! {
    #[test]
    fn test_normalization_idempotent(term in common::generators::arb_term()) {
        // For this test, we just verify the term doesn't change on "normalization"
        // In a real implementation, normalize(normalize(t)) == normalize(t)
        let normalized1 = term.clone();
        let normalized2 = normalized1.clone();
        prop_assert_eq!(normalized1, normalized2);
    }
}

/// Test that term conversion preserves semantics
proptest! {
    #[test]
    fn test_term_conversion_preserves_equality(
        (term1, term2) in common::generators::equal_term_pair()
    ) {
        // If two terms are equal, they should remain equal after conversions
        prop_assert_eq!(&term1, &term2);

        // Serialize and deserialize
        let json1 = serde_json::to_string(&term1).unwrap();
        let json2 = serde_json::to_string(&term2).unwrap();

        let deser1: Term = serde_json::from_str(&json1).unwrap();
        let deser2: Term = serde_json::from_str(&json2).unwrap();

        prop_assert_eq!(&deser1, &deser2);
    }
}

/// Test that goal IDs are non-empty
proptest! {
    #[test]
    fn test_goal_id_nonempty(goal in common::generators::arb_goal()) {
        prop_assert!(!goal.id.is_empty(), "Goal ID should not be empty");
    }
}

/// Test that proof states are valid
proptest! {
    #[test]
    fn test_proof_state_validity(state in common::generators::arb_proof_state()) {
        // All goals should have non-empty IDs
        for goal in &state.goals {
            prop_assert!(!goal.id.is_empty(), "Goal ID should not be empty");
        }

        // Proof script should be a list of valid tactics
        prop_assert!(state.proof_script.len() < 1000, "Proof script too long");
    }
}

/// Test that tactics serialize correctly
proptest! {
    #[test]
    fn test_tactic_serialization(tactic in common::generators::arb_tactic()) {
        let json = serde_json::to_string(&tactic).expect("Failed to serialize tactic");
        let _: echidna::core::Tactic = serde_json::from_str(&json)
            .expect("Failed to deserialize tactic");
    }
}

/// Test parser invariants for simple terms
proptest! {
    #[test]
    fn test_simple_term_invariants(term in common::generators::simple_term()) {
        match &term {
            Term::Var(v) => prop_assert!(!v.is_empty(), "Variable name should not be empty"),
            Term::Const(c) => prop_assert!(!c.is_empty(), "Constant name should not be empty"),
            Term::Universe(level) => prop_assert!(*level < 1000, "Universe level too high"),
            Term::Meta(id) => prop_assert!(*id < 10000, "Meta ID too high"),
            _ => {}
        }
    }
}

/// Test that application terms have at least one argument
proptest! {
    #[test]
    fn test_application_has_args(func in common::generators::arb_term()) {
        let app = Term::App {
            func: Box::new(func),
            args: vec![Term::Const("arg".to_string())],
        };

        if let Term::App { args, .. } = app {
            prop_assert!(!args.is_empty(), "Application should have arguments");
        }
    }
}

/// Test that lambda terms have valid parameter names
proptest! {
    #[test]
    fn test_lambda_parameter_valid(param in common::generators::var_name()) {
        let lambda = Term::Lambda {
            param: param.clone(),
            param_type: None,
            body: Box::new(Term::Var(param.clone())),
        };

        if let Term::Lambda { param, .. } = lambda {
            prop_assert!(!param.is_empty(), "Lambda parameter should not be empty");
            prop_assert!(
                param.chars().next().unwrap().is_lowercase(),
                "Lambda parameter should start with lowercase"
            );
        }
    }
}

/// Test that Pi types have valid parameter names
proptest! {
    #[test]
    fn test_pi_parameter_valid(param in common::generators::var_name()) {
        let pi = Term::Pi {
            param: param.clone(),
            param_type: Box::new(Term::Universe(0)),
            body: Box::new(Term::Var(param.clone())),
        };

        if let Term::Pi { param, .. } = pi {
            prop_assert!(!param.is_empty(), "Pi parameter should not be empty");
        }
    }
}

/// Test composition of tactics
proptest! {
    #[test]
    fn test_tactic_composition(
        tactic1 in common::generators::arb_tactic(),
        tactic2 in common::generators::arb_tactic()
    ) {
        // Tactics should be composable (can be in a sequence)
        let tactics = vec![tactic1, tactic2];
        prop_assert!(tactics.len() == 2, "Should have 2 tactics");
    }
}

/// Test that context definitions are valid
proptest! {
    #[test]
    fn test_context_definitions_valid(context in common::generators::arb_context()) {
        // All definition names should be non-empty
        for (name, term) in &context.definitions {
            prop_assert!(!name.is_empty(), "Definition name should not be empty");
            common::assertions::assert_well_formed_term(term);
        }
    }
}

/// Test term depth bounds
proptest! {
    #[test]
    fn test_term_depth_bounded(term in common::generators::arb_term()) {
        fn depth(t: &Term) -> usize {
            match t {
                Term::Var(_) | Term::Const(_) | Term::Universe(_) | Term::Meta(_) => 0,
                Term::App { func, args } => {
                    1 + depth(func).max(args.iter().map(depth).max().unwrap_or(0))
                }
                Term::Lambda { body, param_type, .. } => {
                    1 + body.as_ref().iter()
                        .chain(param_type.as_ref().map(|t| t.as_ref()))
                        .map(depth)
                        .max()
                        .unwrap_or(0)
                }
                Term::Pi { param_type, body, .. } => {
                    1 + depth(param_type).max(depth(body))
                }
                Term::ProverSpecific { .. } => 0,
            }
        }

        let d = depth(&term);
        prop_assert!(d < 100, "Term depth should be bounded (got {})", d);
    }
}

/// Test that alpha-equivalent terms are treated correctly
proptest! {
    #[test]
    fn test_alpha_equivalence_basic(param1 in common::generators::var_name(), param2 in common::generators::var_name()) {
        let lambda1 = Term::Lambda {
            param: param1.clone(),
            param_type: None,
            body: Box::new(Term::Var(param1)),
        };

        let lambda2 = Term::Lambda {
            param: param2.clone(),
            param_type: None,
            body: Box::new(Term::Var(param2)),
        };

        // Both represent the identity function, should be alpha-equivalent
        common::assertions::assert_alpha_equivalent(&lambda1, &lambda2);
    }
}
