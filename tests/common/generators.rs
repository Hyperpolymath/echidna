// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Property-based testing generators for ECHIDNA types

use echidna::core::{Context, Goal, ProofState, Tactic, Term};
use proptest::prelude::*;
use std::collections::HashMap;

/// Strategy for generating variable names
pub fn var_name() -> impl Strategy<Value = String> {
    "[a-z][a-z0-9]*".prop_map(|s| s.to_string())
}

/// Strategy for generating constant names
pub fn const_name() -> impl Strategy<Value = String> {
    "[A-Z][a-zA-Z0-9]*".prop_map(|s| s.to_string())
}

/// Strategy for generating simple terms (non-recursive)
pub fn simple_term() -> impl Strategy<Value = Term> {
    prop_oneof![
        var_name().prop_map(Term::Var),
        const_name().prop_map(Term::Const),
        (0..10usize).prop_map(Term::Universe),
        (0..100usize).prop_map(Term::Meta),
    ]
}

/// Strategy for generating terms with bounded depth
pub fn term_with_depth(depth: u32) -> impl Strategy<Value = Term> {
    let leaf = simple_term();
    leaf.prop_recursive(depth, 256, 10, |inner| {
        prop_oneof![
            // Application
            (inner.clone(), prop::collection::vec(inner.clone(), 0..4)).prop_map(|(func, args)| {
                Term::App {
                    func: Box::new(func),
                    args,
                }
            }),
            // Lambda
            (var_name(), prop::option::of(inner.clone()), inner.clone()).prop_map(
                |(param, param_type, body)| Term::Lambda {
                    param,
                    param_type: param_type.map(Box::new),
                    body: Box::new(body),
                }
            ),
            // Pi type
            (var_name(), inner.clone(), inner.clone()).prop_map(|(param, param_type, body)| {
                Term::Pi {
                    param,
                    param_type: Box::new(param_type),
                    body: Box::new(body),
                }
            }),
        ]
    })
}

/// Strategy for generating arbitrary terms
pub fn arb_term() -> impl Strategy<Value = Term> {
    term_with_depth(5)
}

/// Strategy for generating goals
pub fn arb_goal() -> impl Strategy<Value = Goal> {
    (
        "[a-z]+[0-9]*",
        prop::collection::vec(arb_term(), 0..5),
        arb_term(),
    )
        .prop_map(|(id, hypotheses, conclusion)| Goal {
            id,
            hypotheses,
            conclusion,
        })
}

/// Strategy for generating contexts
pub fn arb_context() -> impl Strategy<Value = Context> {
    prop::collection::hash_map("[a-z]+", arb_term(), 0..5).prop_map(|definitions| Context {
        definitions,
        theorems: vec![],
    })
}

/// Strategy for generating proof states
pub fn arb_proof_state() -> impl Strategy<Value = ProofState> {
    (
        prop::collection::vec(arb_goal(), 0..3),
        arb_context(),
        prop::collection::vec(arb_tactic(), 0..5),
    )
        .prop_map(|(goals, context, proof_script)| ProofState {
            goals,
            context,
            proof_script,
            metadata: HashMap::new(),
        })
}

/// Strategy for generating tactics
pub fn arb_tactic() -> impl Strategy<Value = Tactic> {
    prop_oneof![
        Just(Tactic::Intro),
        Just(Tactic::Split),
        Just(Tactic::Reflexivity),
        Just(Tactic::Assumption),
        arb_term().prop_map(|t| Tactic::Apply { term: t }),
        arb_term().prop_map(|t| Tactic::Exact { term: t }),
        arb_term().prop_map(|t| Tactic::Rewrite { equation: t }),
        var_name().prop_map(|name| Tactic::Induction { on: name }),
        (var_name(), arb_term()).prop_map(|(name, ty)| Tactic::Have {
            name,
            claim: ty
        }),
    ]
}

/// Generate a pair of terms that should be equal after normalization
pub fn equal_term_pair() -> impl Strategy<Value = (Term, Term)> {
    arb_term().prop_map(|t| (t.clone(), t))
}

/// Generate a valid variable substitution
pub fn valid_substitution() -> impl Strategy<Value = (String, Term, Term)> {
    (var_name(), arb_term(), arb_term()).prop_map(|(var, replacement, body)| {
        // Ensure the variable appears in the body for meaningful test
        let body_with_var = Term::App {
            func: Box::new(body),
            args: vec![Term::Var(var.clone())],
        };
        (var, replacement, body_with_var)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    proptest! {
        #[test]
        fn test_generates_valid_var_names(name in var_name()) {
            assert!(!name.is_empty());
            assert!(name.chars().next().unwrap().is_lowercase());
        }

        #[test]
        fn test_generates_valid_const_names(name in const_name()) {
            assert!(!name.is_empty());
            assert!(name.chars().next().unwrap().is_uppercase());
        }

        #[test]
        fn test_generates_valid_terms(term in arb_term()) {
            // Terms should serialize without panic
            let _ = serde_json::to_string(&term).unwrap();
        }

        #[test]
        fn test_generates_valid_goals(goal in arb_goal()) {
            assert!(!goal.id.is_empty());
        }

        #[test]
        fn test_generates_valid_proof_states(state in arb_proof_state()) {
            // Proof states should serialize
            let _ = serde_json::to_string(&state).unwrap();
        }

        #[test]
        fn test_term_display_doesnt_panic(term in arb_term()) {
            let _ = format!("{}", term);
        }
    }
}
