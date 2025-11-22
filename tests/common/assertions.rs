// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Custom assertions for ECHIDNA tests

use echidna::core::{ProofState, Term};
use pretty_assertions::assert_eq;

/// Assert that two terms are alpha-equivalent (same up to variable renaming)
pub fn assert_alpha_equivalent(left: &Term, right: &Term) {
    assert!(
        alpha_equivalent_impl(left, right, &mut std::collections::HashMap::new()),
        "Terms are not alpha-equivalent:\nLeft:  {:?}\nRight: {:?}",
        left,
        right
    );
}

fn alpha_equivalent_impl(
    left: &Term,
    right: &Term,
    bindings: &mut std::collections::HashMap<String, String>,
) -> bool {
    match (left, right) {
        (Term::Var(v1), Term::Var(v2)) => {
            if let Some(bound) = bindings.get(v1) {
                bound == v2
            } else {
                v1 == v2
            }
        }
        (Term::Const(c1), Term::Const(c2)) => c1 == c2,
        (Term::Universe(l1), Term::Universe(l2)) => l1 == l2,
        (Term::Meta(m1), Term::Meta(m2)) => m1 == m2,
        (
            Term::App {
                func: f1,
                args: a1,
            },
            Term::App {
                func: f2,
                args: a2,
            },
        ) => {
            alpha_equivalent_impl(f1, f2, bindings)
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(t1, t2)| alpha_equivalent_impl(t1, t2, bindings))
        }
        (
            Term::Lambda {
                param: p1,
                param_type: pt1,
                body: b1,
            },
            Term::Lambda {
                param: p2,
                param_type: pt2,
                body: b2,
            },
        ) => {
            let mut new_bindings = bindings.clone();
            new_bindings.insert(p1.clone(), p2.clone());

            let types_match = match (pt1, pt2) {
                (Some(t1), Some(t2)) => alpha_equivalent_impl(t1, t2, bindings),
                (None, None) => true,
                _ => false,
            };

            types_match && alpha_equivalent_impl(b1, b2, &mut new_bindings)
        }
        (
            Term::Pi {
                param: p1,
                param_type: pt1,
                body: b1,
            },
            Term::Pi {
                param: p2,
                param_type: pt2,
                body: b2,
            },
        ) => {
            let mut new_bindings = bindings.clone();
            new_bindings.insert(p1.clone(), p2.clone());

            alpha_equivalent_impl(pt1, pt2, bindings)
                && alpha_equivalent_impl(b1, b2, &mut new_bindings)
        }
        _ => false,
    }
}

/// Assert that a term contains a specific subterm
pub fn assert_contains_subterm(term: &Term, subterm: &Term) {
    assert!(
        contains_subterm(term, subterm),
        "Term {:?} does not contain subterm {:?}",
        term,
        subterm
    );
}

fn contains_subterm(term: &Term, target: &Term) -> bool {
    if term == target {
        return true;
    }

    match term {
        Term::App { func, args } => {
            contains_subterm(func, target) || args.iter().any(|arg| contains_subterm(arg, target))
        }
        Term::Lambda { body, param_type, .. } => {
            contains_subterm(body, target)
                || param_type
                    .as_ref()
                    .map_or(false, |t| contains_subterm(t, target))
        }
        Term::Pi {
            param_type, body, ..
        } => contains_subterm(param_type, target) || contains_subterm(body, target),
        _ => false,
    }
}

/// Assert that a proof state is valid (all goals have conclusions)
pub fn assert_valid_proof_state(state: &ProofState) {
    for (i, goal) in state.goals.iter().enumerate() {
        assert!(
            !goal.id.is_empty(),
            "Goal {} has empty ID",
            i
        );
        // Goals should have conclusions (even if trivial)
        match &goal.conclusion {
            Term::Const(c) if c.is_empty() => {
                panic!("Goal {} has empty constant as conclusion", i)
            }
            _ => {}
        }
    }
}

/// Assert that a proof state has fewer goals than another
pub fn assert_progress(before: &ProofState, after: &ProofState) {
    assert!(
        after.goals.len() < before.goals.len(),
        "No progress made: before had {} goals, after has {} goals",
        before.goals.len(),
        after.goals.len()
    );
}

/// Assert that a term is well-formed (no invalid structures)
pub fn assert_well_formed_term(term: &Term) {
    match term {
        Term::App { func, args } => {
            assert!(!args.is_empty(), "Application with no arguments");
            assert_well_formed_term(func);
            for arg in args {
                assert_well_formed_term(arg);
            }
        }
        Term::Lambda { param, body, param_type, .. } => {
            assert!(!param.is_empty(), "Lambda with empty parameter name");
            assert_well_formed_term(body);
            if let Some(ty) = param_type {
                assert_well_formed_term(ty);
            }
        }
        Term::Pi { param, param_type, body } => {
            assert!(!param.is_empty(), "Pi type with empty parameter name");
            assert_well_formed_term(param_type);
            assert_well_formed_term(body);
        }
        Term::Var(v) => {
            assert!(!v.is_empty(), "Empty variable name");
        }
        Term::Const(c) => {
            assert!(!c.is_empty(), "Empty constant name");
        }
        _ => {}
    }
}

/// Assert that serialization roundtrips correctly
pub fn assert_serialization_roundtrip<T>(value: &T)
where
    T: serde::Serialize + serde::de::DeserializeOwned + PartialEq + std::fmt::Debug,
{
    let json = serde_json::to_string(value).expect("Failed to serialize");
    let deserialized: T = serde_json::from_str(&json).expect("Failed to deserialize");
    assert_eq!(value, &deserialized, "Serialization roundtrip failed");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alpha_equivalent_vars() {
        let t1 = Term::Lambda {
            param: "x".to_string(),
            param_type: None,
            body: Box::new(Term::Var("x".to_string())),
        };
        let t2 = Term::Lambda {
            param: "y".to_string(),
            param_type: None,
            body: Box::new(Term::Var("y".to_string())),
        };
        assert_alpha_equivalent(&t1, &t2);
    }

    #[test]
    fn test_contains_subterm() {
        let subterm = Term::Var("x".to_string());
        let term = Term::App {
            func: Box::new(Term::Const("f".to_string())),
            args: vec![subterm.clone()],
        };
        assert_contains_subterm(&term, &subterm);
    }

    #[test]
    fn test_well_formed_term() {
        let term = Term::Lambda {
            param: "x".to_string(),
            param_type: Some(Box::new(Term::Universe(0))),
            body: Box::new(Term::Var("x".to_string())),
        };
        assert_well_formed_term(&term);
    }

    #[test]
    #[should_panic(expected = "Empty variable name")]
    fn test_ill_formed_term() {
        let term = Term::Var("".to_string());
        assert_well_formed_term(&term);
    }
}
