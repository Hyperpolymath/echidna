// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Integration tests for all 12 theorem prover backends

mod common;

use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind};
use std::path::PathBuf;

/// Test all tier 1 provers
#[cfg(test)]
mod tier1_tests {
    use super::*;

    #[tokio::test]
    async fn test_agda_basic_parse() {
        if !common::is_prover_available(ProverKind::Agda) {
            eprintln!("Skipping: Agda not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Agda);
        let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

        let content = r#"
module Test where

id : {A : Set} → A → A
id x = x
        "#;

        let result = backend.parse_string(content).await;
        assert!(result.is_ok(), "Failed to parse Agda: {:?}", result.err());
    }

    #[tokio::test]
    async fn test_coq_basic_parse() {
        if !common::is_prover_available(ProverKind::Coq) {
            eprintln!("Skipping: Coq not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Coq);
        let backend = ProverFactory::create(ProverKind::Coq, config).unwrap();

        let content = r#"
Theorem id_example : forall (A : Type) (x : A), x = x.
Proof.
  intros.
  reflexivity.
Qed.
        "#;

        let result = backend.parse_string(content).await;
        assert!(result.is_ok(), "Failed to parse Coq: {:?}", result.err());
    }

    #[tokio::test]
    async fn test_lean_basic_parse() {
        if !common::is_prover_available(ProverKind::Lean) {
            eprintln!("Skipping: Lean not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Lean);
        let backend = ProverFactory::create(ProverKind::Lean, config).unwrap();

        let content = r#"
theorem id_example (A : Type) (x : A) : x = x := rfl
        "#;

        let result = backend.parse_string(content).await;
        assert!(result.is_ok(), "Failed to parse Lean: {:?}", result.err());
    }

    #[tokio::test]
    async fn test_isabelle_basic_parse() {
        if !common::is_prover_available(ProverKind::Isabelle) {
            eprintln!("Skipping: Isabelle not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Isabelle);
        let backend = ProverFactory::create(ProverKind::Isabelle, config).unwrap();

        let content = r#"
theory Test
  imports Main
begin

lemma id_example: "x = x"
  by simp

end
        "#;

        let result = backend.parse_string(content).await;
        assert!(result.is_ok(), "Failed to parse Isabelle: {:?}", result.err());
    }

    #[tokio::test]
    async fn test_z3_basic_parse() {
        if !common::is_prover_available(ProverKind::Z3) {
            eprintln!("Skipping: Z3 not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Z3);
        let backend = ProverFactory::create(ProverKind::Z3, config).unwrap();

        let content = r#"
(declare-const x Int)
(assert (= x x))
(check-sat)
        "#;

        let result = backend.parse_string(content).await;
        assert!(result.is_ok(), "Failed to parse Z3: {:?}", result.err());
    }

    #[tokio::test]
    async fn test_cvc5_basic_parse() {
        if !common::is_prover_available(ProverKind::CVC5) {
            eprintln!("Skipping: CVC5 not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::CVC5);
        let backend = ProverFactory::create(ProverKind::CVC5, config).unwrap();

        let content = r#"
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= x x))
(check-sat)
        "#;

        let result = backend.parse_string(content).await;
        assert!(result.is_ok(), "Failed to parse CVC5: {:?}", result.err());
    }
}

/// Test all tier 2 provers
#[cfg(test)]
mod tier2_tests {
    use super::*;

    #[tokio::test]
    async fn test_metamath_basic_parse() {
        if !common::is_prover_available(ProverKind::Metamath) {
            eprintln!("Skipping: Metamath not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Metamath);
        let backend = ProverFactory::create(ProverKind::Metamath, config).unwrap();

        let content = r#"
$( Basic Metamath example $)
$c |- wff $.
$v x $.
wx $f wff x $.
        "#;

        let result = backend.parse_string(content).await;
        assert!(result.is_ok(), "Failed to parse Metamath: {:?}", result.err());
    }

    #[tokio::test]
    async fn test_hol_light_basic_parse() {
        if !common::is_prover_available(ProverKind::HolLight) {
            eprintln!("Skipping: HOL Light not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::HolLight);
        let backend = ProverFactory::create(ProverKind::HolLight, config).unwrap();

        let content = r#"
let id_theorem = prove(`!x:A. x = x`, REFL_TAC);;
        "#;

        let result = backend.parse_string(content).await;
        assert!(result.is_ok(), "Failed to parse HOL Light: {:?}", result.err());
    }

    #[tokio::test]
    async fn test_mizar_basic_parse() {
        if !common::is_prover_available(ProverKind::Mizar) {
            eprintln!("Skipping: Mizar not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Mizar);
        let backend = ProverFactory::create(ProverKind::Mizar, config).unwrap();

        let content = r#"
environ

vocabularies TARSKI;

begin

theorem
  for x being object holds x = x;
        "#;

        let result = backend.parse_string(content).await;
        assert!(result.is_ok(), "Failed to parse Mizar: {:?}", result.err());
    }
}

/// Test all tier 3 provers
#[cfg(test)]
mod tier3_tests {
    use super::*;

    #[tokio::test]
    async fn test_pvs_basic_parse() {
        if !common::is_prover_available(ProverKind::PVS) {
            eprintln!("Skipping: PVS not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::PVS);
        let backend = ProverFactory::create(ProverKind::PVS, config).unwrap();

        let content = r#"
test: THEORY
BEGIN
  id_theorem: THEOREM FORALL (x: int): x = x
END test
        "#;

        let result = backend.parse_string(content).await;
        assert!(result.is_ok(), "Failed to parse PVS: {:?}", result.err());
    }

    #[tokio::test]
    async fn test_acl2_basic_parse() {
        if !common::is_prover_available(ProverKind::ACL2) {
            eprintln!("Skipping: ACL2 not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::ACL2);
        let backend = ProverFactory::create(ProverKind::ACL2, config).unwrap();

        let content = r#"
(defthm id-theorem
  (equal x x))
        "#;

        let result = backend.parse_string(content).await;
        assert!(result.is_ok(), "Failed to parse ACL2: {:?}", result.err());
    }
}

/// Test tier 4 provers
#[cfg(test)]
mod tier4_tests {
    use super::*;

    #[tokio::test]
    async fn test_hol4_basic_parse() {
        if !common::is_prover_available(ProverKind::Hol4) {
            eprintln!("Skipping: HOL4 not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Hol4);
        let backend = ProverFactory::create(ProverKind::Hol4, config).unwrap();

        let content = r#"
val id_theorem = prove(``!x. x = x``, REFL_TAC);
        "#;

        let result = backend.parse_string(content).await;
        assert!(result.is_ok(), "Failed to parse HOL4: {:?}", result.err());
    }
}

/// Test proof verification for all provers
#[cfg(test)]
mod verification_tests {
    use super::*;

    async fn test_prover_verification(kind: ProverKind, content: &str) {
        if !common::is_prover_available(kind) {
            eprintln!("Skipping: {:?} not available", kind);
            return;
        }

        let config = common::test_prover_config(kind);
        let backend = ProverFactory::create(kind, config).unwrap();

        let state = backend.parse_string(content).await.unwrap();
        let verified = backend.verify_proof(&state).await;

        assert!(verified.is_ok(), "Verification failed: {:?}", verified.err());
    }

    #[tokio::test]
    async fn test_all_provers_verify() {
        // Test each prover with a simple theorem
        let provers_and_content = vec![
            (ProverKind::Agda, "module T where\nid : {A : Set} → A → A\nid x = x"),
            (ProverKind::Coq, "Theorem t : forall x, x = x. Proof. reflexivity. Qed."),
            (ProverKind::Lean, "theorem t (x : Nat) : x = x := rfl"),
            (ProverKind::Z3, "(declare-const x Int)\n(assert (= x x))\n(check-sat)"),
        ];

        for (kind, content) in provers_and_content {
            test_prover_verification(kind, content).await;
        }
    }
}

/// Test tactic execution for interactive provers
#[cfg(test)]
mod tactic_tests {
    use super::*;
    use echidna::core::Tactic;

    #[tokio::test]
    async fn test_coq_intro_tactic() {
        if !common::is_prover_available(ProverKind::Coq) {
            eprintln!("Skipping: Coq not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Coq);
        let backend = ProverFactory::create(ProverKind::Coq, config).unwrap();

        let content = "Theorem t : forall x, x = x.";
        let state = backend.parse_string(content).await.unwrap();

        let result = backend.apply_tactic(&state, &Tactic::Intro).await;
        assert!(result.is_ok(), "Intro tactic failed: {:?}", result.err());
    }

    #[tokio::test]
    async fn test_lean_reflexivity_tactic() {
        if !common::is_prover_available(ProverKind::Lean) {
            eprintln!("Skipping: Lean not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Lean);
        let backend = ProverFactory::create(ProverKind::Lean, config).unwrap();

        let content = "theorem t (x : Nat) : x = x := by";
        let state = backend.parse_string(content).await.unwrap();

        let result = backend.apply_tactic(&state, &Tactic::Reflexivity).await;
        assert!(result.is_ok(), "Reflexivity tactic failed: {:?}", result.err());
    }
}

/// Test cross-prover term translation
#[cfg(test)]
mod translation_tests {
    use super::*;
    use echidna::core::Term;

    #[tokio::test]
    async fn test_translate_agda_to_coq() {
        if !common::is_prover_available(ProverKind::Agda)
            || !common::is_prover_available(ProverKind::Coq)
        {
            eprintln!("Skipping: Agda or Coq not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Agda);
        let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

        let term = common::simple_term();
        let result = backend.translate_term(&term, ProverKind::Coq).await;

        assert!(result.is_ok(), "Translation failed: {:?}", result.err());
    }

    #[tokio::test]
    async fn test_translate_z3_to_cvc5() {
        if !common::is_prover_available(ProverKind::Z3)
            || !common::is_prover_available(ProverKind::CVC5)
        {
            eprintln!("Skipping: Z3 or CVC5 not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Z3);
        let backend = ProverFactory::create(ProverKind::Z3, config).unwrap();

        let term = Term::App {
            func: Box::new(Term::Const("=".to_string())),
            args: vec![
                Term::Var("x".to_string()),
                Term::Var("x".to_string()),
            ],
        };

        let result = backend.translate_term(&term, ProverKind::CVC5).await;
        assert!(result.is_ok(), "SMT translation failed: {:?}", result.err());
    }
}

/// Test export functionality
#[cfg(test)]
mod export_tests {
    use super::*;

    #[tokio::test]
    async fn test_agda_export() {
        if !common::is_prover_available(ProverKind::Agda) {
            eprintln!("Skipping: Agda not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Agda);
        let backend = ProverFactory::create(ProverKind::Agda, config).unwrap();

        let state = common::simple_proof_state();
        let result = backend.export(&state).await;

        assert!(result.is_ok(), "Export failed: {:?}", result.err());
        let code = result.unwrap();
        assert!(code.contains("module"), "Exported code should contain module declaration");
    }

    #[tokio::test]
    async fn test_coq_export() {
        if !common::is_prover_available(ProverKind::Coq) {
            eprintln!("Skipping: Coq not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Coq);
        let backend = ProverFactory::create(ProverKind::Coq, config).unwrap();

        let state = common::simple_proof_state();
        let result = backend.export(&state).await;

        assert!(result.is_ok(), "Export failed: {:?}", result.err());
        let code = result.unwrap();
        assert!(
            code.contains("Theorem") || code.contains("Lemma"),
            "Exported code should contain theorem/lemma"
        );
    }
}

/// Test error handling
#[cfg(test)]
mod error_tests {
    use super::*;

    #[tokio::test]
    async fn test_parse_invalid_syntax() {
        if !common::is_prover_available(ProverKind::Coq) {
            eprintln!("Skipping: Coq not available");
            return;
        }

        let config = common::test_prover_config(ProverKind::Coq);
        let backend = ProverFactory::create(ProverKind::Coq, config).unwrap();

        let invalid_content = "This is not valid Coq syntax!!!";
        let result = backend.parse_string(invalid_content).await;

        assert!(result.is_err(), "Should fail on invalid syntax");
    }

    #[tokio::test]
    async fn test_apply_invalid_tactic() {
        let state = common::simple_proof_state();
        let mock = common::mock_prover::MockProver::new(ProverKind::Agda);

        mock.add_tactic_result(Err(anyhow::anyhow!("Invalid tactic")));

        let result = mock.apply_tactic(&state, &Tactic::Intro).await;
        assert!(result.is_err(), "Should fail on invalid tactic");
    }
}
