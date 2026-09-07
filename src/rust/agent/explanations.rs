// SPDX-FileCopyrightText: 2025 ECHIDNA Project Contributors
// SPDX-License-Identifier: AGPL-3.0-or-later

#![allow(dead_code)]

//! Template-Based Explanations
//!
//! Generates human-readable explanations for proof failures, tactic selection,
//! and prover selection decisions.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use super::AgenticGoal;
use crate::core::Term;
use crate::provers::ProverKind;

/// Explanation for a proof attempt
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Explanation {
    /// Title of the explanation
    pub title: String,

    /// Main explanation text
    pub message: String,

    /// Additional details (key-value pairs)
    pub details: HashMap<String, String>,

    /// Suggestions for the user
    pub suggestions: Vec<String>,
}

impl Explanation {
    pub fn new(title: impl Into<String>, message: impl Into<String>) -> Self {
        Explanation {
            title: title.into(),
            message: message.into(),
            details: HashMap::new(),
            suggestions: Vec::new(),
        }
    }

    pub fn with_detail(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.details.insert(key.into(), value.into());
        self
    }

    pub fn with_suggestion(mut self, suggestion: impl Into<String>) -> Self {
        self.suggestions.push(suggestion.into());
        self
    }

    /// Format as human-readable text
    pub fn format(&self) -> String {
        let mut result = format!("# {}\n\n{}\n", self.title, self.message);

        if !self.details.is_empty() {
            result.push_str("\n## Details\n\n");
            for (key, value) in &self.details {
                result.push_str(&format!("- **{}**: {}\n", key, value));
            }
        }

        if !self.suggestions.is_empty() {
            result.push_str("\n## Suggestions\n\n");
            for suggestion in &self.suggestions {
                result.push_str(&format!("- {}\n", suggestion));
            }
        }

        result
    }
}

/// Template-based explanation generator
pub struct ExplanationGenerator {
    /// Custom templates (can be loaded from config)
    templates: HashMap<String, String>,
}

impl ExplanationGenerator {
    pub fn new() -> Self {
        ExplanationGenerator {
            templates: Self::default_templates(),
        }
    }

    /// Load default explanation templates
    fn default_templates() -> HashMap<String, String> {
        let mut templates = HashMap::new();

        templates.insert(
            "proof_failed".to_string(),
            "The proof attempt failed after {attempts} attempts using {prover}.".to_string(),
        );

        templates.insert(
            "timeout".to_string(),
            "The proof attempt timed out after {timeout_secs} seconds.".to_string(),
        );

        templates.insert(
            "no_tactic".to_string(),
            "No suitable tactic could be found for this goal.".to_string(),
        );

        templates.insert(
            "decomposed".to_string(),
            "The goal was decomposed into {num_subgoals} sub-goals.".to_string(),
        );

        templates.insert(
            "max_attempts".to_string(),
            "Maximum attempts ({max_attempts}) exceeded for this goal.".to_string(),
        );

        templates.insert(
            "prover_selected".to_string(),
            "Selected {prover} based on aspect similarity (score: {score:.2}).".to_string(),
        );

        templates
    }

    /// Explain a proof failure
    pub fn explain_failure(
        &self,
        goal: &AgenticGoal,
        reason: &str,
        prover: Option<ProverKind>,
    ) -> Explanation {
        let title = "Proof Attempt Failed";

        let message = if let Some(p) = prover {
            format!(
                "The proof attempt for '{}' failed using prover {:?}. {}",
                goal.goal.id, p, reason
            )
        } else {
            format!(
                "The proof attempt for '{}' failed. {}",
                goal.goal.id, reason
            )
        };

        let mut exp = Explanation::new(title, message)
            .with_detail("Goal ID", &goal.goal.id)
            .with_detail("Target", self.format_term(&goal.goal.target))
            .with_detail("Attempts", goal.attempts.to_string())
            .with_detail("Priority", format!("{:?}", goal.priority));

        if let Some(prover) = prover {
            exp = exp.with_detail("Prover", format!("{:?}", prover));
        }

        // Add context-specific suggestions
        exp = match reason {
            r if r.contains("timeout") => exp
                .with_suggestion("Try decomposing the goal into smaller sub-goals")
                .with_suggestion("Use a faster prover (Z3 or CVC5)")
                .with_suggestion("Simplify the goal using lemmas"),
            r if r.contains("No tactic") => exp
                .with_suggestion("Try a different prover that may have better tactics")
                .with_suggestion("Add more hypotheses to the goal")
                .with_suggestion("Break the goal into simpler parts"),
            r if r.contains("Max attempts") => exp
                .with_suggestion("The goal may be too complex - try manual decomposition")
                .with_suggestion("Check if the goal is actually provable")
                .with_suggestion("Review the goal formulation for errors"),
            _ => exp
                .with_suggestion("Try using a different prover")
                .with_suggestion("Check the goal formulation")
                .with_suggestion("Add more context or hypotheses"),
        };

        exp
    }

    /// Explain prover selection
    pub fn explain_prover_selection(
        &self,
        goal: &AgenticGoal,
        prover: ProverKind,
        score: f64,
        reason: &str,
    ) -> Explanation {
        let title = "Prover Selection";

        let message = format!(
            "Selected prover {:?} for goal '{}' (score: {:.2}). {}",
            prover, goal.goal.id, score, reason
        );

        Explanation::new(title, message)
            .with_detail("Goal ID", &goal.goal.id)
            .with_detail("Prover", format!("{:?}", prover))
            .with_detail("Score", format!("{:.2}", score))
            .with_detail("Aspects", goal.aspects.join(", "))
            .with_suggestion(self.prover_characteristics(prover))
    }

    /// Explain goal decomposition
    pub fn explain_decomposition(
        &self,
        goal: &AgenticGoal,
        sub_goals: &[AgenticGoal],
        strategy: &str,
    ) -> Explanation {
        let title = "Goal Decomposition";

        let message = format!(
            "Decomposed goal '{}' into {} sub-goals using {} strategy.",
            goal.goal.id,
            sub_goals.len(),
            strategy
        );

        let mut exp = Explanation::new(title, message)
            .with_detail("Original Goal", &goal.goal.id)
            .with_detail("Number of Sub-goals", sub_goals.len().to_string())
            .with_detail("Strategy", strategy);

        // List sub-goals
        for (i, sub_goal) in sub_goals.iter().enumerate() {
            exp = exp.with_detail(
                format!("Sub-goal {}", i + 1),
                format!(
                    "{}: {}",
                    sub_goal.goal.id,
                    self.format_term(&sub_goal.goal.target)
                ),
            );
        }

        exp = exp
            .with_suggestion("Sub-goals will be attempted in order of priority")
            .with_suggestion("If any sub-goal fails, the decomposition strategy may be revised");

        exp
    }

    /// Explain tactic selection
    pub fn explain_tactic_selection(
        &self,
        goal: &AgenticGoal,
        tactic: &str,
        confidence: f64,
    ) -> Explanation {
        let title = "Tactic Selection";

        let message = format!(
            "Selected tactic '{}' for goal '{}' (confidence: {:.2}).",
            tactic, goal.goal.id, confidence
        );

        Explanation::new(title, message)
            .with_detail("Goal ID", &goal.goal.id)
            .with_detail("Tactic", tactic)
            .with_detail("Confidence", format!("{:.2}", confidence))
            .with_suggestion(self.tactic_explanation(tactic))
    }

    /// Explain why a proof succeeded
    pub fn explain_success(
        &self,
        goal: &AgenticGoal,
        prover: ProverKind,
        time_ms: u64,
    ) -> Explanation {
        let title = "Proof Succeeded";

        let message = format!(
            "Successfully proved goal '{}' using {:?} in {}ms.",
            goal.goal.id, prover, time_ms
        );

        Explanation::new(title, message)
            .with_detail("Goal ID", &goal.goal.id)
            .with_detail("Prover", format!("{:?}", prover))
            .with_detail("Time", format!("{}ms", time_ms))
            .with_detail("Attempts", goal.attempts.to_string())
    }

    /// Format a term for display
    fn format_term(&self, term: &Term) -> String {
        match term {
            Term::Var(name) => name.clone(),
            Term::Lambda { param, body, .. } => {
                format!("λ{}. {}", param, self.format_term(body))
            },
            Term::Pi {
                param,
                param_type,
                body,
            } => {
                format!(
                    "∀{}:{}. {}",
                    param,
                    self.format_term(param_type),
                    self.format_term(body)
                )
            },
            Term::Sigma {
                param,
                param_type,
                body,
            } => {
                format!(
                    "∃{}:{}. {}",
                    param,
                    self.format_term(param_type),
                    self.format_term(body)
                )
            },
            Term::App { func, args } => {
                let args_str: Vec<_> = args.iter().map(|a| self.format_term(a)).collect();
                format!("({} {})", self.format_term(func), args_str.join(" "))
            },
            Term::Type(level) => format!("Type({})", level),
            Term::Sort(level) => format!("Sort({})", level),
            Term::Let {
                name, value, body, ..
            } => {
                format!(
                    "let {} = {} in {}",
                    name,
                    self.format_term(value),
                    self.format_term(body)
                )
            },
            Term::Match { scrutinee, .. } => {
                format!("match {} with ...", self.format_term(scrutinee))
            },
            Term::Fix { name, body, .. } => {
                format!("fix {}. {}", name, self.format_term(body))
            },
            Term::Const(name) => name.clone(),
            Term::Hole(name) => format!("?{}", name),
            Term::Universe(level) => format!("Type{}", level),
            Term::Meta(id) => format!("?{}", id),
            Term::ProverSpecific { prover, .. } => format!("<{}-term>", prover),
        }
    }

    /// Get prover characteristics
    fn prover_characteristics(&self, prover: ProverKind) -> String {
        match prover {
            ProverKind::Agda => "Agda excels at dependent type theory and functional programming proofs.",
            ProverKind::Coq => "Coq is powerful for general mathematical proofs and software verification.",
            ProverKind::Lean => "Lean is excellent for mathematical formalization with excellent automation.",
            ProverKind::Isabelle => "Isabelle/HOL is robust for higher-order logic and large-scale formalization.",
            ProverKind::Z3 => "Z3 is a fast SMT solver, ideal for decidable theories and automated reasoning.",
            ProverKind::CVC5 => "CVC5 is a versatile SMT solver with support for many theories.",
            ProverKind::Metamath => "Metamath uses minimal axioms for foundational mathematics.",
            ProverKind::HOLLight => "HOL Light is a simple, trustworthy implementation of higher-order logic.",
            ProverKind::Mizar => "Mizar focuses on readable, natural language-like proofs.",
            ProverKind::PVS => "PVS combines specification and verification for critical systems.",
            ProverKind::ACL2 => "ACL2 is based on executable logic for program verification.",
            ProverKind::HOL4 => "HOL4 is the classic HOL implementation with extensive libraries.",
            ProverKind::Idris2 => "Idris 2 excels at dependent types with first-class type-level computation and quantitative types.",
            ProverKind::Vampire => "Vampire is a leading first-order ATP with superposition calculus, winning multiple CASC awards.",
            ProverKind::EProver => "E Prover is a highly optimized first-order theorem prover for clausal logic with auto mode.",
            ProverKind::SPASS => "SPASS handles sorted first-order logic with superposition calculus and sort handling.",
            ProverKind::AltErgo => "Alt-Ergo is an SMT solver designed for program verification with polymorphic first-order logic.",
            ProverKind::FStar => "F* combines dependent types with an effect system for verified programming (Project Everest/HACL*).",
            ProverKind::Dafny => "Dafny is an auto-active verifier generating verification conditions for SMT solvers via Boogie.",
            ProverKind::Why3 => "Why3 orchestrates multiple provers (Z3, CVC5, Alt-Ergo) for deductive program verification.",
            ProverKind::TLAPS => "TLAPS is the TLA+ Proof System for verifying distributed system properties.",
            ProverKind::Twelf => "Twelf is a logical framework (LF) for encoding and checking metatheoretic properties.",
            ProverKind::Nuprl => "Nuprl implements constructive type theory with a large library of formalized mathematics.",
            ProverKind::Minlog => "Minlog extracts certified programs from constructive proofs in minimal logic.",
            ProverKind::Imandra => "Imandra provides ML-based reasoning for industrial verification (finance, autonomous systems).",
            ProverKind::GLPK => "GLPK solves linear programming and mixed-integer programming problems.",
            ProverKind::SCIP => "SCIP handles mixed-integer nonlinear programming beyond SMT solver capabilities.",
            ProverKind::MiniZinc => "MiniZinc is a constraint modelling language compiling to multiple backend solvers.",
            ProverKind::Chuffed => "Chuffed uses lazy clause generation for constraint propagation with SAT-style learning.",
            ProverKind::ORTools => "OR-Tools provides constraint solving, routing, and linear/integer programming.",
            ProverKind::TypedWasm => "TypedWasm is an internal oracle validating 10-level type safety for typed WASM memory regions.",
            ProverKind::SPIN => "SPIN is a model checker for verifying concurrent systems using Promela specifications and LTL.",
            ProverKind::CBMC => "CBMC is a bounded model checker for C/C++ programs verifying assertions and safety properties.",
            ProverKind::SeaHorn => "SeaHorn is an LLVM-based verification framework using abstract interpretation and Constrained Horn Clauses (CHC) to verify safety properties of C programs.",
            ProverKind::CaDiCaL => "CaDiCaL is a state-of-the-art CDCL SAT solver with advanced inprocessing techniques.",
            ProverKind::Kissat => "Kissat is a high-performance SAT solver optimized for competition benchmarks.",
            ProverKind::MiniSat => "MiniSat is a classic DPLL/CDCL SAT solver widely used as a reference implementation.",
            ProverKind::NuSMV => "NuSMV/nuXmv is a symbolic model checker for CTL/LTL verification of finite state systems.",
            ProverKind::TLC => "TLC is the TLA+ model checker for exhaustive state exploration of distributed system specifications.",
            ProverKind::Alloy => "Alloy is a relational model finder using SAT-based bounded analysis for structural properties.",
            ProverKind::Prism => "PRISM is a probabilistic model checker for DTMCs, CTMCs, MDPs, and reward-based properties.",
            ProverKind::UPPAAL => "UPPAAL verifies real-time systems modelled as timed automata against TCTL properties.",
            ProverKind::FramaC => "Frama-C is a C program analysis framework whose WP plugin performs deductive verification of ACSL-annotated code.",
            ProverKind::Viper => "Viper is a permission-based program verifier using separation logic with Silicon and Carbon backends.",
            ProverKind::Tamarin => "Tamarin verifies security protocols via multiset rewriting rules under the Dolev-Yao adversary model.",
            ProverKind::ProVerif => "ProVerif is an automatic cryptographic protocol verifier based on the applied pi-calculus.",
            ProverKind::KeY => "KeY is a deductive verification tool for Java programs using dynamic logic and the JML specification language.",
            ProverKind::DReal => "dReal is a delta-complete SMT solver for nonlinear real arithmetic (QF_NRA/QF_NRA_ODE) using interval constraint propagation.",
            _ => "Unknown prover.",
        }.to_string()
    }

    /// Get tactic explanation
    fn tactic_explanation(&self, tactic: &str) -> String {
        match tactic {
            "intro" => "Introduces a hypothesis or variable into the context.",
            "apply" => "Applies a theorem or hypothesis to the current goal.",
            "rewrite" => "Rewrites the goal using an equation or equivalence.",
            "reflexivity" => "Proves goals of the form 'x = x' automatically.",
            "assumption" => "Solves the goal if it matches a hypothesis exactly.",
            "induction" => "Applies structural induction on a variable.",
            "split" => "Splits a conjunction or existential goal into sub-goals.",
            "left" | "right" => "Chooses a side of a disjunction.",
            "exists" => "Provides a witness for an existential goal.",
            "unfold" => "Unfolds a definition to its underlying form.",
            _ => "A tactic for manipulating the proof state.",
        }
        .to_string()
    }
}

impl Default for ExplanationGenerator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::Priority;
    use crate::aspect::Aspect;
    use crate::core::Goal;

    #[test]
    fn test_failure_explanation() {
        let generator = ExplanationGenerator::new();

        let goal = AgenticGoal {
            goal: Goal {
                id: "test_goal".to_string(),
                target: Term::Var("A".to_string()),
                hypotheses: vec![],
            },
            priority: Priority::High,
            attempts: 2,
            max_attempts: 3,
            preferred_prover: None,
            aspects: vec![Aspect::Groups.dotted_key()],
            parent: None,
        };

        let exp = generator.explain_failure(&goal, "timeout", Some(ProverKind::Z3));
        let formatted = exp.format();

        assert!(formatted.contains("Proof Attempt Failed"));
        assert!(formatted.contains("timeout"));
        assert!(formatted.contains("Suggestions"));
    }

    #[test]
    fn test_success_explanation() {
        let generator = ExplanationGenerator::new();

        let goal = AgenticGoal {
            goal: Goal {
                id: "test_goal".to_string(),
                target: Term::Var("A".to_string()),
                hypotheses: vec![],
            },
            priority: Priority::High,
            attempts: 1,
            max_attempts: 3,
            preferred_prover: None,
            aspects: vec![Aspect::Groups.dotted_key()],
            parent: None,
        };

        let exp = generator.explain_success(&goal, ProverKind::Lean, 150);
        let formatted = exp.format();

        assert!(formatted.contains("Proof Succeeded"));
        assert!(formatted.contains("150ms"));
    }

    #[test]
    fn test_prover_selection_explanation() {
        let generator = ExplanationGenerator::new();

        let goal = AgenticGoal {
            goal: Goal {
                id: "test_goal".to_string(),
                target: Term::Var("A".to_string()),
                hypotheses: vec![],
            },
            priority: Priority::High,
            attempts: 0,
            max_attempts: 3,
            preferred_prover: None,
            aspects: vec![Aspect::Groups.dotted_key()],
            parent: None,
        };

        let exp = generator.explain_prover_selection(
            &goal,
            ProverKind::Lean,
            0.85,
            "High aspect match for algebra",
        );
        let formatted = exp.format();

        assert!(formatted.contains("Prover Selection"));
        assert!(formatted.contains("0.85"));
        assert!(formatted.contains("Lean"));
    }
}
