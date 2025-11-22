// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Mizar theorem prover backend implementation
//!
//! Mizar is a Tier 2 prover (complexity 3/5) with natural-language-like syntax.
//! It features the Mizar Mathematical Library (MML), one of the largest collections
//! of formalized mathematics.
//!
//! Key features:
//! - Natural language proof style (let, assume, thus, per cases)
//! - Environ sections for article dependencies
//! - MML (Mizar Mathematical Library) integration
//! - Multi-phase verification (accommodation, analyzer)
//! - Extensive library of formalized mathematics

use async_trait::async_trait;
use anyhow::{anyhow, Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use tokio::fs;
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use crate::core::{
    Context as ProofContext, Definition, Goal, Hypothesis, ProofState, Tactic, TacticResult,
    Term, Theorem, Variable,
};
use crate::provers::{ProverBackend, ProverConfig, ProverKind};

/// Mizar prover backend
pub struct MizarBackend {
    config: ProverConfig,
    mml_path: PathBuf,
}

impl MizarBackend {
    /// Create a new Mizar backend
    pub fn new(config: ProverConfig) -> Self {
        let mml_path = std::env::var("MIZFILES")
            .map(PathBuf::from)
            .unwrap_or_else(|_| PathBuf::from("/usr/local/share/mizar"));

        MizarBackend { config, mml_path }
    }

    /// Set the MML (Mizar Mathematical Library) path
    pub fn with_mml_path(mut self, path: PathBuf) -> Self {
        self.mml_path = path;
        self
    }

    /// Parse a Mizar article from string content
    fn parse_article(&self, content: &str) -> Result<MizarArticle> {
        let mut parser = MizarParser::new(content);
        parser.parse()
    }

    /// Run Mizar verifier on a file
    async fn verify_file(&self, path: &Path) -> Result<MizarVerificationResult> {
        // Mizar verification is a two-phase process:
        // 1. Accommodation (mizf) - processes environ directives
        // 2. Analyzer (verifier) - type checks and verifies proofs

        // Phase 1: Accommodation
        let mizf_output = self.run_mizf(path).await?;
        if !mizf_output.success {
            return Ok(MizarVerificationResult {
                success: false,
                errors: mizf_output.errors,
                warnings: mizf_output.warnings,
            });
        }

        // Phase 2: Verification
        let verifier_output = self.run_verifier(path).await?;

        Ok(MizarVerificationResult {
            success: verifier_output.success,
            errors: verifier_output.errors,
            warnings: verifier_output.warnings,
        })
    }

    /// Run mizf (accommodation phase)
    async fn run_mizf(&self, path: &Path) -> Result<MizarPhaseOutput> {
        let mizf_path = self.config.executable.parent()
            .unwrap_or_else(|| Path::new("/usr/local/bin"))
            .join("mizf");

        let output = Command::new(&mizf_path)
            .arg(path)
            .env("MIZFILES", &self.mml_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .await
            .context("Failed to run mizf")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let (errors, warnings) = self.parse_mizar_messages(&stdout, &stderr);

        Ok(MizarPhaseOutput {
            success: output.status.success() && errors.is_empty(),
            errors,
            warnings,
        })
    }

    /// Run verifier (verification phase)
    async fn run_verifier(&self, path: &Path) -> Result<MizarPhaseOutput> {
        let verifier_path = self.config.executable.parent()
            .unwrap_or_else(|| Path::new("/usr/local/bin"))
            .join("verifier");

        let output = Command::new(&verifier_path)
            .arg(path)
            .env("MIZFILES", &self.mml_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .await
            .context("Failed to run verifier")?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        let (errors, warnings) = self.parse_mizar_messages(&stdout, &stderr);

        Ok(MizarPhaseOutput {
            success: output.status.success() && errors.is_empty(),
            errors,
            warnings,
        })
    }

    /// Parse Mizar error and warning messages
    fn parse_mizar_messages(&self, stdout: &str, stderr: &str) -> (Vec<MizarError>, Vec<String>) {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        for line in stdout.lines().chain(stderr.lines()) {
            if line.contains("error") || line.starts_with('*') {
                if let Some(error) = self.parse_error_line(line) {
                    errors.push(error);
                }
            } else if line.contains("warning") {
                warnings.push(line.to_string());
            }
        }

        (errors, warnings)
    }

    /// Parse a single error line
    fn parse_error_line(&self, line: &str) -> Option<MizarError> {
        if line.starts_with('*') {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() >= 4 {
                return Some(MizarError {
                    line: parts[1].parse().ok()?,
                    column: parts[2].parse().ok()?,
                    code: parts[3].to_string(),
                    message: parts[4..].join(" "),
                });
            }
        }

        let parts: Vec<&str> = line.splitn(4, ':').collect();
        if parts.len() == 4 {
            return Some(MizarError {
                line: parts[1].trim().parse().ok()?,
                column: parts[2].trim().parse().ok()?,
                code: String::new(),
                message: parts[3].trim().to_string(),
            });
        }

        None
    }

    /// Convert Mizar term to universal Term
    fn mizar_to_term(&self, mizar_term: &MizarTerm) -> Result<Term> {
        match mizar_term {
            MizarTerm::Variable(name) => Ok(Term::Var(name.clone())),
            MizarTerm::Constant(name) => Ok(Term::Const(name.clone())),
            MizarTerm::Application { func, args } => {
                let func_term = Box::new(self.mizar_to_term(func)?);
                let arg_terms: Result<Vec<Term>> =
                    args.iter().map(|a| self.mizar_to_term(a)).collect();
                Ok(Term::App {
                    func: func_term,
                    args: arg_terms?,
                })
            }
            MizarTerm::Quantifier { kind, var, var_type, body } => {
                let var_type_term = self.mizar_to_term(var_type)?;
                let body_term = self.mizar_to_term(body)?;

                match kind {
                    QuantifierKind::ForAll => Ok(Term::Pi {
                        param: var.clone(),
                        param_type: Box::new(var_type_term),
                        body: Box::new(body_term),
                    }),
                    QuantifierKind::Exists => {
                        Ok(Term::App {
                            func: Box::new(Term::Const("Exists".to_string())),
                            args: vec![Term::Lambda {
                                param: var.clone(),
                                param_type: Some(Box::new(var_type_term)),
                                body: Box::new(body_term),
                            }],
                        })
                    }
                }
            }
            MizarTerm::BinaryOp { op, left, right } => {
                let left_term = self.mizar_to_term(left)?;
                let right_term = self.mizar_to_term(right)?;
                Ok(Term::App {
                    func: Box::new(Term::Const(op.to_string())),
                    args: vec![left_term, right_term],
                })
            }
            MizarTerm::UnaryOp { op, operand } => {
                let operand_term = self.mizar_to_term(operand)?;
                Ok(Term::App {
                    func: Box::new(Term::Const(op.to_string())),
                    args: vec![operand_term],
                })
            }
        }
    }

    /// Convert universal Term to Mizar syntax
    fn term_to_mizar(&self, term: &Term) -> String {
        match term {
            Term::Var(name) => name.clone(),
            Term::Const(name) => name.clone(),
            Term::App { func, args } => {
                let func_str = self.term_to_mizar(func);
                let args_str = args
                    .iter()
                    .map(|a| self.term_to_mizar(a))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({})", func_str, args_str)
            }
            Term::Lambda { param, param_type, body } => {
                let type_str = param_type
                    .as_ref()
                    .map(|t| format!(" being {}", self.term_to_mizar(t)))
                    .unwrap_or_default();
                format!("λ {}{} . {}", param, type_str, self.term_to_mizar(body))
            }
            Term::Pi { param, param_type, body } => {
                format!(
                    "for {} being {} holds {}",
                    param,
                    self.term_to_mizar(param_type),
                    self.term_to_mizar(body)
                )
            }
            Term::Universe(level) => format!("Type{}", level),
            Term::Meta(id) => format!("?{}", id),
            Term::ProverSpecific { .. } => "<term>".to_string(),
        }
    }

    /// Export proof state to Mizar article format
    fn export_to_mizar(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();

        output.push_str(":: Generated by ECHIDNA\n");
        output.push_str(":: Mizar article\n\n");

        output.push_str("environ\n\n");
        output.push_str(" vocabularies SUBSET_1, XBOOLE_0, TARSKI;\n");
        output.push_str(" notations TARSKI, XBOOLE_0;\n");
        output.push_str(" constructors TARSKI, XBOOLE_0;\n");
        output.push_str(" registrations XBOOLE_0;\n\n");
        output.push_str("begin\n\n");

        for theorem in &state.context.theorems {
            output.push_str(&format!("theorem {}:\n", theorem.name));
            output.push_str(&format!("  {}\n", self.term_to_mizar(&theorem.statement)));
            output.push_str("proof\n");
            output.push_str("  thus thesis;\n");
            output.push_str("end;\n\n");
        }

        for (i, goal) in state.goals.iter().enumerate() {
            output.push_str(&format!(":: Goal {}\n", i + 1));
            output.push_str(&format!("theorem Goal{}:\n", i + 1));
            output.push_str(&format!("  {}\n", self.term_to_mizar(&goal.target)));
            output.push_str("proof\n");
            output.push_str("  :: Proof to be completed\n");
            output.push_str("  thus thesis;\n");
            output.push_str("end;\n\n");
        }

        Ok(output)
    }
}

#[async_trait]
impl ProverBackend for MizarBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Mizar
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get Mizar version")?;

        Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = fs::read_to_string(&path)
            .await
            .context("Failed to read Mizar file")?;

        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let article = self.parse_article(content)?;

        let mut goals = Vec::new();
        let mut context = ProofContext::default();

        for theorem in &article.theorems {
            let statement = self.mizar_to_term(&theorem.formula)?;

            if theorem.proof.is_none() || !theorem.is_proved {
                goals.push(Goal {
                    id: theorem.name.clone(),
                    target: statement.clone(),
                    hypotheses: vec![],
                });
            }

            context.theorems.push(Theorem {
                name: theorem.name.clone(),
                statement,
                proof: None,
                aspects: vec![],
            });
        }

        for def in &article.definitions {
            let def_type = self.mizar_to_term(&def.def_type)?;
            let def_body = self.mizar_to_term(&def.body)?;

            context.definitions.push(Definition {
                name: def.name.clone(),
                ty: def_type,
                body: def_body,
            });
        }

        Ok(ProofState {
            goals,
            context,
            proof_script: vec![],
            metadata: HashMap::new(),
        })
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        let mut new_state = state.clone();

        match tactic {
            Tactic::Apply(theorem_name) => {
                if new_state.goals.is_empty() {
                    return Ok(TacticResult::QED);
                }
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            }
            Tactic::Intro(name) => {
                if new_state.goals.is_empty() {
                    return Ok(TacticResult::QED);
                }

                let goal = &mut new_state.goals[0];
                let hypothesis_name = name
                    .clone()
                    .unwrap_or_else(|| format!("H{}", goal.hypotheses.len()));

                if let Term::Pi { param, param_type, body } = &goal.target {
                    goal.hypotheses.push(Hypothesis {
                        name: hypothesis_name,
                        ty: *param_type.clone(),
                        body: None,
                    });
                    goal.target = *body.clone();
                    new_state.proof_script.push(tactic.clone());
                    Ok(TacticResult::Success(new_state))
                } else {
                    Err(anyhow!("Cannot introduce: goal is not a Pi type"))
                }
            }
            Tactic::Cases(term) => {
                if new_state.goals.is_empty() {
                    return Ok(TacticResult::QED);
                }
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            }
            Tactic::Assumption => {
                if new_state.goals.is_empty() {
                    return Ok(TacticResult::QED);
                }

                let goal = &new_state.goals[0];
                let found = goal
                    .hypotheses
                    .iter()
                    .any(|h| h.ty == goal.target);

                if found {
                    new_state.goals.remove(0);
                    new_state.proof_script.push(tactic.clone());
                    if new_state.goals.is_empty() {
                        Ok(TacticResult::QED)
                    } else {
                        Ok(TacticResult::Success(new_state))
                    }
                } else {
                    Err(anyhow!("No matching hypothesis found"))
                }
            }
            Tactic::Exact(term) => {
                if new_state.goals.is_empty() {
                    return Ok(TacticResult::QED);
                }

                let goal = &new_state.goals[0];
                if term == &goal.target {
                    new_state.goals.remove(0);
                    new_state.proof_script.push(tactic.clone());
                    if new_state.goals.is_empty() {
                        Ok(TacticResult::QED)
                    } else {
                        Ok(TacticResult::Success(new_state))
                    }
                } else {
                    Err(anyhow!("Exact term does not match goal"))
                }
            }
            Tactic::Custom { prover, command, args } => {
                if prover != "mizar" {
                    return Err(anyhow!("Custom tactic not for Mizar"));
                }

                match command.as_str() {
                    "thus" | "hence" => {
                        new_state.proof_script.push(tactic.clone());
                        Ok(TacticResult::Success(new_state))
                    }
                    "per_cases" => {
                        new_state.proof_script.push(tactic.clone());
                        Ok(TacticResult::Success(new_state))
                    }
                    _ => Err(anyhow!("Unknown Mizar tactic: {}", command)),
                }
            }
            _ => {
                new_state.proof_script.push(tactic.clone());
                Ok(TacticResult::Success(new_state))
            }
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if !state.is_complete() {
            return Ok(false);
        }

        let mizar_content = self.export_to_mizar(state)?;

        let temp_dir = std::env::temp_dir();
        let temp_file = temp_dir.join(format!("echidna_{}.miz", uuid::Uuid::new_v4()));

        let mut file = fs::File::create(&temp_file).await?;
        file.write_all(mizar_content.as_bytes()).await?;
        file.sync_all().await?;
        drop(file);

        let result = self.verify_file(&temp_file).await?;

        let _ = fs::remove_file(&temp_file).await;

        Ok(result.success)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.export_to_mizar(state)
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        if state.goals.is_empty() {
            return Ok(vec![]);
        }

        let goal = &state.goals[0];
        let mut suggestions = Vec::new();

        match &goal.target {
            Term::Pi { .. } => {
                suggestions.push(Tactic::Intro(None));
            }
            Term::App { func, .. } => {
                for theorem in &state.context.theorems {
                    suggestions.push(Tactic::Apply(theorem.name.clone()));
                    if suggestions.len() >= limit {
                        break;
                    }
                }
            }
            _ => {
                suggestions.push(Tactic::Assumption);
            }
        }

        suggestions.truncate(limit);
        Ok(suggestions)
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        let mml_dict = self.mml_path.join("mml.lar");
        if !mml_dict.exists() {
            return Ok(vec![]);
        }

        let content = fs::read_to_string(&mml_dict).await?;
        let mut results = Vec::new();

        for line in content.lines() {
            if line.to_lowercase().contains(&pattern.to_lowercase()) {
                results.push(line.to_string());
                if results.len() >= 100 {
                    break;
                }
            }
        }

        Ok(results)
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

// ============================================================================
// Parser Implementation
// ============================================================================

#[derive(Debug, Clone)]
struct MizarArticle {
    environ: MizarEnviron,
    theorems: Vec<MizarTheorem>,
    definitions: Vec<MizarDefinition>,
    schemes: Vec<MizarScheme>,
}

#[derive(Debug, Clone, Default)]
struct MizarEnviron {
    vocabularies: Vec<String>,
    notations: Vec<String>,
    constructors: Vec<String>,
    registrations: Vec<String>,
    theorems: Vec<String>,
    requirements: Vec<String>,
}

#[derive(Debug, Clone)]
struct MizarTheorem {
    name: String,
    formula: MizarTerm,
    proof: Option<MizarProof>,
    is_proved: bool,
}

#[derive(Debug, Clone)]
struct MizarDefinition {
    name: String,
    def_type: MizarTerm,
    body: MizarTerm,
}

#[derive(Debug, Clone)]
struct MizarScheme {
    name: String,
    parameters: Vec<String>,
    formula: MizarTerm,
}

#[derive(Debug, Clone)]
struct MizarProof {
    steps: Vec<MizarProofStep>,
}

#[derive(Debug, Clone)]
enum MizarProofStep {
    Let { vars: Vec<String>, var_type: String },
    Assume { label: Option<String>, formula: MizarTerm },
    Thus { formula: MizarTerm, justification: Option<String> },
    Hence { formula: MizarTerm, justification: Option<String> },
    PerCases { cases: Vec<MizarProof> },
    Take { term: MizarTerm },
    Consider { vars: Vec<String>, formula: MizarTerm, justification: Option<String> },
}

#[derive(Debug, Clone, PartialEq)]
enum MizarTerm {
    Variable(String),
    Constant(String),
    Application {
        func: Box<MizarTerm>,
        args: Vec<MizarTerm>,
    },
    Quantifier {
        kind: QuantifierKind,
        var: String,
        var_type: Box<MizarTerm>,
        body: Box<MizarTerm>,
    },
    BinaryOp {
        op: String,
        left: Box<MizarTerm>,
        right: Box<MizarTerm>,
    },
    UnaryOp {
        op: String,
        operand: Box<MizarTerm>,
    },
}

#[derive(Debug, Clone, PartialEq)]
enum QuantifierKind {
    ForAll,
    Exists,
}

struct MizarParser {
    input: String,
    pos: usize,
}

impl MizarParser {
    fn new(input: &str) -> Self {
        MizarParser {
            input: input.to_string(),
            pos: 0,
        }
    }

    fn parse(&mut self) -> Result<MizarArticle> {
        self.skip_whitespace_and_comments();

        let environ = self.parse_environ()?;

        self.expect_keyword("begin")?;

        let mut theorems = Vec::new();
        let mut definitions = Vec::new();
        let mut schemes = Vec::new();

        while self.pos < self.input.len() {
            self.skip_whitespace_and_comments();
            if self.pos >= self.input.len() {
                break;
            }

            let keyword = self.peek_keyword();
            match keyword.as_deref() {
                Some("theorem") => {
                    theorems.push(self.parse_theorem()?);
                }
                Some("definition") => {
                    definitions.push(self.parse_definition()?);
                }
                Some("scheme") => {
                    schemes.push(self.parse_scheme()?);
                }
                _ => break,
            }
        }

        Ok(MizarArticle {
            environ,
            theorems,
            definitions,
            schemes,
        })
    }

    fn parse_environ(&mut self) -> Result<MizarEnviron> {
        self.expect_keyword("environ")?;

        let mut environ = MizarEnviron::default();

        while !self.check_keyword("begin") {
            self.skip_whitespace_and_comments();

            let keyword = self.peek_keyword();
            match keyword.as_deref() {
                Some("vocabularies") => {
                    self.consume_keyword("vocabularies");
                    environ.vocabularies = self.parse_identifier_list()?;
                }
                Some("notations") => {
                    self.consume_keyword("notations");
                    environ.notations = self.parse_identifier_list()?;
                }
                Some("constructors") => {
                    self.consume_keyword("constructors");
                    environ.constructors = self.parse_identifier_list()?;
                }
                Some("registrations") => {
                    self.consume_keyword("registrations");
                    environ.registrations = self.parse_identifier_list()?;
                }
                Some("theorems") => {
                    self.consume_keyword("theorems");
                    environ.theorems = self.parse_identifier_list()?;
                }
                Some("requirements") => {
                    self.consume_keyword("requirements");
                    environ.requirements = self.parse_identifier_list()?;
                }
                _ => break,
            }
        }

        Ok(environ)
    }

    fn parse_identifier_list(&mut self) -> Result<Vec<String>> {
        let mut identifiers = Vec::new();

        loop {
            self.skip_whitespace_and_comments();

            if let Some(id) = self.parse_identifier() {
                identifiers.push(id);
                self.skip_whitespace_and_comments();
                if self.check_char(',') {
                    self.consume_char(',');
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        self.expect_char(';')?;
        Ok(identifiers)
    }

    fn parse_theorem(&mut self) -> Result<MizarTheorem> {
        self.expect_keyword("theorem")?;

        let name = self.parse_identifier()
            .unwrap_or_else(|| format!("Theorem{}", self.pos));

        self.expect_char(':')?;

        let formula = self.parse_formula()?;

        let (proof, is_proved) = if self.check_keyword("proof") {
            (Some(self.parse_proof()?), true)
        } else {
            self.expect_char(';')?;
            (None, false)
        };

        Ok(MizarTheorem {
            name,
            formula,
            proof,
            is_proved,
        })
    }

    fn parse_definition(&mut self) -> Result<MizarDefinition> {
        self.expect_keyword("definition")?;

        let name = self.parse_identifier()
            .ok_or_else(|| anyhow!("Expected definition name"))?;

        let def_type = MizarTerm::Constant("Type".to_string());
        let body = MizarTerm::Constant("body".to_string());

        while !self.check_keyword("end") {
            self.pos += 1;
            if self.pos >= self.input.len() {
                break;
            }
        }
        if self.check_keyword("end") {
            self.expect_keyword("end")?;
            self.expect_char(';')?;
        }

        Ok(MizarDefinition {
            name,
            def_type,
            body,
        })
    }

    fn parse_scheme(&mut self) -> Result<MizarScheme> {
        self.expect_keyword("scheme")?;

        let name = self.parse_identifier()
            .ok_or_else(|| anyhow!("Expected scheme name"))?;

        let parameters = vec![];
        let formula = MizarTerm::Constant("scheme".to_string());

        while !self.check_keyword("end") {
            self.pos += 1;
            if self.pos >= self.input.len() {
                break;
            }
        }
        if self.check_keyword("end") {
            self.expect_keyword("end")?;
            self.expect_char(';')?;
        }

        Ok(MizarScheme {
            name,
            parameters,
            formula,
        })
    }

    fn parse_proof(&mut self) -> Result<MizarProof> {
        self.expect_keyword("proof")?;

        let mut steps = Vec::new();

        while !self.check_keyword("end") {
            self.skip_whitespace_and_comments();

            if self.pos >= self.input.len() || self.check_keyword("end") {
                break;
            }

            let keyword = self.peek_keyword();
            match keyword.as_deref() {
                Some("let") => {
                    steps.push(self.parse_let_step()?);
                }
                Some("assume") => {
                    steps.push(self.parse_assume_step()?);
                }
                Some("thus") => {
                    steps.push(self.parse_thus_step()?);
                }
                Some("hence") => {
                    steps.push(self.parse_hence_step()?);
                }
                Some("per") => {
                    steps.push(self.parse_per_cases()?);
                }
                Some("take") => {
                    steps.push(self.parse_take_step()?);
                }
                _ => {
                    self.pos += 1;
                }
            }
        }

        self.expect_keyword("end")?;
        self.expect_char(';')?;

        Ok(MizarProof { steps })
    }

    fn parse_let_step(&mut self) -> Result<MizarProofStep> {
        self.expect_keyword("let")?;

        let mut vars = Vec::new();
        vars.push(self.parse_identifier()
            .ok_or_else(|| anyhow!("Expected variable name"))?);

        while self.check_char(',') {
            self.consume_char(',');
            if let Some(var) = self.parse_identifier() {
                vars.push(var);
            }
        }

        self.expect_keyword("be")?;
        let var_type = self.parse_identifier()
            .ok_or_else(|| anyhow!("Expected type name"))?;

        self.expect_char(';')?;

        Ok(MizarProofStep::Let { vars, var_type })
    }

    fn parse_assume_step(&mut self) -> Result<MizarProofStep> {
        self.expect_keyword("assume")?;

        let label = if self.peek().is_some_and(|c| c.is_ascii_uppercase()) {
            let lbl = self.parse_identifier();
            if self.check_char(':') {
                self.consume_char(':');
                lbl
            } else {
                None
            }
        } else {
            None
        };

        let formula = self.parse_formula()?;
        self.expect_char(';')?;

        Ok(MizarProofStep::Assume { label, formula })
    }

    fn parse_thus_step(&mut self) -> Result<MizarProofStep> {
        self.expect_keyword("thus")?;

        let formula = self.parse_formula()?;

        let justification = if self.check_keyword("by") {
            self.consume_keyword("by");
            Some(self.parse_justification()?)
        } else {
            None
        };

        self.expect_char(';')?;

        Ok(MizarProofStep::Thus { formula, justification })
    }

    fn parse_hence_step(&mut self) -> Result<MizarProofStep> {
        self.expect_keyword("hence")?;

        let formula = self.parse_formula()?;

        let justification = if self.check_keyword("by") {
            self.consume_keyword("by");
            Some(self.parse_justification()?)
        } else {
            None
        };

        self.expect_char(';')?;

        Ok(MizarProofStep::Hence { formula, justification })
    }

    fn parse_per_cases(&mut self) -> Result<MizarProofStep> {
        self.expect_keyword("per")?;
        self.expect_keyword("cases")?;

        let mut cases = Vec::new();

        while self.check_keyword("suppose") {
            self.expect_keyword("suppose")?;
            
            while !self.check_keyword("end") && self.pos < self.input.len() {
                self.pos += 1;
            }
            
            cases.push(MizarProof { steps: vec![] });
        }

        Ok(MizarProofStep::PerCases { cases })
    }

    fn parse_take_step(&mut self) -> Result<MizarProofStep> {
        self.expect_keyword("take")?;

        let term = self.parse_term()?;
        self.expect_char(';')?;

        Ok(MizarProofStep::Take { term })
    }

    fn parse_formula(&mut self) -> Result<MizarTerm> {
        self.skip_whitespace_and_comments();

        if self.check_keyword("for") {
            return self.parse_for_formula();
        }

        self.parse_term()
    }

    fn parse_for_formula(&mut self) -> Result<MizarTerm> {
        self.expect_keyword("for")?;

        let var = self.parse_identifier()
            .ok_or_else(|| anyhow!("Expected variable"))?;

        let mut var_type = MizarTerm::Constant("set".to_string());

        if self.check_keyword("being") {
            self.consume_keyword("being");
            let type_name = self.parse_identifier()
                .ok_or_else(|| anyhow!("Expected type name"))?;
            var_type = MizarTerm::Constant(type_name);
        }

        self.expect_keyword("holds")?;

        let body = self.parse_formula()?;

        Ok(MizarTerm::Quantifier {
            kind: QuantifierKind::ForAll,
            var,
            var_type: Box::new(var_type),
            body: Box::new(body),
        })
    }

    fn parse_term(&mut self) -> Result<MizarTerm> {
        self.skip_whitespace_and_comments();

        if let Some(id) = self.parse_identifier() {
            self.skip_whitespace_and_comments();

            if let Some(op) = self.parse_binary_op() {
                let right = self.parse_term()?;
                return Ok(MizarTerm::BinaryOp {
                    op,
                    left: Box::new(MizarTerm::Variable(id)),
                    right: Box::new(right),
                });
            }

            if self.check_char('(') {
                self.consume_char('(');
                let mut args = vec![];

                if !self.check_char(')') {
                    loop {
                        args.push(self.parse_term()?);
                        self.skip_whitespace_and_comments();
                        if self.check_char(',') {
                            self.consume_char(',');
                        } else {
                            break;
                        }
                    }
                }

                self.expect_char(')')?;

                return Ok(MizarTerm::Application {
                    func: Box::new(MizarTerm::Variable(id)),
                    args,
                });
            }

            if id.chars().next().unwrap().is_uppercase() {
                Ok(MizarTerm::Constant(id))
            } else {
                Ok(MizarTerm::Variable(id))
            }
        } else {
            Err(anyhow!("Expected term"))
        }
    }

    fn parse_binary_op(&mut self) -> Option<String> {
        self.skip_whitespace_and_comments();

        let ops = [
            ("=", "="),
            ("<>", "≠"),
            ("c=", "⊆"),
            ("\\/", "∪"),
            ("/\\", "∩"),
            ("\\", "\\"),
            ("&", "&"),
            ("or", "or"),
            ("implies", "⇒"),
            ("iff", "⇔"),
            ("+", "+"),
            ("-", "-"),
            ("*", "*"),
            ("/", "/"),
            ("<=", "≤"),
            (">=", "≥"),
            ("<", "<"),
            (">", ">"),
        ];

        for (pattern, op) in ops {
            if self.input[self.pos..].starts_with(pattern) {
                self.pos += pattern.len();
                return Some(op.to_string());
            }
        }

        None
    }

    fn parse_justification(&mut self) -> Result<String> {
        let mut justification = String::new();

        loop {
            self.skip_whitespace_and_comments();

            if self.check_char(';') {
                break;
            }

            if let Some(id) = self.parse_identifier() {
                justification.push_str(&id);
                justification.push(' ');
            } else if self.check_char(':') {
                self.consume_char(':');
                justification.push(':');
            } else if self.check_char(',') {
                self.consume_char(',');
                justification.push(',');
                justification.push(' ');
            } else {
                break;
            }
        }

        Ok(justification.trim().to_string())
    }

    fn parse_identifier(&mut self) -> Option<String> {
        self.skip_whitespace_and_comments();

        let start = self.pos;
        while self.pos < self.input.len() {
            let ch = self.input.as_bytes()[self.pos] as char;
            if ch.is_alphanumeric() || ch == '_' {
                self.pos += 1;
            } else {
                break;
            }
        }

        if self.pos > start {
            Some(self.input[start..self.pos].to_string())
        } else {
            None
        }
    }

    fn peek_keyword(&self) -> Option<String> {
        let mut temp_pos = self.pos;

        while temp_pos < self.input.len() && self.input.as_bytes()[temp_pos].is_ascii_whitespace() {
            temp_pos += 1;
        }

        let start = temp_pos;
        while temp_pos < self.input.len() {
            let ch = self.input.as_bytes()[temp_pos] as char;
            if ch.is_alphanumeric() || ch == '_' {
                temp_pos += 1;
            } else {
                break;
            }
        }

        if temp_pos > start {
            Some(self.input[start..temp_pos].to_string())
        } else {
            None
        }
    }

    fn check_keyword(&self, keyword: &str) -> bool {
        self.peek_keyword().as_deref() == Some(keyword)
    }

    fn consume_keyword(&mut self, keyword: &str) {
        self.skip_whitespace_and_comments();
        if self.input[self.pos..].starts_with(keyword) {
            self.pos += keyword.len();
        }
    }

    fn expect_keyword(&mut self, keyword: &str) -> Result<()> {
        self.skip_whitespace_and_comments();
        if self.pos + keyword.len() > self.input.len() || !self.input[self.pos..].starts_with(keyword) {
            return Err(anyhow!("Expected keyword '{}' at position {}", keyword, self.pos));
        }
        self.pos += keyword.len();
        Ok(())
    }

    fn peek(&self) -> Option<char> {
        if self.pos < self.input.len() {
            Some(self.input.as_bytes()[self.pos] as char)
        } else {
            None
        }
    }

    fn check_char(&self, ch: char) -> bool {
        self.peek() == Some(ch)
    }

    fn consume_char(&mut self, ch: char) {
        if self.peek() == Some(ch) {
            self.pos += 1;
        }
    }

    fn expect_char(&mut self, ch: char) -> Result<()> {
        self.skip_whitespace_and_comments();
        if self.peek() != Some(ch) {
            return Err(anyhow!("Expected '{}' at position {}, found {:?}", ch, self.pos, self.peek()));
        }
        self.pos += 1;
        Ok(())
    }

    fn skip_whitespace_and_comments(&mut self) {
        while self.pos < self.input.len() {
            let ch = self.input.as_bytes()[self.pos] as char;

            if ch.is_whitespace() {
                self.pos += 1;
            } else if self.input[self.pos..].starts_with("::") {
                while self.pos < self.input.len() && self.input.as_bytes()[self.pos] as char != '\n' {
                    self.pos += 1;
                }
            } else {
                break;
            }
        }
    }
}

#[derive(Debug, Clone)]
struct MizarVerificationResult {
    success: bool,
    errors: Vec<MizarError>,
    warnings: Vec<String>,
}

#[derive(Debug, Clone)]
struct MizarPhaseOutput {
    success: bool,
    errors: Vec<MizarError>,
    warnings: Vec<String>,
}

#[derive(Debug, Clone)]
struct MizarError {
    line: usize,
    column: usize,
    code: String,
    message: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mizar_parser_basic() {
        let content = r#"
environ
 vocabularies SUBSET_1, XBOOLE_0;
 notations XBOOLE_0;
begin

theorem Th1:
  for P being set holds P = P
proof
  let P be set;
  thus P = P;
end;
"#;

        let mut parser = MizarParser::new(content);
        let article = parser.parse().unwrap();

        assert_eq!(article.theorems.len(), 1);
        assert_eq!(article.theorems[0].name, "Th1");
    }

    #[test]
    fn test_mizar_backend_creation() {
        let config = ProverConfig::default();
        let backend = MizarBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Mizar);
    }
}
