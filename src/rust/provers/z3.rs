// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Z3 SMT Solver Backend
//!
//! Implements Z3 theorem prover integration with SMT-LIB 2.0 support.
//! Z3 is a Tier 1 SMT solver supporting multiple theories:
//! - QF_UF: Uninterpreted functions
//! - QF_LIA/QF_NIA: Linear/nonlinear integer arithmetic
//! - QF_BV: Bitvectors
//! - Arrays, datatypes, quantifiers, etc.

use async_trait::async_trait;
use anyhow::{anyhow, bail, Context as AnyhowContext, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::AsyncWriteExt;
use tokio::process::{Child, Command};
use tokio::time::{timeout, Duration};

use crate::core::{Goal, ProofState, Tactic, TacticResult, Term, Context as ProofContext};
use super::{ProverBackend, ProverConfig, ProverKind};

/// Z3 SMT solver backend
pub struct Z3Backend {
    config: ProverConfig,
}

impl Z3Backend {
    /// Create a new Z3 backend with configuration
    pub fn new(config: ProverConfig) -> Self {
        Z3Backend { config }
    }

    /// Launch Z3 process in interactive mode
    async fn spawn_z3(&self) -> Result<Child> {
        let mut cmd = Command::new(&self.config.executable);
        cmd.arg("-in")  // Read from stdin
            .arg("-smt2")  // SMT-LIB 2.0 format
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        // Add custom arguments
        for arg in &self.config.args {
            cmd.arg(arg);
        }

        cmd.spawn()
            .with_context(|| format!("Failed to spawn Z3 process: {:?}", self.config.executable))
    }

    /// Execute a single SMT-LIB command and get response
    async fn execute_command(&self, command: &str) -> Result<SmtResult> {
        let mut child = self.spawn_z3().await?;

        let mut stdin = child.stdin.take()
            .ok_or_else(|| anyhow!("Failed to open Z3 stdin"))?;
        let stdout = child.stdout.take()
            .ok_or_else(|| anyhow!("Failed to open Z3 stdout"))?;

        // Write command
        stdin.write_all(command.as_bytes()).await?;
        stdin.write_all(b"\n(exit)\n").await?;
        stdin.flush().await?;
        drop(stdin);

        // Read response with timeout
        let timeout_duration = Duration::from_secs(self.config.timeout);
        let output = timeout(timeout_duration, child.wait_with_output()).await
            .map_err(|_| anyhow!("Z3 execution timeout after {} seconds", self.config.timeout))??;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            bail!("Z3 failed: {}", stderr);
        }

        let stdout_str = String::from_utf8_lossy(&output.stdout).to_string();
        self.parse_smt_result(&stdout_str)
    }

    /// Parse SMT-LIB result from Z3 output
    fn parse_smt_result(&self, output: &str) -> Result<SmtResult> {
        let trimmed = output.trim();

        if trimmed.contains("sat") && !trimmed.contains("unsat") {
            Ok(SmtResult::Sat)
        } else if trimmed.contains("unsat") {
            Ok(SmtResult::Unsat)
        } else if trimmed.contains("unknown") {
            Ok(SmtResult::Unknown)
        } else if trimmed.starts_with("(error") {
            let error_msg = trimmed.trim_start_matches("(error").trim_end_matches(')').trim();
            Ok(SmtResult::Error(error_msg.trim_matches('"').to_string()))
        } else {
            // For other commands (get-model, etc.), return raw output
            Ok(SmtResult::Output(trimmed.to_string()))
        }
    }

    /// Parse SMT-LIB 2.0 file into ProofState
    fn parse_smt_file(&self, content: &str) -> Result<ProofState> {
        let mut parser = SmtParser::new(content);
        parser.parse()
    }

    /// Convert SMT term to universal Term
    fn smt_to_term(&self, smt_term: &SmtTerm) -> Term {
        match smt_term {
            SmtTerm::Symbol(s) => Term::Var(s.clone()),
            SmtTerm::Numeral(n) => Term::Const(n.to_string()),
            SmtTerm::Bool(b) => Term::Const(b.to_string()),
            SmtTerm::App { func, args } => {
                Term::App {
                    func: Box::new(Term::Const(func.clone())),
                    args: args.iter().map(|a| self.smt_to_term(a)).collect(),
                }
            }
            SmtTerm::Quantified { quantifier, bindings, body } => {
                let term_body = self.smt_to_term(body);
                bindings.iter().rev().fold(term_body, |acc, (var, ty)| {
                    Term::App {
                        func: Box::new(Term::Const(quantifier.clone())),
                        args: vec![
                            Term::Lambda {
                                param: var.clone(),
                                param_type: Some(Box::new(self.smt_to_term(ty))),
                                body: Box::new(acc),
                            }
                        ],
                    }
                })
            }
            SmtTerm::Let { bindings, body } => {
                let term_body = self.smt_to_term(body);
                bindings.iter().rev().fold(term_body, |acc, (var, val)| {
                    Term::App {
                        func: Box::new(Term::Lambda {
                            param: var.clone(),
                            param_type: None,
                            body: Box::new(acc),
                        }),
                        args: vec![self.smt_to_term(val)],
                    }
                })
            }
        }
    }

    /// Convert universal Term to SMT-LIB format
    fn term_to_smt(&self, term: &Term) -> String {
        match term {
            Term::Var(name) => name.clone(),
            Term::Const(name) => name.clone(),
            Term::App { func, args } => {
                if args.is_empty() {
                    self.term_to_smt(func)
                } else {
                    let func_str = self.term_to_smt(func);
                    let args_str: Vec<String> = args.iter()
                        .map(|a| self.term_to_smt(a))
                        .collect();
                    format!("({} {})", func_str, args_str.join(" "))
                }
            }
            _ => {
                format!("(:echidna {})", serde_json::to_string(term).unwrap_or_default())
            }
        }
    }

    /// Check if assertion is satisfiable
    async fn check_sat(&self, assertions: &[String]) -> Result<SmtResult> {
        let mut commands = String::new();

        for assertion in assertions {
            commands.push_str(&format!("(assert {})\n", assertion));
        }
        commands.push_str("(check-sat)\n");

        self.execute_command(&commands).await
    }
}

#[async_trait]
impl ProverBackend for Z3Backend {
    fn kind(&self) -> ProverKind {
        ProverKind::Z3
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get Z3 version")?;

        let version = String::from_utf8_lossy(&output.stdout).to_string();
        Ok(version.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path).await
            .with_context(|| format!("Failed to read file: {:?}", path))?;

        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        self.parse_smt_file(content)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            Tactic::Simplify => {
                if state.goals.is_empty() {
                    return Ok(TacticResult::QED);
                }

                let goal = &state.goals[0];
                let smt_goal = self.term_to_smt(&goal.target);

                let command = format!("(simplify {})", smt_goal);
                let result = self.execute_command(&command).await?;

                match result {
                    SmtResult::Output(simplified) => {
                        let mut parser = SmtParser::new(&simplified);
                        let simplified_term = parser.parse_term()?;

                        let mut new_state = state.clone();
                        if !new_state.goals.is_empty() {
                            new_state.goals[0].target = self.smt_to_term(&simplified_term);
                        }
                        new_state.proof_script.push(tactic.clone());

                        Ok(TacticResult::Success(new_state))
                    }
                    _ => Ok(TacticResult::Error("Simplification failed".to_string())),
                }
            }

            Tactic::Custom { prover, command, args } if prover == "z3" => {
                let smt_command = if args.is_empty() {
                    command.clone()
                } else {
                    format!("({} {})", command, args.join(" "))
                };

                let result = self.execute_command(&smt_command).await?;

                match result {
                    SmtResult::Output(output) => {
                        let mut new_state = state.clone();
                        new_state.proof_script.push(tactic.clone());
                        new_state.metadata.insert(
                            "last_result".to_string(),
                            serde_json::Value::String(output)
                        );
                        Ok(TacticResult::Success(new_state))
                    }
                    SmtResult::Error(e) => Ok(TacticResult::Error(e)),
                    _ => Ok(TacticResult::Error("Unexpected result".to_string())),
                }
            }

            _ => {
                Ok(TacticResult::Error(format!("Tactic {:?} not supported for Z3", tactic)))
            }
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        if state.goals.is_empty() {
            return Ok(true);
        }

        let mut assertions = Vec::new();

        for goal in &state.goals {
            let smt_goal = self.term_to_smt(&goal.target);
            assertions.push(format!("(not {})", smt_goal));
        }

        let result = self.check_sat(&assertions).await?;

        match result {
            SmtResult::Unsat => Ok(true),
            SmtResult::Sat => Ok(false),
            SmtResult::Unknown => Ok(false),
            SmtResult::Error(e) => bail!("Verification error: {}", e),
            SmtResult::Output(_) => Ok(false),
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();

        output.push_str("; ECHIDNA Z3 Export\n");
        output.push_str("; Generated SMT-LIB 2.0 file\n\n");
        output.push_str("(set-logic ALL)\n\n");

        for var in &state.context.variables {
            let ty_smt = self.term_to_smt(&var.ty);
            output.push_str(&format!("(declare-const {} {})\n", var.name, ty_smt));
        }

        output.push_str("\n");

        for theorem in &state.context.theorems {
            let stmt_smt = self.term_to_smt(&theorem.statement);
            output.push_str(&format!("; Theorem: {}\n", theorem.name));
            output.push_str(&format!("(assert {})\n\n", stmt_smt));
        }

        for goal in &state.goals {
            output.push_str(&format!("; Goal: {}\n", goal.id));
            let goal_smt = self.term_to_smt(&goal.target);
            output.push_str(&format!("(assert {})\n\n", goal_smt));
        }

        output.push_str("(check-sat)\n");
        output.push_str("(get-model)\n");

        Ok(output)
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        if !self.config.neural_enabled {
            return Ok(vec![]);
        }

        let mut tactics = vec![
            Tactic::Simplify,
            Tactic::Custom {
                prover: "z3".to_string(),
                command: "apply".to_string(),
                args: vec!["(then simplify solve-eqs)".to_string()],
            },
            Tactic::Custom {
                prover: "z3".to_string(),
                command: "apply".to_string(),
                args: vec!["(then ctx-simplify propagate-values)".to_string()],
            },
        ];

        if state.goals.iter().any(|g| {
            let term_str = format!("{:?}", g.target);
            term_str.contains('+') || term_str.contains('-') || term_str.contains('*')
        }) {
            tactics.push(Tactic::Custom {
                prover: "z3".to_string(),
                command: "apply".to_string(),
                args: vec!["(then simplify normalize-bounds lia2pb pb2bv bit-blast)".to_string()],
            });
        }

        tactics.truncate(limit);
        Ok(tactics)
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        Ok(vec![])
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

/// SMT-LIB result from Z3
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SmtResult {
    Sat,
    Unsat,
    Unknown,
    Error(String),
    Output(String),
}

/// SMT-LIB term representation
#[derive(Debug, Clone, PartialEq)]
pub enum SmtTerm {
    Symbol(String),
    Numeral(i64),
    Bool(bool),
    App {
        func: String,
        args: Vec<SmtTerm>,
    },
    Quantified {
        quantifier: String,
        bindings: Vec<(String, SmtTerm)>,
        body: Box<SmtTerm>,
    },
    Let {
        bindings: Vec<(String, SmtTerm)>,
        body: Box<SmtTerm>,
    },
}

/// SMT-LIB 2.0 parser
pub struct SmtParser {
    tokens: Vec<String>,
    pos: usize,
}

impl SmtParser {
    pub fn new(input: &str) -> Self {
        let tokens = Self::tokenize(input);
        SmtParser { tokens, pos: 0 }
    }

    fn tokenize(input: &str) -> Vec<String> {
        let mut tokens = Vec::new();
        let mut current = String::new();
        let mut in_string = false;
        let mut in_comment = false;

        for ch in input.chars() {
            if in_comment {
                if ch == '\n' {
                    in_comment = false;
                }
                continue;
            }

            match ch {
                ';' if !in_string => {
                    in_comment = true;
                    if !current.is_empty() {
                        tokens.push(current.clone());
                        current.clear();
                    }
                }
                '"' => {
                    in_string = !in_string;
                    current.push(ch);
                }
                '(' | ')' if !in_string => {
                    if !current.is_empty() {
                        tokens.push(current.clone());
                        current.clear();
                    }
                    tokens.push(ch.to_string());
                }
                ' ' | '\n' | '\t' if !in_string => {
                    if !current.is_empty() {
                        tokens.push(current.clone());
                        current.clear();
                    }
                }
                _ => {
                    current.push(ch);
                }
            }
        }

        if !current.is_empty() {
            tokens.push(current);
        }

        tokens
    }

    fn peek(&self) -> Option<&str> {
        self.tokens.get(self.pos).map(|s| s.as_str())
    }

    fn next(&mut self) -> Option<String> {
        if self.pos < self.tokens.len() {
            let token = self.tokens[self.pos].clone();
            self.pos += 1;
            Some(token)
        } else {
            None
        }
    }

    fn expect(&mut self, expected: &str) -> Result<()> {
        match self.next() {
            Some(token) if token == expected => Ok(()),
            Some(token) => bail!("Expected '{}', got '{}'", expected, token),
            None => bail!("Expected '{}', got EOF", expected),
        }
    }

    pub fn parse(&mut self) -> Result<ProofState> {
        let mut state = ProofState {
            goals: vec![],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: HashMap::new(),
        };

        let mut assertions = Vec::new();

        while self.peek().is_some() {
            self.expect("(")?;

            match self.peek() {
                Some("declare-const") => {
                    self.next();
                    let name = self.next().ok_or_else(|| anyhow!("Expected variable name"))?;
                    let ty_term = self.parse_term()?;
                    self.expect(")")?;

                    state.context.variables.push(crate::core::Variable {
                        name: name.clone(),
                        ty: self.smt_to_term(&ty_term),
                    });
                }

                Some("declare-fun") => {
                    self.next();
                    let name = self.next().ok_or_else(|| anyhow!("Expected function name"))?;
                    self.expect("(")?;

                    let mut param_types = Vec::new();
                    while self.peek() != Some(")") {
                        param_types.push(self.parse_term()?);
                    }
                    self.expect(")")?;

                    let return_type = self.parse_term()?;
                    self.expect(")")?;

                    let mut ty = self.smt_to_term(&return_type);
                    for param_ty in param_types.iter().rev() {
                        ty = Term::App {
                            func: Box::new(Term::Const("->".to_string())),
                            args: vec![self.smt_to_term(param_ty), ty],
                        };
                    }

                    state.context.variables.push(crate::core::Variable {
                        name: name.clone(),
                        ty,
                    });
                }

                Some("assert") => {
                    self.next();
                    let assertion = self.parse_term()?;
                    self.expect(")")?;

                    assertions.push(assertion);
                }

                Some("check-sat") => {
                    self.next();
                    self.expect(")")?;

                    for (idx, assertion) in assertions.iter().enumerate() {
                        state.goals.push(Goal {
                            id: format!("goal_{}", idx),
                            target: self.smt_to_term(assertion),
                            hypotheses: vec![],
                        });
                    }
                }

                Some("set-logic") | Some("set-option") | Some("set-info") => {
                    self.next();
                    let mut depth = 1;
                    while depth > 0 {
                        match self.next() {
                            Some(token) if token == "(" => depth += 1,
                            Some(token) if token == ")" => depth -= 1,
                            None => bail!("Unexpected EOF in command"),
                            _ => {}
                        }
                    }
                }

                _ => {
                    let mut depth = 1;
                    while depth > 0 {
                        match self.next() {
                            Some(token) if token == "(" => depth += 1,
                            Some(token) if token == ")" => depth -= 1,
                            None => bail!("Unexpected EOF"),
                            _ => {}
                        }
                    }
                }
            }
        }

        Ok(state)
    }

    pub fn parse_term(&mut self) -> Result<SmtTerm> {
        match self.peek() {
            Some("(") => {
                self.next();

                match self.peek() {
                    Some("forall") | Some("exists") => {
                        let quantifier = self.next().unwrap();
                        self.expect("(")?;

                        let mut bindings = Vec::new();
                        while self.peek() != Some(")") {
                            self.expect("(")?;
                            let var = self.next().ok_or_else(|| anyhow!("Expected variable"))?;
                            let ty = self.parse_term()?;
                            self.expect(")")?;
                            bindings.push((var, ty));
                        }
                        self.expect(")")?;

                        let body = Box::new(self.parse_term()?);
                        self.expect(")")?;

                        Ok(SmtTerm::Quantified { quantifier, bindings, body })
                    }

                    Some("let") => {
                        self.next();
                        self.expect("(")?;

                        let mut bindings = Vec::new();
                        while self.peek() != Some(")") {
                            self.expect("(")?;
                            let var = self.next().ok_or_else(|| anyhow!("Expected variable"))?;
                            let val = self.parse_term()?;
                            self.expect(")")?;
                            bindings.push((var, val));
                        }
                        self.expect(")")?;

                        let body = Box::new(self.parse_term()?);
                        self.expect(")")?;

                        Ok(SmtTerm::Let { bindings, body })
                    }

                    Some(_) => {
                        let func = self.next().unwrap();
                        let mut args = Vec::new();

                        while self.peek() != Some(")") {
                            args.push(self.parse_term()?);
                        }
                        self.expect(")")?;

                        Ok(SmtTerm::App { func, args })
                    }

                    None => bail!("Unexpected EOF"),
                }
            }

            Some("true") => {
                self.next();
                Ok(SmtTerm::Bool(true))
            }

            Some("false") => {
                self.next();
                Ok(SmtTerm::Bool(false))
            }

            Some(_) => {
                let token = self.next().unwrap();

                if let Ok(n) = token.parse::<i64>() {
                    Ok(SmtTerm::Numeral(n))
                } else {
                    Ok(SmtTerm::Symbol(token))
                }
            }

            None => bail!("Unexpected EOF"),
        }
    }

    fn smt_to_term(&self, smt_term: &SmtTerm) -> Term {
        match smt_term {
            SmtTerm::Symbol(s) => Term::Var(s.clone()),
            SmtTerm::Numeral(n) => Term::Const(n.to_string()),
            SmtTerm::Bool(b) => Term::Const(b.to_string()),
            SmtTerm::App { func, args } => {
                Term::App {
                    func: Box::new(Term::Const(func.clone())),
                    args: args.iter().map(|a| self.smt_to_term(a)).collect(),
                }
            }
            SmtTerm::Quantified { quantifier, bindings, body } => {
                let term_body = self.smt_to_term(body);
                bindings.iter().rev().fold(term_body, |acc, (var, ty)| {
                    Term::App {
                        func: Box::new(Term::Const(quantifier.clone())),
                        args: vec![
                            Term::Lambda {
                                param: var.clone(),
                                param_type: Some(Box::new(self.smt_to_term(ty))),
                                body: Box::new(acc),
                            }
                        ],
                    }
                })
            }
            SmtTerm::Let { bindings, body } => {
                let term_body = self.smt_to_term(body);
                bindings.iter().rev().fold(term_body, |acc, (var, val)| {
                    Term::App {
                        func: Box::new(Term::Lambda {
                            param: var.clone(),
                            param_type: None,
                            body: Box::new(acc),
                        }),
                        args: vec![self.smt_to_term(val)],
                    }
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenize() {
        let input = "(declare-const x Int)";
        let tokens = SmtParser::tokenize(input);
        assert_eq!(tokens, vec!["(", "declare-const", "x", "Int", ")"]);
    }

    #[test]
    fn test_parse_simple_term() {
        let mut parser = SmtParser::new("42");
        let term = parser.parse_term().unwrap();
        assert_eq!(term, SmtTerm::Numeral(42));
    }

    #[test]
    fn test_parse_app() {
        let mut parser = SmtParser::new("(+ x y)");
        let term = parser.parse_term().unwrap();
        match term {
            SmtTerm::App { func, args } => {
                assert_eq!(func, "+");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected App"),
        }
    }

    #[tokio::test]
    async fn test_z3_backend_version() {
        let config = ProverConfig {
            executable: PathBuf::from("z3"),
            ..Default::default()
        };

        let backend = Z3Backend::new(config);

        if let Ok(version) = backend.version().await {
            assert!(version.contains("Z3") || version.contains("version"));
        }
    }
}
