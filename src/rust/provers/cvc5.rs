// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! CVC5 SMT solver backend for ECHIDNA
//!
//! CVC5 is a Tier 1 SMT solver, successor to CVC4, with strong support for:
//! - SMT-LIB 2.0 standard
//! - String and sequence theories
//! - Sets and relations
//! - Separation logic

use async_trait::async_trait;
use anyhow::{anyhow, Context as AnyhowContext, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};

use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};
use crate::provers::{ProverBackend, ProverConfig, ProverKind};

/// CVC5 backend configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CVC5Config {
    #[serde(flatten)]
    pub base: ProverConfig,
    pub produce_proofs: bool,
    pub produce_models: bool,
    pub produce_unsat_cores: bool,
    pub incremental: bool,
    pub cvc5_options: HashMap<String, String>,
}

impl Default for CVC5Config {
    fn default() -> Self {
        let mut cvc5_options = HashMap::new();
        cvc5_options.insert("strings-exp".to_string(), "true".to_string());
        CVC5Config {
            base: ProverConfig::default(),
            produce_proofs: true,
            produce_models: true,
            produce_unsat_cores: false,
            incremental: true,
            cvc5_options,
        }
    }
}

/// CVC5 SMT solver backend
pub struct CVC5Backend {
    config: CVC5Config,
    process: Arc<Mutex<Option<CVC5Process>>>,
}

struct CVC5Process {
    child: Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
    command_count: usize,
    stack_depth: usize,
}

impl CVC5Backend {
    pub fn new(config: ProverConfig) -> Self {
        CVC5Backend {
            config: CVC5Config {
                base: config,
                ..Default::default()
            },
            process: Arc::new(Mutex::new(None)),
        }
    }

    pub fn with_config(config: CVC5Config) -> Self {
        CVC5Backend {
            config,
            process: Arc::new(Mutex::new(None)),
        }
    }

    fn start_process(&self) -> Result<CVC5Process> {
        let mut cmd = Command::new(&self.config.base.executable);
        cmd.arg("--interactive").arg("--lang=smt2");
        
        if self.config.produce_proofs {
            cmd.arg("--dump-proofs").arg("--proof-mode=full");
        }
        if self.config.produce_models {
            cmd.arg("--produce-models");
        }
        if self.config.produce_unsat_cores {
            cmd.arg("--produce-unsat-cores");
        }
        if self.config.incremental {
            cmd.arg("--incremental");
        }

        for (key, value) in &self.config.cvc5_options {
            cmd.arg(format!("--{}", key));
            if !value.is_empty() && value != "true" {
                cmd.arg(value);
            }
        }

        for arg in &self.config.base.args {
            cmd.arg(arg);
        }

        cmd.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped());

        let mut child = cmd.spawn().context("Failed to spawn CVC5 process")?;
        let stdin = child.stdin.take().ok_or_else(|| anyhow!("Failed to open CVC5 stdin"))?;
        let stdout = child.stdout.take().ok_or_else(|| anyhow!("Failed to open CVC5 stdout"))?;

        Ok(CVC5Process {
            child,
            stdin,
            stdout: BufReader::new(stdout),
            command_count: 0,
            stack_depth: 0,
        })
    }

    fn get_process(&self) -> Result<std::sync::MutexGuard<Option<CVC5Process>>> {
        let mut guard = self.process.lock().map_err(|e| anyhow!("Failed to lock process: {}", e))?;
        if guard.is_none() {
            *guard = Some(self.start_process()?);
        }
        Ok(guard)
    }

    fn send_command(&self, command: &str) -> Result<String> {
        let mut guard = self.get_process()?;
        let process = guard.as_mut().ok_or_else(|| anyhow!("CVC5 process not initialized"))?;

        writeln!(process.stdin, "{}", command).context("Failed to write to CVC5 stdin")?;
        process.stdin.flush().context("Failed to flush CVC5 stdin")?;
        process.command_count += 1;

        let mut response = String::new();
        let mut depth = 0;
        let mut in_string = false;
        let mut escape_next = false;

        loop {
            let mut line = String::new();
            let bytes_read = process.stdout.read_line(&mut line).context("Failed to read from CVC5 stdout")?;
            if bytes_read == 0 {
                return Err(anyhow!("CVC5 process closed unexpectedly"));
            }

            response.push_str(&line);

            for ch in line.chars() {
                if escape_next {
                    escape_next = false;
                    continue;
                }
                match ch {
                    '\\' if in_string => escape_next = true,
                    '"' => in_string = !in_string,
                    '(' if !in_string => depth += 1,
                    ')' if !in_string => {
                        depth -= 1;
                        if depth == 0 && !response.trim().is_empty() {
                            return Ok(response.trim().to_string());
                        }
                    }
                    _ => {}
                }
            }

            if depth == 0 && !response.trim().is_empty() {
                let trimmed = response.trim();
                if matches!(trimmed, "sat" | "unsat" | "unknown" | "success" | "unsupported") {
                    return Ok(trimmed.to_string());
                }
                if trimmed.starts_with("(error") {
                    return Err(anyhow!("CVC5 error: {}", trimmed));
                }
            }
        }
    }

    fn push_context(&self) -> Result<()> {
        self.send_command("(push 1)")?;
        let mut guard = self.get_process()?;
        if let Some(process) = guard.as_mut() {
            process.stack_depth += 1;
        }
        Ok(())
    }

    fn pop_context(&self) -> Result<()> {
        let mut guard = self.get_process()?;
        if let Some(process) = guard.as_mut() {
            if process.stack_depth == 0 {
                return Err(anyhow!("Cannot pop: stack is empty"));
            }
            drop(guard);
            self.send_command("(pop 1)")?;
            guard = self.get_process()?;
            if let Some(process) = guard.as_mut() {
                process.stack_depth -= 1;
            }
        }
        Ok(())
    }

    fn check_sat(&self) -> Result<SmtResult> {
        let response = self.send_command("(check-sat)")?;
        match response.as_str() {
            "sat" => Ok(SmtResult::Sat),
            "unsat" => Ok(SmtResult::Unsat),
            "unknown" => Ok(SmtResult::Unknown),
            _ => Err(anyhow!("Unexpected check-sat response: {}", response)),
        }
    }

    fn get_model(&self) -> Result<String> {
        self.send_command("(get-model)")
    }

    fn get_proof(&self) -> Result<String> {
        self.send_command("(get-proof)")
    }

    fn get_unsat_core(&self) -> Result<Vec<String>> {
        let response = self.send_command("(get-unsat-core)")?;
        Self::parse_unsat_core(&response)
    }

    fn parse_unsat_core(response: &str) -> Result<Vec<String>> {
        let trimmed = response.trim();
        if !trimmed.starts_with('(') || !trimmed.ends_with(')') {
            return Err(anyhow!("Invalid unsat core format"));
        }
        let inner = &trimmed[1..trimmed.len() - 1];
        Ok(inner.split_whitespace().map(|s| s.to_string()).collect())
    }

    fn term_to_smtlib(&self, term: &Term) -> Result<String> {
        match term {
            Term::Var(name) => Ok(name.clone()),
            Term::Const(name) => Ok(name.clone()),
            Term::App { func, args } => {
                let func_str = self.term_to_smtlib(func)?;
                if args.is_empty() {
                    Ok(func_str)
                } else {
                    let args_str: Result<Vec<String>> = args.iter().map(|arg| self.term_to_smtlib(arg)).collect();
                    Ok(format!("({} {})", func_str, args_str?.join(" ")))
                }
            }
            Term::Lambda { param, param_type, body } => {
                let body_str = self.term_to_smtlib(body)?;
                if let Some(ty) = param_type {
                    let ty_str = self.term_to_smtlib(ty)?;
                    Ok(format!("(lambda (({} {})) {})", param, ty_str, body_str))
                } else {
                    Err(anyhow!("Lambda requires type annotation for SMT-LIB"))
                }
            }
            Term::ProverSpecific { prover, data } => {
                if prover == "cvc5" || prover == "smtlib" {
                    data.as_str().map(|s| s.to_string()).ok_or_else(|| anyhow!("Invalid prover-specific term"))
                } else {
                    Err(anyhow!("Cannot convert {} term to SMT-LIB", prover))
                }
            }
            _ => Err(anyhow!("Unsupported term type for SMT-LIB: {:?}", term)),
        }
    }

    fn smtlib_to_term(&self, smtlib: &str) -> Result<Term> {
        let trimmed = smtlib.trim();
        if !trimmed.starts_with('(') {
            if trimmed.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
                return Ok(Term::Const(trimmed.to_string()));
            } else {
                return Ok(Term::Var(trimmed.to_string()));
            }
        }

        let inner = &trimmed[1..trimmed.len() - 1];
        let parts = Self::parse_sexp_parts(inner)?;

        if parts.is_empty() {
            return Err(anyhow!("Empty S-expression"));
        }

        if parts[0] == "lambda" {
            if parts.len() < 3 {
                return Err(anyhow!("Invalid lambda expression"));
            }
            return Ok(Term::ProverSpecific {
                prover: "smtlib".to_string(),
                data: serde_json::Value::String(smtlib.to_string()),
            });
        }

        let func = Box::new(self.smtlib_to_term(&parts[0])?);
        let args: Result<Vec<Term>> = parts[1..].iter().map(|p| self.smtlib_to_term(p)).collect();

        Ok(Term::App {
            func,
            args: args?,
        })
    }

    fn parse_sexp_parts(s: &str) -> Result<Vec<String>> {
        let mut parts = Vec::new();
        let mut current = String::new();
        let mut depth = 0;
        let mut in_string = false;
        let mut escape_next = false;

        for ch in s.chars() {
            if escape_next {
                current.push(ch);
                escape_next = false;
                continue;
            }
            match ch {
                '\\' if in_string => {
                    escape_next = true;
                    current.push(ch);
                }
                '"' => {
                    in_string = !in_string;
                    current.push(ch);
                }
                '(' if !in_string => {
                    depth += 1;
                    current.push(ch);
                }
                ')' if !in_string => {
                    depth -= 1;
                    current.push(ch);
                }
                ' ' | '\t' | '\n' if !in_string && depth == 0 => {
                    if !current.is_empty() {
                        parts.push(current.clone());
                        current.clear();
                    }
                }
                _ => {
                    current.push(ch);
                }
            }
        }

        if !current.is_empty() {
            parts.push(current);
        }

        Ok(parts)
    }

    async fn parse_smtlib_content(&self, content: &str) -> Result<ProofState> {
        let lines: Vec<&str> = content.lines().collect();
        let mut state = ProofState {
            goals: vec![],
            context: crate::core::Context::default(),
            proof_script: vec![],
            metadata: HashMap::new(),
        };

        state.metadata.insert("prover".to_string(), serde_json::json!("cvc5"));
        state.metadata.insert("format".to_string(), serde_json::json!("smtlib2"));

        let mut assertions = Vec::new();

        for line in lines {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with(';') {
                continue;
            }
            if trimmed.starts_with("(assert") {
                assertions.push(trimmed.to_string());
            }
            if trimmed.starts_with("(check-sat") {
                if !assertions.is_empty() {
                    let combined = if assertions.len() == 1 {
                        assertions[0].clone()
                    } else {
                        format!("(and {})", assertions.join(" "))
                    };
                    let goal_term = self.smtlib_to_term(&combined)?;
                    state.goals.push(Goal {
                        id: "smt_goal".to_string(),
                        target: goal_term,
                        hypotheses: vec![],
                    });
                }
            }
        }

        if state.goals.is_empty() && !assertions.is_empty() {
            let combined = if assertions.len() == 1 {
                assertions[0].clone()
            } else {
                format!("(and {})", assertions.join(" "))
            };
            let goal_term = self.smtlib_to_term(&combined)?;
            state.goals.push(Goal {
                id: "smt_goal".to_string(),
                target: goal_term,
                hypotheses: vec![],
            });
        }

        Ok(state)
    }

    fn reset(&self) -> Result<()> {
        let mut guard = self.process.lock().map_err(|e| anyhow!("Failed to lock process: {}", e))?;
        if let Some(mut process) = guard.take() {
            let _ = process.child.kill();
            let _ = process.child.wait();
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtResult {
    Sat,
    Unsat,
    Unknown,
}

#[async_trait]
impl ProverBackend for CVC5Backend {
    fn kind(&self) -> ProverKind {
        ProverKind::CVC5
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.base.executable)
            .arg("--version")
            .output()
            .context("Failed to execute CVC5")?;
        let version_str = String::from_utf8_lossy(&output.stdout);
        Ok(version_str.lines().next().unwrap_or("unknown").to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path).await.context(format!("Failed to read file: {:?}", path))?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        self.parse_smtlib_content(content).await
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            Tactic::Custom { prover, command, args } if prover == "cvc5" || prover == "smt" => {
                let full_command = if args.is_empty() {
                    command.clone()
                } else {
                    format!("({} {})", command, args.join(" "))
                };

                let response = self.send_command(&full_command)?;

                if command == "check-sat" {
                    match response.as_str() {
                        "unsat" => Ok(TacticResult::QED),
                        "sat" => {
                            let model = self.get_model().ok();
                            let mut new_state = state.clone();
                            if let Some(m) = model {
                                new_state.metadata.insert("counterexample".to_string(), serde_json::json!(m));
                            }
                            Ok(TacticResult::Error("Formula is satisfiable (not a tautology)".to_string()))
                        }
                        "unknown" => Ok(TacticResult::Error("Solver returned unknown".to_string())),
                        _ => Ok(TacticResult::Success(state.clone())),
                    }
                } else if response == "success" {
                    Ok(TacticResult::Success(state.clone()))
                } else {
                    let mut new_state = state.clone();
                    new_state.metadata.insert("last_response".to_string(), serde_json::json!(response));
                    Ok(TacticResult::Success(new_state))
                }
            }
            Tactic::Simplify => Ok(TacticResult::Success(state.clone())),
            _ => Err(anyhow!("Tactic not supported by CVC5: {:?}", tactic)),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        self.push_context()?;
        let mut success = false;
        for goal in &state.goals {
            let smtlib = self.term_to_smtlib(&goal.target)?;
            self.send_command(&format!("(assert (not {}))", smtlib))?;
        }
        let result = self.check_sat()?;
        success = result == SmtResult::Unsat;
        self.pop_context()?;
        Ok(success)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();
        output.push_str("; Generated by ECHIDNA CVC5 backend\n");
        output.push_str("(set-logic ALL)\n");
        if self.config.produce_models {
            output.push_str("(set-option :produce-models true)\n");
        }
        if self.config.produce_proofs {
            output.push_str("(set-option :produce-proofs true)\n");
        }
        output.push_str("\n");
        for def in &state.context.definitions {
            let ty = self.term_to_smtlib(&def.ty)?;
            let body = self.term_to_smtlib(&def.body)?;
            output.push_str(&format!("(define-fun {} () {} {})\n", def.name, ty, body));
        }
        output.push_str("\n");
        for goal in &state.goals {
            let smtlib = self.term_to_smtlib(&goal.target)?;
            output.push_str(&format!("; Goal: {}\n", goal.id));
            output.push_str(&format!("(assert {})\n", smtlib));
        }
        output.push_str("\n(check-sat)\n");
        if self.config.produce_models {
            output.push_str("(get-model)\n");
        }
        output.push_str("(exit)\n");
        Ok(output)
    }

    async fn suggest_tactics(&self, _state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut tactics = vec![
            Tactic::Custom { prover: "cvc5".to_string(), command: "check-sat".to_string(), args: vec![] },
        ];
        if limit > 1 {
            tactics.push(Tactic::Simplify);
        }
        if limit > 2 {
            tactics.push(Tactic::Custom { prover: "cvc5".to_string(), command: "get-model".to_string(), args: vec![] });
        }
        if limit > 3 && self.config.produce_proofs {
            tactics.push(Tactic::Custom { prover: "cvc5".to_string(), command: "get-proof".to_string(), args: vec![] });
        }
        Ok(tactics.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        Ok(vec![])
    }

    fn config(&self) -> &ProverConfig {
        &self.config.base
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config.base = config;
        let _ = self.reset();
    }
}

impl Drop for CVC5Backend {
    fn drop(&mut self) {
        let _ = self.reset();
    }
}

pub mod string_examples {
    pub fn string_concat_length() -> String {
        r#"(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.len (str.++ x y)) (+ (str.len x) (str.len y))))
(check-sat)"#.to_string()
    }

    pub fn string_substring() -> String {
        r#"(set-logic QF_SLIA)
(declare-const s String)
(assert (= (str.len s) 10))
(assert (= (str.substr s 0 5) "hello"))
(assert (= (str.substr s 5 5) "world"))
(check-sat)
(get-model)"#.to_string()
    }

    pub fn string_contains() -> String {
        r#"(set-logic QF_SLIA)
(declare-const s String)
(assert (str.contains s "abc"))
(assert (not (str.contains s "xyz")))
(assert (< (str.len s) 10))
(check-sat)
(get-model)"#.to_string()
    }

    pub fn regex_match() -> String {
        r#"(set-logic QF_SLIA)
(declare-const email String)
(assert (str.in.re email (re.++ (re.+ (re.range "a" "z")) (str.to.re "@") (re.+ (re.range "a" "z")) (str.to.re ".") (re.+ (re.range "a" "z")))))
(assert (= (str.len email) 15))
(check-sat)
(get-model)"#.to_string()
    }
}

pub mod sequence_examples {
    pub fn sequence_ops() -> String {
        r#"(set-logic QF_SLIA)
(declare-const s (Seq Int))
(declare-const t (Seq Int))
(assert (= (seq.len s) 5))
(assert (= (seq.nth s 0) 1))
(assert (= (seq.nth s 4) 5))
(assert (= t (seq.++ s s)))
(assert (= (seq.len t) 10))
(check-sat)
(get-model)"#.to_string()
    }

    pub fn sequence_contains() -> String {
        r#"(set-logic QF_SLIA)
(declare-const s (Seq Int))
(declare-const sub (Seq Int))
(assert (seq.contains s sub))
(assert (= (seq.len sub) 3))
(assert (= (seq.nth sub 0) 42))
(check-sat)
(get-model)"#.to_string()
    }
}

pub mod sets_examples {
    pub fn set_ops() -> String {
        r#"(set-logic QF_ALL)
(declare-const A (Set Int))
(declare-const B (Set Int))
(assert (set.member 1 A))
(assert (set.member 2 A))
(assert (set.member 2 B))
(assert (set.member 3 B))
(assert (= (set.card (set.inter A B)) 1))
(check-sat)
(get-model)"#.to_string()
    }

    pub fn relation_ops() -> String {
        r#"(set-logic QF_ALL)
(declare-const R (Relation Int Int))
(assert (set.member (tuple 1 2) R))
(assert (set.member (tuple 2 3) R))
(assert (set.member (tuple 1 3) (rel.tclosure R)))
(check-sat)"#.to_string()
    }
}

pub mod separation_logic_examples {
    pub fn sep_logic_basic() -> String {
        r#"(set-logic QF_ALL)
(declare-const x Int)
(declare-const y Int)
(assert (sep (pto x 1) (pto y 2)))
(assert (distinct x y))
(check-sat)"#.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sexp_parser() {
        let result = CVC5Backend::parse_sexp_parts("f x y");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), vec!["f", "x", "y"]);
    }

    #[test]
    fn test_sexp_parser_nested() {
        let result = CVC5Backend::parse_sexp_parts("f (g x) y");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), vec!["f", "(g x)", "y"]);
    }

    #[test]
    fn test_unsat_core_parser() {
        let core = "(a b c)";
        let result = CVC5Backend::parse_unsat_core(core);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), vec!["a", "b", "c"]);
    }

    #[tokio::test]
    async fn test_backend_creation() {
        let config = ProverConfig {
            executable: PathBuf::from("cvc5"),
            ..Default::default()
        };
        let backend = CVC5Backend::new(config);
        assert_eq!(backend.kind(), ProverKind::CVC5);
    }

    #[tokio::test]
    async fn test_string_examples() {
        assert!(!string_examples::string_concat_length().is_empty());
        assert!(!string_examples::string_substring().is_empty());
        assert!(!string_examples::string_contains().is_empty());
        assert!(!string_examples::regex_match().is_empty());
    }
}
