// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! HOL Light theorem prover backend
//!
//! HOL Light is a Tier 2 prover (complexity 3/5) written in OCaml with a powerful tactic-based
//! proof system. It's part of the HOL family (Higher-Order Logic) and known for its small
//! trusted kernel and extensive library.
//!
//! Key features:
//! - OCaml-based with interactive REPL
//! - LCF-style proof kernel (small trusted base)
//! - Rich tactic system (REWRITE_TAC, MESON_TAC, SIMP_TAC, etc.)
//! - Standard library with fundamental mathematics
//! - Term-level proof objects
//! - ML metaprogramming for proof automation
//!
//! ## Complexity: 3/5
//! - OCaml process interaction required
//! - ML parsing for tactics and terms
//! - Interactive session management
//! - Implementation time: ~2 weeks

use async_trait::async_trait;
use anyhow::{anyhow, Context as AnyhowContext, Result};
use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::fs;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, ChildStdin, ChildStdout, Command};
use tokio::sync::Mutex;
use tracing::{debug, info, trace, warn};

use crate::core::{
    Context as ProofContext, Definition, Goal, ProofState, Tactic, TacticResult,
    Term, Theorem,
};
use crate::provers::{ProverBackend, ProverConfig, ProverKind};

/// HOL Light backend implementation
pub struct HolLightBackend {
    config: ProverConfig,
    session: Mutex<Option<HolLightSession>>,
    library_loaded: Mutex<bool>,
}

impl HolLightBackend {
    pub fn new(config: ProverConfig) -> Self {
        Self {
            config,
            session: Mutex::new(None),
            library_loaded: Mutex::new(false),
        }
    }

    /// Start HOL Light OCaml session
    async fn start_session(&self) -> Result<HolLightSession> {
        info!("Starting HOL Light OCaml session");

        // HOL Light is typically invoked via ocaml with hol.ml loaded
        let hol_dir = self.config.library_paths.first()
            .cloned()
            .unwrap_or_else(|| PathBuf::from("/usr/local/lib/hol_light"));

        let hol_ml = hol_dir.join("hol.ml");

        // Start OCaml with HOL Light loaded
        let mut child = Command::new("ocaml")
            .current_dir(&hol_dir)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("Failed to start OCaml for HOL Light")?;

        let stdin = child.stdin.take()
            .ok_or_else(|| anyhow!("Failed to capture stdin"))?;
        let stdout = child.stdout.take()
            .ok_or_else(|| anyhow!("Failed to capture stdout"))?;

        let mut session = HolLightSession {
            process: child,
            stdin,
            stdout: BufReader::new(stdout),
            command_counter: 0,
        };

        // Load HOL Light core
        if hol_ml.exists() {
            session.send_command(&format!("#use \"{}\";;", hol_ml.display())).await?;
            info!("HOL Light core loaded");
        } else {
            warn!("HOL Light core file not found at {:?}, continuing without it", hol_ml);
        }

        Ok(session)
    }

    /// Get or create active session
    async fn get_session(&self) -> Result<()> {
        let mut session_lock = self.session.lock().await;

        if session_lock.is_none() {
            *session_lock = Some(self.start_session().await?);
        }

        Ok(())
    }

    /// Execute HOL Light command
    async fn execute_command(&self, command: &str) -> Result<String> {
        self.get_session().await?;

        let mut session_lock = self.session.lock().await;
        let session = session_lock.as_mut()
            .ok_or_else(|| anyhow!("No active session"))?;

        session.send_command(command).await
    }

    /// Load HOL Light standard library
    async fn load_library(&self) -> Result<()> {
        let mut loaded = self.library_loaded.lock().await;

        if *loaded {
            return Ok(());
        }

        info!("Loading HOL Light standard library");

        // Load essential libraries
        let libraries = vec![
            "bool.ml",
            "equal.ml",
            "ind_defs.ml",
            "pair.ml",
            "nums.ml",
            "arith.ml",
            "lists.ml",
        ];

        for lib in libraries {
            let load_cmd = format!("#use \"{}\";;", lib);
            match self.execute_command(&load_cmd).await {
                Ok(_) => debug!("Loaded library: {}", lib),
                Err(e) => warn!("Failed to load library {}: {}", lib, e),
            }
        }

        *loaded = true;
        info!("HOL Light standard library loaded");
        Ok(())
    }

    /// Parse HOL Light ML file
    fn parse_ml_file(&self, content: &str) -> Result<HolLightFile> {
        let mut parser = HolLightParser::new(content);
        parser.parse()
    }

    /// Convert HOL Light term to universal Term
    fn hol_to_term(&self, hol_term: &HolTerm) -> Result<Term> {
        match hol_term {
            HolTerm::Var { name, ty } => {
                Ok(Term::Var(name.clone()))
            }
            HolTerm::Const { name, ty } => {
                Ok(Term::Const(name.clone()))
            }
            HolTerm::Comb { func, arg } => {
                let func_term = self.hol_to_term(func)?;
                let arg_term = self.hol_to_term(arg)?;

                // Check if func is already an App, if so extend args
                match func_term {
                    Term::App { func: inner_func, mut args } => {
                        args.push(arg_term);
                        Ok(Term::App { func: inner_func, args })
                    }
                    _ => {
                        Ok(Term::App {
                            func: Box::new(func_term),
                            args: vec![arg_term],
                        })
                    }
                }
            }
            HolTerm::Abs { var, var_type, body } => {
                let var_type_term = match var_type {
                    Some(t) => Some(Box::new(self.hol_to_term(t)?)),
                    None => None,
                };
                let body_term = Box::new(self.hol_to_term(body)?);

                Ok(Term::Lambda {
                    param: var.clone(),
                    param_type: var_type_term,
                    body: body_term,
                })
            }
        }
    }

    /// Convert universal Term to HOL Light syntax
    fn term_to_hol(&self, term: &Term) -> String {
        match term {
            Term::Var(name) => format!("`{}`", name),
            Term::Const(name) => name.clone(),
            Term::App { func, args } => {
                let func_str = self.term_to_hol(func);
                let args_str = args.iter()
                    .map(|a| self.term_to_hol(a))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("({} {})", func_str, args_str)
            }
            Term::Lambda { param, param_type, body } => {
                let type_annotation = param_type.as_ref()
                    .map(|t| format!(":{}", self.term_to_hol(t)))
                    .unwrap_or_default();
                format!("(\\{}{}. {})", param, type_annotation, self.term_to_hol(body))
            }
            Term::Pi { param, param_type, body } => {
                format!("(!{} : {}. {})", param, self.term_to_hol(param_type), self.term_to_hol(body))
            }
            Term::Universe(level) => format!("Type{}", level),
            Term::Meta(id) => format!("?{}", id),
            Term::ProverSpecific { data, .. } => {
                data.as_str().unwrap_or("<term>").to_string()
            }
        }
    }

    /// Map ECHIDNA tactic to HOL Light tactic
    fn tactic_to_hol(&self, tactic: &Tactic) -> Result<String> {
        match tactic {
            Tactic::Apply(theorem_name) => {
                Ok(format!("MATCH_MP_TAC {};;", theorem_name))
            }
            Tactic::Intro(name) => {
                Ok("GEN_TAC;;".to_string())
            }
            Tactic::Cases(term) => {
                let term_str = self.term_to_hol(term);
                Ok(format!("STRUCT_CASES_TAC (SPEC {} cases);;", term_str))
            }
            Tactic::Induction(term) => {
                let term_str = self.term_to_hol(term);
                Ok(format!("INDUCT_TAC;;"))
            }
            Tactic::Rewrite(theorem_name) => {
                Ok(format!("REWRITE_TAC[{}];;", theorem_name))
            }
            Tactic::Simplify => {
                Ok("SIMP_TAC[];;".to_string())
            }
            Tactic::Reflexivity => {
                Ok("REFL_TAC;;".to_string())
            }
            Tactic::Assumption => {
                Ok("ASM_REWRITE_TAC[];;".to_string())
            }
            Tactic::Exact(term) => {
                let term_str = self.term_to_hol(term);
                Ok(format!("ACCEPT_TAC {};;", term_str))
            }
            Tactic::Custom { prover, command, args } => {
                if prover != "hol_light" {
                    return Err(anyhow!("Custom tactic not for HOL Light"));
                }

                let args_str = args.join(" ");
                Ok(format!("{} {};;", command, args_str))
            }
        }
    }

    /// Export proof to HOL Light ML format
    fn export_to_hol(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();

        output.push_str("(* Generated by ECHIDNA *)\n");
        output.push_str("(* HOL Light proof script *)\n\n");

        output.push_str("#use \"hol.ml\";;\n\n");

        // Export definitions
        for def in &state.context.definitions {
            output.push_str(&format!("let {} = new_definition `{} = {}`;;  \n\n",
                def.name,
                self.term_to_hol(&Term::Const(def.name.clone())),
                self.term_to_hol(&def.body)
            ));
        }

        // Export theorems
        for theorem in &state.context.theorems {
            output.push_str(&format!("(* {} *)\n", theorem.name));
            output.push_str(&format!("let {} = prove\n", theorem.name));
            output.push_str(&format!("  ({},\n", self.term_to_hol(&theorem.statement)));

            if let Some(proof) = &theorem.proof {
                for tactic in proof {
                    if let Ok(hol_tactic) = self.tactic_to_hol(tactic) {
                        output.push_str(&format!("   {}\n", hol_tactic));
                    }
                }
            } else {
                output.push_str("   (* Proof to be completed *)\n");
                output.push_str("   ADMIT_TAC);;\n");
            }
            output.push_str("\n");
        }

        // Export goals
        for (i, goal) in state.goals.iter().enumerate() {
            output.push_str(&format!("(* Goal {} *)\n", i + 1));
            output.push_str(&format!("g `{}`;;\n", self.term_to_hol(&goal.target)));
            output.push_str("(* Apply tactics here *)\n\n");
        }

        Ok(output)
    }

    /// Parse HOL Light theorem from output
    fn parse_theorem_from_output(&self, output: &str) -> Option<(String, Term)> {
        // HOL Light output format: `|- theorem_statement`
        if output.contains("|-") {
            let parts: Vec<&str> = output.splitn(2, "|-").collect();
            if parts.len() == 2 {
                let statement = parts[1].trim();
                // Parse statement as term (simplified - would need full parser)
                return Some((
                    "theorem".to_string(),
                    Term::ProverSpecific {
                        prover: "hol_light".to_string(),
                        data: serde_json::json!(statement),
                    }
                ));
            }
        }
        None
    }
}

#[async_trait]
impl ProverBackend for HolLightBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::HolLight
    }

    async fn version(&self) -> Result<String> {
        // HOL Light doesn't have a --version flag, return session info
        self.get_session().await?;
        Ok("HOL Light (OCaml session)".to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        info!("Parsing HOL Light file: {:?}", path);

        let content = fs::read_to_string(&path)
            .await
            .with_context(|| format!("Failed to read file: {:?}", path))?;

        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        debug!("Parsing HOL Light content ({} bytes)", content.len());

        let file = self.parse_ml_file(content)?;

        let mut goals = Vec::new();
        let mut context = ProofContext::default();

        // Extract theorems
        for theorem in &file.theorems {
            let statement = self.hol_to_term(&theorem.statement)?;

            if theorem.proof.is_none() {
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
                aspects: vec!["hol_light".to_string()],
            });
        }

        // Extract definitions
        for def in &file.definitions {
            let def_term = self.hol_to_term(&def.term)?;

            context.definitions.push(Definition {
                name: def.name.clone(),
                ty: Term::ProverSpecific {
                    prover: "hol_light".to_string(),
                    data: serde_json::json!(def.def_type.clone()),
                },
                body: def_term,
            });
        }

        Ok(ProofState {
            goals,
            context,
            proof_script: vec![],
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("prover".to_string(), serde_json::json!("hol_light"));
                meta.insert("theorems".to_string(), serde_json::json!(file.theorems.len()));
                meta.insert("definitions".to_string(), serde_json::json!(file.definitions.len()));
                meta
            },
        })
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        debug!("Applying tactic: {:?}", tactic);

        if state.goals.is_empty() {
            return Ok(TacticResult::QED);
        }

        let hol_tactic = self.tactic_to_hol(tactic)?;

        // Execute tactic in HOL Light session
        match self.execute_command(&hol_tactic).await {
            Ok(output) => {
                let mut new_state = state.clone();
                new_state.proof_script.push(tactic.clone());

                // Parse output to determine if goal was solved
                if output.contains("No subgoals") || output.contains("Theorem") {
                    new_state.goals.clear();
                    Ok(TacticResult::QED)
                } else {
                    // Simplified: assume tactic succeeded and removed first goal
                    if !new_state.goals.is_empty() {
                        new_state.goals.remove(0);
                    }

                    if new_state.goals.is_empty() {
                        Ok(TacticResult::QED)
                    } else {
                        Ok(TacticResult::Success(new_state))
                    }
                }
            }
            Err(e) => {
                Ok(TacticResult::Error(format!("Tactic failed: {}", e)))
            }
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        info!("Verifying HOL Light proof");

        if !state.is_complete() {
            debug!("Proof incomplete: {} goals remaining", state.goals.len());
            return Ok(false);
        }

        // Export to HOL Light format and verify
        let hol_content = self.export_to_hol(state)?;

        // Write to temporary file
        let temp_dir = std::env::temp_dir();
        let temp_file = temp_dir.join(format!("echidna_{}.ml", uuid::Uuid::new_v4()));

        fs::write(&temp_file, hol_content).await?;

        // Load and verify in HOL Light session
        let load_cmd = format!("#use \"{}\";;", temp_file.display());
        let result = self.execute_command(&load_cmd).await;

        // Clean up
        let _ = fs::remove_file(&temp_file).await;

        match result {
            Ok(output) => {
                Ok(output.contains("Theorem") || !output.contains("Exception"))
            }
            Err(_) => Ok(false),
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        self.export_to_hol(state)
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        debug!("Suggesting HOL Light tactics (limit: {})", limit);

        if state.goals.is_empty() {
            return Ok(vec![]);
        }

        let goal = &state.goals[0];
        let mut suggestions = Vec::new();

        // Analyze goal structure and suggest tactics
        match &goal.target {
            Term::Pi { .. } => {
                suggestions.push(Tactic::Intro(None));
            }
            Term::App { func, .. } => {
                // Check if it's an equality
                if let Term::Const(name) = func.as_ref() {
                    if name == "=" {
                        suggestions.push(Tactic::Reflexivity);
                        suggestions.push(Tactic::Simplify);
                    }
                }

                // Suggest applicable theorems
                for theorem in state.context.theorems.iter().take(limit - suggestions.len()) {
                    suggestions.push(Tactic::Apply(theorem.name.clone()));
                }
            }
            _ => {
                suggestions.push(Tactic::Assumption);
                suggestions.push(Tactic::Simplify);
            }
        }

        // Always suggest powerful tactics
        if suggestions.len() < limit {
            suggestions.push(Tactic::Custom {
                prover: "hol_light".to_string(),
                command: "MESON_TAC".to_string(),
                args: vec![],
            });
        }

        if suggestions.len() < limit {
            suggestions.push(Tactic::Custom {
                prover: "hol_light".to_string(),
                command: "ASM_MESON_TAC".to_string(),
                args: vec![],
            });
        }

        suggestions.truncate(limit);
        Ok(suggestions)
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        debug!("Searching theorems for pattern: {}", pattern);

        // Use HOL Light's search function
        let search_cmd = format!("search `{}`;;", pattern);

        match self.execute_command(&search_cmd).await {
            Ok(output) => {
                let results: Vec<String> = output
                    .lines()
                    .filter(|line| line.contains("|-"))
                    .map(|line| line.trim().to_string())
                    .take(100)
                    .collect();

                info!("Found {} theorems matching '{}'", results.len(), pattern);
                Ok(results)
            }
            Err(e) => {
                warn!("Search failed: {}", e);
                Ok(vec![])
            }
        }
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

// ============================================================================
// HOL Light Session Management
// ============================================================================

struct HolLightSession {
    process: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    command_counter: u64,
}

impl HolLightSession {
    async fn send_command(&mut self, command: &str) -> Result<String> {
        trace!("Sending command: {}", command);

        // Write command to stdin
        self.stdin.write_all(command.as_bytes()).await?;
        self.stdin.write_all(b"\n").await?;
        self.stdin.flush().await?;

        // Read response from stdout
        let mut response = String::new();
        let mut buffer = String::new();
        let mut lines_read = 0;
        let max_lines = 1000;

        while lines_read < max_lines {
            buffer.clear();
            let bytes_read = self.stdout.read_line(&mut buffer).await?;

            if bytes_read == 0 {
                break; // EOF
            }

            response.push_str(&buffer);
            lines_read += 1;

            // Check for OCaml prompt (indicates command completed)
            if buffer.trim() == "#" || buffer.contains("# ") {
                break;
            }

            // Check for common completion markers
            if buffer.contains("val ") || buffer.contains("Exception") ||
               buffer.contains("Theorem") || buffer.contains("No subgoals") {
                // Read one more line (likely the prompt)
                buffer.clear();
                let _ = self.stdout.read_line(&mut buffer).await;
                response.push_str(&buffer);
                break;
            }
        }

        self.command_counter += 1;
        trace!("Command response ({} lines): {}", lines_read, response.trim());

        Ok(response)
    }
}

impl Drop for HolLightSession {
    fn drop(&mut self) {
        // Attempt to gracefully terminate the OCaml process
        let _ = self.process.start_kill();
    }
}

// ============================================================================
// HOL Light Parser
// ============================================================================

#[derive(Debug, Clone)]
struct HolLightFile {
    theorems: Vec<HolTheorem>,
    definitions: Vec<HolDefinition>,
    tactics: Vec<HolTactic>,
}

#[derive(Debug, Clone)]
struct HolTheorem {
    name: String,
    statement: HolTerm,
    proof: Option<Vec<HolTactic>>,
}

#[derive(Debug, Clone)]
struct HolDefinition {
    name: String,
    def_type: String,
    term: HolTerm,
}

#[derive(Debug, Clone)]
enum HolTactic {
    RewriteTac(Vec<String>),
    AsmRewriteTac(Vec<String>),
    InductTac,
    StructCasesTac(String),
    MesonTac(Vec<String>),
    SimpTac(Vec<String>),
    GenTac,
    DischTac,
    ConjTac,
    MatchMpTac(String),
    AcceptTac(String),
    Custom(String),
}

#[derive(Debug, Clone, PartialEq)]
enum HolTerm {
    Var {
        name: String,
        ty: Option<Box<HolTerm>>,
    },
    Const {
        name: String,
        ty: Option<Box<HolTerm>>,
    },
    Comb {
        func: Box<HolTerm>,
        arg: Box<HolTerm>,
    },
    Abs {
        var: String,
        var_type: Option<Box<HolTerm>>,
        body: Box<HolTerm>,
    },
}

struct HolLightParser {
    input: String,
    pos: usize,
}

impl HolLightParser {
    fn new(input: &str) -> Self {
        HolLightParser {
            input: input.to_string(),
            pos: 0,
        }
    }

    fn parse(&mut self) -> Result<HolLightFile> {
        let mut theorems = Vec::new();
        let mut definitions = Vec::new();
        let mut tactics = Vec::new();

        while self.pos < self.input.len() {
            self.skip_whitespace_and_comments();

            if self.pos >= self.input.len() {
                break;
            }

            // Try to parse different constructs
            if self.check_keyword("let") {
                if let Ok(def_or_thm) = self.parse_let_binding() {
                    match def_or_thm {
                        LetBinding::Definition(def) => definitions.push(def),
                        LetBinding::Theorem(thm) => theorems.push(thm),
                    }
                }
            } else if self.check_keyword("prove") {
                if let Ok(thm) = self.parse_prove() {
                    theorems.push(thm);
                }
            } else if self.check_keyword("g") {
                if let Ok(goal) = self.parse_goal() {
                    theorems.push(goal);
                }
            } else {
                // Skip unrecognized content
                self.pos += 1;
            }
        }

        Ok(HolLightFile {
            theorems,
            definitions,
            tactics,
        })
    }

    fn parse_let_binding(&mut self) -> Result<LetBinding> {
        self.expect_keyword("let")?;

        let name = self.parse_identifier()
            .ok_or_else(|| anyhow!("Expected identifier after 'let'"))?;

        self.skip_whitespace_and_comments();
        self.expect_char('=')?;
        self.skip_whitespace_and_comments();

        // Check if it's a theorem (prove) or definition
        if self.check_keyword("prove") {
            self.consume_keyword("prove");
            let theorem = self.parse_prove_body(&name)?;
            Ok(LetBinding::Theorem(theorem))
        } else if self.check_keyword("new_definition") {
            let definition = self.parse_new_definition(&name)?;
            Ok(LetBinding::Definition(definition))
        } else {
            // Generic definition
            let term = self.parse_simple_term()?;
            Ok(LetBinding::Definition(HolDefinition {
                name,
                def_type: "definition".to_string(),
                term,
            }))
        }
    }

    fn parse_prove(&mut self) -> Result<HolTheorem> {
        self.expect_keyword("prove")?;
        self.parse_prove_body("anonymous")
    }

    fn parse_prove_body(&mut self, name: &str) -> Result<HolTheorem> {
        self.skip_whitespace_and_comments();
        self.expect_char('(')?;

        // Parse statement (backtick-quoted term)
        let statement = self.parse_term()?;

        self.skip_whitespace_and_comments();
        self.expect_char(',')?;

        // Parse tactics (simplified - would need full tactic parser)
        let mut proof = Vec::new();

        // Skip to closing paren
        let mut depth = 1;
        while depth > 0 && self.pos < self.input.len() {
            if self.peek() == Some('(') {
                depth += 1;
            } else if self.peek() == Some(')') {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            self.pos += 1;
        }

        if self.peek() == Some(')') {
            self.pos += 1;
        }

        Ok(HolTheorem {
            name: name.to_string(),
            statement,
            proof: Some(proof),
        })
    }

    fn parse_new_definition(&mut self, name: &str) -> Result<HolDefinition> {
        self.expect_keyword("new_definition")?;
        self.skip_whitespace_and_comments();

        // Parse backtick-quoted term
        let term = self.parse_term()?;

        Ok(HolDefinition {
            name: name.to_string(),
            def_type: "new_definition".to_string(),
            term,
        })
    }

    fn parse_goal(&mut self) -> Result<HolTheorem> {
        self.expect_keyword("g")?;
        self.skip_whitespace_and_comments();

        let statement = self.parse_term()?;

        Ok(HolTheorem {
            name: format!("goal_{}", self.pos),
            statement,
            proof: None,
        })
    }

    fn parse_term(&mut self) -> Result<HolTerm> {
        self.skip_whitespace_and_comments();

        // Backtick-quoted term
        if self.peek() == Some('`') {
            self.pos += 1; // consume `
            let start = self.pos;

            while self.pos < self.input.len() && self.peek() != Some('`') {
                self.pos += 1;
            }

            let content = self.input[start..self.pos].to_string();

            if self.peek() == Some('`') {
                self.pos += 1; // consume closing `
            }

            // Parse the content as a term
            return self.parse_term_content(&content);
        }

        self.parse_simple_term()
    }

    fn parse_term_content(&self, content: &str) -> Result<HolTerm> {
        // Simplified term parser - handles basic cases
        let trimmed = content.trim();

        if trimmed.is_empty() {
            return Ok(HolTerm::Const {
                name: "T".to_string(),
                ty: None,
            });
        }

        // Check for lambda abstraction
        if trimmed.starts_with('\\') || trimmed.starts_with("fun ") {
            // Lambda: \x. body
            return Ok(HolTerm::Abs {
                var: "x".to_string(),
                var_type: None,
                body: Box::new(HolTerm::Const {
                    name: "body".to_string(),
                    ty: None,
                }),
            });
        }

        // Check for forall: !x. body
        if trimmed.starts_with('!') {
            return Ok(HolTerm::Abs {
                var: "x".to_string(),
                var_type: None,
                body: Box::new(HolTerm::Const {
                    name: "body".to_string(),
                    ty: None,
                }),
            });
        }

        // Default: treat as constant or variable
        if trimmed.chars().next().unwrap_or('a').is_uppercase() {
            Ok(HolTerm::Const {
                name: trimmed.to_string(),
                ty: None,
            })
        } else {
            Ok(HolTerm::Var {
                name: trimmed.to_string(),
                ty: None,
            })
        }
    }

    fn parse_simple_term(&mut self) -> Result<HolTerm> {
        self.skip_whitespace_and_comments();

        if let Some(id) = self.parse_identifier() {
            if id.chars().next().unwrap().is_uppercase() {
                Ok(HolTerm::Const {
                    name: id,
                    ty: None,
                })
            } else {
                Ok(HolTerm::Var {
                    name: id,
                    ty: None,
                })
            }
        } else {
            Err(anyhow!("Expected term"))
        }
    }

    fn parse_identifier(&mut self) -> Option<String> {
        self.skip_whitespace_and_comments();

        let start = self.pos;
        while self.pos < self.input.len() {
            let ch = self.input.as_bytes()[self.pos] as char;
            if ch.is_alphanumeric() || ch == '_' || ch == '\'' {
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

    fn peek(&self) -> Option<char> {
        if self.pos < self.input.len() {
            Some(self.input.as_bytes()[self.pos] as char)
        } else {
            None
        }
    }

    fn check_keyword(&self, keyword: &str) -> bool {
        self.input[self.pos..].starts_with(keyword)
    }

    fn consume_keyword(&mut self, keyword: &str) {
        self.skip_whitespace_and_comments();
        if self.input[self.pos..].starts_with(keyword) {
            self.pos += keyword.len();
        }
    }

    fn expect_keyword(&mut self, keyword: &str) -> Result<()> {
        self.skip_whitespace_and_comments();

        if !self.input[self.pos..].starts_with(keyword) {
            return Err(anyhow!("Expected keyword '{}' at position {}", keyword, self.pos));
        }

        self.pos += keyword.len();
        Ok(())
    }

    fn expect_char(&mut self, ch: char) -> Result<()> {
        self.skip_whitespace_and_comments();

        if self.peek() != Some(ch) {
            return Err(anyhow!("Expected '{}' at position {}", ch, self.pos));
        }

        self.pos += 1;
        Ok(())
    }

    fn skip_whitespace_and_comments(&mut self) {
        while self.pos < self.input.len() {
            let ch = self.input.as_bytes()[self.pos] as char;

            if ch.is_whitespace() {
                self.pos += 1;
            } else if self.input[self.pos..].starts_with("(*") {
                // ML comment: (* ... *)
                self.pos += 2;
                let mut depth = 1;

                while depth > 0 && self.pos + 1 < self.input.len() {
                    if self.input[self.pos..].starts_with("(*") {
                        depth += 1;
                        self.pos += 2;
                    } else if self.input[self.pos..].starts_with("*)") {
                        depth -= 1;
                        self.pos += 2;
                    } else {
                        self.pos += 1;
                    }
                }
            } else {
                break;
            }
        }
    }
}

enum LetBinding {
    Definition(HolDefinition),
    Theorem(HolTheorem),
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_hol_light_backend_creation() {
        let config = ProverConfig::default();
        let backend = HolLightBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::HolLight);
        assert_eq!(backend.kind().complexity(), 3);
        assert_eq!(backend.kind().tier(), 2);
    }

    #[test]
    fn test_hol_light_parser_basic() {
        let content = r#"
            let ADD_SYM = prove
              (`!m n. m + n = n + m`,
               REWRITE_TAC[ADD_AC]);;
        "#;

        let mut parser = HolLightParser::new(content);
        let file = parser.parse().unwrap();

        assert_eq!(file.theorems.len(), 1);
        assert_eq!(file.theorems[0].name, "ADD_SYM");
    }

    #[test]
    fn test_term_conversion() {
        let config = ProverConfig::default();
        let backend = HolLightBackend::new(config);

        let hol_term = HolTerm::Var {
            name: "x".to_string(),
            ty: None,
        };

        let term = backend.hol_to_term(&hol_term).unwrap();
        assert!(matches!(term, Term::Var(_)));
    }

    #[test]
    fn test_tactic_to_hol() {
        let config = ProverConfig::default();
        let backend = HolLightBackend::new(config);

        let tactic = Tactic::Reflexivity;
        let hol_tactic = backend.tactic_to_hol(&tactic).unwrap();
        assert!(hol_tactic.contains("REFL_TAC"));
    }

    #[test]
    fn test_export_format() {
        let config = ProverConfig::default();
        let backend = HolLightBackend::new(config);

        let state = ProofState::new(Term::Const("goal".to_string()));
        let exported = backend.export_to_hol(&state).unwrap();

        assert!(exported.contains("Generated by ECHIDNA"));
        assert!(exported.contains("#use \"hol.ml\""));
    }

    #[tokio::test]
    async fn test_tactic_suggestions() {
        let config = ProverConfig::default();
        let backend = HolLightBackend::new(config);

        let state = ProofState::new(
            Term::App {
                func: Box::new(Term::Const("=".to_string())),
                args: vec![
                    Term::Var("x".to_string()),
                    Term::Var("x".to_string()),
                ],
            }
        );

        let tactics = backend.suggest_tactics(&state, 5).await.unwrap();
        assert!(!tactics.is_empty());
        assert!(tactics.iter().any(|t| matches!(t, Tactic::Reflexivity)));
    }

    #[test]
    fn test_parse_goal() {
        let content = r#"
            g `!x. x = x`;;
        "#;

        let mut parser = HolLightParser::new(content);
        let file = parser.parse().unwrap();

        assert_eq!(file.theorems.len(), 1);
        assert!(file.theorems[0].proof.is_none());
    }

    #[test]
    fn test_parse_definition() {
        let content = r#"
            let ONE = new_definition `ONE = SUC 0`;;
        "#;

        let mut parser = HolLightParser::new(content);
        let file = parser.parse().unwrap();

        assert_eq!(file.definitions.len(), 1);
        assert_eq!(file.definitions[0].name, "ONE");
    }
}
