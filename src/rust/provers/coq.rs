// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Coq theorem prover backend implementation
//!
//! Integrates with Coq via SerAPI (sertop) for programmatic interaction.
//! Supports parsing .v files, executing tactics, and proof verification.

use async_trait::async_trait;
use anyhow::{anyhow, Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, Command};
use tokio::sync::Mutex;

use crate::core::{
    Context as ProofContext, Definition, Goal, ProofState, Tactic, TacticResult, Term, Theorem,
};
use crate::provers::{ProverBackend, ProverConfig, ProverKind};

/// Coq theorem prover backend
pub struct CoqBackend {
    config: ProverConfig,
    session: Mutex<Option<CoqSession>>,
}

/// Active Coq session with sertop process
struct CoqSession {
    process: Child,
    state_id: usize,
    cmd_counter: usize,
}

/// S-expression representation for SerAPI
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
enum SExp {
    Atom(String),
    List(Vec<SExp>),
}

impl SExp {
    fn atom(s: &str) -> Self {
        SExp::Atom(s.to_string())
    }

    fn list(items: Vec<SExp>) -> Self {
        SExp::List(items)
    }

    fn to_string_repr(&self) -> String {
        match self {
            SExp::Atom(s) => {
                if s.contains(|c: char| c.is_whitespace() || "()[]{}".contains(c)) {
                    format!("\"{}\"", s.replace('"', "\\\""))
                } else {
                    s.clone()
                }
            }
            SExp::List(items) => {
                let inner = items
                    .iter()
                    .map(|i| i.to_string_repr())
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("({})", inner)
            }
        }
    }

    fn parse(input: &str) -> Result<Self> {
        let mut tokens = tokenize(input)?;
        parse_sexp(&mut tokens)
    }
}

fn tokenize(input: &str) -> Result<Vec<String>> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut in_string = false;
    let mut escape = false;

    for ch in input.chars() {
        if escape {
            current.push(ch);
            escape = false;
        } else if ch == '\\' && in_string {
            escape = true;
            current.push(ch);
        } else if ch == '"' {
            current.push(ch);
            in_string = !in_string;
        } else if in_string {
            current.push(ch);
        } else if ch == '(' || ch == ')' {
            if !current.is_empty() {
                tokens.push(current.clone());
                current.clear();
            }
            tokens.push(ch.to_string());
        } else if ch.is_whitespace() {
            if !current.is_empty() {
                tokens.push(current.clone());
                current.clear();
            }
        } else {
            current.push(ch);
        }
    }

    if !current.is_empty() {
        tokens.push(current);
    }

    Ok(tokens)
}

fn parse_sexp(tokens: &mut Vec<String>) -> Result<SExp> {
    if tokens.is_empty() {
        return Err(anyhow!("Unexpected end of input"));
    }

    let token = tokens.remove(0);

    if token == "(" {
        let mut list = Vec::new();
        while !tokens.is_empty() && tokens[0] != ")" {
            list.push(parse_sexp(tokens)?);
        }
        if tokens.is_empty() {
            return Err(anyhow!("Unmatched opening parenthesis"));
        }
        tokens.remove(0); // Remove closing ')'
        Ok(SExp::List(list))
    } else if token == ")" {
        Err(anyhow!("Unexpected closing parenthesis"))
    } else {
        // Remove quotes from string literals
        let atom = if token.starts_with('"') && token.ends_with('"') && token.len() > 1 {
            token[1..token.len() - 1].to_string()
        } else {
            token
        };
        Ok(SExp::Atom(atom))
    }
}

impl CoqBackend {
    /// Create a new Coq backend with configuration
    pub fn new(config: ProverConfig) -> Self {
        CoqBackend {
            config,
            session: Mutex::new(None),
        }
    }

    /// Start a new sertop session
    async fn start_session(&self) -> Result<CoqSession> {
        let exe = if self.config.executable.as_os_str().is_empty() {
            "sertop"
        } else {
            self.config.executable.to_str().unwrap()
        };

        let mut cmd = Command::new(exe);
        cmd.arg("--printer=sertop")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        for arg in &self.config.args {
            cmd.arg(arg);
        }

        let process = cmd.spawn().context("Failed to start sertop process")?;

        Ok(CoqSession {
            process,
            state_id: 0,
            cmd_counter: 0,
        })
    }

    /// Get or create session
    async fn get_session(&self) -> Result<()> {
        let mut session_lock = self.session.lock().await;
        if session_lock.is_none() {
            *session_lock = Some(self.start_session().await?);
        }
        Ok(())
    }

    /// Send command to sertop and get response
    async fn send_command(&self, session: &mut CoqSession, cmd: SExp) -> Result<SExp> {
        let cmd_str = format!("{}\n", cmd.to_string_repr());

        // Get stdin and stdout from process
        let stdin = session
            .process
            .stdin
            .as_mut()
            .ok_or_else(|| anyhow!("No stdin"))?;
        let stdout = session
            .process
            .stdout
            .as_mut()
            .ok_or_else(|| anyhow!("No stdout"))?;

        // Write command
        stdin
            .write_all(cmd_str.as_bytes())
            .await
            .context("Failed to write command")?;
        stdin.flush().await.context("Failed to flush")?;

        // Read response
        let mut reader = BufReader::new(stdout);
        let mut response_line = String::new();
        reader
            .read_line(&mut response_line)
            .await
            .context("Failed to read response")?;

        SExp::parse(&response_line)
    }

    /// Execute a Coq command
    async fn exec_coq(&self, cmd: &str) -> Result<String> {
        self.get_session().await?;
        let mut session_lock = self.session.lock().await;
        let session = session_lock
            .as_mut()
            .ok_or_else(|| anyhow!("No active session"))?;

        session.cmd_counter += 1;

        // Build SerAPI Add command
        let add_cmd = SExp::list(vec![
            SExp::atom("Add"),
            SExp::list(vec![]),
            SExp::atom(&format!("\"{}\"", cmd.replace('"', "\\\""))),
        ]);

        let response = self.send_command(session, add_cmd).await?;

        // Parse response to extract any output or state info
        self.parse_add_response(response)
    }

    /// Parse Add command response
    fn parse_add_response(&self, resp: SExp) -> Result<String> {
        match resp {
            SExp::List(items) => {
                // Look for Answer or Feedback
                for item in items {
                    if let SExp::List(inner) = item {
                        if !inner.is_empty() {
                            if let SExp::Atom(tag) = &inner[0] {
                                if tag == "Answer" || tag == "Completed" {
                                    return Ok("OK".to_string());
                                } else if tag == "CoqExn" {
                                    return Err(anyhow!("Coq error: {:?}", inner));
                                }
                            }
                        }
                    }
                }
                Ok("OK".to_string())
            }
            _ => Ok("OK".to_string()),
        }
    }

    /// Parse a Coq file into AST
    fn parse_coq_file(&self, content: &str) -> Result<Vec<CoqStatement>> {
        let mut statements = Vec::new();
        let mut current = String::new();
        let mut in_comment = false;
        let mut in_string = false;

        let chars: Vec<char> = content.chars().collect();
        let mut i = 0;

        while i < chars.len() {
            let ch = chars[i];

            // Handle comments
            if !in_string && i + 1 < chars.len() && chars[i] == '(' && chars[i + 1] == '*' {
                in_comment = true;
                current.push(ch);
                i += 1;
                current.push(chars[i]);
                i += 1;
                continue;
            }

            if in_comment && i + 1 < chars.len() && chars[i] == '*' && chars[i + 1] == ')' {
                in_comment = false;
                current.push(ch);
                i += 1;
                current.push(chars[i]);
                i += 1;
                continue;
            }

            if in_comment {
                current.push(ch);
                i += 1;
                continue;
            }

            // Handle strings
            if ch == '"' && (i == 0 || chars[i - 1] != '\\') {
                in_string = !in_string;
            }

            current.push(ch);

            if !in_string && ch == '.' && (i + 1 >= chars.len() || chars[i + 1].is_whitespace())
            {
                // Statement end
                let stmt = current.trim().to_string();
                if !stmt.is_empty() && !stmt.starts_with("(*") {
                    if let Some(parsed) = self.parse_statement(&stmt)? {
                        statements.push(parsed);
                    }
                }
                current.clear();
            }

            i += 1;
        }

        Ok(statements)
    }

    /// Parse a single Coq statement
    fn parse_statement(&self, stmt: &str) -> Result<Option<CoqStatement>> {
        let stmt = stmt.trim();

        if stmt.starts_with("(*") {
            return Ok(None);
        }

        if stmt.starts_with("Theorem ")
            || stmt.starts_with("Lemma ")
            || stmt.starts_with("Example ")
        {
            return Ok(Some(self.parse_theorem(stmt)?));
        }

        if stmt.starts_with("Definition ") || stmt.starts_with("Fixpoint ") {
            return Ok(Some(self.parse_definition(stmt)?));
        }

        if stmt.starts_with("Inductive ") {
            return Ok(Some(self.parse_inductive(stmt)?));
        }

        if stmt.starts_with("Proof.") {
            return Ok(Some(CoqStatement::ProofStart));
        }

        if stmt.starts_with("Qed.") || stmt.starts_with("Defined.") || stmt.starts_with("Admitted.") {
            return Ok(Some(CoqStatement::ProofEnd));
        }

        // Otherwise it's a tactic
        Ok(Some(CoqStatement::Tactic(stmt.to_string())))
    }

    /// Parse a theorem declaration
    fn parse_theorem(&self, stmt: &str) -> Result<CoqStatement> {
        // Format: "Theorem name : type."
        let parts: Vec<&str> = stmt.split(':').collect();
        if parts.len() < 2 {
            return Err(anyhow!("Invalid theorem statement"));
        }

        let name_part = parts[0].trim();
        let name = name_part
            .split_whitespace()
            .nth(1)
            .ok_or_else(|| anyhow!("Missing theorem name"))?
            .to_string();

        let type_part = parts[1].trim().trim_end_matches('.');
        let ty = self.parse_term(type_part)?;

        Ok(CoqStatement::Theorem { name, ty })
    }

    /// Parse a definition
    fn parse_definition(&self, stmt: &str) -> Result<CoqStatement> {
        // Format: "Definition name := body." or "Definition name : type := body."
        let is_fixpoint = stmt.starts_with("Fixpoint");

        let parts: Vec<&str> = stmt.split(":=").collect();
        if parts.len() < 2 {
            return Err(anyhow!("Invalid definition"));
        }

        let left = parts[0].trim();
        let body_str = parts[1].trim().trim_end_matches('.');

        let name_and_type: Vec<&str> = left.split(':').collect();

        let name = if name_and_type.is_empty() {
            return Err(anyhow!("Missing definition name"));
        } else {
            let name_part = name_and_type[0].trim();
            name_part
                .split_whitespace()
                .nth(1)
                .ok_or_else(|| anyhow!("Missing name"))?
                .split('(')
                .next()
                .unwrap()
                .to_string()
        };

        let ty = if name_and_type.len() > 1 {
            Some(self.parse_term(name_and_type[1].trim())?)
        } else {
            None
        };

        let body = self.parse_term(body_str)?;

        Ok(CoqStatement::Definition {
            name,
            ty,
            body,
            is_fixpoint,
        })
    }

    /// Parse an inductive type
    fn parse_inductive(&self, stmt: &str) -> Result<CoqStatement> {
        // Simplified parser for inductive types
        // Format: "Inductive name : type := constructors."
        let name = stmt
            .split_whitespace()
            .nth(1)
            .ok_or_else(|| anyhow!("Missing inductive name"))?
            .split(':')
            .next()
            .unwrap()
            .to_string();

        Ok(CoqStatement::Inductive {
            name,
            constructors: vec![], // Simplified
        })
    }

    /// Parse a Coq term into universal Term representation
    fn parse_term(&self, input: &str) -> Result<Term> {
        let input = input.trim();

        // Handle forall (Pi type)
        if input.starts_with("forall ") {
            return self.parse_forall(input);
        }

        // Handle lambda
        if input.starts_with("fun ") {
            return self.parse_lambda(input);
        }

        // Handle application with parentheses
        if input.starts_with('(') && input.ends_with(')') {
            let inner = &input[1..input.len() - 1];
            return self.parse_term(inner);
        }

        // Handle binary operators
        if let Some(pos) = find_top_level_operator(input, "->") {
            let left = self.parse_term(&input[..pos])?;
            let right = self.parse_term(&input[pos + 2..])?;

            return Ok(Term::Pi {
                param: "_".to_string(),
                param_type: Box::new(left),
                body: Box::new(right),
            });
        }

        if let Some(pos) = find_top_level_operator(input, "/\\") {
            let left = self.parse_term(&input[..pos])?;
            let right = self.parse_term(&input[pos + 2..])?;

            return Ok(Term::App {
                func: Box::new(Term::Const("and".to_string())),
                args: vec![left, right],
            });
        }

        if let Some(pos) = find_top_level_operator(input, "\\/") {
            let left = self.parse_term(&input[..pos])?;
            let right = self.parse_term(&input[pos + 2..])?;

            return Ok(Term::App {
                func: Box::new(Term::Const("or".to_string())),
                args: vec![left, right],
            });
        }

        // Handle negation
        if input.starts_with('~') {
            let inner = self.parse_term(&input[1..])?;
            return Ok(Term::App {
                func: Box::new(Term::Const("not".to_string())),
                args: vec![inner],
            });
        }

        // Handle application (space-separated)
        if let Some(pos) = find_top_level_space(input) {
            let func_str = &input[..pos];
            let args_str = input[pos..].trim();

            let func = self.parse_term(func_str)?;
            let args = self.parse_args(args_str)?;

            return Ok(Term::App {
                func: Box::new(func),
                args,
            });
        }

        // Constants and variables
        if input == "Prop" || input == "Type" || input == "Set" {
            Ok(Term::Universe(0))
        } else if input.chars().next().map_or(false, |c| c.is_uppercase()) {
            Ok(Term::Const(input.to_string()))
        } else {
            Ok(Term::Var(input.to_string()))
        }
    }

    /// Parse forall (Pi type)
    fn parse_forall(&self, input: &str) -> Result<Term> {
        // Format: "forall x : A, B" or "forall x, B"
        let after_forall = input.strip_prefix("forall ").unwrap().trim();

        let comma_pos = after_forall
            .find(',')
            .ok_or_else(|| anyhow!("Invalid forall syntax"))?;

        let binding = after_forall[..comma_pos].trim();
        let body_str = after_forall[comma_pos + 1..].trim();

        let (param, param_type) = if binding.contains(':') {
            let parts: Vec<&str> = binding.split(':').collect();
            let param = parts[0].trim().to_string();
            let ty = self.parse_term(parts[1].trim())?;
            (param, ty)
        } else {
            (binding.to_string(), Term::Universe(0))
        };

        let body = self.parse_term(body_str)?;

        Ok(Term::Pi {
            param,
            param_type: Box::new(param_type),
            body: Box::new(body),
        })
    }

    /// Parse lambda
    fn parse_lambda(&self, input: &str) -> Result<Term> {
        // Format: "fun x : A => B" or "fun x => B"
        let after_fun = input.strip_prefix("fun ").unwrap().trim();

        let arrow_pos = after_fun
            .find("=>")
            .ok_or_else(|| anyhow!("Invalid lambda syntax"))?;

        let binding = after_fun[..arrow_pos].trim();
        let body_str = after_fun[arrow_pos + 2..].trim();

        let (param, param_type) = if binding.contains(':') {
            let parts: Vec<&str> = binding.split(':').collect();
            let param = parts[0].trim().to_string();
            let ty = self.parse_term(parts[1].trim())?;
            (param, Some(Box::new(ty)))
        } else {
            (binding.to_string(), None)
        };

        let body = self.parse_term(body_str)?;

        Ok(Term::Lambda {
            param,
            param_type,
            body: Box::new(body),
        })
    }

    /// Parse function arguments
    fn parse_args(&self, input: &str) -> Result<Vec<Term>> {
        // Simplified: split by spaces, accounting for parentheses
        let mut args = Vec::new();
        let mut current = String::new();
        let mut paren_depth = 0;

        for ch in input.chars() {
            match ch {
                '(' => {
                    paren_depth += 1;
                    current.push(ch);
                }
                ')' => {
                    paren_depth -= 1;
                    current.push(ch);
                }
                ' ' if paren_depth == 0 => {
                    if !current.is_empty() {
                        args.push(self.parse_term(&current)?);
                        current.clear();
                    }
                }
                _ => current.push(ch),
            }
        }

        if !current.is_empty() {
            args.push(self.parse_term(&current)?);
        }

        Ok(args)
    }

    /// Convert universal tactic to Coq-specific command
    fn tactic_to_coq(&self, tactic: &Tactic) -> String {
        match tactic {
            Tactic::Intro(Some(name)) => format!("intro {}.", name),
            Tactic::Intro(None) => "intro.".to_string(),
            Tactic::Apply(thm) => format!("apply {}.", thm),
            Tactic::Rewrite(thm) => format!("rewrite {}.", thm),
            Tactic::Reflexivity => "reflexivity.".to_string(),
            Tactic::Simplify => "simpl.".to_string(),
            Tactic::Assumption => "assumption.".to_string(),
            Tactic::Exact(term) => format!("exact {}.", term),
            Tactic::Cases(term) => format!("destruct {}.", term),
            Tactic::Induction(term) => format!("induction {}.", term),
            Tactic::Custom { command, args, .. } => {
                if args.is_empty() {
                    format!("{}.", command)
                } else {
                    format!("{} {}.", command, args.join(" "))
                }
            }
        }
    }

    /// Extract goals from current state
    async fn get_goals(&self) -> Result<Vec<Goal>> {
        self.get_session().await?;
        let mut session_lock = self.session.lock().await;
        let session = session_lock
            .as_mut()
            .ok_or_else(|| anyhow!("No active session"))?;

        // Send Query command to get goals
        let query_cmd = SExp::list(vec![
            SExp::atom("Query"),
            SExp::list(vec![]),
            SExp::atom("Goals"),
        ]);

        let response = self.send_command(session, query_cmd).await?;

        // Parse response to extract goals
        self.parse_goals_response(response)
    }

    /// Parse goals from SerAPI response
    fn parse_goals_response(&self, _resp: SExp) -> Result<Vec<Goal>> {
        // Simplified goal parsing
        // In a real implementation, this would parse the full S-expression
        // structure returned by SerAPI

        // For now, return a placeholder
        Ok(vec![])
    }

    /// Parse a Coq tactic string to universal Tactic
    fn parse_coq_tactic(&self, tactic_str: &str) -> Option<Tactic> {
        let tactic_str = tactic_str.trim().trim_end_matches('.');

        if tactic_str.starts_with("intro ") {
            let name = tactic_str.strip_prefix("intro ")?.trim().to_string();
            Some(Tactic::Intro(Some(name)))
        } else if tactic_str == "intro" || tactic_str.starts_with("intros") {
            Some(Tactic::Intro(None))
        } else if tactic_str.starts_with("apply ") {
            let thm = tactic_str.strip_prefix("apply ")?.trim().to_string();
            Some(Tactic::Apply(thm))
        } else if tactic_str.starts_with("rewrite ") {
            let thm = tactic_str.strip_prefix("rewrite ")?.trim().to_string();
            Some(Tactic::Rewrite(thm))
        } else if tactic_str == "reflexivity" {
            Some(Tactic::Reflexivity)
        } else if tactic_str == "simpl" {
            Some(Tactic::Simplify)
        } else if tactic_str == "assumption" {
            Some(Tactic::Assumption)
        } else if tactic_str.starts_with("exact ") {
            let term_str = tactic_str.strip_prefix("exact ")?.trim();
            let term = self.parse_term(term_str).ok()?;
            Some(Tactic::Exact(term))
        } else if tactic_str.starts_with("destruct ") {
            let term_str = tactic_str
                .strip_prefix("destruct ")?
                .split(" as")
                .next()?
                .trim();
            let term = self.parse_term(term_str).ok()?;
            Some(Tactic::Cases(term))
        } else if tactic_str.starts_with("induction ") {
            let term_str = tactic_str
                .strip_prefix("induction ")?
                .split(" as")
                .next()?
                .trim();
            let term = self.parse_term(term_str).ok()?;
            Some(Tactic::Induction(term))
        } else {
            // Custom tactic
            let parts: Vec<&str> = tactic_str.split_whitespace().collect();
            if parts.is_empty() {
                None
            } else {
                Some(Tactic::Custom {
                    prover: "coq".to_string(),
                    command: parts[0].to_string(),
                    args: parts[1..].iter().map(|s| s.to_string()).collect(),
                })
            }
        }
    }
}

/// Coq statement types
#[derive(Debug, Clone)]
enum CoqStatement {
    Theorem {
        name: String,
        ty: Term,
    },
    Definition {
        name: String,
        ty: Option<Term>,
        body: Term,
        is_fixpoint: bool,
    },
    Inductive {
        name: String,
        constructors: Vec<String>,
    },
    ProofStart,
    ProofEnd,
    Tactic(String),
}

/// Find top-level operator position
fn find_top_level_operator(input: &str, op: &str) -> Option<usize> {
    let mut depth = 0;
    let chars: Vec<char> = input.chars().collect();
    let op_chars: Vec<char> = op.chars().collect();

    for i in 0..chars.len() {
        match chars[i] {
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => {
                if depth == 0 && i + op_chars.len() <= chars.len() {
                    let slice: String = chars[i..i + op_chars.len()].iter().collect();
                    if slice == op {
                        return Some(i);
                    }
                }
            }
        }
    }

    None
}

/// Find top-level space position
fn find_top_level_space(input: &str) -> Option<usize> {
    let mut depth = 0;
    let chars: Vec<char> = input.chars().collect();

    for (i, &ch) in chars.iter().enumerate() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ' ' if depth == 0 && i > 0 => return Some(i),
            _ => {}
        }
    }

    None
}

#[async_trait]
impl ProverBackend for CoqBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Coq
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new("coqc")
            .arg("--version")
            .output()
            .await
            .context("Failed to get Coq version")?;

        let version = String::from_utf8_lossy(&output.stdout);
        Ok(version.lines().next().unwrap_or("unknown").to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
            .await
            .context("Failed to read file")?;

        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let statements = self.parse_coq_file(content)?;

        let mut context = ProofContext::default();
        let mut current_theorem: Option<(String, Term)> = None;
        let mut proof_tactics: Vec<Tactic> = Vec::new();
        let mut goals = Vec::new();

        for stmt in statements {
            match stmt {
                CoqStatement::Theorem { name, ty } => {
                    current_theorem = Some((name.clone(), ty.clone()));
                    goals.push(Goal {
                        id: format!("goal_{}", name),
                        target: ty,
                        hypotheses: vec![],
                    });
                }
                CoqStatement::Definition {
                    name,
                    ty,
                    body,
                    is_fixpoint: _,
                } => {
                    let def_type = ty.unwrap_or_else(|| Term::Universe(0));
                    context.definitions.push(Definition {
                        name,
                        ty: def_type,
                        body,
                    });
                }
                CoqStatement::Tactic(tactic_str) => {
                    // Convert Coq tactic string to universal tactic
                    if let Some(tactic) = self.parse_coq_tactic(&tactic_str) {
                        proof_tactics.push(tactic);
                    }
                }
                CoqStatement::ProofEnd => {
                    if let Some((name, statement)) = current_theorem.take() {
                        context.theorems.push(Theorem {
                            name,
                            statement,
                            proof: Some(proof_tactics.clone()),
                            aspects: vec![],
                        });
                        proof_tactics.clear();
                        goals.clear();
                    }
                }
                _ => {}
            }
        }

        Ok(ProofState {
            goals,
            context,
            proof_script: proof_tactics,
            metadata: HashMap::new(),
        })
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        let coq_cmd = self.tactic_to_coq(tactic);

        match self.exec_coq(&coq_cmd).await {
            Ok(_) => {
                // Get new goals
                let new_goals = self.get_goals().await.unwrap_or_default();

                let mut new_state = state.clone();
                new_state.goals = new_goals.clone();
                new_state.proof_script.push(tactic.clone());

                if new_goals.is_empty() {
                    Ok(TacticResult::QED)
                } else {
                    Ok(TacticResult::Success(new_state))
                }
            }
            Err(e) => Ok(TacticResult::Error(e.to_string())),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // Export the proof and try to check it
        let proof_script = self.export(state).await?;

        // Write to temporary file and check with coqc
        let temp_file = std::env::temp_dir().join("echidna_coq_verify.v");
        tokio::fs::write(&temp_file, proof_script)
            .await
            .context("Failed to write temp file")?;

        let output = Command::new("coqc")
            .arg(&temp_file)
            .output()
            .await
            .context("Failed to run coqc")?;

        Ok(output.status.success())
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();

        // Export definitions
        for def in &state.context.definitions {
            output.push_str(&format!(
                "Definition {} : {} := {}.\n\n",
                def.name, def.ty, def.body
            ));
        }

        // Export theorems
        for thm in &state.context.theorems {
            output.push_str(&format!("Theorem {} : {}.\n", thm.name, thm.statement));

            if let Some(proof) = &thm.proof {
                output.push_str("Proof.\n");
                for tactic in proof {
                    output.push_str("  ");
                    output.push_str(&self.tactic_to_coq(tactic));
                    output.push('\n');
                }
                output.push_str("Qed.\n\n");
            }
        }

        Ok(output)
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        // Use neural premise selection (placeholder)
        let mut suggestions = Vec::new();

        if state.goals.is_empty() {
            return Ok(suggestions);
        }

        let goal = &state.goals[0];

        // Simple heuristics for tactic suggestion
        match &goal.target {
            Term::Pi { .. } => {
                suggestions.push(Tactic::Intro(None));
            }
            Term::App { func, .. } => {
                if let Term::Const(name) = func.as_ref() {
                    match name.as_str() {
                        "and" => suggestions.push(Tactic::Custom {
                            prover: "coq".to_string(),
                            command: "split".to_string(),
                            args: vec![],
                        }),
                        "or" => {
                            suggestions.push(Tactic::Custom {
                                prover: "coq".to_string(),
                                command: "left".to_string(),
                                args: vec![],
                            });
                            suggestions.push(Tactic::Custom {
                                prover: "coq".to_string(),
                                command: "right".to_string(),
                                args: vec![],
                            });
                        }
                        "eq" => suggestions.push(Tactic::Reflexivity),
                        _ => {}
                    }
                }
            }
            _ => {}
        }

        // Add general tactics
        suggestions.push(Tactic::Simplify);
        suggestions.push(Tactic::Assumption);
        suggestions.push(Tactic::Custom {
            prover: "coq".to_string(),
            command: "auto".to_string(),
            args: vec![],
        });

        Ok(suggestions.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        // Use Coq's Search command
        let search_cmd = format!("Search {}.", pattern);
        let result = self.exec_coq(&search_cmd).await?;

        // Parse results (simplified)
        let theorems: Vec<String> = result
            .lines()
            .filter(|line| !line.is_empty())
            .map(|s| s.to_string())
            .collect();

        Ok(theorems)
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_parse_simple_theorem() {
        let backend = CoqBackend::new(ProverConfig::default());

        let code = r#"
Theorem identity : forall A : Prop, A -> A.
Proof.
  intros A H.
  exact H.
Qed.
        "#;

        let state = backend.parse_string(code).await.unwrap();

        assert_eq!(state.context.theorems.len(), 1);
        assert_eq!(state.context.theorems[0].name, "identity");
    }

    #[test]
    fn test_parse_term() {
        let backend = CoqBackend::new(ProverConfig::default());

        let term = backend.parse_term("A -> B").unwrap();
        assert!(matches!(term, Term::Pi { .. }));

        let term = backend.parse_term("forall A : Prop, A -> A").unwrap();
        assert!(matches!(term, Term::Pi { .. }));
    }

    #[test]
    fn test_sexp_parsing() {
        let sexp = SExp::parse("(Add () \"Definition x := 1.\")").unwrap();
        assert!(matches!(sexp, SExp::List(_)));

        let sexp_str = sexp.to_string_repr();
        assert!(sexp_str.contains("Add"));
    }

    #[test]
    fn test_tactic_conversion() {
        let backend = CoqBackend::new(ProverConfig::default());

        let tactic = Tactic::Intro(Some("H".to_string()));
        let coq_cmd = backend.tactic_to_coq(&tactic);
        assert_eq!(coq_cmd, "intro H.");

        let tactic = Tactic::Reflexivity;
        let coq_cmd = backend.tactic_to_coq(&tactic);
        assert_eq!(coq_cmd, "reflexivity.");
    }

    #[tokio::test]
    async fn test_version() {
        let backend = CoqBackend::new(ProverConfig::default());

        // This test will only pass if Coq is installed
        if let Ok(version) = backend.version().await {
            assert!(version.contains("Coq") || version.contains("version"));
        }
    }
}
