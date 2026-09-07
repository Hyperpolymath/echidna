// SPDX-License-Identifier: AGPL-3.0-or-later
//! Dafny auto-active verification backend
#![allow(dead_code)]
use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};
use anyhow::{Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

pub struct DafnyBackend {
    config: ProverConfig,
}

impl DafnyBackend {
    pub fn new(config: ProverConfig) -> Self {
        DafnyBackend { config }
    }

    /// Generate a minimal valid Dafny program with assertions for the goal and axioms.
    fn to_input_format(&self, state: &ProofState) -> Result<String> {
        let mut s =
            String::from("// SPDX-License-Identifier: AGPL-3.0-or-later\nmethod EchidnaGoal() {\n");

        // Add axioms as assume statements
        for (i, ax) in state.context.axioms.iter().enumerate() {
            s.push_str(&format!("  assume ax_{}: {};\n", i, ax));
        }

        // Add the goal as an assert
        if let Some(g) = state.goals.first() {
            let goal_expr = self.term_to_dafny_expr(&g.target);
            s.push_str(&format!("  assert {};\n", goal_expr));
        }

        s.push_str("}\n");
        Ok(s)
    }

    /// Convert a Term to a Dafny-compatible expression.
    fn term_to_dafny_expr(&self, term: &Term) -> String {
        match term {
            Term::Const(name) => name.clone(),
            Term::Var(name) => name.clone(),
            Term::App { func, args } => {
                let f = self.term_to_dafny_expr(func);
                let a = args
                    .iter()
                    .map(|arg| self.term_to_dafny_expr(arg))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({})", f, a)
            },
            Term::Pi {
                param,
                param_type,
                body,
            } => {
                let t = self.term_to_dafny_expr(param_type);
                let b = self.term_to_dafny_expr(body);
                format!("forall {}: {} :: {}", param, t, b)
            },
            Term::Lambda {
                param,
                param_type,
                body,
            } => {
                let t = param_type
                    .as_ref()
                    .map(|x| self.term_to_dafny_expr(x))
                    .unwrap_or_else(|| "?".to_string());
                let b = self.term_to_dafny_expr(body);
                format!("(({}: {}) => {})", param, t, b)
            },
            _ => "true".to_string(),
        }
    }

    /// Parse Dafny output: check for verification success.
    fn parse_result(&self, output: &str) -> Result<bool> {
        let l = output.to_lowercase();
        if l.contains("verified")
            || l.contains("successful")
            || l.contains("dafny program verifier finished with 0 errors")
        {
            Ok(true)
        } else if l.contains("error")
            || l.contains("failed")
            || l.contains("inconclusive")
            || l.contains("verification might not have been performed")
        {
            Ok(false)
        } else {
            Err(anyhow::anyhow!("Dafny inconclusive"))
        }
    }

    /// Extract named declarations (method, lemma, function, predicate) from Dafny source.
    fn extract_declarations(&self, content: &str) -> Vec<String> {
        let mut results = Vec::new();
        for line in content.lines() {
            let l = line.trim();
            // Check if line starts with declaration keyword
            for keyword in &["method ", "lemma ", "function ", "predicate "] {
                if l.starts_with(keyword) {
                    // Extract identifier after keyword
                    if let Some(rest) = l.strip_prefix(keyword) {
                        // Get the first word (identifier)
                        if let Some(ident) = rest
                            .split_whitespace()
                            .next()
                            .and_then(|w| w.split('(').next())
                        {
                            if !ident.is_empty() {
                                results.push(ident.to_string());
                            }
                        }
                    }
                    break;
                }
            }
        }
        results
    }

    /// Simple scan for ensures clauses in Dafny source.
    fn extract_ensures_goals(&self, content: &str) -> Vec<Goal> {
        let mut goals = Vec::new();

        for line in content.lines() {
            if line.contains("ensures") {
                // Extract the ensures clause content (simple heuristic)
                if let Some(ensures_start) = line.find("ensures") {
                    let rest = &line[ensures_start + 7..].trim();
                    // Find the end: either ; or { or newline
                    let goal_text = rest.split([';', '{', '\n']).next().unwrap_or(rest).trim();
                    if !goal_text.is_empty() {
                        goals.push(Goal {
                            id: format!("goal_{}", goals.len()),
                            target: Term::Const(goal_text.to_string()),
                            hypotheses: vec![],
                        });
                    }
                }
            }
        }

        goals
    }
}
#[async_trait]
impl ProverBackend for DafnyBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Dafny
    }
    async fn version(&self) -> Result<String> {
        let o = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await?;
        Ok(String::from_utf8_lossy(&o.stdout)
            .lines()
            .next()
            .unwrap_or("unknown")
            .to_string())
    }
    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = super::bounded_read_proof_file(&path).await?;
        let mut state = self.parse_string(&content).await?;
        state.metadata.insert(
            "source_path".to_string(),
            serde_json::Value::String(path.to_string_lossy().into_owned()),
        );
        Ok(state)
    }
    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let mut state = ProofState::default();
        state.metadata.insert(
            "dafny_source".to_string(),
            serde_json::Value::String(content.to_string()),
        );

        // Extract ensures clauses first
        let ensures_goals = self.extract_ensures_goals(content);
        if !ensures_goals.is_empty() {
            state.goals = ensures_goals;
            return Ok(state);
        }

        // If no ensures clauses, try to extract method/lemma/function/predicate declarations
        let decls = self.extract_declarations(content);
        if !decls.is_empty() {
            for decl in decls {
                state.goals.push(Goal {
                    id: format!("goal_{}", decl),
                    target: Term::Const("true".to_string()),
                    hypotheses: vec![],
                });
            }
            return Ok(state);
        }

        // Fallback: ensure at least one goal
        state.goals.push(Goal {
            id: "goal_0".to_string(),
            target: Term::Const("true".to_string()),
            hypotheses: vec![],
        });

        Ok(state)
    }
    async fn apply_tactic(&self, _: &ProofState, _: &Tactic) -> Result<TacticResult> {
        Err(anyhow::anyhow!(
            "Dafny: auto-active, no interactive tactics"
        ))
    }
    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        // If source_path is provided, use it directly
        if let Some(path) = state.metadata.get("source_path").and_then(|v| v.as_str()) {
            let output = tokio::time::timeout(
                tokio::time::Duration::from_secs(self.config.timeout + 5),
                Command::new(&self.config.executable)
                    .arg("verify")
                    .arg(path)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .output(),
            )
            .await
            .context("Dafny timed out")??;
            return self.parse_result(&format!(
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }

        // Otherwise, get the source content (from dafny_source or generate it)
        let input = if let Some(src) = state.metadata.get("dafny_source").and_then(|v| v.as_str()) {
            src.to_string()
        } else {
            self.to_input_format(state)?
        };

        // Write to a temp file (Dafny requires a .dfy file, not stdin)
        let temp_file = tempfile::NamedTempFile::new().context("Failed to create temp file")?;
        let temp_path = temp_file.path().to_path_buf();

        // Write content to the temp file
        tokio::fs::write(&temp_path, input.as_bytes())
            .await
            .context("Failed to write Dafny source to temp file")?;

        // Run Dafny on the temp file
        let output = tokio::time::timeout(
            tokio::time::Duration::from_secs(self.config.timeout + 5),
            Command::new(&self.config.executable)
                .arg("verify")
                .arg(&temp_path)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output(),
        )
        .await
        .context("Dafny timed out")??;

        self.parse_result(&format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    }
    async fn export(&self, state: &ProofState) -> Result<String> {
        self.to_input_format(state)
    }
    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut suggestions = Vec::new();

        if state.goals.is_empty() {
            return Ok(suggestions);
        }

        let goal = &state.goals[0];

        // Add general tactics
        suggestions.push(Tactic::Simplify);

        // Dafny-specific custom tactics
        suggestions.push(Tactic::Custom {
            prover: "dafny".to_string(),
            command: "assert".to_string(),
            args: vec![],
        });

        suggestions.push(Tactic::Custom {
            prover: "dafny".to_string(),
            command: "calc".to_string(),
            args: vec![],
        });

        suggestions.push(Tactic::Custom {
            prover: "dafny".to_string(),
            command: "lemma".to_string(),
            args: vec![],
        });

        suggestions.push(Tactic::Custom {
            prover: "dafny".to_string(),
            command: "decreases".to_string(),
            args: vec![],
        });

        // Heuristic: if goal contains quantifiers, suggest intro tactics
        match &goal.target {
            Term::Pi { .. } => {
                suggestions.push(Tactic::Custom {
                    prover: "dafny".to_string(),
                    command: "forall".to_string(),
                    args: vec![],
                });
            },
            Term::Const(s) if s.contains("forall") || s.contains("exists") => {
                suggestions.push(Tactic::Custom {
                    prover: "dafny".to_string(),
                    command: "forall".to_string(),
                    args: vec![],
                });
            },
            _ => {},
        }

        Ok(
            crate::provers::gnn_augment_tactics(&self.config, state, "dafny", suggestions, limit)
                .await,
        )
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        // Dafny doesn't have a standard theorem search command.
        // Return empty for now; could be enhanced with file parsing.
        Ok(Vec::new())
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
    async fn test_dafny_export() {
        let b = DafnyBackend::new(ProverConfig {
            executable: PathBuf::from("dafny"),
            timeout: 10,
            ..Default::default()
        });
        let mut s = ProofState::default();
        s.goals.push(Goal {
            id: "g".to_string(),
            target: Term::Const("true".to_string()),
            hypotheses: vec![],
        });
        assert!(b.to_input_format(&s).unwrap().contains("Goal"));
    }
    #[tokio::test]
    async fn test_dafny_parse() {
        let b = DafnyBackend::new(ProverConfig {
            executable: PathBuf::from("dafny"),
            timeout: 10,
            ..Default::default()
        });
        let s = b.parse_string("method M() {}").await.unwrap();
        assert!(!s.goals.is_empty());
    }
    #[test]
    fn test_dafny_result() {
        let b = DafnyBackend::new(ProverConfig {
            executable: PathBuf::from("dafny"),
            timeout: 10,
            ..Default::default()
        });
        assert!(b.parse_result("Dafny program verified").unwrap());
    }
}
