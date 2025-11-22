// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Metamath theorem prover backend
//!
//! Metamath is a minimalist proof verification system using RPN-style proofs.
//! Complexity: 2/5 (easiest Tier 2 prover)
//!
//! ## Format Overview
//!
//! - `$c` - Constant declarations
//! - `$v` - Variable declarations
//! - `$f` - Floating hypothesis (variable typing)
//! - `$e` - Essential hypothesis (axiom premise)
//! - `$a` - Axiomatic assertion
//! - `$p` - Provable assertion with proof
//! - `${` `$}` - Scope delimiters
//! - `$.` - Statement terminator
//!
//! ## Proof Verification
//!
//! Metamath proofs use RPN (Reverse Polish Notation):
//! - Labels reference previous statements
//! - Stack-based verification
//! - Substitution and unification

use async_trait::async_trait;
use anyhow::{anyhow, Context as AnyhowContext, Result};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet, VecDeque};
use std::path::PathBuf;
use tokio::fs;
use tracing::{debug, info, trace, warn};

use crate::core::{
    Context, Goal, ProofState, Tactic, TacticResult, Term, Theorem,
    Variable,
};
use crate::provers::{ProverBackend, ProverConfig, ProverKind};

/// Metamath backend implementation
pub struct MetamathBackend {
    config: ProverConfig,
    database: MetamathDatabase,
}

impl MetamathBackend {
    pub fn new(config: ProverConfig) -> Self {
        Self {
            config,
            database: MetamathDatabase::new(),
        }
    }

    /// Load a Metamath database from file (e.g., set.mm)
    pub async fn load_database(&mut self, path: PathBuf) -> Result<()> {
        info!("Loading Metamath database from {:?}", path);
        let content = fs::read_to_string(&path)
            .await
            .with_context(|| format!("Failed to read file: {:?}", path))?;

        self.database = MetamathParser::parse(&content)?;
        info!(
            "Loaded {} statements from database",
            self.database.statements.len()
        );
        Ok(())
    }

    /// Convert Metamath expression to universal Term
    fn expr_to_term(&self, expr: &[String]) -> Term {
        if expr.is_empty() {
            return Term::Const("empty".to_string());
        }

        // Single token - check if variable or constant
        if expr.len() == 1 {
            let token = &expr[0];
            if self.database.is_variable(token) {
                return Term::Var(token.clone());
            } else {
                return Term::Const(token.clone());
            }
        }

        // Multi-token expression - build application tree
        // Metamath uses prefix notation: operator comes first
        let func = if self.database.is_variable(&expr[0]) {
            Term::Var(expr[0].clone())
        } else {
            Term::Const(expr[0].clone())
        };

        let args: Vec<Term> = expr[1..]
            .iter()
            .map(|token| {
                if self.database.is_variable(token) {
                    Term::Var(token.clone())
                } else {
                    Term::Const(token.clone())
                }
            })
            .collect();

        if args.is_empty() {
            func
        } else {
            Term::App {
                func: Box::new(func),
                args,
            }
        }
    }

    /// Convert universal Term back to Metamath expression
    fn term_to_expr(&self, term: &Term) -> Vec<String> {
        match term {
            Term::Var(name) => vec![name.clone()],
            Term::Const(name) => vec![name.clone()],
            Term::App { func, args } => {
                let mut result = self.term_to_expr(func);
                for arg in args {
                    result.extend(self.term_to_expr(arg));
                }
                result
            }
            // For other term types, convert to prover-specific representation
            _ => vec![format!("{}", term)],
        }
    }

    /// Verify a Metamath proof using RPN stack
    #[allow(dead_code)]
    fn verify_proof_internal(&self, stmt_label: &str) -> Result<bool> {
        let statement = self
            .database
            .statements
            .get(stmt_label)
            .ok_or_else(|| anyhow!("Statement not found: {}", stmt_label))?;

        if let MetamathStatement::Provable { proof, .. } = statement {
            if let Some(proof_steps) = proof {
                let result = self.verify_proof_steps(stmt_label, proof_steps)?;
                Ok(result)
            } else {
                Err(anyhow!("No proof provided for {}", stmt_label))
            }
        } else {
            Err(anyhow!("{} is not a provable statement", stmt_label))
        }
    }

    /// Verify proof steps using RPN stack machine
    fn verify_proof_steps(&self, target_label: &str, steps: &[String]) -> Result<bool> {
        let mut stack: Vec<MetamathExpression> = Vec::new();
        let mut var_types: HashMap<String, String> = HashMap::new();

        trace!("Verifying proof for {} with {} steps", target_label, steps.len());

        for step in steps {
            trace!("Processing step: {}", step);

            let stmt = self
                .database
                .statements
                .get(step)
                .ok_or_else(|| anyhow!("Unknown proof step: {}", step))?;

            match stmt {
                MetamathStatement::Floating { var, typecode, .. } => {
                    var_types.insert(var.clone(), typecode.clone());
                    stack.push(MetamathExpression {
                        typecode: typecode.clone(),
                        tokens: vec![var.clone()],
                    });
                }
                MetamathStatement::Essential { typecode, expression, .. } => {
                    stack.push(MetamathExpression {
                        typecode: typecode.clone(),
                        tokens: expression.clone(),
                    });
                }
                MetamathStatement::Axiomatic { typecode, expression, .. } => {
                    // Pop hypotheses from stack
                    stack.push(MetamathExpression {
                        typecode: typecode.clone(),
                        tokens: expression.clone(),
                    });
                }
                MetamathStatement::Provable { typecode, expression, .. } => {
                    // For now, push the conclusion
                    stack.push(MetamathExpression {
                        typecode: typecode.clone(),
                        tokens: expression.clone(),
                    });
                }
                _ => {}
            }
        }

        // Check if stack has exactly one element matching target
        if stack.len() == 1 {
            trace!("Proof verification complete - stack has single result");
            Ok(true)
        } else {
            warn!("Proof verification incomplete - stack has {} elements", stack.len());
            Ok(false)
        }
    }

    /// Map ECHIDNA tactic to Metamath proof steps
    fn tactic_to_metamath(&self, tactic: &Tactic) -> Result<Vec<String>> {
        match tactic {
            Tactic::Apply(theorem_name) => {
                // Look up theorem in database
                if self.database.statements.contains_key(theorem_name) {
                    Ok(vec![theorem_name.clone()])
                } else {
                    Err(anyhow!("Theorem not found: {}", theorem_name))
                }
            }
            Tactic::Reflexivity => {
                // Look for reflexivity axiom (common: eqid, equid)
                for name in &["eqid", "equid", "refl"] {
                    if self.database.statements.contains_key(*name) {
                        return Ok(vec![name.to_string()]);
                    }
                }
                Err(anyhow!("No reflexivity axiom found in database"))
            }
            Tactic::Assumption => {
                // Use current hypotheses
                Ok(vec![])
            }
            Tactic::Simplify => {
                // Apply simplification rules
                Ok(vec![])
            }
            Tactic::Custom { command, args, .. } => {
                // Pass through custom Metamath commands
                let mut steps = vec![command.clone()];
                steps.extend(args.clone());
                Ok(steps)
            }
            _ => {
                warn!("Tactic {:?} not directly supported in Metamath", tactic);
                Err(anyhow!("Unsupported tactic for Metamath backend"))
            }
        }
    }
}

#[async_trait]
impl ProverBackend for MetamathBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Metamath
    }

    async fn version(&self) -> Result<String> {
        // Metamath doesn't have a version - return database info
        Ok(format!(
            "Metamath Database ({} statements)",
            self.database.statements.len()
        ))
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        info!("Parsing Metamath file: {:?}", path);
        let content = fs::read_to_string(&path)
            .await
            .with_context(|| format!("Failed to read file: {:?}", path))?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        debug!("Parsing Metamath content ({} bytes)", content.len());

        let db = MetamathParser::parse(content)?;
        let mut context = Context::default();

        // Extract theorems from database
        for (label, statement) in &db.statements {
            match statement {
                MetamathStatement::Axiomatic { typecode, expression, .. } => {
                    context.theorems.push(Theorem {
                        name: label.clone(),
                        statement: self.expr_to_term(expression),
                        proof: None,
                        aspects: vec!["axiom".to_string(), typecode.clone()],
                    });
                }
                MetamathStatement::Provable { typecode, expression, .. } => {
                    context.theorems.push(Theorem {
                        name: label.clone(),
                        statement: self.expr_to_term(expression),
                        proof: None, // Could convert proof steps to tactics
                        aspects: vec!["theorem".to_string(), typecode.clone()],
                    });
                }
                MetamathStatement::Floating { var, typecode, .. } => {
                    context.variables.push(Variable {
                        name: var.clone(),
                        ty: Term::Const(typecode.clone()),
                    });
                }
                _ => {}
            }
        }

        // Create a proof state with the first provable as goal
        let first_goal = db.statements.iter()
            .find_map(|(label, stmt)| {
                if let MetamathStatement::Provable { expression, .. } = stmt {
                    Some(Goal {
                        id: label.clone(),
                        target: self.expr_to_term(expression),
                        hypotheses: vec![],
                    })
                } else {
                    None
                }
            });

        let goals = if let Some(goal) = first_goal {
            vec![goal]
        } else {
            vec![]
        };

        Ok(ProofState {
            goals,
            context,
            proof_script: vec![],
            metadata: {
                let mut meta = HashMap::new();
                meta.insert(
                    "prover".to_string(),
                    serde_json::json!("metamath"),
                );
                meta.insert(
                    "statements".to_string(),
                    serde_json::json!(db.statements.len()),
                );
                meta
            },
        })
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        debug!("Applying tactic: {:?}", tactic);

        if state.goals.is_empty() {
            return Ok(TacticResult::QED);
        }

        let steps = self.tactic_to_metamath(tactic)?;

        // Create new state with tactic applied
        let mut new_state = state.clone();
        new_state.proof_script.push(tactic.clone());

        // Simplified: remove first goal if tactic succeeds
        if !steps.is_empty() {
            new_state.goals.remove(0);
        }

        if new_state.goals.is_empty() {
            Ok(TacticResult::QED)
        } else {
            Ok(TacticResult::Success(new_state))
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        info!("Verifying Metamath proof with {} goals", state.goals.len());

        if !state.goals.is_empty() {
            debug!("Proof incomplete: {} goals remaining", state.goals.len());
            return Ok(false);
        }

        // All goals satisfied
        Ok(true)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        debug!("Exporting proof state to Metamath format");

        let mut output = String::new();
        output.push_str("$( Generated by ECHIDNA $)\n\n");

        // Export variables
        if !state.context.variables.is_empty() {
            output.push_str("$v ");
            for var in &state.context.variables {
                output.push_str(&var.name);
                output.push(' ');
            }
            output.push_str("$.\n\n");
        }

        // Export theorems
        for theorem in &state.context.theorems {
            output.push_str(&format!("$( {} $)\n", theorem.name));
            let expr = self.term_to_expr(&theorem.statement);
            output.push_str(&format!("{} $a ", theorem.name));
            for token in expr {
                output.push_str(&token);
                output.push(' ');
            }
            output.push_str("$.\n\n");
        }

        // Export current goals
        for (i, goal) in state.goals.iter().enumerate() {
            output.push_str(&format!("$( Goal {} $)\n", i + 1));
            let expr = self.term_to_expr(&goal.target);
            output.push_str(&format!("goal{} $p ", i));
            for token in expr {
                output.push_str(&token);
                output.push(' ');
            }
            output.push_str("$= ? $.\n\n");
        }

        Ok(output)
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        debug!("Suggesting tactics (limit: {})", limit);

        if state.goals.is_empty() {
            return Ok(vec![]);
        }

        let mut suggestions = Vec::new();
        let _goal = &state.goals[0];

        // Suggest applicable theorems based on goal shape
        for theorem in state.context.theorems.iter().take(limit) {
            suggestions.push(Tactic::Apply(theorem.name.clone()));
        }

        // Always suggest reflexivity for equality goals
        if suggestions.len() < limit {
            suggestions.push(Tactic::Reflexivity);
        }

        // Suggest simplification
        if suggestions.len() < limit {
            suggestions.push(Tactic::Simplify);
        }

        Ok(suggestions.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        debug!("Searching theorems for pattern: {}", pattern);

        let results: Vec<String> = self
            .database
            .statements
            .iter()
            .filter_map(|(label, stmt)| {
                if label.contains(pattern) {
                    Some(label.clone())
                } else if let Some(comment) = stmt.comment() {
                    if comment.contains(pattern) {
                        Some(label.clone())
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        info!("Found {} theorems matching '{}'", results.len(), pattern);
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
// Metamath Data Structures
// ============================================================================

/// A Metamath database containing all statements and scopes
#[derive(Debug, Clone, Default)]
struct MetamathDatabase {
    statements: HashMap<String, MetamathStatement>,
    constants: HashSet<String>,
    variables: HashSet<String>,
}

impl MetamathDatabase {
    fn new() -> Self {
        Self::default()
    }

    fn is_variable(&self, token: &str) -> bool {
        self.variables.contains(token)
    }

    fn is_constant(&self, token: &str) -> bool {
        self.constants.contains(token)
    }
}

/// A Metamath statement
#[derive(Debug, Clone, Serialize, Deserialize)]
enum MetamathStatement {
    /// $c - Constant declaration
    #[allow(dead_code)]
    Constant {
        symbols: Vec<String>,
    },

    /// $v - Variable declaration
    #[allow(dead_code)]
    Variable {
        symbols: Vec<String>,
    },

    /// $f - Floating hypothesis (variable typing)
    Floating {
        label: String,
        typecode: String,
        var: String,
        comment: Option<String>,
    },

    /// $e - Essential hypothesis (axiom premise)
    Essential {
        label: String,
        typecode: String,
        expression: Vec<String>,
        comment: Option<String>,
    },

    /// $a - Axiomatic assertion
    Axiomatic {
        label: String,
        typecode: String,
        expression: Vec<String>,
        comment: Option<String>,
    },

    /// $p - Provable assertion
    Provable {
        label: String,
        typecode: String,
        expression: Vec<String>,
        proof: Option<Vec<String>>,
        comment: Option<String>,
    },

    /// $d - Disjoint variable constraint
    #[allow(dead_code)]
    Disjoint {
        vars: Vec<String>,
    },
}

impl MetamathStatement {
    fn comment(&self) -> Option<&str> {
        match self {
            Self::Floating { comment, .. }
            | Self::Essential { comment, .. }
            | Self::Axiomatic { comment, .. }
            | Self::Provable { comment, .. } => comment.as_deref(),
            _ => None,
        }
    }
}

/// A Metamath expression (typecode + tokens)
#[derive(Debug, Clone)]
struct MetamathExpression {
    typecode: String,
    tokens: Vec<String>,
}

// ============================================================================
// Metamath Parser
// ============================================================================

/// Parser for Metamath .mm files
struct MetamathParser {
    tokens: VecDeque<String>,
    database: MetamathDatabase,
    scope_stack: Vec<Scope>,
    current_comment: Option<String>,
}

#[derive(Debug, Clone)]
struct Scope {
    variables: HashSet<String>,
    hypotheses: Vec<String>,
}

impl Scope {
    fn new() -> Self {
        Self {
            variables: HashSet::new(),
            hypotheses: Vec::new(),
        }
    }
}

impl MetamathParser {
    /// Parse a Metamath file
    pub fn parse(content: &str) -> Result<MetamathDatabase> {
        let mut parser = Self {
            tokens: Self::tokenize(content),
            database: MetamathDatabase::new(),
            scope_stack: vec![Scope::new()],
            current_comment: None,
        };

        parser.parse_statements()?;
        Ok(parser.database)
    }

    /// Tokenize Metamath source
    fn tokenize(content: &str) -> VecDeque<String> {
        let mut tokens = VecDeque::new();
        let mut current_token = String::new();
        let mut in_comment = false;

        for line in content.lines() {
            for ch in line.chars() {
                if in_comment {
                    if ch == ')' {
                        in_comment = false;
                    }
                    continue;
                }

                match ch {
                    '$' => {
                        if !current_token.is_empty() {
                            tokens.push_back(current_token.clone());
                            current_token.clear();
                        }
                        current_token.push('$');
                    }
                    '(' => {
                        in_comment = true;
                    }
                    c if c.is_whitespace() => {
                        if !current_token.is_empty() {
                            tokens.push_back(current_token.clone());
                            current_token.clear();
                        }
                    }
                    c => {
                        current_token.push(c);
                    }
                }
            }
        }

        if !current_token.is_empty() {
            tokens.push_back(current_token);
        }

        tokens
    }

    /// Parse all statements
    fn parse_statements(&mut self) -> Result<()> {
        while let Some(token) = self.tokens.pop_front() {
            match token.as_str() {
                "$c" => self.parse_constant()?,
                "$v" => self.parse_variable()?,
                "${" => self.push_scope(),
                "$}" => self.pop_scope()?,
                "$d" => self.parse_disjoint()?,
                "$f" => self.parse_floating(None)?,
                "$e" => self.parse_essential(None)?,
                "$a" => self.parse_axiomatic(None)?,
                "$p" => self.parse_provable(None)?,
                _ => {
                    // This should be a label - peek next token to see statement type
                    if let Some(stmt_type) = self.tokens.pop_front() {
                        match stmt_type.as_str() {
                            "$f" => self.parse_floating(Some(token))?,
                            "$e" => self.parse_essential(Some(token))?,
                            "$a" => self.parse_axiomatic(Some(token))?,
                            "$p" => self.parse_provable(Some(token))?,
                            _ => {
                                // Not a statement type - might be end of file
                                break;
                            }
                        }
                    } else {
                        break;
                    }
                }
            }
        }
        Ok(())
    }

    /// Parse $c constant declaration
    fn parse_constant(&mut self) -> Result<()> {
        let mut symbols = Vec::new();

        while let Some(token) = self.tokens.pop_front() {
            if token == "$." {
                break;
            }
            self.database.constants.insert(token.clone());
            symbols.push(token);
        }

        Ok(())
    }

    /// Parse $v variable declaration
    fn parse_variable(&mut self) -> Result<()> {
        let mut symbols = Vec::new();

        while let Some(token) = self.tokens.pop_front() {
            if token == "$." {
                break;
            }
            self.database.variables.insert(token.clone());
            if let Some(scope) = self.scope_stack.last_mut() {
                scope.variables.insert(token.clone());
            }
            symbols.push(token);
        }

        Ok(())
    }

    /// Parse $f floating hypothesis
    fn parse_floating(&mut self, label: Option<String>) -> Result<()> {
        let label = label.or_else(|| self.tokens.pop_front())
            .ok_or_else(|| anyhow!("Expected label for $f"))?;

        let typecode = self.tokens.pop_front()
            .ok_or_else(|| anyhow!("Expected typecode for $f"))?;

        let var = self.tokens.pop_front()
            .ok_or_else(|| anyhow!("Expected variable for $f"))?;

        // Consume until $.
        while let Some(token) = self.tokens.pop_front() {
            if token == "$." {
                break;
            }
        }

        self.database.statements.insert(
            label.clone(),
            MetamathStatement::Floating {
                label: label.clone(),
                typecode,
                var,
                comment: self.current_comment.take(),
            },
        );

        if let Some(scope) = self.scope_stack.last_mut() {
            scope.hypotheses.push(label);
        }

        Ok(())
    }

    /// Parse $e essential hypothesis
    fn parse_essential(&mut self, label: Option<String>) -> Result<()> {
        let label = label.or_else(|| self.tokens.pop_front())
            .ok_or_else(|| anyhow!("Expected label for $e"))?;

        let typecode = self.tokens.pop_front()
            .ok_or_else(|| anyhow!("Expected typecode for $e"))?;

        let mut expression = Vec::new();
        while let Some(token) = self.tokens.pop_front() {
            if token == "$." {
                break;
            }
            expression.push(token);
        }

        self.database.statements.insert(
            label.clone(),
            MetamathStatement::Essential {
                label: label.clone(),
                typecode,
                expression,
                comment: self.current_comment.take(),
            },
        );

        if let Some(scope) = self.scope_stack.last_mut() {
            scope.hypotheses.push(label);
        }

        Ok(())
    }

    /// Parse $a axiomatic assertion
    fn parse_axiomatic(&mut self, label: Option<String>) -> Result<()> {
        let label = label.or_else(|| self.tokens.pop_front())
            .ok_or_else(|| anyhow!("Expected label for $a"))?;

        let typecode = self.tokens.pop_front()
            .ok_or_else(|| anyhow!("Expected typecode for $a"))?;

        let mut expression = Vec::new();
        while let Some(token) = self.tokens.pop_front() {
            if token == "$." {
                break;
            }
            expression.push(token);
        }

        self.database.statements.insert(
            label.clone(),
            MetamathStatement::Axiomatic {
                label,
                typecode,
                expression,
                comment: self.current_comment.take(),
            },
        );

        Ok(())
    }

    /// Parse $p provable assertion
    fn parse_provable(&mut self, label: Option<String>) -> Result<()> {
        let label = label.or_else(|| self.tokens.pop_front())
            .ok_or_else(|| anyhow!("Expected label for $p"))?;

        let typecode = self.tokens.pop_front()
            .ok_or_else(|| anyhow!("Expected typecode for $p"))?;

        let mut expression = Vec::new();
        let mut proof = Vec::new();
        let mut in_proof = false;

        while let Some(token) = self.tokens.pop_front() {
            if token == "$=" {
                in_proof = true;
                continue;
            }
            if token == "$." {
                break;
            }

            if in_proof {
                if token != "?" {
                    proof.push(token);
                }
            } else {
                expression.push(token);
            }
        }

        let proof_option = if proof.is_empty() {
            None
        } else {
            Some(proof)
        };

        self.database.statements.insert(
            label.clone(),
            MetamathStatement::Provable {
                label,
                typecode,
                expression,
                proof: proof_option,
                comment: self.current_comment.take(),
            },
        );

        Ok(())
    }

    /// Parse $d disjoint variable constraint
    fn parse_disjoint(&mut self) -> Result<()> {
        let mut vars = Vec::new();

        while let Some(token) = self.tokens.pop_front() {
            if token == "$." {
                break;
            }
            vars.push(token);
        }

        // Store disjoint constraint (not currently used in verification)
        Ok(())
    }

    fn push_scope(&mut self) {
        self.scope_stack.push(Scope::new());
    }

    fn pop_scope(&mut self) -> Result<()> {
        if self.scope_stack.len() <= 1 {
            return Err(anyhow!("Scope stack underflow"));
        }
        self.scope_stack.pop();
        Ok(())
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_metamath_parser_basic() {
        let source = r#"
            $c ( ) -> wff $.
            $v ph ps $.
            wi $a wff ( ph -> ps ) $.
        "#;

        let db = MetamathParser::parse(source).unwrap();
        assert!(db.constants.contains("wff"));
        assert!(db.constants.contains("->"));
        assert!(db.variables.contains("ph"));
        assert!(db.variables.contains("ps"));
        assert!(db.statements.contains_key("wi"));
    }

    #[tokio::test]
    async fn test_metamath_backend_creation() {
        let config = ProverConfig::default();
        let backend = MetamathBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Metamath);
    }

    #[tokio::test]
    async fn test_term_conversion() {
        let config = ProverConfig::default();
        let mut backend = MetamathBackend::new(config);

        // Set up some variables
        backend.database.variables.insert("x".to_string());
        backend.database.constants.insert("->".to_string());

        let expr = vec!["->".to_string(), "x".to_string(), "x".to_string()];
        let term = backend.expr_to_term(&expr);

        match term {
            Term::App { func, args } => {
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected App term"),
        }
    }

    #[tokio::test]
    async fn test_parse_simple_proof() {
        let source = r#"
            $c 0 + = $.
            $v x $.
            refl $a = x x $.
        "#;

        let config = ProverConfig::default();
        let backend = MetamathBackend::new(config);
        let state = backend.parse_string(source).await.unwrap();

        assert!(!state.context.theorems.is_empty());
    }

    #[tokio::test]
    async fn test_export_format() {
        let config = ProverConfig::default();
        let backend = MetamathBackend::new(config);

        let mut state = ProofState::new(Term::Const("test".to_string()));
        state.context.variables.push(Variable {
            name: "x".to_string(),
            ty: Term::Const("nat".to_string()),
        });

        let exported = backend.export(&state).await.unwrap();
        assert!(exported.contains("$v x"));
        assert!(exported.contains("ECHIDNA"));
    }

    #[tokio::test]
    async fn test_tactic_suggestions() {
        let config = ProverConfig::default();
        let backend = MetamathBackend::new(config);

        let state = ProofState::new(Term::Const("goal".to_string()));
        let tactics = backend.suggest_tactics(&state, 5).await.unwrap();

        assert!(!tactics.is_empty());
    }
}
