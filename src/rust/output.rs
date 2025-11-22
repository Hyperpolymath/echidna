// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Output formatting module for CLI
//!
//! Provides JSON and pretty-printed text output with colors

use anyhow::Result;
use colored::Colorize;
use echidna::core::ProofState;
use serde::Serialize;
use std::fmt::Display;
use std::str::FromStr;

/// Output format options
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutputFormat {
    Text,
    Json,
}

impl FromStr for OutputFormat {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self> {
        match s.to_lowercase().as_str() {
            "text" => Ok(OutputFormat::Text),
            "json" => Ok(OutputFormat::Json),
            _ => Err(anyhow::anyhow!("Invalid output format: {}. Must be 'text' or 'json'", s)),
        }
    }
}

impl Display for OutputFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OutputFormat::Text => write!(f, "text"),
            OutputFormat::Json => write!(f, "json"),
        }
    }
}

/// Output formatter for different output formats
pub struct OutputFormatter {
    format: OutputFormat,
}

impl OutputFormatter {
    pub fn new(format: OutputFormat) -> Self {
        Self { format }
    }

    /// Output a success message
    pub fn success(&self, message: &str) -> Result<()> {
        match self.format {
            OutputFormat::Text => {
                println!("{}", message.green().bold());
            }
            OutputFormat::Json => {
                self.output_json(&JsonMessage {
                    level: "success",
                    message,
                })?;
            }
        }
        Ok(())
    }

    /// Output an error message
    pub fn error(&self, message: &str) -> Result<()> {
        match self.format {
            OutputFormat::Text => {
                eprintln!("{}", message.red().bold());
            }
            OutputFormat::Json => {
                self.output_json(&JsonMessage {
                    level: "error",
                    message,
                })?;
            }
        }
        Ok(())
    }

    /// Output a warning message
    pub fn warning(&self, message: &str) -> Result<()> {
        match self.format {
            OutputFormat::Text => {
                println!("{}", message.yellow());
            }
            OutputFormat::Json => {
                self.output_json(&JsonMessage {
                    level: "warning",
                    message,
                })?;
            }
        }
        Ok(())
    }

    /// Output an info message
    pub fn info(&self, message: &str) -> Result<()> {
        match self.format {
            OutputFormat::Text => {
                println!("{}", message);
            }
            OutputFormat::Json => {
                self.output_json(&JsonMessage {
                    level: "info",
                    message,
                })?;
            }
        }
        Ok(())
    }

    /// Output a section header
    pub fn header(&self, title: &str) -> Result<()> {
        match self.format {
            OutputFormat::Text => {
                println!("\n{}", title.bold().underline());
                println!("{}", "=".repeat(title.len()));
            }
            OutputFormat::Json => {
                self.output_json(&JsonMessage {
                    level: "header",
                    message: title,
                })?;
            }
        }
        Ok(())
    }

    /// Output a section title
    pub fn section(&self, title: &str) -> Result<()> {
        match self.format {
            OutputFormat::Text => {
                println!("\n{}", title.cyan().bold());
            }
            OutputFormat::Json => {
                self.output_json(&JsonMessage {
                    level: "section",
                    message: title,
                })?;
            }
        }
        Ok(())
    }

    /// Output a result item
    pub fn result(&self, item: &str) -> Result<()> {
        match self.format {
            OutputFormat::Text => {
                println!("{}", item);
            }
            OutputFormat::Json => {
                self.output_json(&JsonMessage {
                    level: "result",
                    message: item,
                })?;
            }
        }
        Ok(())
    }

    /// Output a proof state
    pub fn output_proof_state(&self, state: &ProofState) -> Result<()> {
        match self.format {
            OutputFormat::Text => {
                self.output_proof_state_text(state)?;
            }
            OutputFormat::Json => {
                self.output_json(state)?;
            }
        }
        Ok(())
    }

    /// Output proof state in text format
    fn output_proof_state_text(&self, state: &ProofState) -> Result<()> {
        println!();
        println!("{}", "Proof State".cyan().bold());
        println!("{}", "===========".cyan());
        println!();

        // Goals
        if state.goals.is_empty() {
            println!("{}", "✓ No goals remaining (QED)".green().bold());
        } else {
            println!("{} ({}):", "Goals".yellow().bold(), state.goals.len());
            for (i, goal) in state.goals.iter().enumerate() {
                println!("\n  Goal {}: {}", i + 1, goal.id.bright_blue());

                // Hypotheses
                if !goal.hypotheses.is_empty() {
                    println!("  Hypotheses:");
                    for hyp in &goal.hypotheses {
                        println!("    {}: {}", hyp.name.cyan(), hyp.ty);
                    }
                }

                // Target
                println!("  {}", "Target:".yellow());
                println!("    {}", goal.target);
            }
        }

        println!();

        // Context
        if !state.context.theorems.is_empty() {
            println!("{} ({}):", "Available Theorems".magenta().bold(), state.context.theorems.len());
            for theorem in state.context.theorems.iter().take(10) {
                print!("  - {}", theorem.name.bright_magenta());
                if !theorem.aspects.is_empty() {
                    print!(" [{}]", theorem.aspects.join(", ").dimmed());
                }
                println!();
            }
            if state.context.theorems.len() > 10 {
                println!("  ... and {} more", state.context.theorems.len() - 10);
            }
            println!();
        }

        // Proof script
        if !state.proof_script.is_empty() {
            println!("{} ({} steps):", "Proof Script".green().bold(), state.proof_script.len());
            for (i, tactic) in state.proof_script.iter().enumerate() {
                println!("  {}. {:?}", i + 1, tactic);
            }
            println!();
        }

        Ok(())
    }

    /// Output JSON
    fn output_json<T: Serialize>(&self, data: &T) -> Result<()> {
        let json = serde_json::to_string_pretty(data)?;
        println!("{}", json);
        Ok(())
    }
}

#[derive(Serialize)]
struct JsonMessage<'a> {
    level: &'a str,
    message: &'a str,
}
