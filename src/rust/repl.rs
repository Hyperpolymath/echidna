// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Interactive REPL for theorem proving
//!
//! Provides a read-eval-print loop for interactive proof development

use anyhow::{Context, Result};
use colored::Colorize;
use echidna::core::{ProofState, Tactic, TacticResult};
use echidna::{ProverBackend, ProverConfig, ProverKind};
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use std::path::PathBuf;

/// REPL state
pub struct ReplState {
    prover: Box<dyn ProverBackend>,
    proof_state: Option<ProofState>,
    history: Vec<String>,
    current_file: Option<PathBuf>,
}

impl ReplState {
    pub fn new(prover: Box<dyn ProverBackend>) -> Self {
        Self {
            prover,
            proof_state: None,
            history: Vec::new(),
            current_file: None,
        }
    }
}

/// Start the interactive REPL
pub async fn start_repl(
    file: Option<PathBuf>,
    prover_kind: Option<ProverKind>,
    neural: bool,
) -> Result<()> {
    // Determine prover
    let kind = if let Some(k) = prover_kind {
        k
    } else if let Some(ref f) = file {
        echidna::provers::ProverFactory::detect_from_file(f)
            .ok_or_else(|| anyhow::anyhow!("Could not detect prover from file. Use --prover"))?
    } else {
        // Default to Agda
        ProverKind::Agda
    };

    // Create configuration
    let mut config = ProverConfig::default();
    config.neural_enabled = neural;

    // Create prover
    let prover = echidna::provers::ProverFactory::create(kind, config)
        .context("Failed to create prover backend")?;

    let mut repl_state = ReplState::new(prover);

    // Load initial file if provided
    if let Some(path) = file {
        match load_file(&mut repl_state, &path).await {
            Ok(_) => {
                println!("{}", format!("✓ Loaded proof file: {}", path.display()).green());
            }
            Err(e) => {
                eprintln!("{}", format!("✗ Failed to load file: {}", e).red());
            }
        }
    }

    // Print welcome message
    print_welcome(kind);

    // Create readline editor
    let mut rl = DefaultEditor::new()?;

    // Main REPL loop
    loop {
        let prompt = create_prompt(&repl_state);
        let readline = rl.readline(&prompt);

        match readline {
            Ok(line) => {
                let line = line.trim();

                if line.is_empty() {
                    continue;
                }

                rl.add_history_entry(line)?;

                // Handle command
                match handle_command(&mut repl_state, line).await {
                    Ok(should_continue) => {
                        if !should_continue {
                            break;
                        }
                    }
                    Err(e) => {
                        eprintln!("{}", format!("Error: {}", e).red());
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                eprintln!("Error: {:?}", err);
                break;
            }
        }
    }

    println!("{}", "Goodbye!".cyan());

    Ok(())
}

/// Print welcome message
fn print_welcome(prover: ProverKind) {
    println!("{}", "╔═══════════════════════════════════════════════════════════╗".cyan());
    println!("{}", "║  ECHIDNA Interactive Proof Assistant                     ║".cyan().bold());
    println!("{}", "╚═══════════════════════════════════════════════════════════╝".cyan());
    println!();
    println!("Active prover: {}", format!("{:?}", prover).green().bold());
    println!();
    println!("{}", "Commands:".yellow().bold());
    println!("  :load <file>       - Load a proof file");
    println!("  :state             - Show current proof state");
    println!("  :goals             - Show current goals");
    println!("  :context           - Show available theorems");
    println!("  :suggest [n]       - Get tactic suggestions (default: 5)");
    println!("  :apply <tactic>    - Apply a tactic");
    println!("  :search <pattern>  - Search theorems");
    println!("  :switch <prover>   - Switch to different prover");
    println!("  :export            - Export current proof");
    println!("  :help              - Show this help");
    println!("  :quit              - Exit REPL");
    println!();
    println!("Type a tactic directly to apply it, or use commands starting with ':'");
    println!();
}

/// Create prompt string
fn create_prompt(state: &ReplState) -> String {
    let prover = format!("{:?}", state.prover.kind());
    let goal_count = state.proof_state
        .as_ref()
        .map(|s| s.goals.len())
        .unwrap_or(0);

    if goal_count == 0 {
        format!("{}> ", prover.green())
    } else {
        format!("{}[{}]> ", prover.cyan(), goal_count.to_string().yellow())
    }
}

/// Handle a REPL command
async fn handle_command(state: &mut ReplState, input: &str) -> Result<bool> {
    // Check if it's a command (starts with :)
    if input.starts_with(':') {
        handle_meta_command(state, input).await
    } else {
        // Treat as tactic
        handle_tactic(state, input).await?;
        Ok(true)
    }
}

/// Handle meta-commands (starting with :)
async fn handle_meta_command(state: &mut ReplState, input: &str) -> Result<bool> {
    let parts: Vec<&str> = input[1..].split_whitespace().collect();

    if parts.is_empty() {
        return Ok(true);
    }

    let command = parts[0].to_lowercase();
    let args = &parts[1..];

    match command.as_str() {
        "quit" | "exit" | "q" => {
            return Ok(false);
        }

        "help" | "h" => {
            print_welcome(state.prover.kind());
        }

        "load" | "l" => {
            if args.is_empty() {
                eprintln!("{}", "Usage: :load <file>".red());
            } else {
                let path = PathBuf::from(args.join(" "));
                load_file(state, &path).await?;
                println!("{}", format!("✓ Loaded: {}", path.display()).green());
            }
        }

        "state" | "s" => {
            show_proof_state(state)?;
        }

        "goals" | "g" => {
            show_goals(state)?;
        }

        "context" | "c" => {
            show_context(state)?;
        }

        "suggest" => {
            let limit = args.get(0)
                .and_then(|s| s.parse().ok())
                .unwrap_or(5);
            suggest_tactics(state, limit).await?;
        }

        "apply" | "a" => {
            if args.is_empty() {
                eprintln!("{}", "Usage: :apply <tactic>".red());
            } else {
                let tactic_str = args.join(" ");
                handle_tactic(state, &tactic_str).await?;
            }
        }

        "search" => {
            if args.is_empty() {
                eprintln!("{}", "Usage: :search <pattern>".red());
            } else {
                let pattern = args.join(" ");
                search_theorems(state, &pattern).await?;
            }
        }

        "switch" => {
            if args.is_empty() {
                eprintln!("{}", "Usage: :switch <prover>".red());
            } else {
                eprintln!("{}", "Prover switching not yet implemented".yellow());
            }
        }

        "export" | "e" => {
            export_proof(state).await?;
        }

        _ => {
            eprintln!("{}", format!("Unknown command: {}", command).red());
            println!("Type :help for available commands");
        }
    }

    Ok(true)
}

/// Load a proof file
async fn load_file(state: &mut ReplState, path: &PathBuf) -> Result<()> {
    let proof_state = state.prover.parse_file(path.clone()).await
        .context("Failed to parse file")?;

    state.proof_state = Some(proof_state);
    state.current_file = Some(path.clone());

    Ok(())
}

/// Show current proof state
fn show_proof_state(state: &ReplState) -> Result<()> {
    if let Some(proof_state) = &state.proof_state {
        println!();
        println!("{}", "Proof State".cyan().bold());
        println!("{}", "===========".cyan());

        if proof_state.is_complete() {
            println!();
            println!("{}", "✓ Proof complete! (QED)".green().bold());
        } else {
            println!();
            println!("Goals: {}", proof_state.goals.len());
            println!("Tactics applied: {}", proof_state.proof_script.len());
            println!("Theorems available: {}", proof_state.context.theorems.len());
        }

        println!();
    } else {
        println!("{}", "No proof loaded. Use :load <file>".yellow());
    }

    Ok(())
}

/// Show current goals
fn show_goals(state: &ReplState) -> Result<()> {
    if let Some(proof_state) = &state.proof_state {
        if proof_state.goals.is_empty() {
            println!("{}", "✓ No goals remaining".green().bold());
            return Ok(());
        }

        println!();
        for (i, goal) in proof_state.goals.iter().enumerate() {
            println!("{} {}:", "Goal".yellow().bold(), (i + 1).to_string().bright_blue());
            println!();

            if !goal.hypotheses.is_empty() {
                println!("  {}:", "Hypotheses".cyan());
                for hyp in &goal.hypotheses {
                    println!("    {}: {}", hyp.name.bright_cyan(), hyp.ty);
                }
                println!();
            }

            println!("  {}:", "Target".yellow());
            println!("    {}", goal.target);
            println!();
        }
    } else {
        println!("{}", "No proof loaded. Use :load <file>".yellow());
    }

    Ok(())
}

/// Show available context
fn show_context(state: &ReplState) -> Result<()> {
    if let Some(proof_state) = &state.proof_state {
        println!();
        println!("{}", "Available Theorems".magenta().bold());
        println!();

        if proof_state.context.theorems.is_empty() {
            println!("  (none)");
        } else {
            for (i, theorem) in proof_state.context.theorems.iter().enumerate().take(20) {
                print!("  {}. {}", i + 1, theorem.name.bright_magenta());
                if !theorem.aspects.is_empty() {
                    print!(" [{}]", theorem.aspects.join(", ").dimmed());
                }
                println!();
            }

            if proof_state.context.theorems.len() > 20 {
                println!();
                println!("  ... and {} more", proof_state.context.theorems.len() - 20);
            }
        }

        println!();
    } else {
        println!("{}", "No proof loaded. Use :load <file>".yellow());
    }

    Ok(())
}

/// Get tactic suggestions
async fn suggest_tactics(state: &mut ReplState, limit: usize) -> Result<()> {
    if let Some(proof_state) = &state.proof_state {
        if proof_state.is_complete() {
            println!("{}", "Proof already complete!".green().bold());
            return Ok(());
        }

        println!();
        println!("{}", "Suggested Tactics:".cyan().bold());
        println!();

        let suggestions = state.prover.suggest_tactics(proof_state, limit).await?;

        if suggestions.is_empty() {
            println!("  (no suggestions)");
        } else {
            for (i, tactic) in suggestions.iter().enumerate() {
                println!("  {}. {:?}", i + 1, tactic);
            }
        }

        println!();
    } else {
        println!("{}", "No proof loaded. Use :load <file>".yellow());
    }

    Ok(())
}

/// Handle applying a tactic
async fn handle_tactic(state: &mut ReplState, tactic_str: &str) -> Result<()> {
    if state.proof_state.is_none() {
        println!("{}", "No proof loaded. Use :load <file>".yellow());
        return Ok(());
    }

    // Parse tactic from string (simplified)
    let tactic = parse_tactic(tactic_str)?;

    let proof_state = state.proof_state.as_ref().unwrap();

    println!();
    println!("{}", format!("Applying: {:?}", tactic).dimmed());

    let result = state.prover.apply_tactic(proof_state, &tactic).await?;

    match result {
        TacticResult::Success(new_state) => {
            println!("{}", "✓ Tactic succeeded".green());
            state.proof_state = Some(new_state);
            state.history.push(tactic_str.to_string());

            if state.proof_state.as_ref().unwrap().is_complete() {
                println!();
                println!("{}", "🎉 Proof complete! (QED)".green().bold());
            } else {
                let goals = state.proof_state.as_ref().unwrap().goals.len();
                println!("{}", format!("Goals remaining: {}", goals).cyan());
            }
        }

        TacticResult::Error(msg) => {
            println!("{}", format!("✗ Tactic failed: {}", msg).red());
        }

        TacticResult::QED => {
            println!();
            println!("{}", "🎉 Proof complete! (QED)".green().bold());
            state.proof_state.as_mut().unwrap().goals.clear();
        }
    }

    println!();

    Ok(())
}

/// Parse a tactic from string (simplified parser)
fn parse_tactic(s: &str) -> Result<Tactic> {
    let parts: Vec<&str> = s.split_whitespace().collect();

    if parts.is_empty() {
        return Err(anyhow::anyhow!("Empty tactic"));
    }

    let command = parts[0].to_lowercase();
    let args = &parts[1..];

    match command.as_str() {
        "apply" => {
            if args.is_empty() {
                Err(anyhow::anyhow!("apply requires a theorem name"))
            } else {
                Ok(Tactic::Apply(args.join(" ")))
            }
        }

        "intro" => {
            Ok(Tactic::Intro(args.get(0).map(|s| s.to_string())))
        }

        "rewrite" => {
            if args.is_empty() {
                Err(anyhow::anyhow!("rewrite requires a theorem name"))
            } else {
                Ok(Tactic::Rewrite(args.join(" ")))
            }
        }

        "simpl" | "simplify" => {
            Ok(Tactic::Simplify)
        }

        "refl" | "reflexivity" => {
            Ok(Tactic::Reflexivity)
        }

        "assumption" | "auto" => {
            Ok(Tactic::Assumption)
        }

        _ => {
            // Try to parse as custom tactic
            Ok(Tactic::Custom {
                prover: "unknown".to_string(),
                command: parts[0].to_string(),
                args: args.iter().map(|s| s.to_string()).collect(),
            })
        }
    }
}

/// Search for theorems
async fn search_theorems(state: &ReplState, pattern: &str) -> Result<()> {
    println!();
    println!("{}", format!("Searching for: {}", pattern).cyan());
    println!();

    let results = state.prover.search_theorems(pattern).await?;

    if results.is_empty() {
        println!("  (no results)");
    } else {
        for (i, result) in results.iter().enumerate().take(20) {
            println!("  {}. {}", i + 1, result);
        }

        if results.len() > 20 {
            println!();
            println!("  ... and {} more results", results.len() - 20);
        }
    }

    println!();

    Ok(())
}

/// Export current proof
async fn export_proof(state: &ReplState) -> Result<()> {
    if let Some(proof_state) = &state.proof_state {
        let exported = state.prover.export(proof_state).await?;

        println!();
        println!("{}", "Exported Proof:".cyan().bold());
        println!("{}", "==============".cyan());
        println!();
        println!("{}", exported);
        println!();
    } else {
        println!("{}", "No proof loaded. Use :load <file>".yellow());
    }

    Ok(())
}
