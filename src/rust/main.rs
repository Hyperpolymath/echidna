// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! ECHIDNA CLI - Main binary entry point
//!
//! Provides command-line interface, REPL, and HTTP server for theorem proving

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use colored::Colorize;
use echidna::{ProverConfig, ProverKind};
use indicatif::{ProgressBar, ProgressStyle};
use std::path::PathBuf;
use tracing::{info, warn};

mod repl;
mod server;
mod output;

use output::{OutputFormat, OutputFormatter};

/// ECHIDNA - Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance
#[derive(Parser)]
#[command(name = "echidna")]
#[command(version, about, long_about = None)]
#[command(author = "ECHIDNA Project Team")]
struct Cli {
    /// Output format (text, json)
    #[arg(long, global = true, default_value = "text")]
    format: OutputFormat,

    /// Verbose output
    #[arg(short, long, global = true)]
    verbose: bool,

    /// Disable colors
    #[arg(long, global = true)]
    no_color: bool,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Prove a theorem from file
    Prove {
        /// Path to proof file
        file: PathBuf,

        /// Prover to use (auto-detect if not specified)
        #[arg(short, long)]
        prover: Option<ProverKind>,

        /// Timeout in seconds
        #[arg(short, long, default_value = "300")]
        timeout: u64,

        /// Enable neural premise selection
        #[arg(long, default_value = "true")]
        neural: bool,

        /// Prover executable path (override default)
        #[arg(long)]
        executable: Option<PathBuf>,

        /// Library paths
        #[arg(long)]
        library: Vec<PathBuf>,
    },

    /// Verify an existing proof
    Verify {
        /// Path to proof file
        file: PathBuf,

        /// Prover to use (auto-detect if not specified)
        #[arg(short, long)]
        prover: Option<ProverKind>,

        /// Timeout in seconds
        #[arg(short, long, default_value = "300")]
        timeout: u64,

        /// Prover executable path (override default)
        #[arg(long)]
        executable: Option<PathBuf>,

        /// Library paths
        #[arg(long)]
        library: Vec<PathBuf>,
    },

    /// Search theorem libraries
    Search {
        /// Search pattern (regex supported)
        pattern: String,

        /// Prover to search (searches all if not specified)
        #[arg(short, long)]
        prover: Option<ProverKind>,

        /// Maximum results to return
        #[arg(short, long, default_value = "20")]
        limit: usize,
    },

    /// Start interactive REPL mode
    Interactive {
        /// Initial proof file to load
        file: Option<PathBuf>,

        /// Prover to use
        #[arg(short, long)]
        prover: Option<ProverKind>,

        /// Enable neural premise selection
        #[arg(long, default_value = "true")]
        neural: bool,
    },

    /// Start HTTP API server
    Server {
        /// Port to bind to
        #[arg(short, long, default_value = "8080")]
        port: u16,

        /// Host to bind to
        #[arg(long, default_value = "127.0.0.1")]
        host: String,

        /// Enable CORS
        #[arg(long)]
        cors: bool,
    },

    /// List available provers
    ListProvers {
        /// Show detailed information
        #[arg(short, long)]
        detailed: bool,
    },

    /// Show information about a specific prover
    Info {
        /// Prover name
        prover: ProverKind,
    },
}

#[tokio::main]
async fn main() -> Result<()> {
    // Parse CLI arguments
    let cli = Cli::parse();

    // Initialize tracing
    init_tracing(cli.verbose);

    // Disable colors if requested
    if cli.no_color {
        colored::control::set_override(false);
    }

    // Create output formatter
    let formatter = OutputFormatter::new(cli.format);

    // Execute command
    match cli.command {
        Commands::Prove {
            file,
            prover,
            timeout,
            neural,
            executable,
            library,
        } => {
            prove_command(file, prover, timeout, neural, executable, library, &formatter).await?;
        }

        Commands::Verify {
            file,
            prover,
            timeout,
            executable,
            library,
        } => {
            verify_command(file, prover, timeout, executable, library, &formatter).await?;
        }

        Commands::Search {
            pattern,
            prover,
            limit,
        } => {
            search_command(pattern, prover, limit, &formatter).await?;
        }

        Commands::Interactive {
            file,
            prover,
            neural,
        } => {
            interactive_command(file, prover, neural).await?;
        }

        Commands::Server { port, host, cors } => {
            server_command(port, host, cors).await?;
        }

        Commands::ListProvers { detailed } => {
            list_provers_command(detailed, &formatter)?;
        }

        Commands::Info { prover } => {
            info_command(prover, &formatter)?;
        }
    }

    Ok(())
}

/// Initialize tracing/logging
fn init_tracing(verbose: bool) {
    use tracing_subscriber::{fmt, prelude::*};
    use tracing_subscriber::filter::EnvFilter;

    let filter = if verbose {
        EnvFilter::new("echidna=debug,info")
    } else {
        EnvFilter::new("echidna=info,warn")
    };

    tracing_subscriber::registry()
        .with(filter)
        .with(fmt::layer())
        .init();
}

/// Prove command implementation
async fn prove_command(
    file: PathBuf,
    prover_kind: Option<ProverKind>,
    timeout: u64,
    neural: bool,
    executable: Option<PathBuf>,
    library: Vec<PathBuf>,
    formatter: &OutputFormatter,
) -> Result<()> {
    info!("Starting proof for: {}", file.display());

    // Detect or use specified prover
    let kind = detect_prover(prover_kind, &file)?;

    // Create prover configuration
    let config = create_config(kind, timeout, neural, executable, library)?;

    // Create prover backend
    let prover = echidna::provers::ProverFactory::create(kind, config)
        .context("Failed to create prover backend")?;

    // Show progress
    let pb = create_progress_bar("Parsing proof file...");

    // Parse the proof file
    let state = prover
        .parse_file(file.clone())
        .await
        .context("Failed to parse proof file")?;

    pb.set_message("Verifying proof...");

    // Verify the proof
    let result = prover
        .verify_proof(&state)
        .await
        .context("Failed to verify proof")?;

    pb.finish_and_clear();

    // Output result
    if result {
        formatter.success(&format!("✓ Proof verified successfully for {}", file.display()))?;
        formatter.output_proof_state(&state)?;
    } else {
        formatter.error(&format!("✗ Proof verification failed for {}", file.display()))?;
        formatter.output_proof_state(&state)?;
        std::process::exit(1);
    }

    Ok(())
}

/// Verify command implementation
async fn verify_command(
    file: PathBuf,
    prover_kind: Option<ProverKind>,
    timeout: u64,
    executable: Option<PathBuf>,
    library: Vec<PathBuf>,
    formatter: &OutputFormatter,
) -> Result<()> {
    info!("Verifying proof: {}", file.display());

    // Detect or use specified prover
    let kind = detect_prover(prover_kind, &file)?;

    // Create prover configuration
    let config = create_config(kind, timeout, true, executable, library)?;

    // Create prover backend
    let prover = echidna::provers::ProverFactory::create(kind, config)
        .context("Failed to create prover backend")?;

    // Show progress
    let pb = create_progress_bar("Parsing proof file...");

    // Parse the proof file
    let state = prover
        .parse_file(file.clone())
        .await
        .context("Failed to parse proof file")?;

    pb.set_message("Verifying proof...");

    // Verify the proof
    let result = prover
        .verify_proof(&state)
        .await
        .context("Failed to verify proof")?;

    pb.finish_and_clear();

    // Output result
    if result {
        formatter.success(&format!("✓ Proof is valid: {}", file.display()))?;

        // Show proof statistics
        formatter.info(&format!("Goals: {}", state.goals.len()))?;
        formatter.info(&format!("Tactics: {}", state.proof_script.len()))?;
        formatter.info(&format!("Theorems in context: {}", state.context.theorems.len()))?;
    } else {
        formatter.error(&format!("✗ Proof is invalid: {}", file.display()))?;
        std::process::exit(1);
    }

    Ok(())
}

/// Search command implementation
async fn search_command(
    pattern: String,
    prover_kind: Option<ProverKind>,
    limit: usize,
    formatter: &OutputFormatter,
) -> Result<()> {
    info!("Searching for: {}", pattern);

    let provers: Vec<ProverKind> = if let Some(kind) = prover_kind {
        vec![kind]
    } else {
        // Search all provers
        vec![
            ProverKind::Agda,
            ProverKind::Coq,
            ProverKind::Lean,
            ProverKind::Isabelle,
            ProverKind::Z3,
            ProverKind::CVC5,
            ProverKind::Metamath,
            ProverKind::HolLight,
            ProverKind::Mizar,
            ProverKind::PVS,
            ProverKind::ACL2,
            ProverKind::Hol4,
        ]
    };

    formatter.info(&format!("Searching {} prover(s) for pattern: {}", provers.len(), pattern))?;

    let mut total_results = 0;

    for kind in provers {
        let config = ProverConfig::default();

        if let Ok(prover) = echidna::provers::ProverFactory::create(kind, config) {
            formatter.section(&format!("\n{:?} Results:", kind))?;

            match prover.search_theorems(&pattern).await {
                Ok(results) => {
                    total_results += results.len();

                    for (i, result) in results.iter().take(limit).enumerate() {
                        formatter.result(&format!("  {}. {}", i + 1, result))?;
                    }

                    if results.len() > limit {
                        formatter.info(&format!("  ... and {} more results", results.len() - limit))?;
                    }
                }
                Err(e) => {
                    warn!("Failed to search {}: {}", kind, e);
                }
            }
        }
    }

    formatter.info(&format!("\nTotal results found: {}", total_results))?;

    Ok(())
}

/// Interactive REPL command
async fn interactive_command(
    file: Option<PathBuf>,
    prover_kind: Option<ProverKind>,
    neural: bool,
) -> Result<()> {
    info!("Starting interactive REPL mode");

    repl::start_repl(file, prover_kind, neural).await
}

/// HTTP Server command
async fn server_command(port: u16, host: String, cors: bool) -> Result<()> {
    info!("Starting HTTP server on {}:{}", host, port);

    server::start_server(port, host, cors).await
}

/// List provers command
fn list_provers_command(detailed: bool, formatter: &OutputFormatter) -> Result<()> {
    let provers = vec![
        ProverKind::Agda,
        ProverKind::Coq,
        ProverKind::Lean,
        ProverKind::Isabelle,
        ProverKind::Z3,
        ProverKind::CVC5,
        ProverKind::Metamath,
        ProverKind::HolLight,
        ProverKind::Mizar,
        ProverKind::PVS,
        ProverKind::ACL2,
        ProverKind::Hol4,
    ];

    formatter.header("Available Provers")?;
    formatter.info(&format!("Total: {} provers\n", provers.len()))?;

    for prover in provers {
        let tier = prover.tier();
        let complexity = prover.complexity();
        let time = prover.implementation_time();

        if detailed {
            formatter.section(&format!("{:?}", prover))?;
            formatter.info(&format!("  Tier: {}", tier))?;
            formatter.info(&format!("  Complexity: {}/5", complexity))?;
            formatter.info(&format!("  Implementation time: {} weeks", time))?;
            formatter.info("")?;
        } else {
            formatter.result(&format!(
                "{:12} - Tier {} | Complexity {}/5 | {} weeks",
                format!("{:?}", prover),
                tier,
                complexity,
                time
            ))?;
        }
    }

    if !detailed {
        formatter.info("\nUse --detailed flag for more information")?;
    }

    Ok(())
}

/// Info command - show detailed information about a prover
fn info_command(prover: ProverKind, formatter: &OutputFormatter) -> Result<()> {
    formatter.header(&format!("{:?} Prover Information", prover))?;
    formatter.info("")?;

    formatter.section("Classification")?;
    formatter.info(&format!("  Tier: {}", prover.tier()))?;
    formatter.info(&format!("  Complexity: {}/5", prover.complexity()))?;
    formatter.info(&format!("  Implementation time: {} weeks", prover.implementation_time()))?;
    formatter.info("")?;

    formatter.section("Description")?;
    let description = match prover {
        ProverKind::Agda => {
            "Dependently typed functional programming language and proof assistant.\n  \
             Original Quill prover. Strong type system with universe polymorphism."
        }
        ProverKind::Coq => {
            "Interactive theorem prover using the Calculus of Inductive Constructions.\n  \
             Widely used in formal verification and mathematics. Powerful tactic language."
        }
        ProverKind::Lean => {
            "Modern theorem prover and programming language with dependent types.\n  \
             Strong community, extensive mathlib. Excellent for formalized mathematics."
        }
        ProverKind::Isabelle => {
            "Generic proof assistant supporting multiple logics (mainly HOL).\n  \
             Powerful automation through Sledgehammer. Large Archive of Formal Proofs."
        }
        ProverKind::Z3 => {
            "High-performance SMT (Satisfiability Modulo Theories) solver.\n  \
             Excellent for automated reasoning in program verification."
        }
        ProverKind::CVC5 => {
            "Automatic SMT solver for first-order logic with theories.\n  \
             Strong support for quantifiers, datatypes, and strings."
        }
        ProverKind::Metamath => {
            "Ultra-minimal proof verification system with plain-text proofs.\n  \
             EASIEST to integrate (2/5 complexity). Large database of formalized mathematics."
        }
        ProverKind::HolLight => {
            "Simple, elegant HOL (Higher-Order Logic) proof assistant in OCaml.\n  \
             Part of the 'Big Six' theorem provers. Strong mathematical foundations."
        }
        ProverKind::Mizar => {
            "Proof assistant with natural-language-like proof style.\n  \
             Large Mathematical Library. Readable proof documents."
        }
        ProverKind::PVS => {
            "Specification and verification system for safety-critical systems.\n  \
             Strong support for dependent types and predicate subtyping."
        }
        ProverKind::ACL2 => {
            "Computational Logic for Applicative Common Lisp.\n  \
             Industrial-strength theorem prover for software/hardware verification."
        }
        ProverKind::Hol4 => {
            "Interactive theorem prover in the HOL family.\n  \
             Used extensively in hardware verification. ML-based tactic language."
        }
    };
    formatter.info(&format!("  {}", description))?;
    formatter.info("")?;

    formatter.section("File Extensions")?;
    let extension = match prover {
        ProverKind::Agda => ".agda",
        ProverKind::Coq => ".v",
        ProverKind::Lean => ".lean",
        ProverKind::Isabelle => ".thy",
        ProverKind::Z3 | ProverKind::CVC5 => ".smt2",
        ProverKind::Metamath => ".mm",
        ProverKind::HolLight => ".ml",
        ProverKind::Mizar => ".miz",
        ProverKind::PVS => ".pvs",
        ProverKind::ACL2 => ".lisp",
        ProverKind::Hol4 => ".sml",
    };
    formatter.info(&format!("  {}", extension))?;
    formatter.info("")?;

    formatter.section("Features")?;
    formatter.info("  ✓ Neural premise selection")?;
    formatter.info("  ✓ Aspect tagging")?;
    formatter.info("  ✓ OpenCyc integration")?;
    formatter.info("  ✓ Tactic suggestion")?;
    formatter.info("")?;

    // Try to get version if prover is installed
    let config = ProverConfig::default();
    if let Ok(prover_backend) = echidna::provers::ProverFactory::create(prover, config) {
        formatter.section("Installation")?;

        // Spawn async runtime to check version
        let version_check = tokio::task::spawn(async move {
            prover_backend.version().await
        });

        if let Ok(Ok(version)) = futures::executor::block_on(async { version_check.await }) {
            formatter.success(&format!("  ✓ Installed: {}", version))?;
        } else {
            formatter.warning("  ✗ Not detected (may not be installed or not in PATH)")?;
        }
    }

    Ok(())
}

/// Detect prover from file extension or use specified prover
fn detect_prover(prover_kind: Option<ProverKind>, file: &PathBuf) -> Result<ProverKind> {
    if let Some(kind) = prover_kind {
        return Ok(kind);
    }

    echidna::provers::ProverFactory::detect_from_file(file)
        .ok_or_else(|| anyhow::anyhow!(
            "Could not detect prover from file extension: {}. Please specify with --prover",
            file.display()
        ))
}

/// Create prover configuration
fn create_config(
    kind: ProverKind,
    timeout: u64,
    neural: bool,
    executable: Option<PathBuf>,
    library: Vec<PathBuf>,
) -> Result<ProverConfig> {
    let mut config = ProverConfig::default();
    config.timeout = timeout;
    config.neural_enabled = neural;

    if let Some(exec) = executable {
        config.executable = exec;
    } else {
        // Set default executable path based on prover
        config.executable = get_default_executable(kind);
    }

    if !library.is_empty() {
        config.library_paths = library;
    }

    Ok(config)
}

/// Get default executable path for a prover
fn get_default_executable(kind: ProverKind) -> PathBuf {
    match kind {
        ProverKind::Agda => PathBuf::from("agda"),
        ProverKind::Coq => PathBuf::from("coqtop"),
        ProverKind::Lean => PathBuf::from("lean"),
        ProverKind::Isabelle => PathBuf::from("isabelle"),
        ProverKind::Z3 => PathBuf::from("z3"),
        ProverKind::CVC5 => PathBuf::from("cvc5"),
        ProverKind::Metamath => PathBuf::from("metamath"),
        ProverKind::HolLight => PathBuf::from("ocaml"),
        ProverKind::Mizar => PathBuf::from("verifier"),
        ProverKind::PVS => PathBuf::from("pvs"),
        ProverKind::ACL2 => PathBuf::from("acl2"),
        ProverKind::Hol4 => PathBuf::from("hol"),
    }
}

/// Create a progress bar with standard styling
fn create_progress_bar(message: &str) -> ProgressBar {
    let pb = ProgressBar::new_spinner();
    pb.set_style(
        ProgressStyle::default_spinner()
            .template("{spinner:.green} {msg}")
            .expect("Failed to set progress bar template"),
    );
    pb.set_message(message.to_string());
    pb.enable_steady_tick(std::time::Duration::from_millis(100));
    pb
}

// We need to add futures crate for the executor
use futures;
