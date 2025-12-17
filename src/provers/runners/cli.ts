#!/usr/bin/env -S deno run --allow-net --allow-read --allow-write --allow-env

/**
 * ECHIDNA Proof Runner CLI
 * Command-line interface for running the proof daemon
 *
 * SPDX-License-Identifier: MIT OR AGPL-3.0-or-later
 *
 * Usage:
 *   deno run --allow-net --allow-read --allow-write --allow-env cli.ts [options]
 *
 * Options:
 *   --help              Show help
 *   --health            Check service health
 *   --solve <file>      Solve a single problem file
 *   --batch <dir>       Process all problems in directory
 *   --daemon            Run as continuous daemon
 *   --format <fmt>      Input format (tptp, smtlib2, metamath, lean)
 *   --prover <id>       Specific prover to use
 *   --timeout <sec>     Timeout in seconds (default: 60)
 *   --strategy <s>      Strategy: first, cascade, parallel, all (default: cascade)
 *   --output <file>     Output results to file
 */

import { ProofRunnerDaemon } from "./daemon.ts";
import { UnifiedProverClient } from "../clients/unified.ts";
import type { Problem, InputFormat, ProverResult } from "../types/prover.ts";

/** CLI arguments */
interface CLIArgs {
  help: boolean;
  health: boolean;
  solve?: string;
  batch?: string;
  daemon: boolean;
  format: InputFormat;
  prover?: string;
  timeout: number;
  strategy: "first" | "cascade" | "parallel" | "all";
  output?: string;
}

/** Parse command line arguments */
function parseArgs(): CLIArgs {
  const args: CLIArgs = {
    help: false,
    health: false,
    daemon: false,
    format: "tptp",
    timeout: 60,
    strategy: "cascade",
  };

  for (let i = 0; i < Deno.args.length; i++) {
    const arg = Deno.args[i];

    switch (arg) {
      case "--help":
      case "-h":
        args.help = true;
        break;
      case "--health":
        args.health = true;
        break;
      case "--solve":
        args.solve = Deno.args[++i];
        break;
      case "--batch":
        args.batch = Deno.args[++i];
        break;
      case "--daemon":
        args.daemon = true;
        break;
      case "--format":
        args.format = Deno.args[++i] as InputFormat;
        break;
      case "--prover":
        args.prover = Deno.args[++i];
        break;
      case "--timeout":
        args.timeout = parseInt(Deno.args[++i], 10);
        break;
      case "--strategy":
        args.strategy = Deno.args[++i] as CLIArgs["strategy"];
        break;
      case "--output":
        args.output = Deno.args[++i];
        break;
    }
  }

  return args;
}

/** Print help message */
function printHelp(): void {
  console.log(`
ECHIDNA Proof Runner - Neurosymbolic Theorem Proving Platform

Usage:
  echidna-runner [options]

Options:
  -h, --help              Show this help message
  --health                Check health of all prover services
  --solve <file>          Solve a single problem from file
  --batch <dir>           Process all problems in directory
  --daemon                Run as continuous daemon (day and night)
  --format <fmt>          Input format: tptp, smtlib2, metamath, lean, wolfram
  --prover <id>           Use specific prover (e.g., Vampire---4.8, z3-wasm)
  --timeout <sec>         Timeout in seconds (default: 60)
  --strategy <s>          Selection strategy:
                            first    - Use first available prover
                            cascade  - Try in order until success (default)
                            parallel - Run all in parallel
                            all      - Run all, return best result
  --output <file>         Write results to JSON file

Examples:
  # Check service availability
  echidna-runner --health

  # Solve a TPTP problem
  echidna-runner --solve problem.p --format tptp

  # Solve with specific prover
  echidna-runner --solve problem.smt2 --format smtlib2 --prover z3-wasm

  # Run all provers in parallel
  echidna-runner --solve problem.p --strategy parallel

  # Process directory of problems
  echidna-runner --batch ./problems --format tptp --output results.json

  # Run as continuous daemon
  echidna-runner --daemon

Environment Variables:
  WOLFRAM_APP_ID      Wolfram Alpha API key
  LEANTOOL_API_KEY    LeanTool API key
  LEANTOOL_ENDPOINT   Custom LeanTool endpoint

Available Provers:
  SystemOnTPTP: Vampire, E, Z3, CVC5, SPASS, Prover9, Leo-III, Satallax, etc.
  Local:        z3-wasm, metamath-verify
  APIs:         wolfram-prove, wolfram-solve, lean4, lean4-mathlib
`);
}

/** Check health of all services */
async function checkHealth(): Promise<void> {
  console.log("Checking ECHIDNA prover service health...\n");

  const client = new UnifiedProverClient();
  const health = await client.healthCheck();

  console.log("Service Status:");
  console.log("─".repeat(50));

  for (const h of health) {
    const status = h.available ? "✓ Online" : "✗ Offline";
    const latency = h.latency_ms ? `${h.latency_ms}ms` : "N/A";
    console.log(`  ${h.name.padEnd(20)} ${status.padEnd(12)} ${latency.padStart(8)} (${h.provers} provers)`);
  }

  console.log("─".repeat(50));

  const stats = client.getStats();
  console.log(`\nTotal: ${stats.totalProvers} provers across ${stats.backends} backends`);
  console.log(`Healthy: ${stats.healthyBackends}/${stats.backends} backends`);
}

/** Solve a single problem */
async function solveSingle(
  path: string,
  format: InputFormat,
  prover?: string,
  timeout?: number,
  strategy?: CLIArgs["strategy"]
): Promise<ProverResult[]> {
  const content = await Deno.readTextFile(path);

  const problem: Problem = {
    id: path,
    name: path.split("/").pop(),
    format,
    content,
    timeout_sec: timeout,
  };

  console.log(`\nSolving: ${path}`);
  console.log(`Format: ${format}`);
  if (prover) console.log(`Prover: ${prover}`);
  console.log(`Strategy: ${strategy ?? "cascade"}`);
  console.log("─".repeat(50));

  const client = new UnifiedProverClient({ timeout_sec: timeout });
  const result = await client.solveWithStrategy(
    problem,
    strategy ?? "cascade",
    prover ? [prover] : undefined
  );

  // Print results
  for (const r of result.results) {
    const emoji = r.status === "theorem" || r.status === "unsatisfiable" ? "✓" :
                  r.status === "satisfiable" || r.status === "countersatisfiable" ? "✗" :
                  r.status === "timeout" ? "⏱" : "?";

    console.log(`\n${emoji} ${r.prover}: ${r.status} (${r.time_ms}ms)`);

    if (r.proof) {
      console.log("  Proof:");
      console.log("  " + r.proof.split("\n").slice(0, 5).join("\n  "));
    }
    if (r.model) {
      console.log("  Model:");
      console.log("  " + r.model.split("\n").slice(0, 5).join("\n  "));
    }
    if (r.error) {
      console.log(`  Error: ${r.error}`);
    }
  }

  console.log("─".repeat(50));
  console.log(`Total time: ${result.totalTime_ms}ms`);

  if (result.bestResult) {
    console.log(`\nBest result: ${result.bestResult.prover} - ${result.bestResult.status}`);
  }

  return result.results;
}

/** Process batch of problems */
async function processBatch(
  dir: string,
  format: InputFormat,
  prover?: string,
  timeout?: number,
  strategy?: CLIArgs["strategy"],
  output?: string
): Promise<void> {
  const daemon = new ProofRunnerDaemon({
    defaultTimeout: timeout ?? 60,
    strategy: strategy ?? "cascade",
    persistResults: !!output,
    storagePath: output ? output.replace(/\.json$/, "") : "./echidna_results",
  });

  // Find all problem files
  const extensions: Record<string, string[]> = {
    tptp: [".p", ".tptp", ".ax"],
    smtlib2: [".smt2", ".smt"],
    metamath: [".mm"],
    lean: [".lean"],
    dimacs: [".cnf", ".dimacs"],
  };

  const exts = extensions[format] ?? [".p"];

  console.log(`\nScanning ${dir} for ${format} problems...`);

  for await (const entry of Deno.readDir(dir)) {
    if (entry.isFile && exts.some((ext) => entry.name.endsWith(ext))) {
      const path = `${dir}/${entry.name}`;
      const content = await Deno.readTextFile(path);

      daemon.enqueue(
        {
          id: path,
          name: entry.name,
          format,
          content,
          timeout_sec: timeout,
        },
        prover ? [prover] : undefined
      );
    }
  }

  const status = daemon.getQueueStatus();
  console.log(`Queued ${status.pending} problems\n`);

  if (status.pending === 0) {
    console.log("No problems found!");
    return;
  }

  // Run until queue is empty
  await daemon.start();

  // Wait for completion
  while (true) {
    const s = daemon.getQueueStatus();
    if (s.pending === 0 && s.running === 0) break;
    await new Promise((r) => setTimeout(r, 1000));
  }

  await daemon.stop();

  // Print summary
  const stats = daemon.getStats();
  console.log("\n" + "═".repeat(50));
  console.log("BATCH PROCESSING COMPLETE");
  console.log("═".repeat(50));
  console.log(`Problems processed: ${stats.problems_completed + stats.problems_failed}`);
  console.log(`Proofs found: ${stats.proofs_found}`);
  console.log(`Failed: ${stats.problems_failed}`);
  console.log(`Total time: ${stats.total_time_ms}ms`);
}

/** Run as daemon */
async function runDaemon(): Promise<void> {
  const daemon = new ProofRunnerDaemon({
    pollInterval: 1000,
    maxConcurrent: 5,
    maxRetries: 3,
    strategy: "cascade",
    persistResults: true,
    storagePath: "./echidna_results",
    healthCheckInterval: 60000,
  });

  // Add event logging
  daemon.on(async (event) => {
    switch (event.type) {
      case "started":
        console.log("\n🚀 ECHIDNA Daemon started");
        break;
      case "stopped":
        console.log("\n🛑 ECHIDNA Daemon stopped");
        break;
      case "health_check":
        const online = event.results.filter((r) => r.available).length;
        console.log(`\n💓 Health: ${online}/${event.results.length} services online`);
        break;
    }
  });

  // Handle shutdown signals
  const shutdown = async () => {
    console.log("\nReceived shutdown signal...");
    await daemon.stop();
    Deno.exit(0);
  };

  Deno.addSignalListener("SIGINT", shutdown);
  Deno.addSignalListener("SIGTERM", shutdown);

  console.log(`
╔════════════════════════════════════════════════════════╗
║  ECHIDNA - Neurosymbolic Theorem Proving Daemon        ║
║  Running continuously... Press Ctrl+C to stop          ║
╚════════════════════════════════════════════════════════╝
`);

  // Check for initial problems
  try {
    const queueFile = "./echidna_queue.json";
    const content = await Deno.readTextFile(queueFile);
    const problems: Problem[] = JSON.parse(content);
    daemon.enqueueBatch(problems);
    console.log(`Loaded ${problems.length} problems from queue file`);
  } catch {
    console.log("No queue file found. Add problems via API or queue file.");
    console.log("Create echidna_queue.json with array of Problem objects.");
  }

  await daemon.start();

  // Keep running until stopped
  while (true) {
    await new Promise((r) => setTimeout(r, 10000));

    const stats = daemon.getStats();
    const queue = daemon.getQueueStatus();

    console.log(
      `[${new Date().toISOString()}] ` +
      `Queue: ${queue.pending} | Running: ${queue.running} | ` +
      `Completed: ${stats.problems_completed} | Proofs: ${stats.proofs_found}`
    );
  }
}

/** Main entry point */
async function main(): Promise<void> {
  const args = parseArgs();

  if (args.help) {
    printHelp();
    return;
  }

  if (args.health) {
    await checkHealth();
    return;
  }

  if (args.solve) {
    const results = await solveSingle(
      args.solve,
      args.format,
      args.prover,
      args.timeout,
      args.strategy
    );

    if (args.output) {
      await Deno.writeTextFile(args.output, JSON.stringify(results, null, 2));
      console.log(`\nResults written to ${args.output}`);
    }
    return;
  }

  if (args.batch) {
    await processBatch(
      args.batch,
      args.format,
      args.prover,
      args.timeout,
      args.strategy,
      args.output
    );
    return;
  }

  if (args.daemon) {
    await runDaemon();
    return;
  }

  // No action specified
  printHelp();
}

// Run
if (import.meta.main) {
  main().catch((err) => {
    console.error("Fatal error:", err);
    Deno.exit(1);
  });
}
