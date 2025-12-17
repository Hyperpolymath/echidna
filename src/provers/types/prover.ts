/**
 * ECHIDNA Prover Types
 * Core type definitions for the neurosymbolic theorem proving platform
 *
 * SPDX-License-Identifier: MIT OR AGPL-3.0-or-later
 */

/** Supported input formats for theorem provers */
export type InputFormat =
  | "tptp"      // TPTP format (SystemOnTPTP)
  | "smtlib2"   // SMT-LIB 2.0 (Z3, CVC5)
  | "metamath"  // Metamath format
  | "lean"      // Lean 4
  | "wolfram"   // Wolfram Language
  | "dimacs"    // SAT solver CNF format
  | "natural";  // Natural language (for LLM-based)

/** Result status from a prover */
export type ProverStatus =
  | "theorem"      // Proved
  | "countersatisfiable" // Disproved
  | "satisfiable"  // SAT result
  | "unsatisfiable" // UNSAT result
  | "timeout"      // Timed out
  | "unknown"      // Could not determine
  | "error"        // Error occurred
  | "running";     // Still processing

/** A single prover system */
export interface Prover {
  id: string;
  name: string;
  version?: string;
  formats: InputFormat[];
  endpoint?: string;
  tier: 1 | 2 | 3 | 4;
  online: boolean;
}

/** Result from a prover attempt */
export interface ProverResult {
  prover: string;
  status: ProverStatus;
  proof?: string;
  model?: string;
  time_ms: number;
  raw_output?: string;
  error?: string;
  timestamp: Date;
}

/** A problem to be proved */
export interface Problem {
  id: string;
  name?: string;
  format: InputFormat;
  content: string;
  expected?: ProverStatus;
  timeout_sec?: number;
  metadata?: Record<string, unknown>;
}

/** Queue item for continuous runner */
export interface QueueItem {
  problem: Problem;
  provers: string[];
  priority: number;
  created: Date;
  attempts: number;
  results: ProverResult[];
}

/** Configuration for prover clients */
export interface ProverConfig {
  timeout_sec: number;
  retry_count: number;
  retry_delay_ms: number;
  api_key?: string;
  endpoint?: string;
}

/** Client interface all prover clients must implement */
export interface ProverClient {
  readonly name: string;
  readonly provers: Prover[];

  /** Check if service is available */
  ping(): Promise<boolean>;

  /** Submit a problem for solving */
  solve(problem: Problem, prover?: string): Promise<ProverResult>;

  /** List available provers */
  listProvers(): Promise<Prover[]>;
}

/** Batch solving capability */
export interface BatchProverClient extends ProverClient {
  solveBatch(problems: Problem[], prover?: string): Promise<ProverResult[]>;
}

/** Default configuration */
export const DEFAULT_CONFIG: ProverConfig = {
  timeout_sec: 60,
  retry_count: 3,
  retry_delay_ms: 1000,
};

/** Available provers registry */
export const PROVER_REGISTRY: Record<string, Prover> = {
  // Tier 1 - Core provers
  "z3": { id: "z3", name: "Z3", formats: ["smtlib2"], tier: 1, online: true },
  "cvc5": { id: "cvc5", name: "CVC5", formats: ["smtlib2"], tier: 1, online: true },
  "vampire": { id: "vampire", name: "Vampire", formats: ["tptp"], tier: 1, online: true },
  "e": { id: "e", name: "E Theorem Prover", formats: ["tptp"], tier: 1, online: true },

  // Tier 2 - Big Six completion
  "metamath": { id: "metamath", name: "Metamath", formats: ["metamath"], tier: 2, online: true },
  "isabelle": { id: "isabelle", name: "Isabelle/HOL", formats: ["tptp"], tier: 2, online: true },
  "hol-light": { id: "hol-light", name: "HOL Light", formats: ["tptp"], tier: 2, online: true },
  "mizar": { id: "mizar", name: "Mizar", formats: ["tptp"], tier: 2, online: true },

  // Tier 3 - Extended support
  "lean": { id: "lean", name: "Lean 4", formats: ["lean"], tier: 3, online: true },
  "coq": { id: "coq", name: "Coq/Rocq", formats: ["tptp"], tier: 3, online: true },

  // SAT solvers
  "minisat": { id: "minisat", name: "MiniSat", formats: ["dimacs"], tier: 1, online: true },
  "glucose": { id: "glucose", name: "Glucose", formats: ["dimacs"], tier: 1, online: true },
};
