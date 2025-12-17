/**
 * ECHIDNA Z3 WASM Client
 * Z3 SMT Solver via WebAssembly (Deno-compatible)
 *
 * SPDX-License-Identifier: MIT OR AGPL-3.0-or-later
 *
 * Note: This client uses the Z3 WASM build. For Deno, we use esm.sh CDN
 * which provides Deno-compatible ES modules without npm.
 */

import type {
  Problem,
  Prover,
  ProverClient,
  ProverConfig,
  ProverResult,
  ProverStatus,
} from "../types/prover.ts";

// Z3 WASM from esm.sh (Deno-compatible CDN, no npm needed)
const Z3_WASM_URL = "https://esm.sh/z3-solver@4.12.4";

/** Z3 initialization state */
let z3Instance: Z3Instance | null = null;
let z3Loading: Promise<Z3Instance> | null = null;

/** Minimal Z3 API interface */
interface Z3Instance {
  Context: (name: string) => Z3Context;
}

interface Z3Context {
  Solver: () => Z3Solver;
  Bool: {
    const: (name: string) => Z3Bool;
    val: (value: boolean) => Z3Bool;
  };
  Int: {
    const: (name: string) => Z3Int;
    val: (value: number) => Z3Int;
  };
  Real: {
    const: (name: string) => Z3Real;
    val: (value: number) => Z3Real;
  };
}

interface Z3Solver {
  add: (...constraints: Z3Expr[]) => void;
  check: () => Promise<"sat" | "unsat" | "unknown">;
  model: () => Z3Model;
  fromString: (smtlib: string) => void;
  toString: () => string;
}

interface Z3Expr {
  eq: (other: Z3Expr) => Z3Bool;
  neq: (other: Z3Expr) => Z3Bool;
}

interface Z3Bool extends Z3Expr {
  not: () => Z3Bool;
  and: (other: Z3Bool) => Z3Bool;
  or: (other: Z3Bool) => Z3Bool;
  implies: (other: Z3Bool) => Z3Bool;
}

interface Z3Int extends Z3Expr {
  add: (other: Z3Int) => Z3Int;
  sub: (other: Z3Int) => Z3Int;
  mul: (other: Z3Int) => Z3Int;
  lt: (other: Z3Int) => Z3Bool;
  le: (other: Z3Int) => Z3Bool;
  gt: (other: Z3Int) => Z3Bool;
  ge: (other: Z3Int) => Z3Bool;
}

interface Z3Real extends Z3Expr {
  add: (other: Z3Real) => Z3Real;
  sub: (other: Z3Real) => Z3Real;
  mul: (other: Z3Real) => Z3Real;
  div: (other: Z3Real) => Z3Real;
}

interface Z3Model {
  sexpr: () => string;
  eval: (expr: Z3Expr) => Z3Expr;
}

/** Load Z3 WASM module */
async function loadZ3(): Promise<Z3Instance> {
  if (z3Instance) return z3Instance;

  if (z3Loading) return z3Loading;

  z3Loading = (async () => {
    console.log("[Z3] Loading WASM module from esm.sh...");

    try {
      // Dynamic import from esm.sh CDN
      const z3Module = await import(Z3_WASM_URL);
      const { init } = z3Module;

      // Initialize Z3
      z3Instance = await init();
      console.log("[Z3] WASM module loaded successfully");

      return z3Instance;
    } catch (error) {
      console.error("[Z3] Failed to load WASM module:", error);
      throw error;
    }
  })();

  return z3Loading;
}

/** Parse SMT-LIB2 result status */
function parseSMTStatus(result: "sat" | "unsat" | "unknown"): ProverStatus {
  switch (result) {
    case "sat":
      return "satisfiable";
    case "unsat":
      return "unsatisfiable";
    default:
      return "unknown";
  }
}

export class Z3WasmClient implements ProverClient {
  readonly name = "Z3-WASM";
  readonly provers: Prover[] = [
    {
      id: "z3-wasm",
      name: "Z3 WASM",
      version: "4.12.4",
      formats: ["smtlib2"],
      tier: 1,
      online: false, // Local WASM execution
    },
  ];

  private config: ProverConfig;

  constructor(config: Partial<ProverConfig> = {}) {
    this.config = {
      timeout_sec: config.timeout_sec ?? 60,
      retry_count: config.retry_count ?? 3,
      retry_delay_ms: config.retry_delay_ms ?? 1000,
    };
  }

  async ping(): Promise<boolean> {
    try {
      await loadZ3();
      return true;
    } catch {
      return false;
    }
  }

  async listProvers(): Promise<Prover[]> {
    return this.provers;
  }

  async solve(problem: Problem, _prover?: string): Promise<ProverResult> {
    const startTime = Date.now();

    try {
      const z3 = await loadZ3();
      const ctx = z3.Context("main");
      const solver = ctx.Solver();

      // Parse SMT-LIB2 input
      solver.fromString(problem.content);

      // Create timeout promise
      const timeoutMs = (problem.timeout_sec ?? this.config.timeout_sec) * 1000;
      const timeoutPromise = new Promise<"unknown">((resolve) =>
        setTimeout(() => resolve("unknown"), timeoutMs)
      );

      // Race solver against timeout
      const result = await Promise.race([solver.check(), timeoutPromise]);

      const status = parseSMTStatus(result);
      const elapsed = Date.now() - startTime;

      // Get model if satisfiable
      let model: string | undefined;
      if (result === "sat") {
        try {
          model = solver.model().sexpr();
        } catch {
          // Model extraction might fail
        }
      }

      return {
        prover: "z3-wasm",
        status: result === "unknown" && elapsed >= timeoutMs ? "timeout" : status,
        model,
        time_ms: elapsed,
        raw_output: solver.toString(),
        timestamp: new Date(),
      };
    } catch (error) {
      return {
        prover: "z3-wasm",
        status: "error",
        error: error instanceof Error ? error.message : String(error),
        time_ms: Date.now() - startTime,
        timestamp: new Date(),
      };
    }
  }

  /** Solve multiple problems in parallel */
  async solveBatch(problems: Problem[]): Promise<ProverResult[]> {
    // Z3 WASM is single-threaded, so we process sequentially
    const results: ProverResult[] = [];
    for (const problem of problems) {
      results.push(await this.solve(problem));
    }
    return results;
  }
}

/** Alternative: Use Z3 via SystemOnTPTP if WASM fails */
export class Z3FallbackClient implements ProverClient {
  readonly name = "Z3-Fallback";
  readonly provers: Prover[] = [
    { id: "z3-online", name: "Z3 Online", formats: ["smtlib2"], tier: 1, online: true },
  ];

  private config: ProverConfig;
  private wasmClient: Z3WasmClient;
  private tptpFallback: boolean = false;

  constructor(config: Partial<ProverConfig> = {}) {
    this.config = {
      timeout_sec: config.timeout_sec ?? 60,
      retry_count: config.retry_count ?? 3,
      retry_delay_ms: config.retry_delay_ms ?? 1000,
    };
    this.wasmClient = new Z3WasmClient(config);
  }

  async ping(): Promise<boolean> {
    const wasmOk = await this.wasmClient.ping();
    if (!wasmOk) {
      this.tptpFallback = true;
    }
    return true; // Can always fall back to TPTP
  }

  async listProvers(): Promise<Prover[]> {
    return this.provers;
  }

  async solve(problem: Problem, prover?: string): Promise<ProverResult> {
    if (!this.tptpFallback) {
      try {
        return await this.wasmClient.solve(problem, prover);
      } catch {
        this.tptpFallback = true;
      }
    }

    // Fall back to SystemOnTPTP's Z3
    // Import dynamically to avoid circular deps
    const { SystemOnTPTPClient } = await import("./system_on_tptp.ts");
    const tptp = new SystemOnTPTPClient(this.config);
    return tptp.solve(problem, "Z3---4.12.2");
  }
}

export default Z3WasmClient;
