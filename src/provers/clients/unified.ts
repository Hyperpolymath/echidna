/**
 * ECHIDNA Unified Prover Client
 * Aggregates all prover backends into a single interface
 *
 * SPDX-License-Identifier: MIT OR AGPL-3.0-or-later
 */

import type {
  Problem,
  Prover,
  ProverClient,
  ProverConfig,
  ProverResult,
  ProverStatus,
} from "../types/prover.ts";

import { SystemOnTPTPClient } from "./system_on_tptp.ts";
import { MetamathClient } from "./metamath.ts";
import { Z3WasmClient, Z3FallbackClient } from "./z3_wasm.ts";
import { WolframAlphaClient } from "./wolfram.ts";
import { LeanToolClient } from "./lean_tool.ts";

/** Prover selection strategy */
export type SelectionStrategy =
  | "first"      // Use first available prover
  | "fastest"    // Use historically fastest prover
  | "all"        // Try all provers
  | "cascade"    // Try in order until success
  | "parallel";  // Run all in parallel, return first success

/** Result from unified solving */
export interface UnifiedResult {
  problem: Problem;
  results: ProverResult[];
  bestResult?: ProverResult;
  strategy: SelectionStrategy;
  totalTime_ms: number;
}

/** Service health status */
export interface ServiceHealth {
  name: string;
  available: boolean;
  latency_ms?: number;
  provers: number;
  lastCheck: Date;
}

export class UnifiedProverClient implements ProverClient {
  readonly name = "ECHIDNA-Unified";
  readonly provers: Prover[] = [];

  private clients: Map<string, ProverClient> = new Map();
  private proverToClient: Map<string, string> = new Map();
  private config: ProverConfig;
  private healthCache: Map<string, ServiceHealth> = new Map();

  constructor(config: Partial<ProverConfig> = {}) {
    this.config = {
      timeout_sec: config.timeout_sec ?? 60,
      retry_count: config.retry_count ?? 3,
      retry_delay_ms: config.retry_delay_ms ?? 1000,
      api_key: config.api_key,
    };

    this.initializeClients();
  }

  private initializeClients(): void {
    // Initialize all client backends
    const clients: ProverClient[] = [
      new SystemOnTPTPClient(this.config),
      new MetamathClient(this.config),
      new Z3FallbackClient(this.config),
      new WolframAlphaClient(this.config),
      new LeanToolClient(this.config),
    ];

    for (const client of clients) {
      this.clients.set(client.name, client);

      for (const prover of client.provers) {
        this.provers.push(prover);
        this.proverToClient.set(prover.id, client.name);
      }
    }

    console.log(`[Unified] Initialized ${this.clients.size} backends with ${this.provers.length} provers`);
  }

  /** Get client for a specific prover */
  private getClientForProver(proverId: string): ProverClient | undefined {
    const clientName = this.proverToClient.get(proverId);
    if (!clientName) return undefined;
    return this.clients.get(clientName);
  }

  async ping(): Promise<boolean> {
    // Check if at least one backend is available
    const checks = await Promise.all(
      [...this.clients.values()].map((c) => c.ping())
    );
    return checks.some((ok) => ok);
  }

  async listProvers(): Promise<Prover[]> {
    return this.provers;
  }

  /** Check health of all services */
  async healthCheck(): Promise<ServiceHealth[]> {
    const results: ServiceHealth[] = [];

    for (const [name, client] of this.clients) {
      const start = Date.now();
      try {
        const available = await client.ping();
        results.push({
          name,
          available,
          latency_ms: Date.now() - start,
          provers: client.provers.length,
          lastCheck: new Date(),
        });
      } catch {
        results.push({
          name,
          available: false,
          provers: client.provers.length,
          lastCheck: new Date(),
        });
      }
    }

    // Update cache
    for (const health of results) {
      this.healthCache.set(health.name, health);
    }

    return results;
  }

  async solve(problem: Problem, proverId?: string): Promise<ProverResult> {
    if (proverId) {
      const client = this.getClientForProver(proverId);
      if (!client) {
        return {
          prover: proverId,
          status: "error",
          error: `Unknown prover: ${proverId}`,
          time_ms: 0,
          timestamp: new Date(),
        };
      }
      return client.solve(problem, proverId);
    }

    // Default: use appropriate client based on format
    const client = this.selectClientForFormat(problem.format);
    if (!client) {
      return {
        prover: "unknown",
        status: "error",
        error: `No client available for format: ${problem.format}`,
        time_ms: 0,
        timestamp: new Date(),
      };
    }

    return client.solve(problem);
  }

  /** Select best client for a format */
  private selectClientForFormat(format: string): ProverClient | undefined {
    // Priority order for each format
    const formatClients: Record<string, string[]> = {
      tptp: ["SystemOnTPTP"],
      smtlib2: ["Z3-Fallback", "SystemOnTPTP"],
      metamath: ["Metamath"],
      lean: ["LeanTool"],
      wolfram: ["WolframAlpha"],
      natural: ["WolframAlpha"],
      dimacs: ["SystemOnTPTP"],
    };

    const clientNames = formatClients[format] ?? ["SystemOnTPTP"];

    for (const name of clientNames) {
      const client = this.clients.get(name);
      if (client) {
        const health = this.healthCache.get(name);
        if (!health || health.available) {
          return client;
        }
      }
    }

    // Fallback to first available
    return [...this.clients.values()][0];
  }

  /** Solve with multiple strategies */
  async solveWithStrategy(
    problem: Problem,
    strategy: SelectionStrategy = "cascade",
    provers?: string[]
  ): Promise<UnifiedResult> {
    const startTime = Date.now();
    const targetProvers = provers ?? this.selectProversForProblem(problem);

    let results: ProverResult[] = [];
    let bestResult: ProverResult | undefined;

    switch (strategy) {
      case "first": {
        const result = await this.solve(problem, targetProvers[0]);
        results = [result];
        bestResult = result;
        break;
      }

      case "cascade": {
        for (const prover of targetProvers) {
          const result = await this.solve(problem, prover);
          results.push(result);

          if (this.isSuccessful(result.status)) {
            bestResult = result;
            break;
          }
        }
        break;
      }

      case "parallel": {
        const allResults = await Promise.allSettled(
          targetProvers.map((p) => this.solve(problem, p))
        );

        results = allResults.map((r, i) =>
          r.status === "fulfilled"
            ? r.value
            : {
                prover: targetProvers[i],
                status: "error" as ProverStatus,
                error: r.reason?.message ?? "Unknown error",
                time_ms: 0,
                timestamp: new Date(),
              }
        );

        // Find first success or fastest successful
        bestResult = results.find((r) => this.isSuccessful(r.status));
        break;
      }

      case "all": {
        const allResults = await Promise.allSettled(
          targetProvers.map((p) => this.solve(problem, p))
        );

        results = allResults.map((r, i) =>
          r.status === "fulfilled"
            ? r.value
            : {
                prover: targetProvers[i],
                status: "error" as ProverStatus,
                error: r.reason?.message ?? "Unknown error",
                time_ms: 0,
                timestamp: new Date(),
              }
        );

        // Best = successful with shortest time
        const successful = results.filter((r) => this.isSuccessful(r.status));
        if (successful.length > 0) {
          bestResult = successful.reduce((a, b) => (a.time_ms < b.time_ms ? a : b));
        }
        break;
      }

      case "fastest": {
        // Use cached timing data (simplified: just use parallel)
        return this.solveWithStrategy(problem, "parallel", targetProvers);
      }
    }

    return {
      problem,
      results,
      bestResult,
      strategy,
      totalTime_ms: Date.now() - startTime,
    };
  }

  /** Check if status indicates success */
  private isSuccessful(status: ProverStatus): boolean {
    return status === "theorem" || status === "unsatisfiable" || status === "satisfiable";
  }

  /** Select appropriate provers for a problem */
  private selectProversForProblem(problem: Problem): string[] {
    const formatProvers: Record<string, string[]> = {
      tptp: ["Vampire---4.8", "E---3.0", "Z3---4.12.2", "CVC5---1.0.8"],
      smtlib2: ["z3-wasm", "Z3---4.12.2", "CVC5---1.0.8"],
      metamath: ["metamath-verify"],
      lean: ["lean4", "lean4-mathlib"],
      wolfram: ["wolfram-prove", "wolfram-solve"],
      natural: ["wolfram-prove"],
      dimacs: ["MiniSat---2.2.1", "Glucose---4.2.1"],
    };

    return formatProvers[problem.format] ?? ["Vampire---4.8"];
  }

  /** Get statistics */
  getStats(): {
    totalProvers: number;
    backends: number;
    healthyBackends: number;
  } {
    const healthyBackends = [...this.healthCache.values()].filter(
      (h) => h.available
    ).length;

    return {
      totalProvers: this.provers.length,
      backends: this.clients.size,
      healthyBackends,
    };
  }
}

export default UnifiedProverClient;
