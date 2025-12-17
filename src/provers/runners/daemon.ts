/**
 * ECHIDNA Continuous Proof Runner Daemon
 * Runs proof attempts continuously, day and night
 *
 * SPDX-License-Identifier: MIT OR AGPL-3.0-or-later
 */

import type {
  Problem,
  ProverResult,
  QueueItem,
} from "../types/prover.ts";
import { UnifiedProverClient, type UnifiedResult, type SelectionStrategy } from "../clients/unified.ts";
import { sleep } from "../utils/http.ts";

/** Daemon configuration */
export interface DaemonConfig {
  /** Interval between queue checks (ms) */
  pollInterval: number;
  /** Maximum concurrent proof attempts */
  maxConcurrent: number;
  /** Maximum retries per problem */
  maxRetries: number;
  /** Timeout per problem (seconds) */
  defaultTimeout: number;
  /** Strategy for prover selection */
  strategy: SelectionStrategy;
  /** Enable persistent storage */
  persistResults: boolean;
  /** Results storage path */
  storagePath: string;
  /** Health check interval (ms) */
  healthCheckInterval: number;
}

/** Default daemon configuration */
const DEFAULT_DAEMON_CONFIG: DaemonConfig = {
  pollInterval: 1000,
  maxConcurrent: 5,
  maxRetries: 3,
  defaultTimeout: 60,
  strategy: "cascade",
  persistResults: true,
  storagePath: "./echidna_results",
  healthCheckInterval: 60000,
};

/** Daemon statistics */
export interface DaemonStats {
  started: Date;
  problems_queued: number;
  problems_completed: number;
  problems_failed: number;
  proofs_found: number;
  total_time_ms: number;
  uptime_ms: number;
  current_running: number;
}

/** Event types for daemon hooks */
export type DaemonEvent =
  | { type: "started" }
  | { type: "stopped" }
  | { type: "problem_queued"; problem: Problem }
  | { type: "problem_started"; problem: Problem }
  | { type: "problem_completed"; result: UnifiedResult }
  | { type: "problem_failed"; problem: Problem; error: string }
  | { type: "health_check"; results: Array<{ name: string; available: boolean }> };

/** Event handler type */
export type EventHandler = (event: DaemonEvent) => void | Promise<void>;

export class ProofRunnerDaemon {
  private config: DaemonConfig;
  private client: UnifiedProverClient;
  private queue: QueueItem[] = [];
  private running: Map<string, Promise<void>> = new Map();
  private results: Map<string, UnifiedResult> = new Map();
  private stats: DaemonStats;
  private isRunning = false;
  private eventHandlers: EventHandler[] = [];

  constructor(config: Partial<DaemonConfig> = {}) {
    this.config = { ...DEFAULT_DAEMON_CONFIG, ...config };
    this.client = new UnifiedProverClient({
      timeout_sec: this.config.defaultTimeout,
    });
    this.stats = this.initStats();
  }

  private initStats(): DaemonStats {
    return {
      started: new Date(),
      problems_queued: 0,
      problems_completed: 0,
      problems_failed: 0,
      proofs_found: 0,
      total_time_ms: 0,
      uptime_ms: 0,
      current_running: 0,
    };
  }

  /** Add event handler */
  on(handler: EventHandler): void {
    this.eventHandlers.push(handler);
  }

  /** Emit event to all handlers */
  private async emit(event: DaemonEvent): Promise<void> {
    for (const handler of this.eventHandlers) {
      try {
        await handler(event);
      } catch (err) {
        console.error("[Daemon] Event handler error:", err);
      }
    }
  }

  /** Queue a problem for solving */
  enqueue(problem: Problem, provers?: string[], priority = 0): void {
    const item: QueueItem = {
      problem,
      provers: provers ?? [],
      priority,
      created: new Date(),
      attempts: 0,
      results: [],
    };

    // Insert by priority (higher first)
    const idx = this.queue.findIndex((q) => q.priority < priority);
    if (idx === -1) {
      this.queue.push(item);
    } else {
      this.queue.splice(idx, 0, item);
    }

    this.stats.problems_queued++;
    this.emit({ type: "problem_queued", problem });

    console.log(`[Daemon] Queued: ${problem.id} (priority: ${priority}, queue size: ${this.queue.length})`);
  }

  /** Queue multiple problems */
  enqueueBatch(problems: Problem[], provers?: string[], priority = 0): void {
    for (const problem of problems) {
      this.enqueue(problem, provers, priority);
    }
  }

  /** Start the daemon */
  async start(): Promise<void> {
    if (this.isRunning) {
      console.log("[Daemon] Already running");
      return;
    }

    this.isRunning = true;
    this.stats = this.initStats();

    console.log("[Daemon] Starting ECHIDNA Proof Runner...");
    console.log(`[Daemon] Config: ${JSON.stringify(this.config, null, 2)}`);

    // Initial health check
    const health = await this.client.healthCheck();
    console.log("[Daemon] Service health:");
    for (const h of health) {
      console.log(`  - ${h.name}: ${h.available ? "✓" : "✗"} (${h.provers} provers)`);
    }

    await this.emit({ type: "started" });

    // Start main loop
    this.mainLoop();

    // Start health check loop
    this.healthCheckLoop();

    console.log("[Daemon] Running continuously. Press Ctrl+C to stop.");
  }

  /** Stop the daemon */
  async stop(): Promise<void> {
    if (!this.isRunning) return;

    console.log("[Daemon] Stopping...");
    this.isRunning = false;

    // Wait for running tasks to complete
    if (this.running.size > 0) {
      console.log(`[Daemon] Waiting for ${this.running.size} tasks to complete...`);
      await Promise.allSettled([...this.running.values()]);
    }

    // Persist results
    if (this.config.persistResults) {
      await this.saveResults();
    }

    await this.emit({ type: "stopped" });
    console.log("[Daemon] Stopped");
  }

  /** Main processing loop */
  private async mainLoop(): Promise<void> {
    while (this.isRunning) {
      // Update uptime
      this.stats.uptime_ms = Date.now() - this.stats.started.getTime();

      // Process queue if we have capacity
      while (
        this.queue.length > 0 &&
        this.running.size < this.config.maxConcurrent
      ) {
        const item = this.queue.shift()!;
        this.processItem(item);
      }

      // Update running count
      this.stats.current_running = this.running.size;

      await sleep(this.config.pollInterval);
    }
  }

  /** Health check loop */
  private async healthCheckLoop(): Promise<void> {
    while (this.isRunning) {
      await sleep(this.config.healthCheckInterval);

      if (!this.isRunning) break;

      const health = await this.client.healthCheck();
      await this.emit({
        type: "health_check",
        results: health.map((h) => ({ name: h.name, available: h.available })),
      });
    }
  }

  /** Process a single queue item */
  private processItem(item: QueueItem): void {
    const task = (async () => {
      await this.emit({ type: "problem_started", problem: item.problem });

      try {
        const result = await this.client.solveWithStrategy(
          item.problem,
          this.config.strategy,
          item.provers.length > 0 ? item.provers : undefined
        );

        // Store result
        this.results.set(item.problem.id, result);
        item.results.push(...result.results);
        item.attempts++;

        // Update stats
        this.stats.total_time_ms += result.totalTime_ms;

        if (result.bestResult) {
          const status = result.bestResult.status;
          if (status === "theorem" || status === "unsatisfiable") {
            this.stats.proofs_found++;
            this.stats.problems_completed++;
            console.log(
              `[Daemon] ✓ PROVED: ${item.problem.id} by ${result.bestResult.prover} (${result.bestResult.time_ms}ms)`
            );
          } else if (status === "satisfiable" || status === "countersatisfiable") {
            this.stats.problems_completed++;
            console.log(
              `[Daemon] ✗ Counterexample: ${item.problem.id} by ${result.bestResult.prover}`
            );
          } else if (status === "timeout" || status === "unknown") {
            // Retry if under limit
            if (item.attempts < this.config.maxRetries) {
              console.log(
                `[Daemon] ? Retry ${item.attempts}/${this.config.maxRetries}: ${item.problem.id}`
              );
              this.queue.push(item);
            } else {
              this.stats.problems_failed++;
              console.log(`[Daemon] ✗ Failed after ${item.attempts} attempts: ${item.problem.id}`);
            }
          } else {
            this.stats.problems_failed++;
          }

          await this.emit({ type: "problem_completed", result });
        } else {
          // No result at all
          if (item.attempts < this.config.maxRetries) {
            this.queue.push(item);
          } else {
            this.stats.problems_failed++;
            await this.emit({
              type: "problem_failed",
              problem: item.problem,
              error: "No result from any prover",
            });
          }
        }
      } catch (error) {
        const errorMsg = error instanceof Error ? error.message : String(error);
        console.error(`[Daemon] Error processing ${item.problem.id}:`, errorMsg);

        if (item.attempts < this.config.maxRetries) {
          item.attempts++;
          this.queue.push(item);
        } else {
          this.stats.problems_failed++;
          await this.emit({
            type: "problem_failed",
            problem: item.problem,
            error: errorMsg,
          });
        }
      } finally {
        this.running.delete(item.problem.id);
      }
    })();

    this.running.set(item.problem.id, task);
  }

  /** Save results to disk */
  private async saveResults(): Promise<void> {
    try {
      await Deno.mkdir(this.config.storagePath, { recursive: true });

      const data = {
        stats: this.stats,
        results: Object.fromEntries(this.results),
        timestamp: new Date().toISOString(),
      };

      const filename = `${this.config.storagePath}/results_${Date.now()}.json`;
      await Deno.writeTextFile(filename, JSON.stringify(data, null, 2));
      console.log(`[Daemon] Results saved to ${filename}`);
    } catch (error) {
      console.error("[Daemon] Failed to save results:", error);
    }
  }

  /** Load problems from a file */
  async loadProblemsFromFile(path: string): Promise<void> {
    const content = await Deno.readTextFile(path);
    const problems: Problem[] = JSON.parse(content);
    this.enqueueBatch(problems);
  }

  /** Get current stats */
  getStats(): DaemonStats {
    return {
      ...this.stats,
      uptime_ms: Date.now() - this.stats.started.getTime(),
      current_running: this.running.size,
    };
  }

  /** Get queue status */
  getQueueStatus(): { pending: number; running: number; completed: number } {
    return {
      pending: this.queue.length,
      running: this.running.size,
      completed: this.results.size,
    };
  }

  /** Get result for a problem */
  getResult(problemId: string): UnifiedResult | undefined {
    return this.results.get(problemId);
  }

  /** Get all results */
  getAllResults(): Map<string, UnifiedResult> {
    return this.results;
  }
}

export default ProofRunnerDaemon;
