/**
 * ECHIDNA SystemOnTPTP Client
 * Connects to TPTP.org's SystemOnTPTP service (40+ theorem provers)
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
import { postForm, getText } from "../utils/http.ts";

const SYSTEM_ON_TPTP_URL = "https://www.tptp.org/cgi-bin/SystemOnTPTP";
const SYSTEM_ON_TPTP_FORM = "https://www.tptp.org/cgi-bin/SystemOnTPTPFormReply";

/** Available provers on SystemOnTPTP */
const TPTP_PROVERS: Prover[] = [
  // First-order theorem provers
  { id: "Vampire---4.8", name: "Vampire 4.8", formats: ["tptp"], tier: 1, online: true },
  { id: "E---3.0", name: "E 3.0", formats: ["tptp"], tier: 1, online: true },
  { id: "iProver---3.8", name: "iProver 3.8", formats: ["tptp"], tier: 1, online: true },
  { id: "SPASS---3.9", name: "SPASS 3.9", formats: ["tptp"], tier: 2, online: true },
  { id: "Prover9---1109a", name: "Prover9", formats: ["tptp"], tier: 2, online: true },

  // SMT solvers
  { id: "Z3---4.12.2", name: "Z3 4.12.2", formats: ["tptp", "smtlib2"], tier: 1, online: true },
  { id: "CVC5---1.0.8", name: "CVC5 1.0.8", formats: ["tptp", "smtlib2"], tier: 1, online: true },

  // Higher-order provers
  { id: "Leo-III---1.7", name: "Leo-III 1.7", formats: ["tptp"], tier: 2, online: true },
  { id: "Satallax---3.5", name: "Satallax 3.5", formats: ["tptp"], tier: 2, online: true },
  { id: "Zipperposition---2.1", name: "Zipperposition 2.1", formats: ["tptp"], tier: 2, online: true },

  // Model finders
  { id: "Paradox---4.0", name: "Paradox 4.0", formats: ["tptp"], tier: 2, online: true },
  { id: "Mace4---0.5", name: "Mace4 0.5", formats: ["tptp"], tier: 2, online: true },

  // SAT solvers
  { id: "MiniSat---2.2.1", name: "MiniSat 2.2.1", formats: ["dimacs"], tier: 1, online: true },
  { id: "Glucose---4.2.1", name: "Glucose 4.2.1", formats: ["dimacs"], tier: 1, online: true },

  // Proof assistants (limited automation)
  { id: "Isabelle---2024", name: "Isabelle 2024", formats: ["tptp"], tier: 2, online: true },
];

/** Parse SZS status from TPTP output */
function parseSZSStatus(output: string): ProverStatus {
  const statusMatch = output.match(/SZS status (\w+)/);
  if (!statusMatch) return "unknown";

  const status = statusMatch[1].toLowerCase();

  const statusMap: Record<string, ProverStatus> = {
    theorem: "theorem",
    unsatisfiable: "unsatisfiable",
    satisfiable: "satisfiable",
    countersatisfiable: "countersatisfiable",
    timeout: "timeout",
    resourceout: "timeout",
    gaveup: "unknown",
    unknown: "unknown",
    error: "error",
  };

  return statusMap[status] || "unknown";
}

/** Parse timing from TPTP output */
function parseTime(output: string): number {
  const timeMatch = output.match(/(\d+\.?\d*)\s*s(?:econds?)?/i);
  return timeMatch ? parseFloat(timeMatch[1]) * 1000 : 0;
}

/** Extract proof from SZS output */
function extractProof(output: string): string | undefined {
  const proofMatch = output.match(/SZS output start[\s\S]*?SZS output end/);
  return proofMatch ? proofMatch[0] : undefined;
}

export class SystemOnTPTPClient implements ProverClient {
  readonly name = "SystemOnTPTP";
  readonly provers = TPTP_PROVERS;
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
      const response = await getText(SYSTEM_ON_TPTP_URL);
      return response.includes("SystemOnTPTP");
    } catch {
      return false;
    }
  }

  async listProvers(): Promise<Prover[]> {
    // Could scrape the form for dynamic list, but static list is reliable
    return this.provers;
  }

  async solve(problem: Problem, proverId?: string): Promise<ProverResult> {
    const prover = proverId ?? "Vampire---4.8";
    const startTime = Date.now();

    try {
      // SystemOnTPTP uses form POST
      const formData: Record<string, string> = {
        TPTPProblem: "",
        ProblemSource: "FORMULAE",
        FORMULAEProblem: problem.content,
        QuietFlag: "-q2",  // Machine-readable output
        SubmitButton: "RunSelectedSystems",
        System___Vampire___4.8: prover,
        TimeLimit___Vampire___4.8: String(problem.timeout_sec ?? this.config.timeout_sec),
      };

      // Dynamic system selection
      formData[`System___${prover}`] = prover;
      formData[`TimeLimit___${prover}`] = String(problem.timeout_sec ?? this.config.timeout_sec);

      const response = await postForm(SYSTEM_ON_TPTP_FORM, formData, {
        maxRetries: this.config.retry_count,
        baseDelayMs: this.config.retry_delay_ms,
        maxDelayMs: 16000,
      });

      const status = parseSZSStatus(response);
      const proof = extractProof(response);
      const elapsed = Date.now() - startTime;

      return {
        prover,
        status,
        proof,
        time_ms: parseTime(response) || elapsed,
        raw_output: response,
        timestamp: new Date(),
      };
    } catch (error) {
      return {
        prover,
        status: "error",
        error: error instanceof Error ? error.message : String(error),
        time_ms: Date.now() - startTime,
        timestamp: new Date(),
      };
    }
  }

  /** Solve with multiple provers in parallel */
  async solveMultiple(problem: Problem, provers?: string[]): Promise<ProverResult[]> {
    const targetProvers = provers ?? this.provers.map((p) => p.id);

    const results = await Promise.allSettled(
      targetProvers.map((p) => this.solve(problem, p))
    );

    return results.map((r, i) =>
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
  }
}

export default SystemOnTPTPClient;
