/**
 * ECHIDNA Wolfram Alpha API Client
 * Theorem proving and equation solving via Wolfram Alpha
 *
 * SPDX-License-Identifier: MIT OR AGPL-3.0-or-later
 *
 * Free tier: 2,000 non-commercial API calls per month
 * Get API key at: https://developer.wolframalpha.com/
 */

import type {
  Problem,
  Prover,
  ProverClient,
  ProverConfig,
  ProverResult,
  ProverStatus,
} from "../types/prover.ts";
import { fetchWithRetry } from "../utils/http.ts";

const WOLFRAM_API_BASE = "https://api.wolframalpha.com/v2";

/** Wolfram Alpha API response structure */
interface WolframResponse {
  queryresult: {
    success: boolean;
    error: boolean;
    numpods: number;
    pods?: WolframPod[];
    timedout: string;
    timing: number;
  };
}

interface WolframPod {
  title: string;
  id: string;
  primary?: boolean;
  subpods: WolframSubpod[];
}

interface WolframSubpod {
  title: string;
  plaintext?: string;
  img?: {
    src: string;
    alt: string;
  };
}

/** Extract proof-related content from Wolfram response */
function extractProofContent(response: WolframResponse): {
  status: ProverStatus;
  proof?: string;
  model?: string;
} {
  const pods = response.queryresult.pods ?? [];

  // Look for proof-related pods
  const proofPod = pods.find(
    (p) =>
      p.title.toLowerCase().includes("proof") ||
      p.title.toLowerCase().includes("derivation") ||
      p.title.toLowerCase().includes("step")
  );

  const resultPod = pods.find(
    (p) =>
      p.title.toLowerCase().includes("result") ||
      p.title.toLowerCase().includes("solution") ||
      p.primary
  );

  const truthPod = pods.find(
    (p) =>
      p.title.toLowerCase().includes("truth") ||
      p.title.toLowerCase().includes("statement")
  );

  // Determine status
  let status: ProverStatus = "unknown";
  let proof: string | undefined;
  let model: string | undefined;

  if (proofPod) {
    proof = proofPod.subpods.map((s) => s.plaintext).filter(Boolean).join("\n");
    status = "theorem";
  }

  if (truthPod) {
    const text = truthPod.subpods[0]?.plaintext?.toLowerCase() ?? "";
    if (text.includes("true") || text.includes("valid")) {
      status = "theorem";
    } else if (text.includes("false") || text.includes("invalid")) {
      status = "countersatisfiable";
    }
  }

  if (resultPod) {
    model = resultPod.subpods.map((s) => s.plaintext).filter(Boolean).join("\n");
    if (model && status === "unknown") {
      status = "satisfiable";
    }
  }

  return { status, proof, model };
}

export class WolframAlphaClient implements ProverClient {
  readonly name = "WolframAlpha";
  readonly provers: Prover[] = [
    {
      id: "wolfram-prove",
      name: "Wolfram Alpha Prover",
      formats: ["natural", "wolfram"],
      tier: 3,
      online: true,
    },
    {
      id: "wolfram-solve",
      name: "Wolfram Alpha Solver",
      formats: ["natural", "wolfram"],
      tier: 3,
      online: true,
    },
  ];

  private config: ProverConfig;
  private apiKey: string;

  constructor(config: Partial<ProverConfig> = {}) {
    this.config = {
      timeout_sec: config.timeout_sec ?? 60,
      retry_count: config.retry_count ?? 3,
      retry_delay_ms: config.retry_delay_ms ?? 1000,
    };

    // Get API key from environment
    this.apiKey = config.api_key ?? Deno.env.get("WOLFRAM_APP_ID") ?? "";
  }

  async ping(): Promise<boolean> {
    if (!this.apiKey) {
      console.warn("[Wolfram] No API key configured (set WOLFRAM_APP_ID)");
      return false;
    }

    try {
      const url = new URL(`${WOLFRAM_API_BASE}/query`);
      url.searchParams.set("appid", this.apiKey);
      url.searchParams.set("input", "2+2");
      url.searchParams.set("format", "plaintext");
      url.searchParams.set("output", "json");

      const response = await fetchWithRetry(url.toString());
      const data: WolframResponse = await response.json();
      return data.queryresult.success;
    } catch {
      return false;
    }
  }

  async listProvers(): Promise<Prover[]> {
    return this.provers;
  }

  async solve(problem: Problem, prover?: string): Promise<ProverResult> {
    const startTime = Date.now();
    const proverId = prover ?? "wolfram-prove";

    if (!this.apiKey) {
      return {
        prover: proverId,
        status: "error",
        error: "No Wolfram Alpha API key configured. Set WOLFRAM_APP_ID environment variable.",
        time_ms: Date.now() - startTime,
        timestamp: new Date(),
      };
    }

    try {
      // Format query based on prover type
      let query = problem.content;

      if (proverId === "wolfram-prove") {
        // Prepend "prove" if not already a proof query
        if (!query.toLowerCase().startsWith("prove")) {
          query = `prove ${query}`;
        }
      }

      const url = new URL(`${WOLFRAM_API_BASE}/query`);
      url.searchParams.set("appid", this.apiKey);
      url.searchParams.set("input", query);
      url.searchParams.set("format", "plaintext");
      url.searchParams.set("output", "json");
      url.searchParams.set("podtimeout", String(problem.timeout_sec ?? this.config.timeout_sec));

      const response = await fetchWithRetry(url.toString(), undefined, {
        maxRetries: this.config.retry_count,
        baseDelayMs: this.config.retry_delay_ms,
        maxDelayMs: 16000,
      });

      const data: WolframResponse = await response.json();

      if (!data.queryresult.success) {
        return {
          prover: proverId,
          status: data.queryresult.timedout ? "timeout" : "unknown",
          error: data.queryresult.error ? "Wolfram Alpha query failed" : undefined,
          time_ms: (data.queryresult.timing ?? 0) * 1000,
          timestamp: new Date(),
        };
      }

      const { status, proof, model } = extractProofContent(data);

      return {
        prover: proverId,
        status,
        proof,
        model,
        time_ms: (data.queryresult.timing ?? 0) * 1000,
        raw_output: JSON.stringify(data, null, 2),
        timestamp: new Date(),
      };
    } catch (error) {
      return {
        prover: proverId,
        status: "error",
        error: error instanceof Error ? error.message : String(error),
        time_ms: Date.now() - startTime,
        timestamp: new Date(),
      };
    }
  }

  /** Prove a mathematical statement */
  async prove(statement: string): Promise<ProverResult> {
    return this.solve(
      { id: crypto.randomUUID(), format: "natural", content: statement },
      "wolfram-prove"
    );
  }

  /** Solve an equation or system */
  async equation(equation: string): Promise<ProverResult> {
    return this.solve(
      { id: crypto.randomUUID(), format: "natural", content: `solve ${equation}` },
      "wolfram-solve"
    );
  }
}

export default WolframAlphaClient;
