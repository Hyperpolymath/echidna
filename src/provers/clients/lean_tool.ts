/**
 * ECHIDNA LeanTool Client
 * Lean 4 theorem proving via OpenAI-compatible API
 *
 * SPDX-License-Identifier: MIT OR AGPL-3.0-or-later
 *
 * Uses the LeanTool OpenAI-compatible API server
 * Demo: http://www.codeproofarena.com:8800/v1
 */

import type {
  Problem,
  Prover,
  ProverClient,
  ProverConfig,
  ProverResult,
  ProverStatus,
} from "../types/prover.ts";
import { postJSON } from "../utils/http.ts";

/** Default LeanTool API endpoint */
const LEANTOOL_DEFAULT_ENDPOINT = "http://www.codeproofarena.com:8800/v1";

/** Lean Playground endpoint for fallback */
const LEAN_PLAYGROUND_URL = "https://live.lean-lang.org";

/** OpenAI-compatible chat completion request */
interface ChatCompletionRequest {
  model: string;
  messages: Array<{
    role: "system" | "user" | "assistant";
    content: string;
  }>;
  temperature?: number;
  max_tokens?: number;
}

/** OpenAI-compatible chat completion response */
interface ChatCompletionResponse {
  id: string;
  object: string;
  created: number;
  model: string;
  choices: Array<{
    index: number;
    message: {
      role: string;
      content: string;
    };
    finish_reason: string;
  }>;
  usage?: {
    prompt_tokens: number;
    completion_tokens: number;
    total_tokens: number;
  };
}

/** Parse Lean output for proof status */
function parseLeanOutput(output: string): {
  status: ProverStatus;
  proof?: string;
  error?: string;
} {
  const lowerOutput = output.toLowerCase();

  // Check for errors
  if (
    lowerOutput.includes("error") ||
    lowerOutput.includes("unknown identifier") ||
    lowerOutput.includes("type mismatch")
  ) {
    return {
      status: "error",
      error: output,
    };
  }

  // Check for successful proof
  if (
    lowerOutput.includes("no goals") ||
    lowerOutput.includes("goals accomplished") ||
    lowerOutput.includes("qed") ||
    lowerOutput.includes("exact") ||
    lowerOutput.includes("rfl")
  ) {
    return {
      status: "theorem",
      proof: output,
    };
  }

  // Check for counterexample
  if (
    lowerOutput.includes("counterexample") ||
    lowerOutput.includes("failed")
  ) {
    return {
      status: "countersatisfiable",
      error: output,
    };
  }

  return {
    status: "unknown",
  };
}

export class LeanToolClient implements ProverClient {
  readonly name = "LeanTool";
  readonly provers: Prover[] = [
    {
      id: "lean4",
      name: "Lean 4",
      formats: ["lean"],
      tier: 3,
      online: true,
    },
    {
      id: "lean4-mathlib",
      name: "Lean 4 + Mathlib",
      formats: ["lean"],
      tier: 3,
      online: true,
    },
  ];

  private config: ProverConfig;
  private endpoint: string;
  private apiKey: string;

  constructor(config: Partial<ProverConfig> = {}) {
    this.config = {
      timeout_sec: config.timeout_sec ?? 120,
      retry_count: config.retry_count ?? 3,
      retry_delay_ms: config.retry_delay_ms ?? 1000,
    };

    this.endpoint = config.endpoint ?? Deno.env.get("LEANTOOL_ENDPOINT") ?? LEANTOOL_DEFAULT_ENDPOINT;
    this.apiKey = config.api_key ?? Deno.env.get("LEANTOOL_API_KEY") ?? "";
  }

  async ping(): Promise<boolean> {
    try {
      const response = await fetch(`${this.endpoint}/models`, {
        headers: this.apiKey ? { Authorization: `Bearer ${this.apiKey}` } : {},
      });
      return response.ok;
    } catch {
      // Try playground as fallback
      try {
        const response = await fetch(LEAN_PLAYGROUND_URL);
        return response.ok;
      } catch {
        return false;
      }
    }
  }

  async listProvers(): Promise<Prover[]> {
    return this.provers;
  }

  async solve(problem: Problem, prover?: string): Promise<ProverResult> {
    const startTime = Date.now();
    const proverId = prover ?? "lean4";

    try {
      // Build chat completion request
      const request: ChatCompletionRequest = {
        model: proverId === "lean4-mathlib" ? "lean4-mathlib" : "lean4",
        messages: [
          {
            role: "system",
            content:
              "You are a Lean 4 theorem prover. Verify the given Lean code and report whether it type-checks successfully.",
          },
          {
            role: "user",
            content: problem.content,
          },
        ],
        temperature: 0,
        max_tokens: 2048,
      };

      const headers: Record<string, string> = {};
      if (this.apiKey) {
        headers["Authorization"] = `Bearer ${this.apiKey}`;
      }

      const response = await postJSON<ChatCompletionResponse>(
        `${this.endpoint}/chat/completions`,
        request,
        headers,
        {
          maxRetries: this.config.retry_count,
          baseDelayMs: this.config.retry_delay_ms,
          maxDelayMs: 16000,
        }
      );

      const output = response.choices[0]?.message?.content ?? "";
      const { status, proof, error } = parseLeanOutput(output);

      return {
        prover: proverId,
        status,
        proof,
        error,
        time_ms: Date.now() - startTime,
        raw_output: output,
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

  /** Check a Lean theorem */
  async checkTheorem(code: string): Promise<ProverResult> {
    return this.solve(
      {
        id: crypto.randomUUID(),
        format: "lean",
        content: code,
      },
      "lean4"
    );
  }

  /** Check with Mathlib imports */
  async checkWithMathlib(code: string): Promise<ProverResult> {
    return this.solve(
      {
        id: crypto.randomUUID(),
        format: "lean",
        content: code,
      },
      "lean4-mathlib"
    );
  }
}

export default LeanToolClient;
