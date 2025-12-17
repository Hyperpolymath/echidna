/**
 * ECHIDNA Prover Types Tests
 *
 * SPDX-License-Identifier: MIT OR AGPL-3.0-or-later
 */

import { assertEquals, assertExists } from "https://deno.land/std@0.224.0/assert/mod.ts";
import { DEFAULT_CONFIG, PROVER_REGISTRY } from "./prover.ts";
import type { Problem, ProverResult } from "./prover.ts";

Deno.test("DEFAULT_CONFIG - has required fields", () => {
  assertExists(DEFAULT_CONFIG.timeout_sec);
  assertExists(DEFAULT_CONFIG.retry_count);
  assertExists(DEFAULT_CONFIG.retry_delay_ms);

  assertEquals(DEFAULT_CONFIG.timeout_sec, 60);
  assertEquals(DEFAULT_CONFIG.retry_count, 3);
  assertEquals(DEFAULT_CONFIG.retry_delay_ms, 1000);
});

Deno.test("PROVER_REGISTRY - contains expected provers", () => {
  assertExists(PROVER_REGISTRY.z3);
  assertExists(PROVER_REGISTRY.vampire);
  assertExists(PROVER_REGISTRY.metamath);

  assertEquals(PROVER_REGISTRY.z3.tier, 1);
  assertEquals(PROVER_REGISTRY.metamath.tier, 2);
});

Deno.test("Problem type - can create valid problem", () => {
  const problem: Problem = {
    id: "test-problem-1",
    name: "Test Problem",
    format: "tptp",
    content: "fof(test, axiom, p).",
    expected: "theorem",
    timeout_sec: 30,
    metadata: { source: "test" },
  };

  assertEquals(problem.id, "test-problem-1");
  assertEquals(problem.format, "tptp");
  assertExists(problem.content);
});

Deno.test("ProverResult type - can create valid result", () => {
  const result: ProverResult = {
    prover: "z3-wasm",
    status: "theorem",
    proof: "QED",
    time_ms: 123,
    timestamp: new Date(),
  };

  assertEquals(result.prover, "z3-wasm");
  assertEquals(result.status, "theorem");
  assertExists(result.timestamp);
});
