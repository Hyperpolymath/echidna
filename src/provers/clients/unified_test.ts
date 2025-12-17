/**
 * ECHIDNA Unified Prover Client Tests
 *
 * SPDX-License-Identifier: MIT OR AGPL-3.0-or-later
 */

import { assertEquals, assertExists } from "https://deno.land/std@0.224.0/assert/mod.ts";
import { UnifiedProverClient } from "./unified.ts";
import type { Problem } from "../types/prover.ts";

Deno.test("UnifiedProverClient - initialization", () => {
  const client = new UnifiedProverClient();

  assertEquals(client.name, "ECHIDNA-Unified");
  assertExists(client.provers);
  assertEquals(client.provers.length > 0, true);
});

Deno.test("UnifiedProverClient - listProvers", async () => {
  const client = new UnifiedProverClient();
  const provers = await client.listProvers();

  assertExists(provers);
  assertEquals(provers.length > 0, true);

  // Check for expected provers
  const ids = provers.map((p) => p.id);
  assertEquals(ids.includes("Vampire---4.8") || ids.includes("z3-wasm"), true);
});

Deno.test("UnifiedProverClient - getStats", () => {
  const client = new UnifiedProverClient();
  const stats = client.getStats();

  assertExists(stats);
  assertEquals(stats.totalProvers > 0, true);
  assertEquals(stats.backends > 0, true);
});

// Integration test - only run if network is available
Deno.test({
  name: "UnifiedProverClient - healthCheck (integration)",
  ignore: Deno.env.get("CI") === "true", // Skip in CI
  async fn() {
    const client = new UnifiedProverClient();
    const health = await client.healthCheck();

    assertExists(health);
    assertEquals(health.length > 0, true);

    // At least one service should have been checked
    for (const h of health) {
      assertExists(h.name);
      assertExists(h.lastCheck);
    }
  },
});

// Simple solve test with mock problem
Deno.test({
  name: "UnifiedProverClient - solve simple TPTP (integration)",
  ignore: Deno.env.get("CI") === "true", // Skip in CI
  async fn() {
    const client = new UnifiedProverClient({ timeout_sec: 30 });

    // Simple tautology
    const problem: Problem = {
      id: "test-1",
      format: "tptp",
      content: `
        fof(axiom1, axiom, p).
        fof(goal, conjecture, p).
      `,
    };

    const result = await client.solve(problem);

    assertExists(result);
    assertExists(result.prover);
    assertExists(result.status);
    assertExists(result.timestamp);
  },
});
