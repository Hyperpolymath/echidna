/**
 * ECHIDNA Prover Integration Module
 * Deno-native theorem prover integration (NO NPM)
 *
 * SPDX-License-Identifier: MIT OR AGPL-3.0-or-later
 */

// Types
export type {
  InputFormat,
  ProverStatus,
  Prover,
  ProverResult,
  Problem,
  QueueItem,
  ProverConfig,
  ProverClient,
  BatchProverClient,
} from "./types/prover.ts";

export { DEFAULT_CONFIG, PROVER_REGISTRY } from "./types/prover.ts";

// Clients
export { SystemOnTPTPClient } from "./clients/system_on_tptp.ts";
export { MetamathClient } from "./clients/metamath.ts";
export { Z3WasmClient, Z3FallbackClient } from "./clients/z3_wasm.ts";
export { WolframAlphaClient } from "./clients/wolfram.ts";
export { LeanToolClient } from "./clients/lean_tool.ts";
export { UnifiedProverClient } from "./clients/unified.ts";
export type { SelectionStrategy, UnifiedResult, ServiceHealth } from "./clients/unified.ts";

// Runners
export { ProofRunnerDaemon } from "./runners/daemon.ts";
export type { DaemonConfig, DaemonStats, DaemonEvent, EventHandler } from "./runners/daemon.ts";

// Utilities
export { fetchWithRetry, postForm, postJSON, getText, sleep, backoffDelay } from "./utils/http.ts";
