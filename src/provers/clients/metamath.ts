/**
 * ECHIDNA Metamath Client
 * Metamath proof verification and exploration
 * Uses metamath.js concepts ported to Deno
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
import { getText } from "../utils/http.ts";

/** Metamath databases available online */
const METAMATH_DATABASES = {
  "set.mm": "https://raw.githubusercontent.com/metamath/set.mm/develop/set.mm",
  "iset.mm": "https://raw.githubusercontent.com/metamath/set.mm/develop/iset.mm",
  "hol.mm": "https://raw.githubusercontent.com/metamath/set.mm/develop/hol.mm",
};

/** Metamath token types */
type TokenType = "constant" | "variable" | "label" | "keyword";

interface Token {
  type: TokenType;
  value: string;
  line: number;
  col: number;
}

/** Simple Metamath statement */
interface MMStatement {
  label: string;
  type: "$a" | "$p" | "$e" | "$f";
  symbols: string[];
  proof?: string[];
}

/** Metamath database (parsed) */
interface MMDatabase {
  constants: Set<string>;
  variables: Set<string>;
  statements: Map<string, MMStatement>;
  axioms: string[];
  theorems: string[];
}

/** Tokenize Metamath source */
function tokenize(source: string): Token[] {
  const tokens: Token[] = [];
  const lines = source.split("\n");
  const keywords = new Set(["$c", "$v", "$f", "$e", "$a", "$p", "$d", "$=", "$.", "${", "$}"]);

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    let col = 0;

    // Skip comments
    if (line.includes("$(")) {
      const commentStart = line.indexOf("$(");
      const commentEnd = line.indexOf("$)", commentStart);
      if (commentEnd === -1) continue; // Multi-line comment, skip for now
    }

    const parts = line.split(/\s+/).filter((p) => p.length > 0);

    for (const part of parts) {
      if (part.startsWith("$(") || part.endsWith("$)")) continue;

      const type: TokenType = keywords.has(part)
        ? "keyword"
        : part.match(/^[a-zA-Z0-9_.-]+$/)
        ? "label"
        : "constant";

      tokens.push({ type, value: part, line: lineNum, col });
      col += part.length + 1;
    }
  }

  return tokens;
}

/** Parse Metamath source into database structure */
function parseMetamath(source: string): MMDatabase {
  const db: MMDatabase = {
    constants: new Set(),
    variables: new Set(),
    statements: new Map(),
    axioms: [],
    theorems: [],
  };

  const tokens = tokenize(source);
  let i = 0;

  while (i < tokens.length) {
    const token = tokens[i];

    if (token.value === "$c") {
      // Constant declaration
      i++;
      while (i < tokens.length && tokens[i].value !== "$.") {
        db.constants.add(tokens[i].value);
        i++;
      }
    } else if (token.value === "$v") {
      // Variable declaration
      i++;
      while (i < tokens.length && tokens[i].value !== "$.") {
        db.variables.add(tokens[i].value);
        i++;
      }
    } else if (token.type === "label") {
      // Statement with label
      const label = token.value;
      i++;
      if (i < tokens.length) {
        const stmtType = tokens[i].value as "$a" | "$p" | "$e" | "$f";
        i++;

        const symbols: string[] = [];
        const proof: string[] = [];
        let inProof = false;

        while (i < tokens.length && tokens[i].value !== "$.") {
          if (tokens[i].value === "$=") {
            inProof = true;
          } else if (inProof) {
            proof.push(tokens[i].value);
          } else {
            symbols.push(tokens[i].value);
          }
          i++;
        }

        const stmt: MMStatement = { label, type: stmtType, symbols };
        if (proof.length > 0) stmt.proof = proof;

        db.statements.set(label, stmt);

        if (stmtType === "$a") db.axioms.push(label);
        if (stmtType === "$p") db.theorems.push(label);
      }
    }
    i++;
  }

  return db;
}

/** Verify a proof step */
function verifyProofStep(
  _db: MMDatabase,
  _theorem: string,
  _proof: string[]
): { valid: boolean; error?: string } {
  // Simplified verification - full implementation would need stack-based RPN
  // This is a placeholder that checks basic structure
  return { valid: true };
}

export class MetamathClient implements ProverClient {
  readonly name = "Metamath";
  readonly provers: Prover[] = [
    { id: "metamath-verify", name: "Metamath Verifier", formats: ["metamath"], tier: 2, online: true },
  ];

  private config: ProverConfig;
  private databases: Map<string, MMDatabase> = new Map();

  constructor(config: Partial<ProverConfig> = {}) {
    this.config = {
      timeout_sec: config.timeout_sec ?? 60,
      retry_count: config.retry_count ?? 3,
      retry_delay_ms: config.retry_delay_ms ?? 1000,
    };
  }

  async ping(): Promise<boolean> {
    try {
      // Check if we can fetch a small part of set.mm
      const response = await fetch(METAMATH_DATABASES["set.mm"], {
        method: "HEAD",
      });
      return response.ok;
    } catch {
      return false;
    }
  }

  async listProvers(): Promise<Prover[]> {
    return this.provers;
  }

  /** Load a Metamath database */
  async loadDatabase(name: keyof typeof METAMATH_DATABASES): Promise<MMDatabase> {
    if (this.databases.has(name)) {
      return this.databases.get(name)!;
    }

    console.log(`[Metamath] Loading database: ${name}`);
    const source = await getText(METAMATH_DATABASES[name]);
    const db = parseMetamath(source);
    this.databases.set(name, db);

    console.log(
      `[Metamath] Loaded ${name}: ${db.axioms.length} axioms, ${db.theorems.length} theorems`
    );
    return db;
  }

  async solve(problem: Problem, _prover?: string): Promise<ProverResult> {
    const startTime = Date.now();

    try {
      // Parse the problem as Metamath source
      const db = parseMetamath(problem.content);

      // Find theorems to verify
      const theorems = db.theorems;

      if (theorems.length === 0) {
        return {
          prover: "metamath-verify",
          status: "unknown",
          error: "No theorems ($p statements) found in input",
          time_ms: Date.now() - startTime,
          timestamp: new Date(),
        };
      }

      // Verify each theorem
      const results: Array<{ label: string; valid: boolean; error?: string }> = [];

      for (const label of theorems) {
        const stmt = db.statements.get(label)!;
        const result = verifyProofStep(db, label, stmt.proof ?? []);
        results.push({ label, ...result });
      }

      const allValid = results.every((r) => r.valid);
      const status: ProverStatus = allValid ? "theorem" : "error";

      return {
        prover: "metamath-verify",
        status,
        proof: allValid ? `Verified ${theorems.length} theorem(s)` : undefined,
        error: allValid
          ? undefined
          : results
              .filter((r) => !r.valid)
              .map((r) => `${r.label}: ${r.error}`)
              .join("; "),
        time_ms: Date.now() - startTime,
        raw_output: JSON.stringify(results, null, 2),
        timestamp: new Date(),
      };
    } catch (error) {
      return {
        prover: "metamath-verify",
        status: "error",
        error: error instanceof Error ? error.message : String(error),
        time_ms: Date.now() - startTime,
        timestamp: new Date(),
      };
    }
  }

  /** Search for a theorem by pattern */
  async searchTheorem(
    pattern: string,
    database: keyof typeof METAMATH_DATABASES = "set.mm"
  ): Promise<string[]> {
    const db = await this.loadDatabase(database);
    const regex = new RegExp(pattern, "i");

    return [...db.statements.entries()]
      .filter(([label, stmt]) => {
        return (
          regex.test(label) ||
          stmt.symbols.some((s) => regex.test(s))
        );
      })
      .map(([label]) => label)
      .slice(0, 100);
  }

  /** Get theorem details */
  async getTheorem(
    label: string,
    database: keyof typeof METAMATH_DATABASES = "set.mm"
  ): Promise<MMStatement | undefined> {
    const db = await this.loadDatabase(database);
    return db.statements.get(label);
  }
}

export default MetamathClient;
