## Machine-Readable Artefacts

The following files in `.machine_readable/` contain structured project metadata:

- `.machine_readable/descriptiles/STATE.a2ml` - Current project state and progress
- `.machine_readable/descriptiles/META.a2ml` - Architecture decisions and development practices
- `.machine_readable/descriptiles/ECOSYSTEM.a2ml` - Position in the ecosystem and related projects
- `.machine_readable/descriptiles/AGENTIC.a2ml` - AI agent interaction patterns
- `.machine_readable/descriptiles/NEUROSYM.a2ml` - Neurosymbolic integration config
- `.machine_readable/descriptiles/PLAYBOOK.a2ml` - Operational runbook
- `.machine_readable/bot_directives/*.a2ml` - Per-bot permission and scope rules

## Canonical Roadmap

See [`docs/ROADMAP.md`](../docs/ROADMAP.md) for the single source of truth on
where ECHIDNA is going: the 8‑stage map, row‑by‑row endpoint targets,
current sprint (S1–S5), and agent‑tier guidance.  Record decisions
there, not in chat.

## Supervised Multi-Agent Execution

When a supervising agent (Opus) plans work that will be implemented by
a focused executor (Sonnet) or a mechanical bulk agent (Haiku), the
supervisor MUST run a **Haiku scout pass** immediately before spawning
the implementation agent, unless the scope is strictly single‑file
and under ten lines of change.

### Scout pattern

**Purpose**: clear obvious cruft (unused imports, stale comments,
dead stubs, broken references) so the implementation agent arrives
to clean ground and does not burn tokens on trivial lint.

**When to run**: once per upcoming step, after the step's scope is
locked and before the implementation agent is launched.

**Prompt template** (copy this verbatim, fill in the file list):

```
Haiku scout, scope = <exact file list for the step>

1. Confirm each file compiles in isolation (cargo check --lib / julia -e).
2. Scan for: unused imports, dead code, `todo!()/FIXME/XXX`,
   orphan type references, stale doc comments referring to
   renamed symbols, broken `mod.rs` exports.
3. Trivially fix:
   - unused imports (remove)
   - obvious typos in comments
   - unused `_var` renames
4. DO NOT fix — FLAG to me:
   - any TODO with semantic content (may be load-bearing)
   - anything requiring judgement about intent
   - any cross-module change
5. Report: <20 lines. Green-light or list of blockers.
```

**Caveats**:

- Scout is **not** a full audit.  Full audits remain the periodic
  cross‑module sweep (cf. the Agent A + Agent B pattern in session
  history); scout is narrow prep for an imminent step.
- Scout must **not over‑fix**.  TODO/FIXME comments sometimes
  contain the spec for the upcoming work — flag, don't delete.
- Scout is **idempotent**.  Re‑running on unchanged code should
  produce the same report.
- If scout flags a blocker, the supervisor decides whether to
  resolve it inline, expand the step's scope, or defer.  The
  implementation agent does not launch until the supervisor
  green‑lights.

**Commit convention** (when the scout applied trivial fixes):

```
chore(<scope>): scout-pass trivial cleanup ahead of <step id>
```

### CRITICAL: .scm metadata files are DEPRECATED

**All `.scm` state/metadata files have been replaced by `.a2ml`.**

If you find any `.scm` file under `.machine_readable/` (state/metadata descriptors
such as STATE, META, ECOSYSTEM, AGENTIC, NEUROSYM or PLAYBOOK carrying the legacy
Scheme extension, bot directive files, or similar), you MUST:

1. Check whether an equivalent `.a2ml` file already exists
2. If yes — delete the `.scm` file immediately (`git rm`)
3. If no — convert its content to A2ML format first, then delete the `.scm` original

**Exception:** `guix.scm` files and files under `guix/` or `guix-channel/` are Guix
package definitions (not metadata files) and must NOT be deleted.

---

# CLAUDE.md - AI Assistant Instructions

## Language Policy (Hyperpolymath Standard)

### ALLOWED Languages & Tools

| Language/Tool | Use Case | Notes |
|---------------|----------|-------|
| **Rust** | Core systems, prover backends, trust pipeline, CLI, WASM | Primary implementation language |
| **Julia** | ML inference, batch data processing, extract scripts | Per RSR |
| **Idris2** | ABI formal proofs (zero `believe_me`) | `src/abi/` — 16 modules, constructive |
| **Agda** | Trust-pipeline meta-checker proofs | `proofs/agda/` |
| **Zig** | FFI shim between Rust and Chapel | `src/zig_ffi/` |
| **Chapel** | Optional parallel proof dispatch | Wired via Cargo `chapel` feature |
| **Guile Scheme** | Guix package definitions (`guix.scm`, `manifests/*.scm`) | `.scm` metadata files are deprecated — see below |
| **Bash/POSIX Shell** | Build scripts, CI glue | Keep minimal |
| **AffineScript** | UI components (TEA architecture, compiled to typed-wasm / wasm, served via Deno) | Replaces AffineScript per `docs/ROADMAP.md`; migration in progress at `src/ui/` |
| **Bun** | Runtime for compiled AffineScript-TEA UI | Replaces Node/npm/Deno |
| **JavaScript** | Build tooling only (Tailwind config, test harness) | Not for business logic |
| **OCaml** | AffineScript compiler host | Decision locked — AffineScript selected for UI |
| **Nickel** | Configuration language | Used across `configs/`, `echidna-playground/contractiles/k9/`, `.machine_readable/`, `echidnabot/config/` (11+ `.ncl` files) |

### BANNED - Do Not Use

| Banned | Replacement |
|--------|-------------|
| TypeScript | AffineScript |
| ReScript | AffineScript |
| Deno | Bun |
| Node.js | Bun |
| npm / pnpm / yarn | Bun |
| Go | Rust |
| Python | Julia / Rust |

### Enforcement Rules

1. **No new TypeScript or ReScript files** - Use AffineScript-TEA; migrate existing `src/ui/` to AffineScript per `docs/ROADMAP.md`
2. **Use `package.json` + `bun.lock` for JS runtime deps** - Bun is npm-compatible; a manifest is REQUIRED
3. **`bun install --production --frozen-lockfile` for production deps** - resolved from `package.json` and pinned via `bun.lock`; `--frozen-lockfile` makes a lockfile mismatch a build failure rather than a silent re-resolve
4. **No Go code** - Use Rust instead
5. **No Python anywhere** - Use Julia for data/batch, Rust for systems

### Package Management

- **Sole primary**: Guix (`guix.scm`, `manifests/*.scm`)
- **Escape hatch**: a sealed container (`.containerization/Containerfile.wave3`)
  for the not-in-Guix / non-free tail. **NO Guix anywhere** — estate ruling
  2026-05-18 (Guix primary + sealed-container escape), hardened 2026-06-01
  (guix deprecated estate-wide; do NOT add `flake.guix`/`flake.lock` back).
  A second packager is permitted only where it is the sole source of a
  specific named dependency, documented as such.
- **JS deps**: Bun (`package.json` + `bun.lock`). Declare tooling as a devDependency and run `bunx --no-install --bun <tool>` — a bare `bunx <tool>` can fetch an unpinned package and may start Node via its shebang.

### Security Requirements

- No MD5/SHA1 for security (use SHA256+)
- HTTPS only (no HTTP URLs)
- No hardcoded secrets
- SHA-pinned dependencies
- SPDX license headers on all files

