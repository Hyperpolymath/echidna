<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# Architecture

The canonical, current architecture overview lives in the repo at
[`docs/ARCHITECTURE.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ARCHITECTURE.md).
This page is a short summary; consult the in-repo doc for the up-to-date
component map and the 11-step trust pipeline walkthrough.

## Component map (one paragraph)

ECHIDNA is a polyglot system. The **Rust core** (`src/rust/`, plus extracted
workspace crates in `crates/`) owns dispatch, the trust pipeline, and the prover
backend implementations (105 implementation files behind 141 `ProverKind`
variants — see [`docs/PROVER_COUNT.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.md)). Four API surfaces (CLI, REPL, REST/GraphQL
on port 8000, gRPC on port 50051) hit `ProverDispatcher`, which picks a
backend, runs the verification under sandboxing (Podman / bubblewrap), and
walks the proof through the trust pipeline. A **Julia ML sidecar**
(`src/julia/`, port 8090) provides GNN-based premise ranking, tactic
suggestion, and accumulates per-(prover, domain) success-rate weights from
proof outcomes. **VeriSimDB** (cross-repo) persists `proof_attempts` rows
and serves `mv_prover_success_by_class` for history-guided routing; the
on-the-wire data dictionary is the formal E-R schema in
[`docs/architecture/VERISIM-ER-SCHEMA.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/architecture/VERISIM-ER-SCHEMA.md)
(companion Cap'n Proto schema:
[`crates/echidna-wire/schemas/verisim_er.capnp`](https://github.com/hyperpolymath/echidna/blob/main/crates/echidna-wire/schemas/verisim_er.capnp)).
**Idris2** (`src/abi/`) carries the FFI ABI proofs (zero `believe_me`).
**Agda** (`meta-checker/`) carries trust-pipeline meta-proofs. **AffineScript-TEA** sources live in `src/ui/tea/`; their compile pipeline
is not yet wired. The working static shell is `src/ui/public/prove.html`,
which can be opened directly in a browser.

## Corpus Ingest

Seventeen structural ingest adapters live under `src/rust/corpus/<name>.rs`,
each exposing `pub fn ingest(root: &Path) -> Result<Corpus>` that returns the
canonical `Corpus` struct ([`src/rust/corpus/mod.rs:156`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/corpus/mod.rs#L156)).
The adapters use a **two-pass extraction pattern**
([`src/rust/corpus/mod.rs:25`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/corpus/mod.rs#L25)):

1. **Pass 1** enumerates module names and decl names from the source tree.
2. **Pass 2** walks each decl's text and records references to any name in
   pass-1's known set. Comments (`--`, `{- … -}`, `(* … *)`, `;` etc. per
   language) are stripped before reference scanning. Decl boundaries are
   detected heuristically from column-0 identifiers followed by syntactic
   anchors. Hazards (axioms, sorry, believe_me, cheat, ?, mk_thm, …) populate
   `AxiomUsage` ([`src/rust/corpus/mod.rs:92`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/corpus/mod.rs#L92))
   per entry.

| Adapter | Source format | Notes |
|---|---|---|
| `agda` / `coq` / `lean` / `idris2` | native | pre-2026-04 |
| `isabelle` / `metamath` / `mizar` | `.thy` / `.mm` / `.miz` `.abs` | 2026-06-01 |
| `hol_light` / `hol4` | `.ml` filter / `*Script.sml` | 2026-06-01 |
| `dafny` / `why3` / `fstar` | `.dfy` / `.mlw` `.why` / `.fst` `.fsti` | 2026-06-01 |
| `acl2_books` | `.lisp` / `.acl2` | 2026-06-01 |
| `tptp` / `smtlib` | `.p` `.tptp` / `.smt2` `.smt` | 2026-06-01 |
| `proofnet` / `minif2f` | `.jsonl` / multi-target | 2026-06-01 |

Full per-adapter hazard inventory, fixture layout, and downstream consumer
wiring (`suggest` synonym table, `octad-emit` → VeriSimDB, GNN training data)
are documented in
[`docs/CORPUS-ADAPTERS.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/CORPUS-ADAPTERS.md).

## Cross-prover Vocabulary

Three layers stack over the per-prover synonym tables to give the
`echidna suggest` variant tester a cross-prover mathematical vocabulary:

1. **Per-prover synonym TOMLs** (`data/synonyms/<prover>.toml`). Each entry
   carries `canonical`, `aliases`, optional `tactic_class` and version range.
   The schema and variant-tester contract are documented in
   [`data/synonyms/README.adoc`](https://github.com/hyperpolymath/echidna/blob/main/data/synonyms/README.adoc).
   Loaded by `src/rust/suggest/synonyms.rs::SynonymTable::load_all()`.
2. **MSC2020** — `data/synonyms/_msc2020.toml`, 87 codes covering the
   Mathematics Subject Classification 2020 surface (e.g. `03B45` modal
   logic, `68V20` formalised mathematics). Merged via
   `SynonymTable::with_msc2020()`.
3. **WordNet 3.1 math sub-hierarchy** — `data/synonyms/_wordnet_math.toml`,
   ~80 lemmas anchoring natural-language terms to formal concepts.
   Merged via `SynonymTable::with_wordnet()`.
4. **ConceptNet 5.7 seed** — `data/synonyms/_conceptnet_seed.toml`, ~55
   pre-fetched edges so `semantic_class` resolution stays offline-resilient.
   Merged via `SynonymTable::with_conceptnet()`.

The cross-prover dictionaries are deliberately underscore-prefixed so the
loader can distinguish them from per-prover tables and route them through
`merge_external()` instead of `merge_prover()`.

## Arbitration Stack

When multiple provers attack the same goal, four arbitration mechanisms turn
the multiset of outcomes into a single decision. They compose: the typical
pipeline runs portfolio first to detect agreement, then Bayesian for a
posterior, then Pareto to pick the best-on-time-and-trust survivor.

### Portfolio majority-vote (`src/rust/verification/portfolio.rs`)

Simple agreement count across solvers in a SMT / ATP / ITP pool; flags
disagreements for human review. Original cross-checking surface.

### Bayesian posterior (`src/rust/verification/bayesian_arbiter.rs`)

```rust
pub fn combine(&self, evidence: &[ProverEvidence]) -> PosteriorVerdict
```

Treats each prover as a noisy binary sensor with calibrated
`(p_correct_given_true, p_correct_given_false)` likelihoods, then combines
independent observations using **log-odds accumulation** (numerically
stable). Timeout / Unknown / Error verdicts contribute a likelihood ratio of
1.0 (no update). Returns a `PosteriorVerdict` with `p_proven`, `p_refuted`,
`p_unknown`, `entropy_bits`, and `winning: Verdict`.

### Dempster-Shafer (`src/rust/verification/dempster_shafer.rs`)

```rust
pub fn submit(&mut self, prover: ProverKind, mass: MassFunction)
pub fn combine_all(&self) -> Result<BeliefPlausibility, ArbiterError>
```

Mass-function combination via Dempster's rule with **explicit ignorance**
(`MassFunction::ignorance()`); tracks the conflict scalar `K` across
combinations. Refuses to fuse when total conflict exceeds 0.95
(`ArbiterError::ExcessiveConflict`), surfacing the disagreement rather than
emitting a misleading belief.

### Pareto multi-objective arbiter (`src/rust/verification/pareto_arbiter.rs`)

```rust
pub fn arbitrate(&self, outcomes: &[AttemptOutcome]) -> ParetoDecision
```

Computes the Pareto frontier across (time, trust, memory, proof_size) and
applies a configurable `Tiebreak` policy via `with_tiebreak()` to pick a
single recommended outcome from the frontier. Callers should pre-filter to a
single agreed verdict (e.g. via the Bayesian arbiter) — mixed verdicts will
still return *some* frontier but its interpretation is undefined. Sibling of
the older `verification/pareto.rs` candidate-ranker; the arbiter operates on
already-completed `AttemptOutcome`s rather than candidates.

## Exchange Bridges

Six cross-prover proof-exchange formats live under `src/rust/exchange/`
([`src/rust/exchange/mod.rs:11`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/exchange/mod.rs#L11)):

| Bridge | Module | Use |
|---|---|---|
| OpenTheory | `exchange/opentheory.rs` | HOL family interop (HOL Light ↔ HOL4 ↔ Isabelle/HOL) |
| Dedukti | `exchange/dedukti.rs` | λΠ-calculus modulo rewriting — universal kernel |
| TPTP | `exchange/tptp.rs` | First-order ATP universal exchange (Vampire, E, SPASS, Princess, iProver, Twee). Imports / exports CNF + FOF; best-effort translation to/from SMT-LIB v2. TFF/THF dialects recognised at parse but rejected for translation to stay conservative |
| SMT-LIB v2 | `exchange/smtlib.rs` | Cross-solver normalisation (Z3, CVC5, Yices, MathSAT, Boolector); best-effort translator to TPTP FOF for the pure first-order fragment |
| SMTCoq | `exchange/smtcoq.rs` | STUB BRIDGE — Alethe / LFSC / DRAT parser + honest-skeleton emitter; the actual SMTCoq Coq-plugin invocation is gated on the upstream SMTCoq binary. Heavy operations are explicitly labelled `(* TODO: SMTCoq integration not yet wired *)` so callers detect skeleton-vs-reconstructed |
| Lambdapi | `exchange/lambdapi.rs` | Dedukti's successor — independent structured representation + syntactic translators to and from Dedukti so existing `dedukti.rs` consumers can upgrade without losing fidelity |

## Data Flow / Persistence Layer

Outcome emission (step 11 of the trust pipeline) writes through the formal
**VeriSim ↔ ECHIDNA E-R schema** rather than an ad-hoc payload. Authoritative
spec:

- [`docs/architecture/VERISIM-ER-SCHEMA.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/architecture/VERISIM-ER-SCHEMA.md)
  — **12 first-class entities** (`Octad`, `SemanticModality`, …) and
  **7 first-class relationships**. Each entity declares its Rust struct
  (e.g. `src/rust/verisim_bridge.rs::OctadPayload`), its VeriSimDB table
  (e.g. `octads`), its Cap'n Proto struct ID (e.g. `@0x80…001`), and its
  PK + FK set.
- [`crates/echidna-wire/schemas/verisim_er.capnp`](https://github.com/hyperpolymath/echidna/blob/main/crates/echidna-wire/schemas/verisim_er.capnp)
  — Cap'n Proto wire schema (file id `@0xe4dc7b1f01a06001`).

Drift between the prose spec and the `.capnp` schema is detected by a hash
over both files; the per-PR `er-drift` gate is tracked alongside.

## Trust pipeline (11 steps)

1. Integrity (SHAKE3-512 + BLAKE3 of solver binaries against `config/solver-manifest.toml`)
2. Dispatch (select backend; optionally history-guided via `VeriSimAdvisor`)
3. Sandbox (Podman / bubblewrap)
4. Portfolio cross-check (SMT: two independent solvers must agree)
5. Certificate verification (replay Alethe / DRAT-LRAT / TSTP independently)
6. Axiom tracking (Safe / Noted / Warning / Reject)
7. Confidence scoring (5-tier Bayesian)
8. Mutation testing (specifications)
9. Pareto frontier (speed × trust × certificate-availability)
10. Statistics update (per-(prover, domain) success rate)
11. Outcome emission to VeriSimDB (closes the learning loop)

## ProverBackend trait

```rust
#[async_trait]
trait ProverBackend: Send + Sync {
    fn kind(&self) -> ProverKind;
    async fn version(&self) -> Result<String>;
    async fn parse_string(&self, content: &str) -> Result<ProofState>;
    async fn apply_tactic(&self, state: &ProofState, t: &Tactic) -> Result<TacticResult>;
    async fn verify_proof(&self, state: &ProofState) -> Result<bool>;
    async fn check(&self, state: &ProofState) -> Result<ProverOutcome>; // rich variant
    async fn suggest_tactics(&self, state: &ProofState, limit: usize) -> Result<Vec<Tactic>>;
    async fn export(&self, state: &ProofState) -> Result<String>;
}
```

See [`src/rust/provers/mod.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/provers/mod.rs).

## Polyglot source layout

| Path | Language | Role |
|---|---|---|
| `src/rust/` + `crates/` | Rust | Core, dispatch, trust, backends, servers |
| `src/julia/` | Julia | ML sidecar, GNN, training, eval |
| `src/abi/` | Idris 2 | Formal FFI ABI proofs |
| `meta-checker/` | Agda | Trust-pipeline meta-proofs |
| `src/chapel/` + `src/zig_ffi/` | Chapel + Zig | Parallel proof search (L2.1 live) |
| `src/ada/` + `spark/` | Ada/SPARK | Formal companion library |
| `src/ui/tea/` | AffineScript-TEA | UI sources; compile pipeline unavailable |
| `src/ui/public/` | HTML/static assets | Working browser shell |

Pointers and history evolve; the in-repo [`docs/ARCHITECTURE.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ARCHITECTURE.md) is authoritative.
