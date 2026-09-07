// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: AGPL-3.0-or-later

#![allow(dead_code)]

//! Theorem prover backend implementations
//!
//! Supports 12 theorem provers across 4 tiers

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

use crate::core::{ProofState, Tactic, TacticResult};

pub mod outcome;
pub use outcome::{classify_anyhow_error, ProverOutcome};

pub mod io;
pub use io::{bounded_read_corpus_file, bounded_read_proof_file, MAX_PROOF_BYTES};

pub mod abc;
pub mod abella;
pub mod acl2;
pub mod acl2s;
pub mod agda;
pub mod agsyhol;
pub mod alloy;
pub mod altergo;
pub mod aprove;
pub mod arend;
pub mod athena;
pub mod boogie;
pub mod cadical;
pub mod cameleer;
pub mod cbmc;
pub mod chuffed;
pub mod connection_method;
pub mod coq;
pub mod cryptoverif;
pub mod csi;
pub mod cubical_agda;
pub mod cvc5;
pub mod dafny;
pub mod dedukti;
pub mod dreal;
pub mod easycrypt;
pub mod elk;
pub mod eprover;
pub mod faial;
pub mod framac;
pub mod fstar;
pub mod glpk;
pub mod gnatprove;
pub mod gpuverify;
pub mod hol4;
pub mod hol_light;
pub mod hp_ecosystem;
pub mod idris2;
pub mod ileancop;
pub mod imandra;
pub mod iprover;
pub mod isabelle;
pub mod isabelle_zf;
pub mod key;
pub mod keymaerax;
pub mod kissat;
pub mod konclude;
pub mod lambda_prolog;
pub mod lash;
pub mod lean;
pub mod lean3;
pub mod leo3;
pub mod liquid_haskell;
pub mod matita;
pub mod mercury;
pub mod metamath;
pub mod metitarski;
pub mod mettel2;
pub mod minisat;
pub mod minizinc;
pub mod minlog;
pub mod mizar;
pub mod mizar_ar;
pub mod mleancop;
pub mod nanocop;
pub mod naproche;
pub mod nitpick;
pub mod nunchaku;
pub mod nuprl;
pub mod nusmv;
pub mod opensmt;
pub mod ortools;
pub mod princess;
pub mod prism;
pub mod prob;
pub mod prover9;
pub mod proverif;
pub mod pvs;
pub mod qepcad;
pub mod redlog;
pub mod rocq;
pub mod satallax;
pub mod scip;
pub mod seahorn;
pub mod smtrat;
pub mod spass;
pub mod spin_checker;
pub mod stainless;
pub mod storm;
pub mod tamarin;
pub mod tlaps;
pub mod tlc;
pub mod tptp_output;
pub mod twee;
pub mod twelf;
pub mod typed_wasm;
pub mod uppaal;
pub mod uppaal_stratego;
pub mod vampire;
pub mod viper;
pub mod why3;
pub mod z3;
pub mod zipperposition;

/// Enumeration of all supported provers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, strum::EnumIter)]
pub enum ProverKind {
    // Tier 1: Original + SMT solvers
    Agda,
    Coq,
    Lean,
    Isabelle,
    Z3,
    CVC5,

    // Tier 2: "Big Six" completion
    Metamath,
    HOLLight,
    Mizar,

    // Tier 3: Additional coverage
    PVS,
    ACL2,

    // Tier 4: Advanced
    HOL4,

    // Extended: Additional provers
    Idris2,
    /// Lean 3 — sibling prover to Lean 4 (not a version of it).
    /// mathlib3 preserves a substantial corpus that never fully ported
    /// to mathlib4; port-pairs between mathlib3 and mathlib4 give the
    /// arbiter ready-made cross-system evidence for the same theorem.
    Lean3,

    // Tier 5: First-Order ATPs
    Vampire,
    EProver,
    SPASS,
    AltErgo,

    // Tier 5b: Higher-Order ATPs
    Leo3,
    Satallax,
    Lash,
    AgsyHOL,

    // Tier 5c: Frontier First-Order ATPs
    IProver,
    Princess,
    Twee,
    MetiTarski,
    CSI,
    AProVE,

    // Tier 5d: Hybrid systems / differential dynamic logic
    KeYmaeraX,

    // Tier 5e: Real-algebraic decision (CAD / virtual substitution)
    Qepcad,
    Redlog,

    // Tier 5f: Connection-method classical / intuitionistic / lean kernel
    MleanCoP,
    IleanCoP,
    NanoCoP,

    // Tier 5g: Tableau-prover generator for arbitrary modal logics
    MetTeL2,

    // Tier 5h: Description-logic reasoners (OWL EL / OWL DL).
    // ELK is the EL-profile specialist; Konclude handles full SROIQ.
    ELK,
    Konclude,

    // Tier 5i: Probabilistic model checking (modern PRISM successor).
    Storm,

    // Tier 5j: B-method / Event-B model checker.
    ProB,

    // Tier 5k: Computational-cryptography proof assistant
    // (game-based, interactive).
    EasyCrypt,

    // Tier 5l: Computational-cryptography automated prover
    // (game-hopping, complementary to EasyCrypt).
    CryptoVerif,

    // Tier 6: Dependent types + effects, auto-active, orchestration
    FStar,
    Dafny,
    Why3,

    // Tier 6b: Refinement-types + SPARK auto-active
    GNATprove,     // SPARK/Ada — Why3 + Z3/CVC5/Alt-Ergo backend
    Stainless,     // Scala / Inox refinement-types
    LiquidHaskell, // GHC plugin refinement-types

    // Tier 7: Specialized / niche
    TLAPS,
    Twelf,
    Nuprl,
    Minlog,
    Imandra,

    // Tier 8: Constraint solvers
    GLPK,
    SCIP,
    MiniZinc,
    Chuffed,
    ORTools,

    // Prover oracles (internal structural validators)
    TypedWasm,

    // Tier 9: Model checkers and program verifiers
    SPIN,
    CBMC,
    SeaHorn,

    // Tier 9: SAT Solvers
    CaDiCaL,
    Kissat,
    MiniSat,

    // Tier 9: Model checkers (extended)
    NuSMV,
    TLC,
    Alloy,
    Prism,
    UPPAAL,

    // Tier 9: Program verifiers (deductive)
    FramaC,

    // Tier 9: Permission-based program verifiers
    Viper,

    // Tier 9: Security protocol verifiers
    Tamarin,
    ProVerif,

    // Tier 9: Deductive Java verifiers (JavaDL + JML)
    KeY,

    // Tier 10: Delta-complete SMT solvers
    DReal,

    // Tier 10: Logic synthesis & hardware verification
    ABC,

    // Tier 10: GPU kernel verification
    /// GPUVerify — verifies CUDA/OpenCL kernels for data races and barrier
    /// divergence. Translates GPU kernels to Boogie/BPL then uses Z3/CVC4
    /// as the backend SMT solver. Input: `.cu` (CUDA) or `.cl` (OpenCL).
    GPUVerify,
    /// Faial — detects data races in GPU parallel kernels via access pattern
    /// analysis. Lighter-weight than GPUVerify; focuses on CUDA shared-memory
    /// race freedom without a Boogie translation step.
    Faial,

    // Tier 11: HP type-checker ecosystem. These dispatch through one
    // unified HPEcosystemBackend that routes to the real HP upstreams
    // (TypeLL, Katagoria, tropical-resource-typing). They are
    // type-discipline views rather than separate binaries.
    //
    // Exhaustive enumeration of every type discipline we intend to support.
    // Adding a variant here is cheap (dispatch-level only); the goal is to
    // never have to re-open this enum once the ecosystem grows. See
    // `src/rust/disciplines/` for the family grouping and katagoria pipeline.
    TypeLL,
    KatagoriaVerifier,
    TropicalTypeChecker,
    ChoreographicTypeChecker,
    EpistemicTypeChecker,
    EchoTypeChecker,
    SessionTypeChecker,
    ModalTypeChecker,
    QTTTypeChecker,
    EffectRowTypeChecker,
    DependentTypeChecker,
    RefinementTypeChecker,
    // Foundations
    OrdinaryTypeChecker,
    // Polymorphism family
    PhantomTypeChecker,
    PolymorphicTypeChecker,
    ExistentialTypeChecker,
    HigherKindedTypeChecker,
    RowTypeChecker,
    // Subtyping family
    SubtypingTypeChecker,
    IntersectionTypeChecker,
    UnionTypeChecker,
    GradualTypeChecker,
    // Dependent / refinement family (siblings of Dependent/Refinement)
    HoareTypeChecker,
    IndexedTypeChecker,
    // Substructural family (siblings / specialisations of QTT)
    LinearTypeChecker,
    AffineTypeChecker,
    RelevantTypeChecker,
    OrderedTypeChecker,
    UniquenessTypeChecker,
    // Mutability / capability family
    ImmutableTypeChecker,
    CapabilityTypeChecker,
    BunchedTypeChecker,
    // Modal family (siblings of Modal/Epistemic)
    TemporalTypeChecker,
    ProvabilityTypeChecker,
    // Effects / coeffects family (siblings of EffectRow)
    ImpureTypeChecker,
    CoeffectTypeChecker,
    ProbabilisticTypeChecker,
    // Process / communication family (siblings of Session/Choreographic/Echo)
    DyadicTypeChecker,
    // Homotopy foundations
    HomotopyTypeChecker,
    CubicalTypeChecker,
    /// Nominal logic / HOAS / λ-tree syntax dispatcher. Added 2026-04-18 as
    /// an honest one-time correction — nominal logic was missed in the
    /// original 40-variant exhaustive enumeration. See
    /// `src/rust/disciplines/mod.rs :: TypeDiscipline::Nominal` for the
    /// full rationale.
    NominalTypeChecker,
    /// Abella — classical Axis-1 prover for nominal logic / HOAS.
    /// Two-level logic (λProlog specification + sequent reasoning with
    /// the ∇ generic quantifier). Sibling to Twelf in logical framework
    /// style but with distinct proof theory.
    Abella,
    /// Dedukti — universal λΠ-modulo framework. Already in echidna as
    /// a proof-exchange format (`src/rust/exchange/dedukti.rs`); this
    /// variant adds the prover-as-solver role (invoking `dkcheck` /
    /// `lambdapi` to typecheck a `.dk` source end-to-end).
    Dedukti,
    /// Cameleer — OCaml front-end for Why3 via GOSPEL contracts.
    /// Thin pipeline over Why3's solver fleet; own variant so the
    /// OCaml-proofs niche gets its own corpus slot and port-pairs
    /// with F*/Dafny are trackable for the arbiter.
    Cameleer,
    /// ACL2s — sibling dialect to ACL2 with richer type annotations.
    /// Different binary, different default libraries, different
    /// tactic distributions; separate variant keeps the corpus slot
    /// distinct from ACL2 proper.
    ACL2s,
    /// Isabelle/ZF — Isabelle with Zermelo-Fraenkel set-theory
    /// object logic. Same `isabelle` binary as Isabelle/HOL but
    /// different session name and stdlib; distinct proof style
    /// and theorem namespace warrant a distinct slot.
    IsabelleZF,
    /// Boogie — intermediate verification language standalone
    /// backend. Currently reached via Viper; exposing directly lets
    /// echidna consume `.bpl` programs without a Viper wrapper
    /// (e.g. Dafny-generated output, Chalice, VCC front-ends).
    Boogie,
    // Phase 4 "variety" batch (2026-04-18) — from the prover story's
    // unique-and-unusual + pure-variety lists. Each genuinely distinct
    // from what echidna already covers; skipping Coq-variants
    // (Edukera, Bedrock2, CompCert) and F*-libraries (LowStar) since
    // those don't warrant new ProverKind slots.
    /// Naproche — controlled natural-language (ForTheL) proof checker.
    /// Only text-style prover in echidna's roster; token distribution
    /// unlike any other.
    Naproche,
    /// Matita — Bologna's Calculus of Inductive Constructions variant.
    /// Coq-adjacent but semantically distinct enough to deserve its
    /// own corpus slot.
    Matita,
    /// Arend — JetBrains's cubical HoTT prover. Distinct from Cubical
    /// Agda in having path primitives as first-class syntax and IDE
    /// tooling. Co-serves `TypeDiscipline::Cubical`.
    Arend,
    /// Athena — Arkoudas's denotational-proof-language with
    /// intermixed deductive and computational phases.
    Athena,
    /// λProlog — higher-order logic programming with HOAS (Teyjus /
    /// Elpi implementations). Co-serves `TypeDiscipline::Nominal`
    /// alongside Abella.
    LambdaProlog,
    /// Mercury — pure logic programming with static types and modes.
    /// Proof-adjacent via termination and determinism proofs.
    Mercury,
    /// Nitpick — Isabelle-integrated counter-example finder.
    /// Produces refutations; corpus records are negative-class data
    /// balancing the otherwise positive-only proof corpus.
    Nitpick,
    /// Nunchaku — standalone model / counter-example finder for HOL.
    /// Sibling to Nitpick; same negative-class story but not
    /// Isabelle-coupled, wider input format range.
    Nunchaku,
    /// Cubical Agda — Agda in --cubical mode; HIT, univalence, path types.
    CubicalAgda,
    /// Zipperposition — first-order + higher-order ATP (TPTP/TSTP output).
    Zipperposition,
    /// Prover9 — equational/clause-based ATP (McCune); pairs with Mace4.
    Prover9,
    /// OpenSMT — SMT solver with Craig interpolant generation.
    OpenSmt,
    /// SMT-RAT — nonlinear arithmetic SMT (NIA/NRA) from RWTH Aachen.
    SmtRat,
    /// Rocq — the 2024 Coq community rename; detects `rocq` binary first.
    Rocq,
    /// UPPAAL Stratego — strategy synthesis + stochastic model checking.
    UppaalStratego,
    /// MizAR — automated reasoning integrated with the Mizar Mathematical Library.
    MizAR,
}

impl ProverKind {
    /// True if this kind is served by the unified HP-ecosystem backend.
    pub fn is_hp_ecosystem(&self) -> bool {
        matches!(
            self,
            ProverKind::TypeLL
                | ProverKind::KatagoriaVerifier
                | ProverKind::TropicalTypeChecker
                | ProverKind::ChoreographicTypeChecker
                | ProverKind::EpistemicTypeChecker
                | ProverKind::EchoTypeChecker
                | ProverKind::SessionTypeChecker
                | ProverKind::ModalTypeChecker
                | ProverKind::QTTTypeChecker
                | ProverKind::EffectRowTypeChecker
                | ProverKind::DependentTypeChecker
                | ProverKind::RefinementTypeChecker
                | ProverKind::OrdinaryTypeChecker
                | ProverKind::PhantomTypeChecker
                | ProverKind::PolymorphicTypeChecker
                | ProverKind::ExistentialTypeChecker
                | ProverKind::HigherKindedTypeChecker
                | ProverKind::RowTypeChecker
                | ProverKind::SubtypingTypeChecker
                | ProverKind::IntersectionTypeChecker
                | ProverKind::UnionTypeChecker
                | ProverKind::GradualTypeChecker
                | ProverKind::HoareTypeChecker
                | ProverKind::IndexedTypeChecker
                | ProverKind::LinearTypeChecker
                | ProverKind::AffineTypeChecker
                | ProverKind::RelevantTypeChecker
                | ProverKind::OrderedTypeChecker
                | ProverKind::UniquenessTypeChecker
                | ProverKind::ImmutableTypeChecker
                | ProverKind::CapabilityTypeChecker
                | ProverKind::BunchedTypeChecker
                | ProverKind::TemporalTypeChecker
                | ProverKind::ProvabilityTypeChecker
                | ProverKind::ImpureTypeChecker
                | ProverKind::CoeffectTypeChecker
                | ProverKind::ProbabilisticTypeChecker
                | ProverKind::DyadicTypeChecker
                | ProverKind::HomotopyTypeChecker
                | ProverKind::CubicalTypeChecker
                | ProverKind::NominalTypeChecker
        )
    }
}

impl std::str::FromStr for ProverKind {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "agda" => Ok(ProverKind::Agda),
            "coq" => Ok(ProverKind::Coq),
            "lean" => Ok(ProverKind::Lean),
            "isabelle" => Ok(ProverKind::Isabelle),
            "z3" => Ok(ProverKind::Z3),
            "cvc5" => Ok(ProverKind::CVC5),
            "metamath" => Ok(ProverKind::Metamath),
            "hollight" | "hol-light" => Ok(ProverKind::HOLLight),
            "mizar" => Ok(ProverKind::Mizar),
            "pvs" => Ok(ProverKind::PVS),
            "acl2" => Ok(ProverKind::ACL2),
            "hol4" => Ok(ProverKind::HOL4),
            "idris2" | "idris" => Ok(ProverKind::Idris2),
            "lean3" | "lean-3" | "lean3-legacy" | "mathlib3" => Ok(ProverKind::Lean3),
            "vampire" => Ok(ProverKind::Vampire),
            "eprover" | "e" => Ok(ProverKind::EProver),
            "spass" => Ok(ProverKind::SPASS),
            "altergo" | "alt-ergo" => Ok(ProverKind::AltErgo),
            "leo3" | "leo-iii" | "leo-3" => Ok(ProverKind::Leo3),
            "satallax" => Ok(ProverKind::Satallax),
            "lash" => Ok(ProverKind::Lash),
            "agsyhol" | "agsy-hol" => Ok(ProverKind::AgsyHOL),
            "iprover" | "iprover-eq" => Ok(ProverKind::IProver),
            "princess" => Ok(ProverKind::Princess),
            "twee" => Ok(ProverKind::Twee),
            "metitarski" | "metit" => Ok(ProverKind::MetiTarski),
            "csi" => Ok(ProverKind::CSI),
            "aprove" => Ok(ProverKind::AProVE),
            "keymaerax" | "keymaera-x" | "keymaera_x" | "kyx" => Ok(ProverKind::KeYmaeraX),
            "qepcad" | "qepcad-b" | "qepcad_b" => Ok(ProverKind::Qepcad),
            "redlog" => Ok(ProverKind::Redlog),
            "mleancop" | "mlean-cop" | "mlean_cop" => Ok(ProverKind::MleanCoP),
            "ileancop" | "ilean-cop" | "ilean_cop" => Ok(ProverKind::IleanCoP),
            "nanocop" | "nano-cop" | "nano_cop" => Ok(ProverKind::NanoCoP),
            "mettel2" | "mettel-2" | "mettel" => Ok(ProverKind::MetTeL2),
            "elk" | "elk-reasoner" => Ok(ProverKind::ELK),
            "konclude" => Ok(ProverKind::Konclude),
            "storm" | "stormpy" | "storm-checker" => Ok(ProverKind::Storm),
            "prob" | "probcli" | "prob-cli" => Ok(ProverKind::ProB),
            "easycrypt" | "easy-crypt" | "ec-prover" => Ok(ProverKind::EasyCrypt),
            "cryptoverif" | "crypto-verif" | "cryptoverif-prover" => Ok(ProverKind::CryptoVerif),
            "fstar" | "f*" | "f-star" => Ok(ProverKind::FStar),
            "dafny" => Ok(ProverKind::Dafny),
            "why3" => Ok(ProverKind::Why3),
            "gnatprove" | "spark" | "ada" => Ok(ProverKind::GNATprove),
            "stainless" | "scala-stainless" => Ok(ProverKind::Stainless),
            "liquid" | "liquid-haskell" | "liquidhaskell" | "lh" => Ok(ProverKind::LiquidHaskell),
            "tlaps" | "tla+" => Ok(ProverKind::TLAPS),
            "twelf" => Ok(ProverKind::Twelf),
            "nuprl" => Ok(ProverKind::Nuprl),
            "minlog" => Ok(ProverKind::Minlog),
            "imandra" => Ok(ProverKind::Imandra),
            "glpk" => Ok(ProverKind::GLPK),
            "scip" => Ok(ProverKind::SCIP),
            "minizinc" | "mzn" => Ok(ProverKind::MiniZinc),
            "chuffed" => Ok(ProverKind::Chuffed),
            "ortools" | "or-tools" => Ok(ProverKind::ORTools),
            "typedwasm" | "typed-wasm" | "typed_wasm" | "twasm" => Ok(ProverKind::TypedWasm),
            "spin" | "promela" => Ok(ProverKind::SPIN),
            "cbmc" | "c-bounded" => Ok(ProverKind::CBMC),
            "seahorn" | "sea" | "sea-horn" => Ok(ProverKind::SeaHorn),
            "cadical" => Ok(ProverKind::CaDiCaL),
            "kissat" => Ok(ProverKind::Kissat),
            "minisat" | "mini-sat" => Ok(ProverKind::MiniSat),
            "nusmv" | "nuxmv" => Ok(ProverKind::NuSMV),
            "tlc" | "tlc2" => Ok(ProverKind::TLC),
            "alloy" => Ok(ProverKind::Alloy),
            "prism" => Ok(ProverKind::Prism),
            "uppaal" | "verifyta" => Ok(ProverKind::UPPAAL),
            "framac" | "frama-c" | "frama_c" | "wp" => Ok(ProverKind::FramaC),
            "viper" | "silicon" | "carbon" => Ok(ProverKind::Viper),
            "tamarin" | "tamarin-prover" | "spthy" => Ok(ProverKind::Tamarin),
            "proverif" | "pv" => Ok(ProverKind::ProVerif),
            "key" | "key-project" | "javadl" => Ok(ProverKind::KeY),
            "dreal" | "d-real" | "dreal4" => Ok(ProverKind::DReal),
            "abc" | "berkeley-abc" => Ok(ProverKind::ABC),
            "gpuverify" | "gpu-verify" | "gpu_verify" => Ok(ProverKind::GPUVerify),
            "faial" | "faial-drf" => Ok(ProverKind::Faial),
            "typell" | "type-ll" | "typell-kernel" => Ok(ProverKind::TypeLL),
            "katagoria" | "katagoriaverifier" | "katagoria-verifier" => {
                Ok(ProverKind::KatagoriaVerifier)
            },
            "tropicaltypechecker" | "tropical" | "tropical-type-checker" => {
                Ok(ProverKind::TropicalTypeChecker)
            },
            "choreographictypechecker" | "choreographic" => {
                Ok(ProverKind::ChoreographicTypeChecker)
            },
            "epistemictypechecker" | "epistemic" => Ok(ProverKind::EpistemicTypeChecker),
            "echotypechecker" | "echo" => Ok(ProverKind::EchoTypeChecker),
            "sessiontypechecker" | "session" => Ok(ProverKind::SessionTypeChecker),
            "modaltypechecker" | "modal" => Ok(ProverKind::ModalTypeChecker),
            "qtttypechecker" | "qtt" | "quantitative" => Ok(ProverKind::QTTTypeChecker),
            "effectrowtypechecker" | "effect-row" | "effectrow" => {
                Ok(ProverKind::EffectRowTypeChecker)
            },
            "dependenttypechecker" | "dependent" => Ok(ProverKind::DependentTypeChecker),
            "refinementtypechecker" | "refinement" => Ok(ProverKind::RefinementTypeChecker),
            "ordinarytypechecker" | "ordinary" | "simple" | "simply-typed" | "stlc" => {
                Ok(ProverKind::OrdinaryTypeChecker)
            },
            "phantomtypechecker" | "phantom" => Ok(ProverKind::PhantomTypeChecker),
            "polymorphictypechecker" | "polymorphic" | "systemf" | "system-f" | "parametric" => {
                Ok(ProverKind::PolymorphicTypeChecker)
            },
            "existentialtypechecker" | "existential" | "packed" => {
                Ok(ProverKind::ExistentialTypeChecker)
            },
            "higherkindedtypechecker" | "higher-kinded" | "higherkinded" | "hkt" | "hk" => {
                Ok(ProverKind::HigherKindedTypeChecker)
            },
            "rowtypechecker" | "row" | "row-polymorphic" | "row-polymorphism" => {
                Ok(ProverKind::RowTypeChecker)
            },
            "subtypingtypechecker" | "subtyping" | "sub" => Ok(ProverKind::SubtypingTypeChecker),
            "intersectiontypechecker" | "intersection" | "inter" => {
                Ok(ProverKind::IntersectionTypeChecker)
            },
            "uniontypechecker" | "union" => Ok(ProverKind::UnionTypeChecker),
            "gradualtypechecker" | "gradual" | "gradual-typing" => {
                Ok(ProverKind::GradualTypeChecker)
            },
            "hoaretypechecker" | "hoare" | "hoare-types" => Ok(ProverKind::HoareTypeChecker),
            "indexedtypechecker" | "indexed" | "indexed-monad" | "indexed-monads" => {
                Ok(ProverKind::IndexedTypeChecker)
            },
            "lineartypechecker" | "linear" | "linear-types" => Ok(ProverKind::LinearTypeChecker),
            "affinetypechecker" | "affine" | "affine-types" => Ok(ProverKind::AffineTypeChecker),
            "relevanttypechecker" | "relevant" | "relevant-types" => {
                Ok(ProverKind::RelevantTypeChecker)
            },
            "orderedtypechecker" | "ordered" | "ordered-logic" | "no-exchange" => {
                Ok(ProverKind::OrderedTypeChecker)
            },
            "uniquenesstypechecker" | "uniqueness" | "unique" | "unique-types" => {
                Ok(ProverKind::UniquenessTypeChecker)
            },
            "immutabletypechecker" | "immutable" | "frozen" | "const-types" => {
                Ok(ProverKind::ImmutableTypeChecker)
            },
            "capabilitytypechecker" | "capability" | "cap" | "capability-types" => {
                Ok(ProverKind::CapabilityTypeChecker)
            },
            "bunchedtypechecker" | "bunched" | "bi" | "bi-logic" | "separation" => {
                Ok(ProverKind::BunchedTypeChecker)
            },
            "temporaltypechecker" | "temporal" | "ltl" | "ctl" => {
                Ok(ProverKind::TemporalTypeChecker)
            },
            "provabilitytypechecker" | "provability" | "lob" | "löb" | "gl" => {
                Ok(ProverKind::ProvabilityTypeChecker)
            },
            "impuretypechecker" | "impure" | "effect-tracked" => Ok(ProverKind::ImpureTypeChecker),
            "coeffecttypechecker" | "coeffect" | "graded-context" | "coeffects" => {
                Ok(ProverKind::CoeffectTypeChecker)
            },
            "probabilistictypechecker" | "probabilistic" | "prob-types" => {
                Ok(ProverKind::ProbabilisticTypeChecker)
            },
            "dyadictypechecker" | "dyadic" | "binary-channel" | "dyadic-session" => {
                Ok(ProverKind::DyadicTypeChecker)
            },
            "homotopytypechecker" | "homotopy" | "hott" => Ok(ProverKind::HomotopyTypeChecker),
            "cubicaltypechecker" | "cubical" | "cubical-tt" => Ok(ProverKind::CubicalTypeChecker),
            "nominaltypechecker" | "nominal" | "hoas" | "lambda-tree" => {
                Ok(ProverKind::NominalTypeChecker)
            },
            "abella" => Ok(ProverKind::Abella),
            "dedukti" | "dkcheck" | "lambdapi" => Ok(ProverKind::Dedukti),
            "cameleer" | "gospel" => Ok(ProverKind::Cameleer),
            "acl2s" | "acl2-s" => Ok(ProverKind::ACL2s),
            "isabellezf" | "isabelle-zf" | "isabelle/zf" | "zf" => Ok(ProverKind::IsabelleZF),
            "boogie" | "bpl" => Ok(ProverKind::Boogie),
            "naproche" | "forthel" | "ftl" => Ok(ProverKind::Naproche),
            "matita" => Ok(ProverKind::Matita),
            "arend" => Ok(ProverKind::Arend),
            "athena" => Ok(ProverKind::Athena),
            "lambdaprolog" | "lambda-prolog" | "teyjus" | "elpi" => Ok(ProverKind::LambdaProlog),
            "mercury" | "mmc" => Ok(ProverKind::Mercury),
            "nitpick" => Ok(ProverKind::Nitpick),
            "nunchaku" => Ok(ProverKind::Nunchaku),
            "cubicalagda" | "cubical-agda" | "agda-cubical" => Ok(ProverKind::CubicalAgda),
            "zipperposition" => Ok(ProverKind::Zipperposition),
            "prover9" => Ok(ProverKind::Prover9),
            "opensmt" | "open-smt" => Ok(ProverKind::OpenSmt),
            "smtrat" | "smt-rat" => Ok(ProverKind::SmtRat),
            "rocq" | "rocq-compile" => Ok(ProverKind::Rocq),
            "uppaal-stratego" | "stratego" => Ok(ProverKind::UppaalStratego),
            "mizar-ar" | "mizatp" | "mizar-atp" => Ok(ProverKind::MizAR),
            _ => Err(anyhow::anyhow!("Unknown prover: {}", s)),
        }
    }
}

impl std::fmt::Display for ProverKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl ProverKind {
    /// All core provers for 1.0 (12 total)
    pub fn all_core() -> Vec<ProverKind> {
        vec![
            ProverKind::Agda,
            ProverKind::Coq,
            ProverKind::Lean,
            ProverKind::Isabelle,
            ProverKind::Z3,
            ProverKind::CVC5,
            ProverKind::Metamath,
            ProverKind::HOLLight,
            ProverKind::Mizar,
            ProverKind::PVS,
            ProverKind::ACL2,
            ProverKind::HOL4,
        ]
    }

    /// All provers including extended coverage
    pub fn all() -> Vec<ProverKind> {
        let mut provers = Self::all_core();
        provers.extend_from_slice(&[
            ProverKind::Idris2,
            ProverKind::Lean3,
            ProverKind::Vampire,
            ProverKind::EProver,
            ProverKind::SPASS,
            ProverKind::AltErgo,
            ProverKind::FStar,
            ProverKind::Dafny,
            ProverKind::Why3,
            ProverKind::TLAPS,
            ProverKind::Twelf,
            ProverKind::Nuprl,
            ProverKind::Minlog,
            ProverKind::Imandra,
            ProverKind::GLPK,
            ProverKind::SCIP,
            ProverKind::MiniZinc,
            ProverKind::Chuffed,
            ProverKind::ORTools,
            ProverKind::TypedWasm,
            ProverKind::SPIN,
            ProverKind::CBMC,
            ProverKind::SeaHorn,
            ProverKind::CaDiCaL,
            ProverKind::Kissat,
            ProverKind::MiniSat,
            ProverKind::NuSMV,
            ProverKind::TLC,
            ProverKind::Alloy,
            ProverKind::Prism,
            ProverKind::UPPAAL,
            ProverKind::FramaC,
            ProverKind::Viper,
            ProverKind::Tamarin,
            ProverKind::ProVerif,
            ProverKind::KeY,
            ProverKind::DReal,
            ProverKind::ABC,
            ProverKind::GPUVerify,
            ProverKind::Faial,
            ProverKind::CubicalAgda,
            ProverKind::Zipperposition,
            ProverKind::Prover9,
            ProverKind::OpenSmt,
            ProverKind::SmtRat,
            ProverKind::Rocq,
            ProverKind::UppaalStratego,
            ProverKind::MizAR,
            ProverKind::IProver,
            ProverKind::Princess,
            ProverKind::Twee,
            ProverKind::MetiTarski,
            ProverKind::CSI,
            ProverKind::AProVE,
            ProverKind::KeYmaeraX,
            ProverKind::Qepcad,
            ProverKind::Redlog,
            ProverKind::MleanCoP,
            ProverKind::IleanCoP,
            ProverKind::NanoCoP,
            ProverKind::MetTeL2,
            ProverKind::ELK,
            ProverKind::Konclude,
            ProverKind::Storm,
            ProverKind::ProB,
            ProverKind::EasyCrypt,
            ProverKind::CryptoVerif,
        ]);
        provers
    }

    /// Get complexity rating (1-5, lower is easier)
    pub fn complexity(&self) -> u8 {
        match self {
            ProverKind::Metamath => 2,
            ProverKind::Agda => 3,
            ProverKind::HOLLight => 3,
            ProverKind::Mizar => 3,
            ProverKind::Lean => 3,
            ProverKind::Coq => 3,
            ProverKind::Isabelle => 4,
            ProverKind::Z3 => 2,
            ProverKind::CVC5 => 2,
            ProverKind::PVS => 4,
            ProverKind::ACL2 => 4,
            ProverKind::HOL4 => 5,
            ProverKind::Idris2 => 3,
            ProverKind::Lean3 => 3,          // Same complexity as Lean 4.
            ProverKind::Abella => 3,         // Two-level logic, HOAS proof state.
            ProverKind::Dedukti => 3,        // λΠ-modulo framework.
            ProverKind::Cameleer => 2,       // Thin OCaml→Why3 pipeline.
            ProverKind::ACL2s => 4,          // Sibling to ACL2.
            ProverKind::IsabelleZF => 4,     // Sibling to Isabelle/HOL.
            ProverKind::Boogie => 2,         // Intermediate verification language.
            ProverKind::Naproche => 3,       // Controlled-NL parsing non-trivial.
            ProverKind::Matita => 3,         // CIC variant, same family as Coq.
            ProverKind::Arend => 3,          // Cubical HoTT.
            ProverKind::Athena => 4,         // Denotational + rewriting engine.
            ProverKind::LambdaProlog => 3,   // HOAS logic programming.
            ProverKind::Mercury => 3,        // Logic programming with types/modes.
            ProverKind::Nitpick => 2,        // Isabelle-wrapped counter-example finder.
            ProverKind::Nunchaku => 2,       // Standalone counter-example finder.
            ProverKind::CubicalAgda => 4,    // Cubical HoTT; harder than plain Agda.
            ProverKind::Zipperposition => 2, // Automated ATP.
            ProverKind::Prover9 => 2,        // Classic equational ATP.
            ProverKind::OpenSmt => 2,        // SMT solver.
            ProverKind::SmtRat => 3,         // Nonlinear arithmetic needs careful encoding.
            ProverKind::Rocq => 3,           // Same as Coq.
            ProverKind::UppaalStratego => 4, // Strategy synthesis is hard.
            ProverKind::MizAR => 3,          // Mizar with ATP assist.
            ProverKind::Vampire => 2,        // Automated, relatively simple
            ProverKind::EProver => 2,        // Similar to Vampire
            ProverKind::SPASS => 2,          // Automated FOL
            ProverKind::AltErgo => 2,        // SMT + FOL

            ProverKind::FStar => 3,         // Dependent types + effects
            ProverKind::Dafny => 2,         // Auto-active
            ProverKind::Why3 => 3,          // Multi-prover orchestration
            ProverKind::GNATprove => 3,     // SPARK auto-active via Why3 backends
            ProverKind::Stainless => 3,     // Scala/Inox refinement types
            ProverKind::LiquidHaskell => 3, // GHC plugin refinement types
            ProverKind::TLAPS => 4,         // TLA+ proof system
            ProverKind::Twelf => 4,         // Logical framework
            ProverKind::Nuprl => 4,         // Constructive type theory
            ProverKind::Minlog => 4,        // Minimal logic
            ProverKind::Imandra => 3,       // ML-based reasoning
            ProverKind::GLPK => 2,          // LP solver
            ProverKind::SCIP => 3,          // MINLP solver
            ProverKind::MiniZinc => 2,      // Constraint modelling
            ProverKind::Chuffed => 2,       // CP solver
            ProverKind::ORTools => 2,       // Constraint/optimization solver
            ProverKind::TypedWasm => 3,     // Internal oracle, structural analysis
            ProverKind::SPIN => 3,          // Model checker, Promela language
            ProverKind::CBMC => 2,          // Bounded model checker, C input
            ProverKind::SeaHorn => 2,       // LLVM-based verifier, abstract interpretation + CHC
            ProverKind::CaDiCaL => 1,       // SAT solver, DIMACS CNF
            ProverKind::Kissat => 1,        // SAT solver, DIMACS CNF
            ProverKind::MiniSat => 1,       // SAT solver, DIMACS CNF
            ProverKind::NuSMV => 3,         // Symbolic model checker, SMV language
            ProverKind::TLC => 3,           // TLA+ model checker
            ProverKind::Alloy => 3,         // Relational model finder
            ProverKind::Prism => 3,         // Probabilistic model checker
            ProverKind::UPPAAL => 3,        // Timed automata model checker
            ProverKind::FramaC => 3,        // Deductive C verifier (ACSL + WP)
            ProverKind::Viper => 3,         // Permission-based verifier (Silver + Silicon/Carbon)
            ProverKind::Tamarin => 3,       // Security protocol verifier, multiset rewriting
            ProverKind::ProVerif => 2,      // Automated protocol verifier, applied pi-calculus
            ProverKind::KeY => 3, // Deductive Java verifier (JavaDL + JML), auto + interactive
            ProverKind::DReal => 2, // Automated delta-complete SMT solver, NRA
            ProverKind::ABC => 2, // Automated hardware verification, AIG-based
            ProverKind::GPUVerify => 2, // Automated GPU kernel verifier (Boogie/Z3 backend)
            ProverKind::Faial => 2, // Lightweight GPU race detector (access pattern analysis)
            // Phase 1a: Higher-order ATPs
            ProverKind::Leo3 => 3,     // Leo III HOL-to-TPTP translator + ATP
            ProverKind::Satallax => 3, // Satallax HOL-based ATP
            ProverKind::Lash => 3,     // Lash higher-order prover
            ProverKind::AgsyHOL => 4,  // Agsy HOL dependent-type prover
            // Phase 1b: Frontier first-order provers
            ProverKind::IProver => 2,    // Competitive ATP, standard FOL
            ProverKind::Princess => 3,   // LA-extended ATP
            ProverKind::Twee => 2,       // Equational only, deterministic
            ProverKind::MetiTarski => 3, // Transcendental function encoding
            ProverKind::CSI => 3,        // TRS/CTRS parsing + CPF output
            ProverKind::AProVE => 3,     // TRS/XTC parsing
            ProverKind::KeYmaeraX => 4,  // dL + hybrid programs + tactic language
            ProverKind::Qepcad => 4,     // CAD doubly-exponential in variable count
            ProverKind::Redlog => 3,     // virtual substitution + CAD
            ProverKind::MleanCoP => 3,   // classical connection-method + equality
            ProverKind::IleanCoP => 3,   // intuitionistic connection-method
            ProverKind::NanoCoP => 3,    // small-kernel connection-method
            ProverKind::MetTeL2 => 4,    // JVM tableau-generator + spec config
            // Phase 4: DL + probabilistic + B-method + computational crypto
            ProverKind::ELK => 3,         // consequence-based EL kernel
            ProverKind::Konclude => 4,    // full SROIQ tableau saturation
            ProverKind::Storm => 3,       // numerical fixed-point computation
            ProverKind::ProB => 3,        // B-method semantics + constraint engine
            ProverKind::EasyCrypt => 4,   // probabilistic relational HL + tactics
            ProverKind::CryptoVerif => 4, // game-hopping + indistinguishability lib
            // HP type-checker ecosystem: complexity 3 — they are real
            // type-checkers with non-trivial unification/elaboration.
            // Heavier disciplines (HoTT/Cubical, Hoare) rate 4.
            ProverKind::TypeLL
            | ProverKind::KatagoriaVerifier
            | ProverKind::TropicalTypeChecker
            | ProverKind::ChoreographicTypeChecker
            | ProverKind::EpistemicTypeChecker
            | ProverKind::EchoTypeChecker
            | ProverKind::SessionTypeChecker
            | ProverKind::ModalTypeChecker
            | ProverKind::QTTTypeChecker
            | ProverKind::EffectRowTypeChecker
            | ProverKind::DependentTypeChecker
            | ProverKind::RefinementTypeChecker
            | ProverKind::PhantomTypeChecker
            | ProverKind::PolymorphicTypeChecker
            | ProverKind::ExistentialTypeChecker
            | ProverKind::HigherKindedTypeChecker
            | ProverKind::RowTypeChecker
            | ProverKind::SubtypingTypeChecker
            | ProverKind::IntersectionTypeChecker
            | ProverKind::UnionTypeChecker
            | ProverKind::GradualTypeChecker
            | ProverKind::IndexedTypeChecker
            | ProverKind::LinearTypeChecker
            | ProverKind::AffineTypeChecker
            | ProverKind::RelevantTypeChecker
            | ProverKind::OrderedTypeChecker
            | ProverKind::UniquenessTypeChecker
            | ProverKind::ImmutableTypeChecker
            | ProverKind::CapabilityTypeChecker
            | ProverKind::BunchedTypeChecker
            | ProverKind::TemporalTypeChecker
            | ProverKind::ProvabilityTypeChecker
            | ProverKind::ImpureTypeChecker
            | ProverKind::CoeffectTypeChecker
            | ProverKind::ProbabilisticTypeChecker
            | ProverKind::DyadicTypeChecker => 3,
            // Heavier disciplines: Hoare triples (SL proofs), HoTT (univalence),
            // Cubical (interval primitives).
            ProverKind::HoareTypeChecker
            | ProverKind::HomotopyTypeChecker
            | ProverKind::CubicalTypeChecker
            | ProverKind::NominalTypeChecker => 4,
            // Baseline: simply-typed lambda calculus — cheap to check.
            ProverKind::OrdinaryTypeChecker => 2,
        }
    }

    /// Get tier (1-5)
    pub fn tier(&self) -> u8 {
        match self {
            ProverKind::Agda
            | ProverKind::Coq
            | ProverKind::Lean
            | ProverKind::Isabelle
            | ProverKind::Z3
            | ProverKind::CVC5 => 1,

            ProverKind::Metamath | ProverKind::HOLLight | ProverKind::Mizar => 2,

            ProverKind::PVS | ProverKind::ACL2 => 3,

            ProverKind::HOL4 => 4,

            // Extended tier (same as Tier 1 in capability)
            ProverKind::Idris2 => 1,
            ProverKind::Lean3 => 1, // Sibling to Lean 4.
            // Tier 7 niche: specialized proof framework for HOAS / nominal.
            ProverKind::Abella => 2,
            ProverKind::Dedukti => 2,        // Logical framework tier.
            ProverKind::Cameleer => 2,       // Auto-active via Why3.
            ProverKind::ACL2s => 3,          // Sibling to ACL2 (tier 3).
            ProverKind::IsabelleZF => 1,     // Sibling to Isabelle (tier 1).
            ProverKind::Boogie => 5,         // Deductive program verifier tier.
            ProverKind::Naproche => 2,       // Specialised, text-style.
            ProverKind::Matita => 1,         // Coq-adjacent, Tier 1 capability.
            ProverKind::Arend => 1,          // Cubical HoTT, Tier 1.
            ProverKind::Athena => 4,         // Niche framework.
            ProverKind::LambdaProlog => 4,   // Logical framework / HOAS.
            ProverKind::Mercury => 4,        // Specialised logic programming.
            ProverKind::Nitpick => 5,        // Counter-example finder tier.
            ProverKind::Nunchaku => 5,       // Counter-example finder tier.
            ProverKind::CubicalAgda => 2,    // Tier 2: HoTT proof assistant.
            ProverKind::Zipperposition => 3, // Tier 3: HO-ATP.
            ProverKind::Prover9 => 4,        // Tier 4: classic ATP.
            ProverKind::OpenSmt => 3,        // Tier 3: interpolant SMT.
            ProverKind::SmtRat => 5,         // Tier 5: research NL SMT.
            ProverKind::Rocq => 1,           // Tier 1: Coq rename.
            ProverKind::UppaalStratego => 4, // Tier 4: strategy synthesis.
            ProverKind::MizAR => 3,          // Tier 3: ATP-assisted Mizar.

            // Tier 5: First-Order ATPs
            ProverKind::Vampire => 5,
            ProverKind::EProver => 5,
            ProverKind::SPASS => 5,
            ProverKind::AltErgo => 5,

            // Tier 6: Dependent types + effects, auto-active
            ProverKind::FStar => 1,         // Small kernel, dependent types
            ProverKind::Dafny => 2,         // Auto-active (relies on Boogie->Z3)
            ProverKind::Why3 => 2,          // Multi-prover orchestration
            ProverKind::GNATprove => 4,     // SPARK — small-kernel via Why3
            ProverKind::Stainless => 3,     // Scala refinement types
            ProverKind::LiquidHaskell => 3, // GHC refinement types

            // Tier 7: Specialized / niche
            ProverKind::TLAPS => 2,
            ProverKind::Twelf => 4,
            ProverKind::Nuprl => 4,
            ProverKind::Minlog => 4,
            ProverKind::Imandra => 2,

            // Tier 8: Constraint solvers
            ProverKind::GLPK => 5,
            ProverKind::SCIP => 5,
            ProverKind::MiniZinc => 5,
            ProverKind::Chuffed => 5,
            ProverKind::ORTools => 5,
            ProverKind::TypedWasm => 1, // Internal oracle, tier 1 capability

            // Tier 9: Model checkers and program verifiers
            ProverKind::SPIN => 5,
            ProverKind::CBMC => 5,
            ProverKind::SeaHorn => 5,

            // Tier 9: SAT Solvers
            ProverKind::CaDiCaL => 5,
            ProverKind::Kissat => 5,
            ProverKind::MiniSat => 5,

            // Tier 9: Model checkers (extended)
            ProverKind::NuSMV => 5,
            ProverKind::TLC => 5,
            ProverKind::Alloy => 5,
            ProverKind::Prism => 5,
            ProverKind::UPPAAL => 5,
            ProverKind::FramaC => 5,    // Deductive program verifier
            ProverKind::Viper => 5,     // Permission-based program verifier
            ProverKind::Tamarin => 5,   // Security protocol verifier
            ProverKind::ProVerif => 5,  // Security protocol verifier (automated)
            ProverKind::KeY => 5,       // Deductive Java verifier
            ProverKind::DReal => 5,     // Delta-complete SMT solver (NRA/ODE)
            ProverKind::ABC => 5,       // Logic synthesis & hardware verification
            ProverKind::GPUVerify => 5, // GPU kernel verifier (CUDA/OpenCL → Boogie → Z3)
            ProverKind::Faial => 5,     // Lightweight GPU data-race detector
            // Phase 1a: Higher-order ATPs
            ProverKind::Leo3 => 5,     // Tier 5: HOL-to-TPTP translator
            ProverKind::Satallax => 5, // Tier 5: HOL-based ATP
            ProverKind::Lash => 5,     // Tier 5: higher-order ATP
            ProverKind::AgsyHOL => 5,  // Tier 5: HOL dependent-type prover
            // Phase 1b: Frontier first-order provers
            ProverKind::IProver => 2,    // Trust tier 2 (TPTP FOL)
            ProverKind::Princess => 2,   // Trust tier 2 (TPTP + LA)
            ProverKind::Twee => 3,       // Trust tier 3 (deterministic equational)
            ProverKind::MetiTarski => 2, // Trust tier 2 (TPTP + transcendental)
            ProverKind::CSI => 2,        // Trust tier 2 (TRS/CPF)
            ProverKind::AProVE => 2,     // Trust tier 2 (TRS/XTC)
            ProverKind::KeYmaeraX => 2,  // Trust tier 2 (dL; QE delegated to external CAS)
            ProverKind::Qepcad => 2,     // Trust tier 2 (CAD; no machine-checked certificate)
            ProverKind::Redlog => 2,     // Trust tier 2 (parallel to QEPCAD)
            ProverKind::MleanCoP => 2,   // Trust tier 2 (classical leanCoP kernel)
            ProverKind::IleanCoP => 3,   // Trust tier 3 (intuitionistic kernel; small + checkable)
            ProverKind::NanoCoP => 3,    // Trust tier 3 (small kernel — Level-4 cohort)
            ProverKind::MetTeL2 => 2, // Trust tier 2 (generated tableau correct by construction; spec unverified)
            // Phase 4: DL + probabilistic + B-method + computational crypto.
            ProverKind::ELK => 3, // Trust tier 3 (consequence-based, peer-reviewed soundness)
            ProverKind::Konclude => 3, // Trust tier 3 (peer-reviewed tableau kernel)
            ProverKind::Storm => 2, // Trust tier 2 (DD/symbolic engines, no certificate)
            ProverKind::ProB => 2, // Trust tier 2 (constraint-based BMC, validated for railway)
            ProverKind::EasyCrypt => 3, // Trust tier 3 (small kernel + Why3/SMT for VC discharge)
            ProverKind::CryptoVerif => 3, // Trust tier 3 (small game-hopping engine, peer-reviewed)
            // HP ecosystem — tier 11 (beyond the existing 10-tier scheme
            // but placed as 3 here to share the ML guidance budget with
            // dependent/interactive provers).
            ProverKind::TypeLL
            | ProverKind::KatagoriaVerifier
            | ProverKind::TropicalTypeChecker
            | ProverKind::ChoreographicTypeChecker
            | ProverKind::EpistemicTypeChecker
            | ProverKind::EchoTypeChecker
            | ProverKind::SessionTypeChecker
            | ProverKind::ModalTypeChecker
            | ProverKind::QTTTypeChecker
            | ProverKind::EffectRowTypeChecker
            | ProverKind::DependentTypeChecker
            | ProverKind::RefinementTypeChecker
            | ProverKind::OrdinaryTypeChecker
            | ProverKind::PhantomTypeChecker
            | ProverKind::PolymorphicTypeChecker
            | ProverKind::ExistentialTypeChecker
            | ProverKind::HigherKindedTypeChecker
            | ProverKind::RowTypeChecker
            | ProverKind::SubtypingTypeChecker
            | ProverKind::IntersectionTypeChecker
            | ProverKind::UnionTypeChecker
            | ProverKind::GradualTypeChecker
            | ProverKind::HoareTypeChecker
            | ProverKind::IndexedTypeChecker
            | ProverKind::LinearTypeChecker
            | ProverKind::AffineTypeChecker
            | ProverKind::RelevantTypeChecker
            | ProverKind::OrderedTypeChecker
            | ProverKind::UniquenessTypeChecker
            | ProverKind::ImmutableTypeChecker
            | ProverKind::CapabilityTypeChecker
            | ProverKind::BunchedTypeChecker
            | ProverKind::TemporalTypeChecker
            | ProverKind::ProvabilityTypeChecker
            | ProverKind::ImpureTypeChecker
            | ProverKind::CoeffectTypeChecker
            | ProverKind::ProbabilisticTypeChecker
            | ProverKind::DyadicTypeChecker
            | ProverKind::HomotopyTypeChecker
            | ProverKind::CubicalTypeChecker
            | ProverKind::NominalTypeChecker => 3,
        }
    }

    /// Get expected implementation time in weeks
    pub fn implementation_time(&self) -> f32 {
        match self {
            ProverKind::Metamath => 1.5,
            ProverKind::Z3 | ProverKind::CVC5 => 1.0,
            ProverKind::HOLLight | ProverKind::Mizar => 2.0,
            ProverKind::Agda | ProverKind::Lean | ProverKind::Coq => 2.5,
            ProverKind::Isabelle => 3.0,
            ProverKind::PVS | ProverKind::ACL2 => 3.5,
            ProverKind::HOL4 => 4.0,
            ProverKind::Idris2 => 2.5,
            ProverKind::Lean3 => 1.0,        // Thin fork of Lean 4 backend.
            ProverKind::Abella => 2.0,       // New parser, HOAS proof state model.
            ProverKind::Dedukti => 1.5,      // Extends existing exchange module.
            ProverKind::Cameleer => 1.0,     // Thin wrapper over Why3.
            ProverKind::ACL2s => 1.0,        // Thin fork of ACL2.
            ProverKind::IsabelleZF => 1.0,   // Thin variant of Isabelle.
            ProverKind::Boogie => 1.5,       // Extract from Viper internals.
            ProverKind::Naproche => 2.0,     // Controlled-NL parser wrapper.
            ProverKind::Matita => 2.0,       // Coq-parser fork.
            ProverKind::Arend => 2.0,        // Cubical parser + elaborator.
            ProverKind::Athena => 2.5,       // Rich denotational framework.
            ProverKind::LambdaProlog => 2.0, // HOAS parser + unifier.
            ProverKind::Mercury => 2.0,      // Logic programming interpreter bridge.
            ProverKind::Nitpick => 1.0,      // Thin wrapper over Isabelle.
            ProverKind::Nunchaku => 1.5,     // Standalone counter-example tool.
            ProverKind::CubicalAgda => 2.5,  // Thin fork of Agda backend.
            ProverKind::Zipperposition => 1.5, // TSTP-output ATP.
            ProverKind::Prover9 => 1.5,      // Simple output parsing.
            ProverKind::OpenSmt => 1.5,      // SMT-LIB2 like CVC5.
            ProverKind::SmtRat => 1.5,       // Same pattern.
            ProverKind::Rocq => 1.0,         // Alias for Coq.
            ProverKind::UppaalStratego => 2.0, // Fork of UPPAAL backend.
            ProverKind::MizAR => 2.0,        // Mizar ATP integration.
            ProverKind::Vampire => 1.5,      // Automated, TPTP format
            ProverKind::EProver => 1.5,      // Similar to Vampire
            ProverKind::SPASS => 1.5,        // DFG format
            ProverKind::AltErgo => 1.5,      // Native format

            ProverKind::FStar => 2.5,         // Dependent types + effects
            ProverKind::Dafny => 2.0,         // Auto-active, Boogie pipeline
            ProverKind::Why3 => 2.0,          // Multi-prover
            ProverKind::GNATprove => 3.0,     // SPARK toolchain wrapping
            ProverKind::Stainless => 2.5,     // Scala JVM
            ProverKind::LiquidHaskell => 2.5, // GHC plugin
            ProverKind::TLAPS => 2.5,         // TLA+ specific
            ProverKind::Twelf => 3.0,         // LF framework
            ProverKind::Nuprl => 3.0,         // Constructive type theory
            ProverKind::Minlog => 2.5,        // Minimal logic
            ProverKind::Imandra => 2.0,       // ML-based
            ProverKind::GLPK => 1.0,          // LP API
            ProverKind::SCIP => 1.5,          // MINLP API
            ProverKind::MiniZinc => 1.0,      // Constraint modelling
            ProverKind::Chuffed => 1.0,       // CP solver
            ProverKind::ORTools => 1.5,       // Constraint/optimization
            ProverKind::TypedWasm => 2.0,     // Internal oracle
            ProverKind::SPIN => 1.5,          // Model checker
            ProverKind::CBMC => 1.5,          // Bounded model checker
            ProverKind::SeaHorn => 1.5,       // LLVM-based CHC verifier
            ProverKind::CaDiCaL => 1.0,       // SAT solver, DIMACS CNF
            ProverKind::Kissat => 1.0,        // SAT solver, DIMACS CNF
            ProverKind::MiniSat => 1.0,       // SAT solver, DIMACS CNF
            ProverKind::NuSMV => 1.5,         // Symbolic model checker
            ProverKind::TLC => 1.5,           // TLA+ model checker
            ProverKind::Alloy => 1.5,         // Relational model finder
            ProverKind::Prism => 1.5,         // Probabilistic model checker
            ProverKind::UPPAAL => 1.5,        // Timed automata model checker
            ProverKind::FramaC => 1.5,        // Deductive C verifier
            ProverKind::Viper => 2.0,         // Permission-based verifier (Silver + two backends)
            ProverKind::Tamarin => 2.0,       // Security protocol verifier (.spthy)
            ProverKind::ProVerif => 1.5,      // Automated protocol verifier (.pv)
            ProverKind::KeY => 2.0,           // Deductive Java verifier (JavaDL + JML)
            ProverKind::DReal => 1.0,         // Automated SMT solver, SMT-LIB input
            ProverKind::ABC => 1.5,           // Hardware verification, AIGER/BLIF input
            ProverKind::GPUVerify => 1.5,     // GPU kernel verifier, CUDA/OpenCL input
            ProverKind::Faial => 1.0,         // Lightweight GPU race detector, CUDA input
            ProverKind::IProver => 1.5,       // First-order ATP with SZS output
            ProverKind::Princess => 1.5,      // SMT-based first-order solver
            ProverKind::Twee => 1.5,          // Equational logic (Knuth-Bendix)
            ProverKind::MetiTarski => 1.5,    // Transcendental arithmetic extension
            ProverKind::CSI => 2.0,           // Confluence/termination checker
            ProverKind::AProVE => 2.0,        // Automated termination verifier
            ProverKind::KeYmaeraX => 2.5,     // Hybrid systems / differential dynamic logic
            ProverKind::Qepcad => 2.5,        // CAD / real quantifier elimination
            ProverKind::Redlog => 2.0,        // REDUCE-CAS QE frontend
            ProverKind::MleanCoP => 1.5,      // Classical connection-method
            ProverKind::IleanCoP => 2.0,      // Intuitionistic connection-method
            ProverKind::NanoCoP => 1.5,       // Lean-kernel connection-method
            ProverKind::MetTeL2 => 2.5,       // Modal-logic tableau generator
            // Phase 4: DL + probabilistic + B-method + computational crypto.
            ProverKind::ELK => 1.5,         // OWL EL classifier
            ProverKind::Konclude => 2.0,    // OWL DL tableau reasoner
            ProverKind::Storm => 2.0,       // Probabilistic model checker (PRISM successor)
            ProverKind::ProB => 2.0,        // B-method / Event-B model checker
            ProverKind::EasyCrypt => 2.5,   // Game-based crypto proofs
            ProverKind::CryptoVerif => 2.5, // Automated computational-crypto prover
            ProverKind::Leo3 => 2.5,        // Higher-order ATP
            ProverKind::Satallax => 2.5,    // Higher-order ATP
            ProverKind::Lash => 2.5,        // Higher-order ATP
            ProverKind::AgsyHOL => 2.5,     // Higher-order ATP
            ProverKind::TypeLL
            | ProverKind::KatagoriaVerifier
            | ProverKind::TropicalTypeChecker
            | ProverKind::ChoreographicTypeChecker
            | ProverKind::EpistemicTypeChecker
            | ProverKind::EchoTypeChecker
            | ProverKind::SessionTypeChecker
            | ProverKind::ModalTypeChecker
            | ProverKind::QTTTypeChecker
            | ProverKind::EffectRowTypeChecker
            | ProverKind::DependentTypeChecker
            | ProverKind::RefinementTypeChecker
            | ProverKind::OrdinaryTypeChecker
            | ProverKind::PhantomTypeChecker
            | ProverKind::PolymorphicTypeChecker
            | ProverKind::ExistentialTypeChecker
            | ProverKind::HigherKindedTypeChecker
            | ProverKind::RowTypeChecker
            | ProverKind::SubtypingTypeChecker
            | ProverKind::IntersectionTypeChecker
            | ProverKind::UnionTypeChecker
            | ProverKind::GradualTypeChecker
            | ProverKind::HoareTypeChecker
            | ProverKind::IndexedTypeChecker
            | ProverKind::LinearTypeChecker
            | ProverKind::AffineTypeChecker
            | ProverKind::RelevantTypeChecker
            | ProverKind::OrderedTypeChecker
            | ProverKind::UniquenessTypeChecker
            | ProverKind::ImmutableTypeChecker
            | ProverKind::CapabilityTypeChecker
            | ProverKind::BunchedTypeChecker
            | ProverKind::TemporalTypeChecker
            | ProverKind::ProvabilityTypeChecker
            | ProverKind::ImpureTypeChecker
            | ProverKind::CoeffectTypeChecker
            | ProverKind::ProbabilisticTypeChecker
            | ProverKind::DyadicTypeChecker
            | ProverKind::HomotopyTypeChecker
            | ProverKind::CubicalTypeChecker
            | ProverKind::NominalTypeChecker => 2.0, // HP ecosystem
        }
    }

    /// Default executable name for this prover (what to look for on PATH)
    pub fn default_executable(&self) -> &'static str {
        match self {
            ProverKind::Agda => "agda",
            ProverKind::Coq => "coqc",
            ProverKind::Lean => "lean",
            ProverKind::Isabelle => "isabelle",
            ProverKind::Z3 => "z3",
            ProverKind::CVC5 => "cvc5",
            ProverKind::Metamath => "metamath",
            ProverKind::HOLLight => "ocaml",
            ProverKind::Mizar => "mizf",
            ProverKind::PVS => "pvs",
            ProverKind::ACL2 => "acl2",
            ProverKind::HOL4 => "hol",
            ProverKind::Idris2 => "idris2",
            ProverKind::Lean3 => "lean3",
            ProverKind::Abella => "abella",
            ProverKind::Dedukti => "dkcheck",
            ProverKind::Cameleer => "cameleer",
            ProverKind::ACL2s => "acl2s",
            ProverKind::IsabelleZF => "isabelle", // Same binary, different session.
            ProverKind::Boogie => "boogie",
            ProverKind::Naproche => "naproche",
            ProverKind::Matita => "matitac",
            ProverKind::Arend => "arend",
            ProverKind::Athena => "athena",
            ProverKind::LambdaProlog => "tjsim",
            ProverKind::Mercury => "mmc",
            ProverKind::Nitpick => "isabelle", // Shared binary via `isabelle process -e nitpick`.
            ProverKind::Nunchaku => "nunchaku",
            ProverKind::Vampire => "vampire",
            ProverKind::EProver => "eprover",
            ProverKind::SPASS => "SPASS",
            ProverKind::AltErgo => "alt-ergo",

            ProverKind::FStar => "fstar.exe",
            ProverKind::Dafny => "dafny",
            ProverKind::Why3 => "why3",
            ProverKind::GNATprove => "gnatprove",
            ProverKind::Stainless => "stainless",
            ProverKind::LiquidHaskell => "liquid",
            ProverKind::TLAPS => "tlapm",
            ProverKind::Twelf => "twelf-server",
            ProverKind::Nuprl => "nuprl",
            ProverKind::Minlog => "minlog",
            ProverKind::Imandra => "imandra",
            ProverKind::GLPK => "glpsol",
            ProverKind::SCIP => "scip",
            ProverKind::MiniZinc => "minizinc",
            ProverKind::Chuffed => "fzn-chuffed",
            ProverKind::ORTools => "ortools_solve",
            ProverKind::TypedWasm => "idris2", // Validates via Idris2 ABI
            ProverKind::SPIN => "spin",
            ProverKind::CBMC => "cbmc",
            ProverKind::SeaHorn => "sea", // SeaHorn verification framework CLI
            ProverKind::CaDiCaL => "cadical", // CaDiCaL SAT solver
            ProverKind::Kissat => "kissat", // Kissat SAT solver
            ProverKind::MiniSat => "minisat", // MiniSat SAT solver
            ProverKind::NuSMV => "nuXmv", // nuXmv / NuSMV model checker
            ProverKind::TLC => "tlc2",    // TLA+ model checker (Java)
            ProverKind::Alloy => "alloy", // Alloy Analyzer (Java JAR)
            ProverKind::Prism => "prism", // PRISM probabilistic model checker
            ProverKind::UPPAAL => "verifyta", // UPPAAL verification engine
            ProverKind::FramaC => "frama-c", // Frama-C platform (WP plugin)
            ProverKind::Viper => "silicon", // Viper Silicon verifier (default backend)
            ProverKind::Tamarin => "tamarin-prover", // Tamarin security protocol prover
            ProverKind::ProVerif => "proverif", // ProVerif protocol verifier
            ProverKind::KeY => "key",     // KeY Java verifier (Java, headless mode)
            ProverKind::DReal => "dreal", // dReal delta-complete SMT solver
            ProverKind::ABC => "abc",     // Berkeley ABC logic synthesis system
            ProverKind::GPUVerify => "gpuverify", // GPUVerify CUDA/OpenCL kernel verifier
            ProverKind::Faial => "faial-drf", // Faial data-race freedom checker
            ProverKind::CubicalAgda => "agda",
            ProverKind::Zipperposition => "zipperposition",
            ProverKind::Prover9 => "prover9",
            ProverKind::OpenSmt => "opensmt",
            ProverKind::SmtRat => "smtrat",
            ProverKind::Rocq => "rocq",
            ProverKind::UppaalStratego => "stratego",
            ProverKind::MizAR => "mizar-atp",
            ProverKind::IProver => "iprover",
            ProverKind::Princess => "princess",
            ProverKind::Twee => "twee",
            ProverKind::MetiTarski => "metit",
            ProverKind::CSI => "csi",
            ProverKind::AProVE => "aprove",
            ProverKind::KeYmaeraX => "keymaerax",
            ProverKind::Qepcad => "qepcad",
            ProverKind::Redlog => "redcsl",
            ProverKind::MleanCoP => "mleancop",
            ProverKind::IleanCoP => "ileancop",
            ProverKind::NanoCoP => "nanocop",
            ProverKind::MetTeL2 => "mettel2",
            ProverKind::ELK => "elk",
            ProverKind::Konclude => "konclude",
            ProverKind::Storm => "storm",
            ProverKind::ProB => "probcli",
            ProverKind::EasyCrypt => "easycrypt",
            ProverKind::CryptoVerif => "cryptoverif",
            ProverKind::Leo3 => "leo3",
            ProverKind::Satallax => "satallax",
            ProverKind::Lash => "lash",
            ProverKind::AgsyHOL => "agsyhol",
            // HP ecosystem — all route through the TypeLL kernel CLI;
            // the discipline field on HPEcosystemBackend selects the
            // actual upstream (typell / katagoria / tropical-resource-typing).
            ProverKind::TypeLL => "typell",
            ProverKind::KatagoriaVerifier => "katagoria",
            ProverKind::TropicalTypeChecker => "tropical-type-check",
            ProverKind::ChoreographicTypeChecker => "typell",
            ProverKind::EpistemicTypeChecker => "typell",
            ProverKind::EchoTypeChecker => "typell",
            ProverKind::SessionTypeChecker => "typell",
            ProverKind::ModalTypeChecker => "typell",
            ProverKind::QTTTypeChecker => "typell",
            ProverKind::EffectRowTypeChecker => "typell",
            ProverKind::DependentTypeChecker => "typell",
            ProverKind::RefinementTypeChecker => "typell",
            ProverKind::OrdinaryTypeChecker
            | ProverKind::PhantomTypeChecker
            | ProverKind::PolymorphicTypeChecker
            | ProverKind::ExistentialTypeChecker
            | ProverKind::HigherKindedTypeChecker
            | ProverKind::RowTypeChecker
            | ProverKind::SubtypingTypeChecker
            | ProverKind::IntersectionTypeChecker
            | ProverKind::UnionTypeChecker
            | ProverKind::GradualTypeChecker
            | ProverKind::HoareTypeChecker
            | ProverKind::IndexedTypeChecker
            | ProverKind::LinearTypeChecker
            | ProverKind::AffineTypeChecker
            | ProverKind::RelevantTypeChecker
            | ProverKind::OrderedTypeChecker
            | ProverKind::UniquenessTypeChecker
            | ProverKind::ImmutableTypeChecker
            | ProverKind::CapabilityTypeChecker
            | ProverKind::BunchedTypeChecker
            | ProverKind::TemporalTypeChecker
            | ProverKind::ProvabilityTypeChecker
            | ProverKind::ImpureTypeChecker
            | ProverKind::CoeffectTypeChecker
            | ProverKind::ProbabilisticTypeChecker
            | ProverKind::DyadicTypeChecker
            | ProverKind::HomotopyTypeChecker
            | ProverKind::CubicalTypeChecker
            | ProverKind::NominalTypeChecker => "typell",
        }
    }
}

/// Configuration for a prover backend
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProverConfig {
    /// Path to prover executable
    pub executable: PathBuf,

    /// Library/standard library paths
    pub library_paths: Vec<PathBuf>,

    /// Additional arguments
    pub args: Vec<String>,

    /// Timeout in seconds
    pub timeout: u64,

    /// Enable neural premise selection
    pub neural_enabled: bool,

    /// Optional GNN inference server URL for neural tactic ranking.
    /// When set and `neural_enabled` is true, suggest_tactics calls the GNN.
    pub gnn_api_url: Option<String>,

    /// Project root directory (EI-1, 2026-04-26).
    ///
    /// When `Some(p)`, prover backends that support session-based builds
    /// (today: Isabelle) will treat `p` as the project root and resolve
    /// theory imports from `p/ROOT`. Without this, `echidna prove` only
    /// understands single-file goals importing `Main` — which made
    /// Burrower's `attempt` mode unusable on real project proofs.
    /// We deliberately did NOT repurpose `library_paths` because Lean
    /// and HOL-Light already use it differently.
    pub project_root: Option<PathBuf>,

    /// Sandbox mode for prover invocation (safe-learning b, 2026-04-26).
    ///
    /// `None` (the default) preserves backwards-compatible behaviour and
    /// runs the prover as a plain subprocess. `Bwrap` and `Podman` route
    /// through `crate::executor::sandbox::SandboxConfig` and run the
    /// prover under the named isolation layer. The wiring uses the
    /// existing executor module — we do not reimplement sandboxing here.
    pub sandbox: SandboxMode,
}

/// Sandbox mode for prover invocation.
///
/// Stays a separate enum from `executor::sandbox::SandboxKind` so the
/// CLI surface is stable across executor refactors.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum SandboxMode {
    /// No sandbox — direct subprocess. Backwards-compatible default.
    #[default]
    None,
    /// Bubblewrap namespace isolation (lightweight, no daemon required).
    Bwrap,
    /// Podman container isolation (full-featured, requires podman daemon).
    Podman,
}

impl std::str::FromStr for SandboxMode {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_ascii_lowercase().as_str() {
            "none" | "off" | "" => Ok(SandboxMode::None),
            "bwrap" | "bubblewrap" => Ok(SandboxMode::Bwrap),
            "podman" | "container" => Ok(SandboxMode::Podman),
            other => Err(format!(
                "unknown sandbox mode: {other} (expected one of: none, bwrap, podman)"
            )),
        }
    }
}

impl Default for ProverConfig {
    fn default() -> Self {
        ProverConfig {
            executable: PathBuf::new(),
            library_paths: vec![],
            args: vec![],
            timeout: 300, // 5 minutes
            neural_enabled: true,
            gnn_api_url: None,
            project_root: None,
            sandbox: SandboxMode::None,
        }
    }
}

/// GNN-augmented tactic suggestions: calls the Julia GNN server to rank premises,
/// then prepends top-k `Apply` and prover-specific `apply` tactics to the list.
/// Falls back silently (returns `hints` unchanged) if the server is unreachable
/// or `neural_enabled` is false or `gnn_api_url` is unset.
///
/// # Arguments
/// * `config`      – prover config supplying the GNN URL and neural flag
/// * `state`       – current proof state (goals, context, theorems)
/// * `prover_name` – short prover identifier used in `Tactic::Custom` args
/// * `hints`       – heuristic suggestions already assembled by the caller
/// * `limit`       – maximum number of tactics to return
#[allow(dead_code)]
pub(crate) async fn gnn_augment_tactics(
    config: &ProverConfig,
    state: &ProofState,
    prover_name: &str,
    mut hints: Vec<Tactic>,
    limit: usize,
) -> Vec<Tactic> {
    let url = match config.gnn_api_url.as_deref() {
        Some(u) if config.neural_enabled => u.to_string(),
        _ => return hints.into_iter().take(limit).collect(),
    };

    use crate::gnn::client::{GnnClient, GnnConfig};
    use crate::gnn::graph::ProofGraphBuilder;

    let graph = ProofGraphBuilder::new(4).build_from_proof_state(state);
    let mut gnn = GnnClient::with_config(GnnConfig {
        api_url: url,
        timeout_ms: 2000,
        top_k: 8,
        min_score: 0.1,
        request_embeddings: false,
        num_gnn_layers: 3,
        use_attention: true,
    });

    // Extract goal aspects from state metadata (written by AgentCore::process_goal)
    // so Julia's /gnn/rank can apply per-domain weights from prior outcomes.
    // When metadata has no "aspects" key (e.g. direct REPL invocation), aspects
    // is empty and behaviour is identical to the no-hint path.
    // Ping the server so rank_premises_with_aspects sees server_available = true.
    // Graceful: if check_health errors (server down), gnn.server_available stays
    // false and rank_premises_with_aspects returns empty — no disruption to callers.
    let _ = gnn.check_health().await;

    let aspects: Vec<String> = state
        .metadata
        .get("aspects")
        .and_then(|v| serde_json::from_value(v.clone()).ok())
        .unwrap_or_default();
    // Boundary filter: only dotted "category.aspect" strings reach the learning-loop
    // key space. Structural meta-tags without a dot (e.g. "axiom", "constructor")
    // are excluded here so they never pollute domain_hints or training records.
    let aspects: Vec<String> = aspects.into_iter().filter(|s| s.contains('.')).collect();
    let result = gnn.rank_premises_with_aspects(&graph, &aspects).await;
    // Prepend apply tactics for top premises (in score order, before heuristic hints)
    let mut gnn_tactics: Vec<Tactic> = result
        .ranked_premises
        .iter()
        .take(5)
        .map(|premise: &String| Tactic::Custom {
            prover: prover_name.to_string(),
            command: "apply".to_string(),
            args: vec![premise.clone()],
        })
        .collect();
    gnn_tactics.append(&mut hints);
    gnn_tactics.into_iter().take(limit).collect()
}

/// Universal trait for theorem prover backends
#[async_trait]
pub trait ProverBackend: Send + Sync {
    /// Get prover kind
    fn kind(&self) -> ProverKind;

    /// Get prover version
    async fn version(&self) -> anyhow::Result<String>;

    /// Parse a proof file into ProofState
    async fn parse_file(&self, path: PathBuf) -> anyhow::Result<ProofState>;

    /// Parse a proof from string
    async fn parse_string(&self, content: &str) -> anyhow::Result<ProofState>;

    /// Apply a tactic to current proof state
    async fn apply_tactic(
        &self,
        state: &ProofState,
        tactic: &Tactic,
    ) -> anyhow::Result<TacticResult>;

    /// Check if a proof is valid
    async fn verify_proof(&self, state: &ProofState) -> anyhow::Result<bool>;

    /// Rich variant of `verify_proof` — returns a `ProverOutcome` describing
    /// exactly *what kind* of result was produced (proved, no-proof-found,
    /// timeout, input error, inconsistent premises, prover crash, system
    /// failure).
    ///
    /// The default implementation wraps `verify_proof`: on `Ok(true)` it
    /// returns `Proved`, on `Ok(false)` `NoProofFound`, and on `Err(e)` it
    /// hands the error to `classify_anyhow_error` so the system distinguishes
    /// timeouts, parse errors, and prover crashes from each other.  Backends
    /// that can observe richer signals (e.g. the Z3 backend can spot
    /// `assertions` produce UNSAT in isolation → `InconsistentPremises`)
    /// override this method to produce better classifications.
    async fn check(&self, state: &ProofState) -> anyhow::Result<ProverOutcome> {
        let start = std::time::Instant::now();
        let limit = self.config().timeout;
        match self.verify_proof(state).await {
            Ok(true) => Ok(ProverOutcome::Proved {
                elapsed_ms: start.elapsed().as_millis() as u64,
            }),
            Ok(false) => Ok(ProverOutcome::NoProofFound {
                elapsed_ms: start.elapsed().as_millis() as u64,
                reason: None,
            }),
            Err(e) => Ok(classify_anyhow_error(&e, limit)),
        }
    }

    /// Export proof to prover-specific format
    async fn export(&self, state: &ProofState) -> anyhow::Result<String>;

    /// Get suggested tactics using neural premise selection
    async fn suggest_tactics(
        &self,
        state: &ProofState,
        limit: usize,
    ) -> anyhow::Result<Vec<Tactic>>;

    /// Search for theorems matching a pattern
    async fn search_theorems(&self, pattern: &str) -> anyhow::Result<Vec<String>>;

    /// Get configuration
    fn config(&self) -> &ProverConfig;

    /// Set configuration
    fn set_config(&mut self, config: ProverConfig);

    /// Attempt to prove a goal (synchronous wrapper for actor use)
    fn prove(&self, goal: &crate::core::Goal) -> anyhow::Result<ProofState> {
        // Default implementation: create initial proof state from goal
        Ok(ProofState {
            goals: vec![goal.clone()],
            context: crate::core::Context::default(),
            proof_script: vec![],
            metadata: std::collections::HashMap::new(),
        })
    }
}

/// Factory for creating prover backends
pub struct ProverFactory;

impl ProverFactory {
    pub fn create(
        kind: ProverKind,
        config: ProverConfig,
    ) -> anyhow::Result<Box<dyn ProverBackend>> {
        // Fill in default executable if not specified
        let config = if config.executable.as_os_str().is_empty() {
            ProverConfig {
                executable: PathBuf::from(kind.default_executable()),
                ..config
            }
        } else {
            config
        };

        match kind {
            ProverKind::Agda => Ok(Box::new(agda::AgdaBackend::new(config))),
            ProverKind::Coq => Ok(Box::new(coq::CoqBackend::new(config))),
            ProverKind::Lean => Ok(Box::new(lean::LeanBackend::new(config))),
            ProverKind::Isabelle => Ok(Box::new(isabelle::IsabelleBackend::new(config))),
            ProverKind::Z3 => Ok(Box::new(z3::Z3Backend::new(config))),
            ProverKind::CVC5 => Ok(Box::new(cvc5::CVC5Backend::new(config))),
            ProverKind::Metamath => Ok(Box::new(metamath::MetamathBackend::new(config))),
            ProverKind::HOLLight => Ok(Box::new(hol_light::HolLightBackend::new(config))),
            ProverKind::Mizar => Ok(Box::new(mizar::MizarBackend::new(config))),
            ProverKind::PVS => Ok(Box::new(pvs::PVSBackend::new(config))),
            ProverKind::ACL2 => Ok(Box::new(acl2::ACL2Backend::new(config))),
            ProverKind::HOL4 => Ok(Box::new(hol4::Hol4Backend::new(config))),
            ProverKind::Idris2 => Ok(Box::new(idris2::Idris2Backend::new(config))),
            ProverKind::Lean3 => Ok(Box::new(lean3::Lean3Backend::new(config))),
            ProverKind::Abella => Ok(Box::new(abella::AbellaBackend::new(config))),
            ProverKind::Dedukti => Ok(Box::new(dedukti::DeduktiBackend::new(config))),
            ProverKind::Cameleer => Ok(Box::new(cameleer::CameleerBackend::new(config))),
            ProverKind::ACL2s => Ok(Box::new(acl2s::Acl2sBackend::new(config))),
            ProverKind::IsabelleZF => Ok(Box::new(isabelle_zf::IsabelleZfBackend::new(config))),
            ProverKind::Boogie => Ok(Box::new(boogie::BoogieBackend::new(config))),
            ProverKind::Naproche => Ok(Box::new(naproche::NaprocheBackend::new(config))),
            ProverKind::Matita => Ok(Box::new(matita::MatitaBackend::new(config))),
            ProverKind::Arend => Ok(Box::new(arend::ArendBackend::new(config))),
            ProverKind::Athena => Ok(Box::new(athena::AthenaBackend::new(config))),
            ProverKind::LambdaProlog => {
                Ok(Box::new(lambda_prolog::LambdaPrologBackend::new(config)))
            },
            ProverKind::Mercury => Ok(Box::new(mercury::MercuryBackend::new(config))),
            ProverKind::Nitpick => Ok(Box::new(nitpick::NitpickBackend::new(config))),
            ProverKind::Nunchaku => Ok(Box::new(nunchaku::NunchakuBackend::new(config))),
            ProverKind::Vampire => Ok(Box::new(vampire::VampireBackend::new(config))),
            ProverKind::EProver => Ok(Box::new(eprover::EProverBackend::new(config))),
            ProverKind::SPASS => Ok(Box::new(spass::SPASSBackend::new(config))),
            ProverKind::AltErgo => Ok(Box::new(altergo::AltErgoBackend::new(config))),

            ProverKind::FStar => Ok(Box::new(fstar::FStarBackend::new(config))),
            ProverKind::Dafny => Ok(Box::new(dafny::DafnyBackend::new(config))),
            ProverKind::Why3 => Ok(Box::new(why3::Why3Backend::new(config))),
            ProverKind::GNATprove => Ok(Box::new(gnatprove::GNATproveBackend::new(config))),
            ProverKind::Stainless => Ok(Box::new(stainless::StainlessBackend::new(config))),
            ProverKind::LiquidHaskell => {
                Ok(Box::new(liquid_haskell::LiquidHaskellBackend::new(config)))
            },
            ProverKind::TLAPS => Ok(Box::new(tlaps::TLAPSBackend::new(config))),
            ProverKind::Twelf => Ok(Box::new(twelf::TwelfBackend::new(config))),
            ProverKind::Nuprl => Ok(Box::new(nuprl::NuprlBackend::new(config))),
            ProverKind::Minlog => Ok(Box::new(minlog::MinlogBackend::new(config))),
            ProverKind::Imandra => Ok(Box::new(imandra::ImandraBackend::new(config))),
            ProverKind::GLPK => Ok(Box::new(glpk::GLPKBackend::new(config))),
            ProverKind::SCIP => Ok(Box::new(scip::SCIPBackend::new(config))),
            ProverKind::MiniZinc => Ok(Box::new(minizinc::MiniZincBackend::new(config))),
            ProverKind::Chuffed => Ok(Box::new(chuffed::ChuffedBackend::new(config))),
            ProverKind::ORTools => Ok(Box::new(ortools::ORToolsBackend::new(config))),
            ProverKind::TypedWasm => Ok(Box::new(typed_wasm::TypedWasmBackend::new(config))),
            ProverKind::SPIN => Ok(Box::new(spin_checker::SpinBackend::new(config))),
            ProverKind::CBMC => Ok(Box::new(cbmc::CBMCBackend::new(config))),
            ProverKind::SeaHorn => Ok(Box::new(seahorn::SeaHornBackend::new(config))),
            ProverKind::CaDiCaL => Ok(Box::new(cadical::CaDiCaLBackend::new(config))),
            ProverKind::Kissat => Ok(Box::new(kissat::KissatBackend::new(config))),
            ProverKind::MiniSat => Ok(Box::new(minisat::MiniSatBackend::new(config))),
            ProverKind::NuSMV => Ok(Box::new(nusmv::NuSMVBackend::new(config))),
            ProverKind::TLC => Ok(Box::new(tlc::TLCBackend::new(config))),
            ProverKind::Alloy => Ok(Box::new(alloy::AlloyBackend::new(config))),
            ProverKind::Prism => Ok(Box::new(prism::PrismBackend::new(config))),
            ProverKind::UPPAAL => Ok(Box::new(uppaal::UppaalBackend::new(config))),
            ProverKind::FramaC => Ok(Box::new(framac::FramaCBackend::new(config))),
            ProverKind::Viper => Ok(Box::new(viper::ViperBackend::new(config))),
            ProverKind::Tamarin => Ok(Box::new(tamarin::TamarinBackend::new(config))),
            ProverKind::ProVerif => Ok(Box::new(proverif::ProVerifBackend::new(config))),
            ProverKind::KeY => Ok(Box::new(key::KeyBackend::new(config))),
            ProverKind::DReal => Ok(Box::new(dreal::DRealBackend::new(config))),
            ProverKind::ABC => Ok(Box::new(abc::AbcBackend::new(config))),
            ProverKind::GPUVerify => Ok(Box::new(gpuverify::GpuVerifyBackend::new(config))),
            ProverKind::Faial => Ok(Box::new(faial::FaialBackend::new(config))),
            ProverKind::CubicalAgda => Ok(Box::new(cubical_agda::CubicalAgdaBackend::new(config))),
            ProverKind::Zipperposition => {
                Ok(Box::new(zipperposition::ZipperpositionBackend::new(config)))
            },
            ProverKind::Prover9 => Ok(Box::new(prover9::Prover9Backend::new(config))),
            ProverKind::OpenSmt => Ok(Box::new(opensmt::OpenSmtBackend::new(config))),
            ProverKind::SmtRat => Ok(Box::new(smtrat::SmtRatBackend::new(config))),
            ProverKind::Rocq => Ok(Box::new(rocq::RocqBackend::new(config))),
            ProverKind::UppaalStratego => Ok(Box::new(
                uppaal_stratego::UppaalStrategoBackend::new(config),
            )),
            ProverKind::MizAR => Ok(Box::new(mizar_ar::MizARBackend::new(config))),
            ProverKind::IProver => Ok(Box::new(iprover::IProverBackend::new(config))),
            ProverKind::Princess => Ok(Box::new(princess::PrincessBackend::new(config))),
            ProverKind::Twee => Ok(Box::new(twee::TweeBackend::new(config))),
            ProverKind::MetiTarski => Ok(Box::new(metitarski::MetiTarskiBackend::new(config))),
            ProverKind::CSI => Ok(Box::new(csi::CSIBackend::new(config))),
            ProverKind::AProVE => Ok(Box::new(aprove::AProVEBackend::new(config))),
            ProverKind::KeYmaeraX => Ok(Box::new(keymaerax::KeYmaeraXBackend::new(config))),
            ProverKind::Qepcad => Ok(Box::new(qepcad::QepcadBackend::new(config))),
            ProverKind::Redlog => Ok(Box::new(redlog::RedlogBackend::new(config))),
            ProverKind::MleanCoP => Ok(Box::new(mleancop::MleanCopBackend::new(config))),
            ProverKind::IleanCoP => Ok(Box::new(ileancop::IleanCopBackend::new(config))),
            ProverKind::NanoCoP => Ok(Box::new(nanocop::NanoCopBackend::new(config))),
            ProverKind::MetTeL2 => Ok(Box::new(mettel2::MetTeL2Backend::new(config))),
            ProverKind::ELK => Ok(Box::new(elk::ElkBackend::new(config))),
            ProverKind::Konclude => Ok(Box::new(konclude::KoncludeBackend::new(config))),
            ProverKind::Storm => Ok(Box::new(storm::StormBackend::new(config))),
            ProverKind::ProB => Ok(Box::new(prob::ProBBackend::new(config))),
            ProverKind::EasyCrypt => Ok(Box::new(easycrypt::EasyCryptBackend::new(config))),
            ProverKind::CryptoVerif => Ok(Box::new(cryptoverif::CryptoVerifBackend::new(config))),
            ProverKind::Leo3 => Ok(Box::new(leo3::Leo3Backend::new(config))),
            ProverKind::Satallax => Ok(Box::new(satallax::SatallaxBackend::new(config))),
            ProverKind::Lash => Ok(Box::new(lash::LashBackend::new(config))),
            ProverKind::AgsyHOL => Ok(Box::new(agsyhol::AgsyholBackend::new(config))),
            // TypeLL and KatagoriaVerifier are real HP upstream binaries —
            // they continue to dispatch through HPEcosystemBackend.
            ProverKind::TypeLL | ProverKind::KatagoriaVerifier => Ok(Box::new(
                hp_ecosystem::HPEcosystemBackend::new(kind, config),
            )),

            // S3 extraction (2026-04-22): the 39 *TypeChecker discipline
            // variants all route through the unified TypedWasm engine,
            // parametrised by a discipline-specific TypeInfo. See
            // `typed_wasm::type_info_for` for the level-set mapping.
            ProverKind::TropicalTypeChecker
            | ProverKind::ChoreographicTypeChecker
            | ProverKind::EpistemicTypeChecker
            | ProverKind::EchoTypeChecker
            | ProverKind::SessionTypeChecker
            | ProverKind::ModalTypeChecker
            | ProverKind::QTTTypeChecker
            | ProverKind::EffectRowTypeChecker
            | ProverKind::DependentTypeChecker
            | ProverKind::RefinementTypeChecker
            | ProverKind::OrdinaryTypeChecker
            | ProverKind::PhantomTypeChecker
            | ProverKind::PolymorphicTypeChecker
            | ProverKind::ExistentialTypeChecker
            | ProverKind::HigherKindedTypeChecker
            | ProverKind::RowTypeChecker
            | ProverKind::SubtypingTypeChecker
            | ProverKind::IntersectionTypeChecker
            | ProverKind::UnionTypeChecker
            | ProverKind::GradualTypeChecker
            | ProverKind::HoareTypeChecker
            | ProverKind::IndexedTypeChecker
            | ProverKind::LinearTypeChecker
            | ProverKind::AffineTypeChecker
            | ProverKind::RelevantTypeChecker
            | ProverKind::OrderedTypeChecker
            | ProverKind::UniquenessTypeChecker
            | ProverKind::ImmutableTypeChecker
            | ProverKind::CapabilityTypeChecker
            | ProverKind::BunchedTypeChecker
            | ProverKind::TemporalTypeChecker
            | ProverKind::ProvabilityTypeChecker
            | ProverKind::ImpureTypeChecker
            | ProverKind::CoeffectTypeChecker
            | ProverKind::ProbabilisticTypeChecker
            | ProverKind::DyadicTypeChecker
            | ProverKind::HomotopyTypeChecker
            | ProverKind::CubicalTypeChecker
            | ProverKind::NominalTypeChecker => Ok(Box::new(
                typed_wasm::TypedWasmBackend::for_kind(kind, config),
            )),
        }
    }

    /// Detect prover from file extension
    pub fn detect_from_file(path: &Path) -> Option<ProverKind> {
        path.extension()?.to_str().and_then(|ext| match ext {
            "agda" => Some(ProverKind::Agda),
            "v" => Some(ProverKind::Coq),
            "lean" => Some(ProverKind::Lean),
            "thy" => Some(ProverKind::Isabelle),
            "smt2" => Some(ProverKind::Z3), // Could be CVC5 too
            "mm" => Some(ProverKind::Metamath),
            "ml" => Some(ProverKind::HOLLight),
            "miz" => Some(ProverKind::Mizar),
            "pvs" => Some(ProverKind::PVS),
            "lisp" => Some(ProverKind::ACL2),
            "sml" => Some(ProverKind::HOL4),
            "idr" => Some(ProverKind::Idris2),
            "p" | "tptp" => Some(ProverKind::Vampire), // TPTP format (could be E too)
            "dfg" => Some(ProverKind::SPASS),          // SPASS DFG format
            "ae" => Some(ProverKind::AltErgo),         // Alt-Ergo native format
            "why" | "mlw" => Some(ProverKind::Why3),   // Why3 / WhyML
            "fst" | "fsti" => Some(ProverKind::FStar), // F* source / interface
            "dfy" => Some(ProverKind::Dafny),          // Dafny format
            "ads" | "adb" | "gpr" => Some(ProverKind::GNATprove), // SPARK/Ada
            // Note: ".scala" and ".hs" are NOT auto-mapped to Stainless /
            // Liquid Haskell because plain Scala/Haskell sources are not
            // necessarily refinement-typed.  Caller must pass explicit kind.
            "tla" => Some(ProverKind::TLAPS),        // TLA+ format
            "elf" => Some(ProverKind::Twelf),        // Twelf LF format
            "nuprl" => Some(ProverKind::Nuprl),      // Nuprl format
            "minlog" => Some(ProverKind::Minlog),    // Minlog format
            "iml" => Some(ProverKind::Imandra),      // Imandra ML format
            "lp" | "mps" => Some(ProverKind::GLPK),  // LP/MIP format
            "pip" | "zpl" => Some(ProverKind::SCIP), // SCIP/ZIMPL format
            "mzn" | "dzn" => Some(ProverKind::MiniZinc), // MiniZinc format
            "fzn" => Some(ProverKind::Chuffed),      // FlatZinc (Chuffed input)
            "twasm" => Some(ProverKind::TypedWasm),  // TypedWasm program
            "pml" => Some(ProverKind::SPIN),         // Promela model
            "smv" => Some(ProverKind::NuSMV),        // SMV specification
            "als" => Some(ProverKind::Alloy),        // Alloy specification
            "pm" | "prism" => Some(ProverKind::Prism), // PRISM model
            "vpr" => Some(ProverKind::Viper),        // Viper Silver language
            "spthy" => Some(ProverKind::Tamarin),    // Tamarin security protocol theory
            "pv" => Some(ProverKind::ProVerif),      // ProVerif applied pi-calculus
            "cnf" => Some(ProverKind::CaDiCaL),      // DIMACS CNF (default SAT solver)
            "dr" => Some(ProverKind::DReal),         // dReal SMT-LIB (.dr extension)
            "aig" => Some(ProverKind::ABC),          // AIGER format (And-Inverter Graph)
            "blif" => Some(ProverKind::ABC),         // Berkeley Logic Interchange Format
            // GPU source files — default to GPUVerify for extension-only detection.
            // Use detect_from_file_content() to distinguish GPUVerify vs Faial.
            "cu" => Some(ProverKind::GPUVerify), // CUDA source (GPUVerify or Faial)
            "cl" => Some(ProverKind::GPUVerify), // OpenCL source (GPUVerify)
            "key" => Some(ProverKind::KeY),      // KeY proof problem file (JavaDL)
            // Note: .java files with JML annotations can also be detected via content-aware detection
            // Note: .c files only map to CBMC when containing __CPROVER directives
            // Note: .lean is shared between Lean 3 and Lean 4; default is Lean 4.
            // Use detect_from_file_content() for Lean 3 vs 4 disambiguation.
            "lean3" => Some(ProverKind::Lean3), // explicit extension
            "thm" => Some(ProverKind::Abella),  // Abella .thm files
            // Dedukti uses .dk; .lp (lambdapi dialect) is shadowed by GLPK above
            // since LP/MIP files dominate that extension in the wild — a .lp
            // input ambiguous between lambdapi and linear programming is
            // resolved as GLPK.  Use detect_from_file_content() to disambiguate.
            "dk" => Some(ProverKind::Dedukti),   // Dedukti / λΠ
            "bpl" => Some(ProverKind::Boogie),   // Boogie intermediate language
            "ftl" => Some(ProverKind::Naproche), // Naproche controlled-NL
            "ma" => Some(ProverKind::Matita),    // Matita proof file
            "ard" => Some(ProverKind::Arend),    // Arend cubical HoTT
            "ath" => Some(ProverKind::Athena),   // Athena
            "mod" | "sig" => Some(ProverKind::LambdaProlog), // λProlog module / signature
            "nun" => Some(ProverKind::Nunchaku), // Nunchaku input
            // Mercury uses .m which collides with OCaml conventions in
            // some file sets; content-aware detection deferred to
            // phase 2 (look for Mercury `:- module`, `:- pred`, etc).
            "pri" => Some(ProverKind::Princess), // Princess native format
            "trs" => Some(ProverKind::CSI),      // TRS rewriting system format (CSI/AProVE)
            _ => None,
        })
    }

    /// Content-aware prover detection for ambiguous file extensions
    ///
    /// For .c files, checks whether the source contains __CPROVER directives
    /// to determine if CBMC is the appropriate prover. For .lean files,
    /// checks for Lean 3 vs Lean 4 syntax markers.
    pub fn detect_from_file_content(path: &Path, content: &str) -> Option<ProverKind> {
        // Lean 3 / Lean 4 disambiguation — both share `.lean`. Lean 4
        // introduced `by` tactic blocks in place of `begin … end`, uses
        // `section`/`namespace` with `end <name>` trailers, and commonly
        // imports from `Mathlib.*` (capitalised). Lean 3 uses lowercase
        // `mathlib` paths, `begin … end` blocks, and `universes u v`
        // without the `u v : Level` annotation.
        if let Some(ext) = path.extension().and_then(|e| e.to_str()) {
            if ext == "lean" {
                let is_lean3 = content.contains("begin\n")
                    || content.contains("\nbegin ")
                    || content.contains("\nend.")
                    || (content.contains("universes ") && !content.contains(" : Level"))
                    || content.contains("import data.")
                    || content.contains("import tactic.");
                let is_lean4 = content.contains("import Mathlib.")
                    || content.contains(":= by\n")
                    || content.contains(":= by ")
                    || content.contains("theorem ") && content.contains("= by");
                if is_lean3 && !is_lean4 {
                    return Some(ProverKind::Lean3);
                }
                if is_lean4 {
                    return Some(ProverKind::Lean);
                }
                // Ambiguous → default to Lean 4 (current).
                return Some(ProverKind::Lean);
            }
        }

        // First try extension-based detection for non-Lean cases.
        if let Some(kind) = Self::detect_from_file(path) {
            return Some(kind);
        }

        // Content-aware fallback for .java and .c files
        if let Some(ext) = path.extension().and_then(|e| e.to_str()) {
            // Java files with JML annotations → KeY
            if ext == "java"
                && (content.contains("//@")
                    || content.contains("/*@")
                    || content.contains("requires") && content.contains("ensures"))
            {
                return Some(ProverKind::KeY);
            }

            if ext == "c" || ext == "h" {
                // Frama-C ACSL annotations take priority (deductive verification)
                if content.contains("/*@") || content.contains("//@") {
                    return Some(ProverKind::FramaC);
                }
                // SeaHorn sassert / seahorn.h (LLVM-based CHC verification)
                if content.contains("sassert(")
                    || content.contains("seahorn/seahorn.h")
                    || content.contains("nd_int(")
                {
                    return Some(ProverKind::SeaHorn);
                }
                // CBMC __CPROVER directives (bounded model checking)
                if content.contains("__CPROVER_assert")
                    || content.contains("__CPROVER_assume")
                    || content.contains("__CPROVER")
                {
                    return Some(ProverKind::CBMC);
                }
            }
        }

        None
    }
}
