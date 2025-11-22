// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Aspect tagging system for classifying theorems by domain/topic
//!
//! This module provides comprehensive aspect tagging to improve premise selection
//! and neural learning. Theorems are classified into multiple aspects based on:
//! - Mathematical domain (algebra, analysis, topology, etc.)
//! - Logical structure (propositional, predicate, modal, etc.)
//! - Computational properties (algorithms, complexity, verification)
//!
//! Multiple tagging strategies are supported:
//! - Rule-based: Keyword and pattern matching
//! - Neural: ML-based classification (integrates with Julia)
//! - OpenCyc: Ontology-based semantic tagging
//! - Composite: Combines multiple strategies

use crate::core::Term;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::fmt;

/// Mathematical and logical aspects for theorem classification
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub enum Aspect {
    // ========== Logic ==========
    /// Propositional logic (∧, ∨, ¬, →, ↔)
    PropositionalLogic,

    /// First-order/predicate logic (∀, ∃)
    PredicateLogic,

    /// Modal logic (□, ◇, necessity, possibility)
    ModalLogic,

    /// Temporal logic (always, eventually, until)
    TemporalLogic,

    /// Higher-order logic
    HigherOrderLogic,

    /// Intuitionistic/constructive logic
    IntuitionisticLogic,

    /// Classical logic
    ClassicalLogic,

    // ========== Arithmetic ==========
    /// Natural numbers (ℕ, Peano axioms)
    NaturalNumbers,

    /// Integers (ℤ)
    Integers,

    /// Rational numbers (ℚ)
    Rationals,

    /// Real numbers (ℝ, completeness)
    Reals,

    /// Complex numbers (ℂ)
    Complex,

    /// Number theory (primes, divisibility)
    NumberTheory,

    /// Arithmetic operations (+, -, *, /, mod)
    Arithmetic,

    // ========== Algebra ==========
    /// Group theory
    Groups,

    /// Ring theory
    Rings,

    /// Field theory
    Fields,

    /// Vector spaces, linear algebra
    VectorSpaces,

    /// Modules
    Modules,

    /// Lattices and order theory
    Lattices,

    /// Category theory
    CategoryTheory,

    /// Universal algebra
    UniversalAlgebra,

    // ========== Analysis ==========
    /// Limits and convergence
    Limits,

    /// Continuity
    Continuity,

    /// Derivatives, differential calculus
    Derivatives,

    /// Integrals, integral calculus
    Integrals,

    /// Sequences and series
    Sequences,

    /// Measure theory
    MeasureTheory,

    /// Functional analysis
    FunctionalAnalysis,

    // ========== Topology ==========
    /// Metric spaces
    MetricSpaces,

    /// Topological spaces
    TopologicalSpaces,

    /// Compactness
    Compactness,

    /// Connectedness
    Connectedness,

    /// Continuity (topological)
    TopologicalContinuity,

    // ========== Set Theory ==========
    /// Basic set operations (∪, ∩, ⊆)
    SetOperations,

    /// Cardinality
    Cardinality,

    /// Ordinals
    Ordinals,

    /// Axiom of choice
    AxiomOfChoice,

    /// ZFC set theory
    ZFC,

    // ========== Type Theory ==========
    /// Dependent types
    DependentTypes,

    /// Type universes
    Universes,

    /// Inductive types
    InductiveTypes,

    /// Coinductive types
    CoinductiveTypes,

    /// Polymorphism
    Polymorphism,

    /// Type equivalence
    TypeEquivalence,

    // ========== Computer Science ==========
    /// Algorithms and data structures
    Algorithms,

    /// Computational complexity
    Complexity,

    /// Formal verification
    FormalVerification,

    /// Program semantics
    ProgramSemantics,

    /// Concurrency
    Concurrency,

    /// Cryptography
    Cryptography,

    /// Automata theory
    Automata,

    /// Lambda calculus
    LambdaCalculus,

    // ========== Proof Techniques ==========
    /// Induction (mathematical, structural)
    Induction,

    /// Coinduction
    Coinduction,

    /// Recursion
    Recursion,

    /// Case analysis
    CaseAnalysis,

    /// Contradiction/reductio ad absurdum
    Contradiction,

    /// Direct proof
    DirectProof,

    // ========== Other ==========
    /// Combinatorics
    Combinatorics,

    /// Graph theory
    GraphTheory,

    /// Probability theory
    Probability,

    /// Game theory
    GameTheory,

    /// Geometry
    Geometry,

    /// Abstract nonsense (very general categorical results)
    AbstractNonsense,
}

impl Aspect {
    /// Get human-readable name
    pub fn name(&self) -> &'static str {
        match self {
            Aspect::PropositionalLogic => "Propositional Logic",
            Aspect::PredicateLogic => "Predicate Logic",
            Aspect::ModalLogic => "Modal Logic",
            Aspect::TemporalLogic => "Temporal Logic",
            Aspect::HigherOrderLogic => "Higher-Order Logic",
            Aspect::IntuitionisticLogic => "Intuitionistic Logic",
            Aspect::ClassicalLogic => "Classical Logic",
            Aspect::NaturalNumbers => "Natural Numbers",
            Aspect::Integers => "Integers",
            Aspect::Rationals => "Rational Numbers",
            Aspect::Reals => "Real Numbers",
            Aspect::Complex => "Complex Numbers",
            Aspect::NumberTheory => "Number Theory",
            Aspect::Arithmetic => "Arithmetic",
            Aspect::Groups => "Group Theory",
            Aspect::Rings => "Ring Theory",
            Aspect::Fields => "Field Theory",
            Aspect::VectorSpaces => "Vector Spaces",
            Aspect::Modules => "Modules",
            Aspect::Lattices => "Lattices",
            Aspect::CategoryTheory => "Category Theory",
            Aspect::UniversalAlgebra => "Universal Algebra",
            Aspect::Limits => "Limits",
            Aspect::Continuity => "Continuity",
            Aspect::Derivatives => "Derivatives",
            Aspect::Integrals => "Integrals",
            Aspect::Sequences => "Sequences",
            Aspect::MeasureTheory => "Measure Theory",
            Aspect::FunctionalAnalysis => "Functional Analysis",
            Aspect::MetricSpaces => "Metric Spaces",
            Aspect::TopologicalSpaces => "Topological Spaces",
            Aspect::Compactness => "Compactness",
            Aspect::Connectedness => "Connectedness",
            Aspect::TopologicalContinuity => "Topological Continuity",
            Aspect::SetOperations => "Set Operations",
            Aspect::Cardinality => "Cardinality",
            Aspect::Ordinals => "Ordinals",
            Aspect::AxiomOfChoice => "Axiom of Choice",
            Aspect::ZFC => "ZFC Set Theory",
            Aspect::DependentTypes => "Dependent Types",
            Aspect::Universes => "Type Universes",
            Aspect::InductiveTypes => "Inductive Types",
            Aspect::CoinductiveTypes => "Coinductive Types",
            Aspect::Polymorphism => "Polymorphism",
            Aspect::TypeEquivalence => "Type Equivalence",
            Aspect::Algorithms => "Algorithms",
            Aspect::Complexity => "Complexity Theory",
            Aspect::FormalVerification => "Formal Verification",
            Aspect::ProgramSemantics => "Program Semantics",
            Aspect::Concurrency => "Concurrency",
            Aspect::Cryptography => "Cryptography",
            Aspect::Automata => "Automata Theory",
            Aspect::LambdaCalculus => "Lambda Calculus",
            Aspect::Induction => "Induction",
            Aspect::Coinduction => "Coinduction",
            Aspect::Recursion => "Recursion",
            Aspect::CaseAnalysis => "Case Analysis",
            Aspect::Contradiction => "Proof by Contradiction",
            Aspect::DirectProof => "Direct Proof",
            Aspect::Combinatorics => "Combinatorics",
            Aspect::GraphTheory => "Graph Theory",
            Aspect::Probability => "Probability Theory",
            Aspect::GameTheory => "Game Theory",
            Aspect::Geometry => "Geometry",
            Aspect::AbstractNonsense => "Abstract Nonsense",
        }
    }

    /// Get category (high-level grouping)
    pub fn category(&self) -> AspectCategory {
        match self {
            Aspect::PropositionalLogic | Aspect::PredicateLogic | Aspect::ModalLogic
            | Aspect::TemporalLogic | Aspect::HigherOrderLogic | Aspect::IntuitionisticLogic
            | Aspect::ClassicalLogic => AspectCategory::Logic,

            Aspect::NaturalNumbers | Aspect::Integers | Aspect::Rationals | Aspect::Reals
            | Aspect::Complex | Aspect::NumberTheory | Aspect::Arithmetic => AspectCategory::Arithmetic,

            Aspect::Groups | Aspect::Rings | Aspect::Fields | Aspect::VectorSpaces
            | Aspect::Modules | Aspect::Lattices | Aspect::CategoryTheory
            | Aspect::UniversalAlgebra => AspectCategory::Algebra,

            Aspect::Limits | Aspect::Continuity | Aspect::Derivatives | Aspect::Integrals
            | Aspect::Sequences | Aspect::MeasureTheory | Aspect::FunctionalAnalysis => AspectCategory::Analysis,

            Aspect::MetricSpaces | Aspect::TopologicalSpaces | Aspect::Compactness
            | Aspect::Connectedness | Aspect::TopologicalContinuity => AspectCategory::Topology,

            Aspect::SetOperations | Aspect::Cardinality | Aspect::Ordinals
            | Aspect::AxiomOfChoice | Aspect::ZFC => AspectCategory::SetTheory,

            Aspect::DependentTypes | Aspect::Universes | Aspect::InductiveTypes
            | Aspect::CoinductiveTypes | Aspect::Polymorphism | Aspect::TypeEquivalence => AspectCategory::TypeTheory,

            Aspect::Algorithms | Aspect::Complexity | Aspect::FormalVerification
            | Aspect::ProgramSemantics | Aspect::Concurrency | Aspect::Cryptography
            | Aspect::Automata | Aspect::LambdaCalculus => AspectCategory::ComputerScience,

            Aspect::Induction | Aspect::Coinduction | Aspect::Recursion | Aspect::CaseAnalysis
            | Aspect::Contradiction | Aspect::DirectProof => AspectCategory::ProofTechniques,

            _ => AspectCategory::Other,
        }
    }
}

impl fmt::Display for Aspect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// High-level aspect categories
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AspectCategory {
    Logic,
    Arithmetic,
    Algebra,
    Analysis,
    Topology,
    SetTheory,
    TypeTheory,
    ComputerScience,
    ProofTechniques,
    Other,
}

/// Features extracted from a theorem for aspect classification
#[derive(Debug, Clone, Default)]
pub struct TheoremFeatures {
    /// Symbols found in the theorem
    pub symbols: HashSet<String>,

    /// Keywords found in theorem name/statement
    pub keywords: HashSet<String>,

    /// Term structure patterns
    pub patterns: HashSet<String>,

    /// Quantifier count (∀, ∃)
    pub quantifier_count: usize,

    /// Lambda abstraction depth
    pub lambda_depth: usize,

    /// Pi type (dependent function) count
    pub pi_count: usize,

    /// Universe levels used
    pub universe_levels: HashSet<usize>,

    /// Function application depth
    pub app_depth: usize,
}

/// Trait for aspect tagging strategies
pub trait AspectTagger: Send + Sync {
    /// Tag a theorem with relevant aspects
    fn tag(&self, theorem_name: &str, statement: &Term) -> Vec<Aspect>;

    /// Extract features from theorem (optional, for analysis)
    fn extract_features(&self, _statement: &Term) -> TheoremFeatures {
        TheoremFeatures::default()
    }

    /// Get confidence scores for each aspect (0.0 to 1.0)
    fn tag_with_confidence(&self, theorem_name: &str, statement: &Term) -> HashMap<Aspect, f64> {
        self.tag(theorem_name, statement)
            .into_iter()
            .map(|aspect| (aspect, 1.0))
            .collect()
    }
}

/// Rule-based tagger using keyword and pattern matching
pub struct RuleBasedTagger {
    /// Keyword to aspects mapping
    keyword_rules: HashMap<String, Vec<Aspect>>,

    /// Symbol to aspects mapping
    symbol_rules: HashMap<String, Vec<Aspect>>,

    /// Minimum confidence threshold (0.0 to 1.0)
    threshold: f64,
}

impl RuleBasedTagger {
    /// Create new rule-based tagger with default rules
    pub fn new() -> Self {
        let mut tagger = RuleBasedTagger {
            keyword_rules: HashMap::new(),
            symbol_rules: HashMap::new(),
            threshold: 0.3,
        };
        tagger.initialize_default_rules();
        tagger
    }

    /// Create with custom threshold
    pub fn with_threshold(threshold: f64) -> Self {
        let mut tagger = Self::new();
        tagger.threshold = threshold;
        tagger
    }

    /// Initialize default keyword and symbol rules
    fn initialize_default_rules(&mut self) {
        // Logic keywords
        self.add_keyword_rule("prop", vec![Aspect::PropositionalLogic]);
        self.add_keyword_rule("predicate", vec![Aspect::PredicateLogic]);
        self.add_keyword_rule("modal", vec![Aspect::ModalLogic]);
        self.add_keyword_rule("temporal", vec![Aspect::TemporalLogic]);
        self.add_keyword_rule("intuitionistic", vec![Aspect::IntuitionisticLogic]);
        self.add_keyword_rule("classical", vec![Aspect::ClassicalLogic]);
        self.add_keyword_rule("forall", vec![Aspect::PredicateLogic]);
        self.add_keyword_rule("exists", vec![Aspect::PredicateLogic]);

        // Arithmetic keywords
        self.add_keyword_rule("nat", vec![Aspect::NaturalNumbers]);
        self.add_keyword_rule("natural", vec![Aspect::NaturalNumbers]);
        self.add_keyword_rule("int", vec![Aspect::Integers]);
        self.add_keyword_rule("integer", vec![Aspect::Integers]);
        self.add_keyword_rule("rational", vec![Aspect::Rationals]);
        self.add_keyword_rule("real", vec![Aspect::Reals]);
        self.add_keyword_rule("complex", vec![Aspect::Complex]);
        self.add_keyword_rule("prime", vec![Aspect::NumberTheory]);
        self.add_keyword_rule("divisible", vec![Aspect::NumberTheory, Aspect::Arithmetic]);
        self.add_keyword_rule("add", vec![Aspect::Arithmetic]);
        self.add_keyword_rule("mult", vec![Aspect::Arithmetic]);
        self.add_keyword_rule("plus", vec![Aspect::Arithmetic]);
        self.add_keyword_rule("times", vec![Aspect::Arithmetic]);

        // Algebra keywords
        self.add_keyword_rule("group", vec![Aspect::Groups]);
        self.add_keyword_rule("ring", vec![Aspect::Rings]);
        self.add_keyword_rule("field", vec![Aspect::Fields]);
        self.add_keyword_rule("vector", vec![Aspect::VectorSpaces]);
        self.add_keyword_rule("module", vec![Aspect::Modules]);
        self.add_keyword_rule("lattice", vec![Aspect::Lattices]);
        self.add_keyword_rule("category", vec![Aspect::CategoryTheory]);
        self.add_keyword_rule("functor", vec![Aspect::CategoryTheory]);
        self.add_keyword_rule("morphism", vec![Aspect::CategoryTheory]);

        // Analysis keywords
        self.add_keyword_rule("limit", vec![Aspect::Limits]);
        self.add_keyword_rule("continuous", vec![Aspect::Continuity]);
        self.add_keyword_rule("derivative", vec![Aspect::Derivatives]);
        self.add_keyword_rule("integral", vec![Aspect::Integrals]);
        self.add_keyword_rule("sequence", vec![Aspect::Sequences]);
        self.add_keyword_rule("series", vec![Aspect::Sequences]);
        self.add_keyword_rule("measure", vec![Aspect::MeasureTheory]);
        self.add_keyword_rule("convergence", vec![Aspect::Limits, Aspect::Sequences]);

        // Topology keywords
        self.add_keyword_rule("metric", vec![Aspect::MetricSpaces]);
        self.add_keyword_rule("topology", vec![Aspect::TopologicalSpaces]);
        self.add_keyword_rule("topological", vec![Aspect::TopologicalSpaces]);
        self.add_keyword_rule("compact", vec![Aspect::Compactness]);
        self.add_keyword_rule("connected", vec![Aspect::Connectedness]);
        self.add_keyword_rule("open", vec![Aspect::TopologicalSpaces]);
        self.add_keyword_rule("closed", vec![Aspect::TopologicalSpaces]);

        // Set theory keywords
        self.add_keyword_rule("set", vec![Aspect::SetOperations]);
        self.add_keyword_rule("union", vec![Aspect::SetOperations]);
        self.add_keyword_rule("intersection", vec![Aspect::SetOperations]);
        self.add_keyword_rule("subset", vec![Aspect::SetOperations]);
        self.add_keyword_rule("cardinality", vec![Aspect::Cardinality]);
        self.add_keyword_rule("countable", vec![Aspect::Cardinality]);
        self.add_keyword_rule("uncountable", vec![Aspect::Cardinality]);
        self.add_keyword_rule("ordinal", vec![Aspect::Ordinals]);
        self.add_keyword_rule("choice", vec![Aspect::AxiomOfChoice]);
        self.add_keyword_rule("zfc", vec![Aspect::ZFC]);

        // Type theory keywords
        self.add_keyword_rule("dependent", vec![Aspect::DependentTypes]);
        self.add_keyword_rule("universe", vec![Aspect::Universes]);
        self.add_keyword_rule("inductive", vec![Aspect::InductiveTypes]);
        self.add_keyword_rule("coinductive", vec![Aspect::CoinductiveTypes]);
        self.add_keyword_rule("polymorphic", vec![Aspect::Polymorphism]);
        self.add_keyword_rule("type", vec![Aspect::DependentTypes]);

        // Computer science keywords
        self.add_keyword_rule("algorithm", vec![Aspect::Algorithms]);
        self.add_keyword_rule("complexity", vec![Aspect::Complexity]);
        self.add_keyword_rule("verify", vec![Aspect::FormalVerification]);
        self.add_keyword_rule("verification", vec![Aspect::FormalVerification]);
        self.add_keyword_rule("program", vec![Aspect::ProgramSemantics]);
        self.add_keyword_rule("semantic", vec![Aspect::ProgramSemantics]);
        self.add_keyword_rule("concurrent", vec![Aspect::Concurrency]);
        self.add_keyword_rule("crypto", vec![Aspect::Cryptography]);
        self.add_keyword_rule("automaton", vec![Aspect::Automata]);
        self.add_keyword_rule("lambda", vec![Aspect::LambdaCalculus]);

        // Proof technique keywords
        self.add_keyword_rule("induction", vec![Aspect::Induction]);
        self.add_keyword_rule("inductive", vec![Aspect::Induction, Aspect::InductiveTypes]);
        self.add_keyword_rule("coinduction", vec![Aspect::Coinduction]);
        self.add_keyword_rule("recursive", vec![Aspect::Recursion]);
        self.add_keyword_rule("recursion", vec![Aspect::Recursion]);
        self.add_keyword_rule("case", vec![Aspect::CaseAnalysis]);
        self.add_keyword_rule("contradiction", vec![Aspect::Contradiction]);

        // Other keywords
        self.add_keyword_rule("combinatorial", vec![Aspect::Combinatorics]);
        self.add_keyword_rule("graph", vec![Aspect::GraphTheory]);
        self.add_keyword_rule("probability", vec![Aspect::Probability]);
        self.add_keyword_rule("game", vec![Aspect::GameTheory]);
        self.add_keyword_rule("geometric", vec![Aspect::Geometry]);
        self.add_keyword_rule("geometry", vec![Aspect::Geometry]);

        // Symbol rules (mathematical notation)
        self.add_symbol_rule("∀", vec![Aspect::PredicateLogic]);
        self.add_symbol_rule("∃", vec![Aspect::PredicateLogic]);
        self.add_symbol_rule("∧", vec![Aspect::PropositionalLogic]);
        self.add_symbol_rule("∨", vec![Aspect::PropositionalLogic]);
        self.add_symbol_rule("¬", vec![Aspect::PropositionalLogic]);
        self.add_symbol_rule("→", vec![Aspect::PropositionalLogic]);
        self.add_symbol_rule("↔", vec![Aspect::PropositionalLogic]);
        self.add_symbol_rule("□", vec![Aspect::ModalLogic]);
        self.add_symbol_rule("◇", vec![Aspect::ModalLogic]);
        self.add_symbol_rule("λ", vec![Aspect::LambdaCalculus, Aspect::HigherOrderLogic]);
        self.add_symbol_rule("Π", vec![Aspect::DependentTypes]);
        self.add_symbol_rule("ℕ", vec![Aspect::NaturalNumbers]);
        self.add_symbol_rule("ℤ", vec![Aspect::Integers]);
        self.add_symbol_rule("ℚ", vec![Aspect::Rationals]);
        self.add_symbol_rule("ℝ", vec![Aspect::Reals]);
        self.add_symbol_rule("ℂ", vec![Aspect::Complex]);
        self.add_symbol_rule("∪", vec![Aspect::SetOperations]);
        self.add_symbol_rule("∩", vec![Aspect::SetOperations]);
        self.add_symbol_rule("⊆", vec![Aspect::SetOperations]);
        self.add_symbol_rule("∈", vec![Aspect::SetOperations]);
        self.add_symbol_rule("lim", vec![Aspect::Limits]);
        self.add_symbol_rule("∫", vec![Aspect::Integrals]);
        self.add_symbol_rule("∑", vec![Aspect::Sequences]);
        self.add_symbol_rule("∏", vec![Aspect::Sequences]);
    }

    /// Add a keyword rule
    pub fn add_keyword_rule(&mut self, keyword: &str, aspects: Vec<Aspect>) {
        self.keyword_rules.insert(keyword.to_lowercase(), aspects);
    }

    /// Add a symbol rule
    pub fn add_symbol_rule(&mut self, symbol: &str, aspects: Vec<Aspect>) {
        self.symbol_rules.insert(symbol.to_string(), aspects);
    }

    /// Extract keywords from theorem name
    fn extract_keywords(&self, name: &str) -> HashSet<String> {
        name.to_lowercase()
            .split(|c: char| !c.is_alphanumeric())
            .filter(|s| !s.is_empty())
            .map(|s| s.to_string())
            .collect()
    }

    /// Extract symbols from term
    fn extract_symbols(&self, term: &Term) -> HashSet<String> {
        let mut symbols = HashSet::new();
        self.extract_symbols_recursive(term, &mut symbols);
        symbols
    }

    fn extract_symbols_recursive(&self, term: &Term, symbols: &mut HashSet<String>) {
        match term {
            Term::Var(_) | Term::Meta(_) => {},
            Term::Const(name) => {
                symbols.insert(name.clone());
            },
            Term::App { func, args } => {
                self.extract_symbols_recursive(func, symbols);
                for arg in args {
                    self.extract_symbols_recursive(arg, symbols);
                }
            },
            Term::Lambda { body, .. } => {
                self.extract_symbols_recursive(body, symbols);
            },
            Term::Pi { param_type, body, .. } => {
                self.extract_symbols_recursive(param_type, symbols);
                self.extract_symbols_recursive(body, symbols);
            },
            Term::Universe(_) => {},
            Term::ProverSpecific { .. } => {},
        }
    }
}

impl Default for RuleBasedTagger {
    fn default() -> Self {
        Self::new()
    }
}

impl AspectTagger for RuleBasedTagger {
    fn tag(&self, theorem_name: &str, statement: &Term) -> Vec<Aspect> {
        let scores = self.tag_with_confidence(theorem_name, statement);
        let mut aspects: Vec<_> = scores
            .into_iter()
            .filter(|(_, score)| *score >= self.threshold)
            .map(|(aspect, _)| aspect)
            .collect();
        aspects.sort();
        aspects
    }

    fn tag_with_confidence(&self, theorem_name: &str, statement: &Term) -> HashMap<Aspect, f64> {
        let mut aspect_counts: HashMap<Aspect, usize> = HashMap::new();
        let mut total_matches = 0;

        // Extract keywords from name
        let keywords = self.extract_keywords(theorem_name);

        // Match keywords
        for keyword in &keywords {
            if let Some(aspects) = self.keyword_rules.get(keyword) {
                for aspect in aspects {
                    *aspect_counts.entry(*aspect).or_insert(0) += 1;
                    total_matches += 1;
                }
            }
        }

        // Extract symbols from statement
        let symbols = self.extract_symbols(statement);

        // Match symbols
        for symbol in &symbols {
            if let Some(aspects) = self.symbol_rules.get(symbol) {
                for aspect in aspects {
                    *aspect_counts.entry(*aspect).or_insert(0) += 1;
                    total_matches += 1;
                }
            }
        }

        // Analyze term structure
        let features = self.extract_features(statement);

        // Add structural aspects
        if features.quantifier_count > 0 {
            *aspect_counts.entry(Aspect::PredicateLogic).or_insert(0) += features.quantifier_count;
            total_matches += features.quantifier_count;
        }

        if features.lambda_depth > 0 {
            *aspect_counts.entry(Aspect::HigherOrderLogic).or_insert(0) += 1;
            *aspect_counts.entry(Aspect::LambdaCalculus).or_insert(0) += 1;
            total_matches += 2;
        }

        if features.pi_count > 0 {
            *aspect_counts.entry(Aspect::DependentTypes).or_insert(0) += features.pi_count;
            total_matches += features.pi_count;
        }

        if !features.universe_levels.is_empty() {
            *aspect_counts.entry(Aspect::Universes).or_insert(0) += 1;
            total_matches += 1;
        }

        // Convert counts to confidence scores
        let mut confidence_scores = HashMap::new();
        if total_matches > 0 {
            for (aspect, count) in aspect_counts {
                let score = count as f64 / total_matches as f64;
                confidence_scores.insert(aspect, score);
            }
        }

        confidence_scores
    }

    fn extract_features(&self, statement: &Term) -> TheoremFeatures {
        let mut features = TheoremFeatures::default();
        self.analyze_term(statement, &mut features, 0);
        features
    }
}

impl RuleBasedTagger {
    fn analyze_term(&self, term: &Term, features: &mut TheoremFeatures, depth: usize) {
        match term {
            Term::Var(name) => {
                features.symbols.insert(name.clone());
            },
            Term::Const(name) => {
                features.symbols.insert(name.clone());

                // Check for quantifiers
                if name == "forall" || name == "∀" {
                    features.quantifier_count += 1;
                } else if name == "exists" || name == "∃" {
                    features.quantifier_count += 1;
                }
            },
            Term::App { func, args } => {
                features.app_depth = features.app_depth.max(depth + 1);
                self.analyze_term(func, features, depth + 1);
                for arg in args {
                    self.analyze_term(arg, features, depth + 1);
                }
            },
            Term::Lambda { param_type, body, .. } => {
                features.lambda_depth = features.lambda_depth.max(depth + 1);
                if let Some(ty) = param_type {
                    self.analyze_term(ty, features, depth + 1);
                }
                self.analyze_term(body, features, depth + 1);
            },
            Term::Pi { param_type, body, .. } => {
                features.pi_count += 1;
                self.analyze_term(param_type, features, depth + 1);
                self.analyze_term(body, features, depth + 1);
            },
            Term::Universe(level) => {
                features.universe_levels.insert(*level);
            },
            Term::Meta(_) => {},
            Term::ProverSpecific { .. } => {},
        }
    }
}

/// Neural tagger using ML-based classification
///
/// This integrates with Julia ML components for neural aspect classification.
/// The neural model is trained on a corpus of tagged theorems.
pub struct NeuralTagger {
    /// Confidence threshold for aspect prediction
    threshold: f64,

    /// URL of Julia ML service (if remote)
    service_url: Option<String>,
}

impl NeuralTagger {
    /// Create new neural tagger
    pub fn new() -> Self {
        NeuralTagger {
            threshold: 0.5,
            service_url: None,
        }
    }

    /// Create with custom threshold
    pub fn with_threshold(threshold: f64) -> Self {
        NeuralTagger {
            threshold,
            service_url: None,
        }
    }

    /// Set Julia ML service URL
    pub fn with_service_url(mut self, url: String) -> Self {
        self.service_url = Some(url);
        self
    }

    /// Get embeddings for a term (to be implemented with Julia integration)
    async fn get_embeddings(&self, _statement: &Term) -> Vec<f64> {
        // TODO: Implement Julia FFI or HTTP call to Julia ML service
        // For now, return dummy embeddings
        vec![0.0; 128]
    }

    /// Classify embeddings into aspects (to be implemented)
    async fn classify_embeddings(&self, _embeddings: &[f64]) -> HashMap<Aspect, f64> {
        // TODO: Implement Julia FFI or HTTP call to Julia ML service
        // For now, return empty predictions
        HashMap::new()
    }
}

impl Default for NeuralTagger {
    fn default() -> Self {
        Self::new()
    }
}

impl AspectTagger for NeuralTagger {
    fn tag(&self, _theorem_name: &str, _statement: &Term) -> Vec<Aspect> {
        // TODO: Implement async neural tagging
        // For now, return empty (requires Julia integration)
        Vec::new()
    }

    fn tag_with_confidence(&self, _theorem_name: &str, _statement: &Term) -> HashMap<Aspect, f64> {
        // TODO: Implement async neural tagging with confidence scores
        // This will call Julia ML service for predictions
        HashMap::new()
    }
}

/// OpenCyc ontology-based tagger
///
/// Maps mathematical concepts to OpenCyc ontology and uses semantic relationships
/// to infer aspects.
pub struct OpenCycTagger {
    /// OpenCyc service URL
    service_url: String,

    /// Cached concept mappings
    concept_cache: HashMap<String, Vec<Aspect>>,
}

impl OpenCycTagger {
    /// Create new OpenCyc tagger
    pub fn new(service_url: String) -> Self {
        OpenCycTagger {
            service_url,
            concept_cache: HashMap::new(),
        }
    }

    /// Query OpenCyc for concept relationships
    async fn query_concept(&self, _concept: &str) -> Option<Vec<Aspect>> {
        // TODO: Implement OpenCyc API integration
        // For now, return None
        None
    }
}

impl AspectTagger for OpenCycTagger {
    fn tag(&self, _theorem_name: &str, _statement: &Term) -> Vec<Aspect> {
        // TODO: Implement OpenCyc ontology-based tagging
        // For now, return empty (requires OpenCyc integration)
        Vec::new()
    }
}

/// Composite tagger that combines multiple tagging strategies
pub struct CompositeTagger {
    taggers: Vec<Box<dyn AspectTagger>>,

    /// Weights for each tagger (must match length of taggers)
    weights: Vec<f64>,

    /// Aggregation strategy
    strategy: AggregationStrategy,
}

/// Strategy for combining multiple tagger results
#[derive(Debug, Clone, Copy)]
pub enum AggregationStrategy {
    /// Take union of all aspects
    Union,

    /// Take intersection of all aspects
    Intersection,

    /// Weighted voting (use confidence scores)
    WeightedVoting,

    /// Take aspects with majority vote
    Majority,
}

impl CompositeTagger {
    /// Create new composite tagger
    pub fn new(strategy: AggregationStrategy) -> Self {
        CompositeTagger {
            taggers: Vec::new(),
            weights: Vec::new(),
            strategy,
        }
    }

    /// Add a tagger with weight
    pub fn add_tagger(mut self, tagger: Box<dyn AspectTagger>, weight: f64) -> Self {
        self.taggers.push(tagger);
        self.weights.push(weight);
        self
    }
}

impl AspectTagger for CompositeTagger {
    fn tag(&self, theorem_name: &str, statement: &Term) -> Vec<Aspect> {
        if self.taggers.is_empty() {
            return Vec::new();
        }

        match self.strategy {
            AggregationStrategy::Union => {
                let mut all_aspects = HashSet::new();
                for tagger in &self.taggers {
                    for aspect in tagger.tag(theorem_name, statement) {
                        all_aspects.insert(aspect);
                    }
                }
                let mut result: Vec<_> = all_aspects.into_iter().collect();
                result.sort();
                result
            },

            AggregationStrategy::Intersection => {
                if self.taggers.is_empty() {
                    return Vec::new();
                }

                let mut common_aspects: Option<HashSet<Aspect>> = None;
                for tagger in &self.taggers {
                    let aspects: HashSet<_> = tagger.tag(theorem_name, statement).into_iter().collect();
                    common_aspects = Some(match common_aspects {
                        None => aspects,
                        Some(prev) => prev.intersection(&aspects).copied().collect(),
                    });
                }

                let mut result: Vec<_> = common_aspects.unwrap_or_default().into_iter().collect();
                result.sort();
                result
            },

            AggregationStrategy::WeightedVoting | AggregationStrategy::Majority => {
                let scores = self.tag_with_confidence(theorem_name, statement);
                let threshold = match self.strategy {
                    AggregationStrategy::WeightedVoting => 0.3,
                    AggregationStrategy::Majority => 0.5,
                    _ => 0.0,
                };

                let mut aspects: Vec<_> = scores
                    .into_iter()
                    .filter(|(_, score)| *score >= threshold)
                    .map(|(aspect, _)| aspect)
                    .collect();
                aspects.sort();
                aspects
            },
        }
    }

    fn tag_with_confidence(&self, theorem_name: &str, statement: &Term) -> HashMap<Aspect, f64> {
        let mut combined_scores: HashMap<Aspect, f64> = HashMap::new();
        let total_weight: f64 = self.weights.iter().sum();

        if total_weight == 0.0 {
            return combined_scores;
        }

        for (tagger, weight) in self.taggers.iter().zip(&self.weights) {
            let scores = tagger.tag_with_confidence(theorem_name, statement);
            for (aspect, score) in scores {
                *combined_scores.entry(aspect).or_insert(0.0) += score * weight / total_weight;
            }
        }

        combined_scores
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_aspect_categories() {
        assert_eq!(Aspect::PropositionalLogic.category(), AspectCategory::Logic);
        assert_eq!(Aspect::NaturalNumbers.category(), AspectCategory::Arithmetic);
        assert_eq!(Aspect::Groups.category(), AspectCategory::Algebra);
        assert_eq!(Aspect::Limits.category(), AspectCategory::Analysis);
        assert_eq!(Aspect::MetricSpaces.category(), AspectCategory::Topology);
        assert_eq!(Aspect::SetOperations.category(), AspectCategory::SetTheory);
        assert_eq!(Aspect::DependentTypes.category(), AspectCategory::TypeTheory);
        assert_eq!(Aspect::Algorithms.category(), AspectCategory::ComputerScience);
        assert_eq!(Aspect::Induction.category(), AspectCategory::ProofTechniques);
    }

    #[test]
    fn test_aspect_names() {
        assert_eq!(Aspect::PropositionalLogic.name(), "Propositional Logic");
        assert_eq!(Aspect::NaturalNumbers.name(), "Natural Numbers");
        assert_eq!(Aspect::CategoryTheory.name(), "Category Theory");
    }

    #[test]
    fn test_rule_based_tagger_keywords() {
        let tagger = RuleBasedTagger::new();

        // Test arithmetic theorem
        let theorem_name = "nat_add_comm";
        let statement = Term::Const("add".to_string());
        let aspects = tagger.tag(theorem_name, &statement);

        assert!(aspects.contains(&Aspect::NaturalNumbers));
        assert!(aspects.contains(&Aspect::Arithmetic));
    }

    #[test]
    fn test_rule_based_tagger_structure() {
        let tagger = RuleBasedTagger::new();

        // Test dependent type theorem
        let theorem_name = "vector_type";
        let statement = Term::Pi {
            param: "n".to_string(),
            param_type: Box::new(Term::Const("Nat".to_string())),
            body: Box::new(Term::Universe(0)),
        };

        let aspects = tagger.tag(theorem_name, &statement);
        assert!(aspects.contains(&Aspect::DependentTypes));
    }

    #[test]
    fn test_rule_based_tagger_quantifiers() {
        let tagger = RuleBasedTagger::new();

        // Test predicate logic theorem
        let theorem_name = "forall_intro";
        let statement = Term::App {
            func: Box::new(Term::Const("forall".to_string())),
            args: vec![Term::Var("P".to_string())],
        };

        let aspects = tagger.tag(theorem_name, &statement);
        assert!(aspects.contains(&Aspect::PredicateLogic));
    }

    #[test]
    fn test_feature_extraction() {
        let tagger = RuleBasedTagger::new();

        let statement = Term::Lambda {
            param: "x".to_string(),
            param_type: Some(Box::new(Term::Const("Nat".to_string()))),
            body: Box::new(Term::App {
                func: Box::new(Term::Const("add".to_string())),
                args: vec![
                    Term::Var("x".to_string()),
                    Term::Const("1".to_string()),
                ],
            }),
        };

        let features = tagger.extract_features(&statement);
        assert!(features.lambda_depth > 0);
        assert!(features.symbols.contains("Nat"));
        assert!(features.symbols.contains("add"));
    }

    #[test]
    fn test_composite_tagger_union() {
        let mut tagger = CompositeTagger::new(AggregationStrategy::Union);
        tagger = tagger.add_tagger(Box::new(RuleBasedTagger::new()), 1.0);

        let theorem_name = "nat_add_comm";
        let statement = Term::Const("add".to_string());
        let aspects = tagger.tag(theorem_name, &statement);

        assert!(!aspects.is_empty());
    }

    #[test]
    fn test_confidence_scores() {
        let tagger = RuleBasedTagger::new();

        let theorem_name = "group_homomorphism";
        let statement = Term::Const("group".to_string());
        let scores = tagger.tag_with_confidence(theorem_name, &statement);

        assert!(scores.contains_key(&Aspect::Groups));
        assert!(scores[&Aspect::Groups] > 0.0);
        assert!(scores[&Aspect::Groups] <= 1.0);
    }

    #[test]
    fn test_multi_aspect_tagging() {
        let tagger = RuleBasedTagger::new();

        // Theorem involving both topology and analysis
        let theorem_name = "continuous_limit";
        let statement = Term::App {
            func: Box::new(Term::Const("continuous".to_string())),
            args: vec![Term::Const("limit".to_string())],
        };

        let aspects = tagger.tag(theorem_name, &statement);
        assert!(aspects.contains(&Aspect::Continuity));
        assert!(aspects.contains(&Aspect::Limits));
    }

    #[test]
    fn test_threshold_filtering() {
        let tagger = RuleBasedTagger::with_threshold(0.8);

        let theorem_name = "simple_test";
        let statement = Term::Const("test".to_string());
        let aspects = tagger.tag(theorem_name, &statement);

        // High threshold should filter out low-confidence aspects
        assert!(aspects.is_empty() || aspects.len() <= 2);
    }

    #[test]
    fn test_category_theory_aspects() {
        let tagger = RuleBasedTagger::new();

        let theorem_name = "functor_composition";
        let statement = Term::App {
            func: Box::new(Term::Const("functor".to_string())),
            args: vec![Term::Const("compose".to_string())],
        };

        let aspects = tagger.tag(theorem_name, &statement);
        assert!(aspects.contains(&Aspect::CategoryTheory));
    }

    #[test]
    fn test_induction_detection() {
        let tagger = RuleBasedTagger::new();

        let theorem_name = "nat_induction_principle";
        let statement = Term::Const("induction".to_string());
        let aspects = tagger.tag(theorem_name, &statement);

        assert!(aspects.contains(&Aspect::Induction));
    }
}
