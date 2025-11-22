// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Example demonstrating aspect tagging system usage

use echidna::aspect::{
    Aspect, AspectTagger, RuleBasedTagger, CompositeTagger,
    AggregationStrategy, NeuralTagger, TheoremFeatures
};
use echidna::core::Term;

fn main() {
    println!("=== ECHIDNA Aspect Tagging System Demo ===\n");

    // Create a rule-based tagger
    let tagger = RuleBasedTagger::new();

    // Example 1: Natural number arithmetic theorem
    println!("1. Natural Number Arithmetic:");
    let theorem_name = "nat_add_comm";
    let statement = Term::App {
        func: Box::new(Term::Const("add".to_string())),
        args: vec![
            Term::Var("n".to_string()),
            Term::Var("m".to_string()),
        ],
    };

    let aspects = tagger.tag(theorem_name, &statement);
    println!("   Theorem: {}", theorem_name);
    println!("   Aspects: {:?}", aspects);
    println!("   Categories: {:?}",
        aspects.iter().map(|a| a.category()).collect::<Vec<_>>());
    println!();

    // Example 2: Dependent type theorem
    println!("2. Dependent Type Theory:");
    let theorem_name = "vector_length_type";
    let statement = Term::Pi {
        param: "n".to_string(),
        param_type: Box::new(Term::Const("Nat".to_string())),
        body: Box::new(Term::Universe(0)),
    };

    let aspects = tagger.tag(theorem_name, &statement);
    println!("   Theorem: {}", theorem_name);
    println!("   Aspects: {:?}", aspects);
    println!();

    // Example 3: Group theory theorem
    println!("3. Group Theory:");
    let theorem_name = "group_homomorphism_composition";
    let statement = Term::App {
        func: Box::new(Term::Const("group".to_string())),
        args: vec![Term::Const("homomorphism".to_string())],
    };

    let aspects = tagger.tag(theorem_name, &statement);
    let scores = tagger.tag_with_confidence(theorem_name, &statement);
    println!("   Theorem: {}", theorem_name);
    println!("   Aspects: {:?}", aspects);
    println!("   Confidence scores:");
    for (aspect, score) in scores {
        println!("      {} = {:.2}", aspect.name(), score);
    }
    println!();

    // Example 4: Lambda calculus theorem
    println!("4. Lambda Calculus:");
    let theorem_name = "beta_reduction";
    let statement = Term::Lambda {
        param: "x".to_string(),
        param_type: Some(Box::new(Term::Universe(0))),
        body: Box::new(Term::Var("x".to_string())),
    };

    let features = tagger.extract_features(&statement);
    let aspects = tagger.tag(theorem_name, &statement);
    println!("   Theorem: {}", theorem_name);
    println!("   Features:");
    println!("      Lambda depth: {}", features.lambda_depth);
    println!("      Symbols: {:?}", features.symbols);
    println!("   Aspects: {:?}", aspects);
    println!();

    // Example 5: Topology theorem
    println!("5. Topology:");
    let theorem_name = "continuous_compact_preserving";
    let statement = Term::App {
        func: Box::new(Term::Const("continuous".to_string())),
        args: vec![
            Term::Const("compact".to_string()),
            Term::Const("metric".to_string()),
        ],
    };

    let aspects = tagger.tag(theorem_name, &statement);
    println!("   Theorem: {}", theorem_name);
    println!("   Aspects: {:?}", aspects);
    println!();

    // Example 6: Composite tagger with multiple strategies
    println!("6. Composite Tagger:");
    let composite = CompositeTagger::new(AggregationStrategy::WeightedVoting)
        .add_tagger(Box::new(RuleBasedTagger::new()), 1.0)
        .add_tagger(Box::new(NeuralTagger::new()), 0.5); // Neural tagger stub

    let theorem_name = "functor_category_theory";
    let statement = Term::Const("functor".to_string());
    let aspects = composite.tag(theorem_name, &statement);
    println!("   Theorem: {}", theorem_name);
    println!("   Aspects (composite): {:?}", aspects);
    println!();

    // Example 7: Predicate logic with quantifiers
    println!("7. Predicate Logic:");
    let theorem_name = "forall_elim";
    let statement = Term::App {
        func: Box::new(Term::Const("forall".to_string())),
        args: vec![Term::Var("P".to_string())],
    };

    let features = tagger.extract_features(&statement);
    let aspects = tagger.tag(theorem_name, &statement);
    println!("   Theorem: {}", theorem_name);
    println!("   Quantifier count: {}", features.quantifier_count);
    println!("   Aspects: {:?}", aspects);
    println!();

    // Example 8: Induction principle
    println!("8. Induction:");
    let theorem_name = "nat_induction_principle";
    let statement = Term::Const("induction".to_string());
    let aspects = tagger.tag(theorem_name, &statement);
    println!("   Theorem: {}", theorem_name);
    println!("   Aspects: {:?}", aspects);
    println!();

    // Example 9: All aspects enumeration
    println!("9. All Available Aspects:");
    println!("   Total aspects: {}", count_all_aspects());
    println!("   Sample aspects:");
    println!("      - {}", Aspect::PropositionalLogic.name());
    println!("      - {}", Aspect::NaturalNumbers.name());
    println!("      - {}", Aspect::Groups.name());
    println!("      - {}", Aspect::Limits.name());
    println!("      - {}", Aspect::TopologicalSpaces.name());
    println!("      - {}", Aspect::DependentTypes.name());
    println!("      - {}", Aspect::Algorithms.name());
    println!();

    println!("=== Demo Complete ===");
}

fn count_all_aspects() -> usize {
    // Count using exhaustive match
    use Aspect::*;
    vec![
        PropositionalLogic, PredicateLogic, ModalLogic, TemporalLogic,
        HigherOrderLogic, IntuitionisticLogic, ClassicalLogic,
        NaturalNumbers, Integers, Rationals, Reals, Complex, NumberTheory, Arithmetic,
        Groups, Rings, Fields, VectorSpaces, Modules, Lattices, CategoryTheory, UniversalAlgebra,
        Limits, Continuity, Derivatives, Integrals, Sequences, MeasureTheory, FunctionalAnalysis,
        MetricSpaces, TopologicalSpaces, Compactness, Connectedness, TopologicalContinuity,
        SetOperations, Cardinality, Ordinals, AxiomOfChoice, ZFC,
        DependentTypes, Universes, InductiveTypes, CoinductiveTypes, Polymorphism, TypeEquivalence,
        Algorithms, Complexity, FormalVerification, ProgramSemantics, Concurrency,
        Cryptography, Automata, LambdaCalculus,
        Induction, Coinduction, Recursion, CaseAnalysis, Contradiction, DirectProof,
        Combinatorics, GraphTheory, Probability, GameTheory, Geometry, AbstractNonsense,
    ].len()
}
