<!--
SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
SPDX-License-Identifier: MIT
-->

# ECHIDNA Lean 4 Proof Examples

This directory contains comprehensive Lean 4 proof examples demonstrating progressive complexity for the ECHIDNA neurosymbolic theorem proving platform.

## Files

### 1. Basic.lean
Foundation-level proofs covering:
- Identity proofs (A → A)
- Modus ponens ((A → B) → A → B)
- Transitivity ((A → B) → (B → C) → (A → C))
- Conjunction (AND) properties
- Disjunction (OR) properties
- Implication chains
- Distribution laws
- Curry-Howard correspondence examples

**Complexity**: Beginner
**Lines**: ~350
**Key Tactics**: `intro`, `exact`, `apply`, `constructor`, `cases`, `left`, `right`

### 2. Propositional.lean
Propositional logic theorems:
- De Morgan's laws (both directions)
- Double negation introduction/elimination
- Classical logic principles (excluded middle, Peirce's law)
- Contrapositive reasoning
- Proof by contradiction
- Material implication
- Currying/uncurrying
- Ex falso quodlibet
- Distributivity laws
- Logical equivalence properties

**Complexity**: Intermediate
**Lines**: ~450
**Key Tactics**: `by_cases`, `exfalso`, `intro`, `cases`, `constructor`

### 3. Nat.lean
Natural number proofs:
- Basic arithmetic (addition, multiplication identities)
- Commutativity and associativity
- Distributivity
- Induction examples
- Comparison and ordering
- Cancellation laws
- Subtraction properties
- Number theory (even/odd definitions)
- Division and modulo properties
- GCD properties

**Complexity**: Intermediate-Advanced
**Lines**: ~500
**Key Tactics**: `induction`, `rw`, `rfl`, `omega`, `ring`, `simp`

### 4. List.lean
List data structure proofs:
- Append properties (identity, associativity)
- Length theorems
- Reverse properties (involutive, length preservation)
- Map properties (length preservation, composition, identity)
- Filter properties
- Fold (left/right) properties
- Sum and product
- Membership properties
- Take/drop operations
- Zip properties
- All/any predicates
- Replicate properties

**Complexity**: Advanced
**Lines**: ~550
**Key Tactics**: `induction`, `simp`, `rw`, `cases`, `omega`, `generalizing`

## Usage

### Type-Checking

To verify these proofs with Lean 4:

```bash
# Install Lean 4 (if not already installed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Navigate to this directory
cd /home/user/echidna/proofs/lean

# Initialize Lake project (if needed)
lake init

# Build and type-check all proofs
lake build
```

### Running Individual Files

```bash
# Check a specific file
lean Basic.lean
lean Propositional.lean
lean Nat.lean
lean List.lean
```

### Interactive Mode

Open any `.lean` file in VS Code with the Lean 4 extension installed for interactive theorem proving with inline feedback.

## Integration with ECHIDNA

These proof files serve multiple purposes in the ECHIDNA system:

1. **Test Cases**: Verify that the Lean backend integration correctly handles various proof patterns
2. **Benchmarks**: Measure performance across different complexity levels
3. **Examples**: Demonstrate proof techniques to users
4. **Regression Tests**: Ensure system updates don't break existing functionality

### Aspect Tagging

Each file corresponds to different proof aspects:
- **Basic.lean**: `logic.foundation`, `proof.intro`, `curry-howard`
- **Propositional.lean**: `logic.classical`, `proof.contradiction`, `logic.equivalence`
- **Nat.lean**: `arithmetic.basic`, `induction.nat`, `number-theory.elementary`
- **List.lean**: `data-structures.list`, `functional.map-fold`, `induction.structural`

## Lean 4 Features Used

### Syntax
- Pattern matching with `cases`
- Structured tactic proofs with `by`
- Anonymous constructor (`⟨⟩` notation)
- Function composition (`∘`)
- Unicode symbols (`→`, `∧`, `∨`, `¬`, `∀`, `∃`)

### Tactics
- **intro**: Introduce hypotheses
- **exact**: Provide exact proof term
- **apply**: Apply function/theorem
- **rw/rewrite**: Rewrite using equality
- **rfl**: Reflexivity of equality
- **cases**: Case analysis
- **induction**: Structural induction
- **simp**: Simplification
- **omega**: Linear arithmetic solver
- **ring**: Ring normalization
- **by_cases**: Classical case split
- **constructor**: Build inductive types
- **left/right**: Disjunction introduction
- **exfalso**: Proof from False

### Standard Library
- `Nat`: Natural numbers
- `List`: Polymorphic lists
- `Prop`: Propositions
- `Bool`: Boolean values

## Verification Status

- [x] Basic.lean - Type-checks with Lean 4.13.0
- [x] Propositional.lean - Type-checks with Lean 4.13.0
- [x] Nat.lean - Type-checks with Lean 4.13.0 (1 `sorry` for advanced theorem)
- [x] List.lean - Type-checks with Lean 4.13.0

## Dependencies

- **Lean 4**: v4.13.0 or later
- **Lake**: Lean 4 build system
- **Mathlib** (optional): For advanced theorems

## License

Dual-licensed under:
- MIT License
- Palimpsest License v0.6

## Contributing

When adding new proofs:
1. Follow existing naming conventions
2. Include clear doc comments (`/-- ... -/`)
3. Use standard tactics where possible
4. Ensure proofs type-check before committing
5. Update this README with new content

## References

- [Lean 4 Documentation](https://lean-lang.org/documentation/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Lean 4 Mathlib](https://github.com/leanprover-community/mathlib4)
- [ECHIDNA Project](https://gitlab.com/non-initiate/rhodinised/quill)

---

**Last Updated**: 2025-11-22
**Lean Version**: 4.13.0
**Status**: Production Ready
