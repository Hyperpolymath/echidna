/-
SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
SPDX-License-Identifier: MIT

Basic Lean 4 Proofs - Foundation Level

This file demonstrates fundamental proof patterns in Lean 4:
- Identity proofs
- Modus ponens
- Transitivity
- Basic implication reasoning

These serve as test cases for ECHIDNA's Lean backend integration.
-/

namespace ECHIDNA.Basic

/-! ## Identity Proofs -/

/--
Identity: For any proposition A, A implies A.
This is the most basic proof in logic.
-/
theorem identity (A : Prop) : A → A := by
  intro h
  exact h

/-- Alternative proof using function syntax -/
theorem identity' (A : Prop) : A → A :=
  fun h => h

/-- Identity for types (not just propositions) -/
theorem identity_type {α : Type} (x : α) : x = x := by
  rfl


/-! ## Modus Ponens -/

/--
Modus Ponens: If we have A → B and A, then we can derive B.
This is the fundamental rule of implication elimination.
-/
theorem modus_ponens (A B : Prop) : (A → B) → A → B := by
  intro hab ha
  apply hab
  exact ha

/-- Shorter proof using direct application -/
theorem modus_ponens' (A B : Prop) : (A → B) → A → B :=
  fun hab ha => hab ha


/-! ## Transitivity -/

/--
Transitivity: If A implies B and B implies C, then A implies C.
Chain of implications.
-/
theorem transitivity (A B C : Prop) : (A → B) → (B → C) → (A → C) := by
  intro hab hbc ha
  apply hbc
  apply hab
  exact ha

/-- More concise proof -/
theorem transitivity' (A B C : Prop) : (A → B) → (B → C) → (A → C) :=
  fun hab hbc ha => hbc (hab ha)


/-! ## Conjunction (AND) -/

/--
Conjunction introduction: If we have A and B separately, we can combine them.
-/
theorem and_intro (A B : Prop) : A → B → (A ∧ B) := by
  intro ha hb
  constructor
  · exact ha
  · exact hb

/--
Conjunction elimination (left): From A ∧ B, we can get A.
-/
theorem and_elim_left (A B : Prop) : (A ∧ B) → A := by
  intro hab
  cases hab with
  | intro ha _ => exact ha

/--
Conjunction elimination (right): From A ∧ B, we can get B.
-/
theorem and_elim_right (A B : Prop) : (A ∧ B) → B := by
  intro hab
  cases hab with
  | intro _ hb => exact hb

/--
Conjunction is commutative.
-/
theorem and_comm (A B : Prop) : (A ∧ B) → (B ∧ A) := by
  intro hab
  cases hab with
  | intro ha hb =>
    constructor
    · exact hb
    · exact ha


/-! ## Disjunction (OR) -/

/--
Disjunction introduction (left): From A, we can get A ∨ B.
-/
theorem or_intro_left (A B : Prop) : A → (A ∨ B) := by
  intro ha
  left
  exact ha

/--
Disjunction introduction (right): From B, we can get A ∨ B.
-/
theorem or_intro_right (A B : Prop) : B → (A ∨ B) := by
  intro hb
  right
  exact hb

/--
Disjunction is commutative.
-/
theorem or_comm (A B : Prop) : (A ∨ B) → (B ∨ A) := by
  intro hab
  cases hab with
  | inl ha =>
    right
    exact ha
  | inr hb =>
    left
    exact hb


/-! ## Implication Chains -/

/--
Hypothetical syllogism: Another form of transitivity.
-/
theorem hypothetical_syllogism (A B C : Prop) :
  (A → B) → (B → C) → (A → C) := by
  intro hab hbc ha
  exact hbc (hab ha)

/--
Composition of three implications.
-/
theorem triple_transitivity (A B C D : Prop) :
  (A → B) → (B → C) → (C → D) → (A → D) := by
  intro hab hbc hcd ha
  apply hcd
  apply hbc
  apply hab
  exact ha


/-! ## Distribution Laws -/

/--
Conjunction distributes over disjunction (left).
-/
theorem and_or_distrib_left (A B C : Prop) :
  A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
  intro h
  cases h with
  | intro ha hbc =>
    cases hbc with
    | inl hb =>
      left
      constructor
      · exact ha
      · exact hb
    | inr hc =>
      right
      constructor
      · exact ha
      · exact hc

/--
Conjunction distributes over disjunction (right).
-/
theorem and_or_distrib_right (A B C : Prop) :
  (A ∨ B) ∧ C → (A ∧ C) ∨ (B ∧ C) := by
  intro h
  cases h with
  | intro hab hc =>
    cases hab with
    | inl ha =>
      left
      constructor <;> assumption
    | inr hb =>
      right
      constructor <;> assumption


/-! ## Curry-Howard Correspondence Examples -/

/--
The identity function corresponds to the identity proof.
-/
def id_function {α : Type} : α → α :=
  fun x => x

/--
Function composition corresponds to transitivity.
-/
def compose {α β γ : Type} (f : β → γ) (g : α → β) : α → γ :=
  fun x => f (g x)

/--
Proof that composition is associative.
-/
theorem compose_assoc {α β γ δ : Type}
  (f : γ → δ) (g : β → γ) (h : α → β) :
  compose f (compose g h) = compose (compose f g) h := by
  rfl


end ECHIDNA.Basic
