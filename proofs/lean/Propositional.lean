/-
SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
SPDX-License-Identifier: MIT

Propositional Logic Proofs in Lean 4

This file demonstrates propositional logic theorems:
- De Morgan's laws
- Double negation
- Classical logic principles
- Contrapositive reasoning
- Proof by contradiction

These serve as test cases for ECHIDNA's Lean backend integration.
-/

namespace ECHIDNA.Propositional

/-! ## De Morgan's Laws -/

/--
De Morgan's First Law: ¬(A ∧ B) → (¬A ∨ ¬B)
The negation of a conjunction implies the disjunction of negations.
Note: This direction requires classical logic (excluded middle).
-/
theorem de_morgan_1 (A B : Prop) : ¬(A ∧ B) → (¬A ∨ ¬B) := by
  intro h
  by_cases ha : A
  · right
    intro hb
    apply h
    constructor <;> assumption
  · left
    exact ha

/--
De Morgan's First Law (reverse): (¬A ∨ ¬B) → ¬(A ∧ B)
This direction is constructively valid.
-/
theorem de_morgan_1_rev (A B : Prop) : (¬A ∨ ¬B) → ¬(A ∧ B) := by
  intro h hab
  cases h with
  | inl hna =>
    cases hab with
    | intro ha _ => exact hna ha
  | inr hnb =>
    cases hab with
    | intro _ hb => exact hnb hb

/--
De Morgan's Second Law: ¬(A ∨ B) → (¬A ∧ ¬B)
The negation of a disjunction implies the conjunction of negations.
This is constructively valid.
-/
theorem de_morgan_2 (A B : Prop) : ¬(A ∨ B) → (¬A ∧ ¬B) := by
  intro h
  constructor
  · intro ha
    apply h
    left
    exact ha
  · intro hb
    apply h
    right
    exact hb

/--
De Morgan's Second Law (reverse): (¬A ∧ ¬B) → ¬(A ∨ B)
This is also constructively valid.
-/
theorem de_morgan_2_rev (A B : Prop) : (¬A ∧ ¬B) → ¬(A ∨ B) := by
  intro h hab
  cases hab with
  | inl ha => exact h.left ha
  | inr hb => exact h.right hb


/-! ## Double Negation -/

/--
Double negation introduction: A → ¬¬A
This is constructively valid - we can always add double negation.
-/
theorem double_neg_intro (A : Prop) : A → ¬¬A := by
  intro ha hna
  exact hna ha

/--
Double negation elimination: ¬¬A → A
This requires classical logic (excluded middle).
-/
theorem double_neg_elim (A : Prop) : ¬¬A → A := by
  intro hnna
  by_cases h : A
  · exact h
  · exfalso
    exact hnna h

/--
Triple negation: ¬¬¬A → ¬A
This is constructively valid.
-/
theorem triple_neg (A : Prop) : ¬¬¬A → ¬A := by
  intro hnnna ha
  apply hnnna
  intro hna
  exact hna ha


/-! ## Classical Logic Principles -/

/--
Law of Excluded Middle: For any proposition A, either A or ¬A holds.
This is an axiom in classical logic.
-/
theorem excluded_middle (A : Prop) : A ∨ ¬A := by
  by_cases h : A
  · left; exact h
  · right; exact h

/--
Peirce's Law: ((A → B) → A) → A
This is equivalent to the law of excluded middle.
-/
theorem peirce (A B : Prop) : ((A → B) → A) → A := by
  intro h
  by_cases ha : A
  · exact ha
  · apply h
    intro ha
    exfalso
    exact ha ha

/--
Double negation of excluded middle is constructively provable.
-/
theorem double_neg_excluded_middle (A : Prop) : ¬¬(A ∨ ¬A) := by
  intro h
  apply h
  right
  intro ha
  apply h
  left
  exact ha


/-! ## Contrapositive and Contradiction -/

/--
Contrapositive: (A → B) → (¬B → ¬A)
This is constructively valid.
-/
theorem contrapositive (A B : Prop) : (A → B) → (¬B → ¬A) := by
  intro hab hnb ha
  apply hnb
  exact hab ha

/--
Contrapositive reverse: (¬B → ¬A) → (A → B)
This requires classical logic.
-/
theorem contrapositive_rev (A B : Prop) : (¬B → ¬A) → (A → B) := by
  intro h ha
  by_cases hb : B
  · exact hb
  · exfalso
    exact h hb ha

/--
Proof by contradiction: (¬A → False) → A
This requires classical logic.
-/
theorem proof_by_contradiction (A : Prop) : (¬A → False) → A := by
  intro h
  by_cases ha : A
  · exact ha
  · exfalso
    exact h ha


/-! ## Material Implication -/

/--
Material implication: (A → B) ↔ (¬A ∨ B)
Forward direction (requires classical logic).
-/
theorem material_impl_fwd (A B : Prop) : (A → B) → (¬A ∨ B) := by
  intro hab
  by_cases ha : A
  · right
    exact hab ha
  · left
    exact ha

/--
Material implication: (A → B) ↔ (¬A ∨ B)
Reverse direction (constructively valid).
-/
theorem material_impl_rev (A B : Prop) : (¬A ∨ B) → (A → B) := by
  intro h ha
  cases h with
  | inl hna => exfalso; exact hna ha
  | inr hb => exact hb


/-! ## Implication Properties -/

/--
Implication is transitive (another proof).
-/
theorem impl_trans (A B C : Prop) : (A → B) → (B → C) → (A → C) := by
  intro hab hbc ha
  exact hbc (hab ha)

/--
Currying: (A ∧ B → C) → (A → B → C)
-/
theorem curry (A B C : Prop) : (A ∧ B → C) → (A → B → C) := by
  intro h ha hb
  apply h
  constructor <;> assumption

/--
Uncurrying: (A → B → C) → (A ∧ B → C)
-/
theorem uncurry (A B C : Prop) : (A → B → C) → (A ∧ B → C) := by
  intro h hab
  cases hab with
  | intro ha hb => exact h ha hb


/-! ## Absurdity and Explosion -/

/--
Ex falso quodlibet: From False, anything follows.
Principle of explosion.
-/
theorem ex_falso (A : Prop) : False → A := by
  intro h
  exfalso
  exact h

/--
Negation of True is False.
-/
theorem not_true : ¬True → False := by
  intro h
  exact h trivial

/--
Double negation of False is constructively provable.
-/
theorem not_not_false : ¬¬False → False := by
  intro h
  apply h
  intro hf
  exact hf


/-! ## Distributivity Laws -/

/--
Conjunction distributes over disjunction.
-/
theorem and_distrib_or (A B C : Prop) :
  A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) := by
  constructor
  · intro ⟨ha, hbc⟩
    cases hbc with
    | inl hb => left; exact ⟨ha, hb⟩
    | inr hc => right; exact ⟨ha, hc⟩
  · intro h
    cases h with
    | inl ⟨ha, hb⟩ => exact ⟨ha, Or.inl hb⟩
    | inr ⟨ha, hc⟩ => exact ⟨ha, Or.inr hc⟩

/--
Disjunction distributes over conjunction (requires classical logic).
-/
theorem or_distrib_and (A B C : Prop) :
  A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C) := by
  intro h
  cases h with
  | inl ha =>
    constructor
    · left; exact ha
    · left; exact ha
  | inr ⟨hb, hc⟩ =>
    constructor
    · right; exact hb
    · right; exact hc


/-! ## Logical Equivalence -/

/--
Reflexivity of equivalence.
-/
theorem iff_refl (A : Prop) : A ↔ A := by
  constructor <;> intro h <;> exact h

/--
Symmetry of equivalence.
-/
theorem iff_symm (A B : Prop) : (A ↔ B) → (B ↔ A) := by
  intro ⟨hab, hba⟩
  exact ⟨hba, hab⟩

/--
Transitivity of equivalence.
-/
theorem iff_trans (A B C : Prop) : (A ↔ B) → (B ↔ C) → (A ↔ C) := by
  intro ⟨hab, hba⟩ ⟨hbc, hcb⟩
  constructor
  · intro ha; exact hbc (hab ha)
  · intro hc; exact hba (hcb hc)


end ECHIDNA.Propositional
