-- SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
-- SPDX-License-Identifier: MIT AND Palimpsest-0.6
--
-- Propositional.agda - Propositional logic proofs
--
-- This file demonstrates propositional logic in Agda, including De Morgan's laws,
-- double negation, and constructive logic principles.

module Propositional where

--------------------------------------------------------------------------------
-- Basic Logical Connectives
--------------------------------------------------------------------------------

-- Top (true) - the unit type with one constructor
data ⊤ : Set where
  tt : ⊤

-- Bottom (false) - the empty type with no constructors
data ⊥ : Set where

-- Negation is defined as a function to the empty type
¬_ : Set → Set
¬ A = A → ⊥

infix 3 ¬_

-- Conjunction (and) - product type
data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

infixr 4 _∧_
infixr 5 _,_

-- Disjunction (or) - sum type
data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

infixr 3 _∨_

-- Implication is just function type (→)

-- Bi-implication (if and only if)
_⇔_ : Set → Set → Set
A ⇔ B = (A → B) ∧ (B → A)

infix 2 _⇔_

--------------------------------------------------------------------------------
-- Propositional Equality
--------------------------------------------------------------------------------

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

-- Symmetry of equality
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Transitivity of equality
trans-eq : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans-eq refl refl = refl

-- Congruence
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

--------------------------------------------------------------------------------
-- Basic Logic Laws
--------------------------------------------------------------------------------

-- Conjunction is commutative
∧-comm : {A B : Set} → A ∧ B → B ∧ A
∧-comm (a , b) = (b , a)

-- Conjunction is associative
∧-assoc : {A B C : Set} → (A ∧ B) ∧ C → A ∧ (B ∧ C)
∧-assoc ((a , b) , c) = (a , (b , c))

-- Disjunction is commutative
∨-comm : {A B : Set} → A ∨ B → B ∨ A
∨-comm (inl a) = inr a
∨-comm (inr b) = inl b

-- Disjunction is associative
∨-assoc : {A B C : Set} → (A ∨ B) ∨ C → A ∨ (B ∨ C)
∨-assoc (inl (inl a)) = inl a
∨-assoc (inl (inr b)) = inr (inl b)
∨-assoc (inr c) = inr (inr c)

-- Conjunction distributes over disjunction
∧-dist-∨ : {A B C : Set} → A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
∧-dist-∨ (a , inl b) = inl (a , b)
∧-dist-∨ (a , inr c) = inr (a , c)

-- Disjunction distributes over conjunction
∨-dist-∧ : {A B C : Set} → A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C)
∨-dist-∧ (inl a) = (inl a , inl a)
∨-dist-∧ (inr (b , c)) = (inr b , inr c)

--------------------------------------------------------------------------------
-- Projection and Elimination Rules
--------------------------------------------------------------------------------

-- Conjunction projections
∧-proj₁ : {A B : Set} → A ∧ B → A
∧-proj₁ (a , b) = a

∧-proj₂ : {A B : Set} → A ∧ B → B
∧-proj₂ (a , b) = b

-- Disjunction elimination
∨-elim : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
∨-elim f g (inl a) = f a
∨-elim f g (inr b) = g b

-- Ex falso quodlibet: from falsehood, anything follows
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

--------------------------------------------------------------------------------
-- De Morgan's Laws (Constructively Provable)
--------------------------------------------------------------------------------

-- ¬(A ∧ B) → ¬A ∨ ¬B is NOT constructively provable
-- But we can prove: ¬A ∨ ¬B → ¬(A ∧ B)
de-morgan₁ : {A B : Set} → ¬ A ∨ ¬ B → ¬ (A ∧ B)
de-morgan₁ (inl ¬a) (a , b) = ¬a a
de-morgan₁ (inr ¬b) (a , b) = ¬b b

-- ¬(A ∨ B) ⇔ ¬A ∧ ¬B (both directions are constructively provable)
de-morgan₂ : {A B : Set} → ¬ (A ∨ B) → ¬ A ∧ ¬ B
de-morgan₂ ¬a∨b = (λ a → ¬a∨b (inl a)) , (λ b → ¬a∨b (inr b))

de-morgan₂-rev : {A B : Set} → ¬ A ∧ ¬ B → ¬ (A ∨ B)
de-morgan₂-rev (¬a , ¬b) (inl a) = ¬a a
de-morgan₂-rev (¬a , ¬b) (inr b) = ¬b b

-- The full biconditional
de-morgan₂-iff : {A B : Set} → ¬ (A ∨ B) ⇔ (¬ A ∧ ¬ B)
de-morgan₂-iff = de-morgan₂ , de-morgan₂-rev

--------------------------------------------------------------------------------
-- Double Negation
--------------------------------------------------------------------------------

-- Double negation introduction is constructively valid
dni : {A : Set} → A → ¬ ¬ A
dni a ¬a = ¬a a

-- Double negation elimination is NOT constructively provable
-- (it requires classical logic)
-- postulate dne : {A : Set} → ¬ ¬ A → A

-- However, triple negation can be reduced to single negation
¬¬¬-elim : {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬a a = ¬¬¬a (dni a)

-- Contrapositive is constructively valid
contrapositive : {A B : Set} → (A → B) → (¬ B → ¬ A)
contrapositive f ¬b a = ¬b (f a)

--------------------------------------------------------------------------------
-- Constructive Logic Examples
--------------------------------------------------------------------------------

-- Peirce's law is NOT constructively provable
-- postulate peirce : {A B : Set} → ((A → B) → A) → A

-- Law of excluded middle is NOT constructively provable
-- postulate lem : {A : Set} → A ∨ ¬ A

-- However, the double negation of LEM is constructively provable
lem-¬¬ : {A : Set} → ¬ ¬ (A ∨ ¬ A)
lem-¬¬ f = f (inr (λ a → f (inl a)))

-- Weak law of excluded middle: ¬A ∨ ¬¬A
wlem : {A : Set} → ¬ A ∨ ¬ ¬ A
wlem {A} = inr (λ ¬a → ¬a)
-- Note: This is actually provable constructively by always choosing inr

-- The negation of LEM leads to a contradiction in the presence of DNE
lem-necessary-for-dne : {A : Set} → ¬ (A ∨ ¬ A) → ⊥
lem-necessary-for-dne ¬lem = ¬lem (inr (λ a → ¬lem (inl a)))

--------------------------------------------------------------------------------
-- Implication Properties
--------------------------------------------------------------------------------

-- Curry-Howard correspondence examples

-- A → B → A (first projection as implication)
impl-fst : {A B : Set} → A → B → A
impl-fst a b = a

-- (A → B → C) → (A → B) → A → C (S combinator)
impl-S : {A B C : Set} → (A → B → C) → (A → B) → A → C
impl-S f g a = f a (g a)

-- Modus tollens
modus-tollens : {A B : Set} → (A → B) → ¬ B → ¬ A
modus-tollens = contrapositive

-- Hypothetical syllogism (transitivity of implication)
hyp-syll : {A B C : Set} → (A → B) → (B → C) → (A → C)
hyp-syll f g a = g (f a)

--------------------------------------------------------------------------------
-- Decidability
--------------------------------------------------------------------------------

-- A proposition is decidable if we can prove it or its negation
data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : ¬ A → Dec A

-- Decidability is preserved under negation
¬-dec : {A : Set} → Dec A → Dec (¬ A)
¬-dec (yes a) = no (λ ¬a → ¬a a)
¬-dec (no ¬a) = yes ¬a

-- Decidability of conjunction
∧-dec : {A B : Set} → Dec A → Dec B → Dec (A ∧ B)
∧-dec (yes a) (yes b) = yes (a , b)
∧-dec (yes a) (no ¬b) = no (λ { (a , b) → ¬b b })
∧-dec (no ¬a) _       = no (λ { (a , b) → ¬a a })

-- Decidability of disjunction
∨-dec : {A B : Set} → Dec A → Dec B → Dec (A ∨ B)
∨-dec (yes a) _       = yes (inl a)
∨-dec (no ¬a) (yes b) = yes (inr b)
∨-dec (no ¬a) (no ¬b) = no (λ { (inl a) → ¬a a ; (inr b) → ¬b b })

--------------------------------------------------------------------------------
-- Stability
--------------------------------------------------------------------------------

-- A proposition is stable if double negation elimination holds for it
Stable : Set → Set
Stable A = ¬ ¬ A → A

-- Negation is always stable
¬-stable : {A : Set} → Stable (¬ A)
¬-stable = ¬¬¬-elim

-- Decidable propositions are stable
dec-stable : {A : Set} → Dec A → Stable A
dec-stable (yes a) ¬¬a = a
dec-stable (no ¬a) ¬¬a = ⊥-elim (¬¬a ¬a)

--------------------------------------------------------------------------------
-- Classical axioms and their relationships
--------------------------------------------------------------------------------

module ClassicalRelationships where
  -- Law of excluded middle
  LEM : Set₁
  LEM = {A : Set} → A ∨ ¬ A

  -- Double negation elimination
  DNE : Set₁
  DNE = {A : Set} → ¬ ¬ A → A

  -- Peirce's law
  Peirce : Set₁
  Peirce = {A B : Set} → ((A → B) → A) → A

  -- These are all equivalent in constructive logic + any one of them

  -- LEM implies DNE
  lem→dne : LEM → DNE
  lem→dne lem {A} ¬¬a with lem {A}
  ... | inl a  = a
  ... | inr ¬a = ⊥-elim (¬¬a ¬a)

  -- DNE implies Peirce
  dne→peirce : DNE → Peirce
  dne→peirce dne {A} {B} f = dne (λ ¬a → ¬a (f (λ a → ⊥-elim (¬a a))))

  -- Peirce implies LEM
  peirce→lem : Peirce → LEM
  peirce→lem peirce {A} = peirce (λ f → inr (λ a → f (inl a)))
