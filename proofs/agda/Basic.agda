-- SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
-- SPDX-License-Identifier: MIT AND Palimpsest-0.6
--
-- Basic.agda - Simple proofs demonstrating fundamental logical principles
--
-- This file contains basic proofs for ECHIDNA's Agda backend integration testing.
-- It demonstrates identity, modus ponens, and transitivity using proof by construction.

module Basic where

--------------------------------------------------------------------------------
-- Identity Proof
--------------------------------------------------------------------------------

-- The identity function: any proposition implies itself
-- Type: A → A
-- This is the simplest proof, returning exactly what we receive
id : {A : Set} → A → A
id x = x

-- Example: identity for a specific type
id-nat : (n : ℕ) → ℕ
id-nat = id
  where
    data ℕ : Set where
      zero : ℕ
      suc  : ℕ → ℕ

-- The identity function can also be written explicitly with a lambda
id′ : {A : Set} → A → A
id′ = λ x → x

--------------------------------------------------------------------------------
-- Modus Ponens
--------------------------------------------------------------------------------

-- Modus ponens: if we have A → B and we have A, then we can derive B
-- This is function application
modus-ponens : {A B : Set} → (A → B) → A → B
modus-ponens f x = f x

-- Alternative notation emphasizing the logical interpretation
mp : {A B : Set} → (A → B) → A → B
mp f a = f a

-- Example: applying modus ponens with concrete propositions
module ModusPonensExample where
  -- Define simple propositions
  data ⊤ : Set where
    tt : ⊤

  data ⊥ : Set where

  -- Example: if ⊤ → ⊤ and we have ⊤, we get ⊤
  example-mp : ⊤
  example-mp = mp id tt

--------------------------------------------------------------------------------
-- Transitivity
--------------------------------------------------------------------------------

-- Transitivity: if A → B and B → C, then A → C
-- This is function composition
trans : {A B C : Set} → (A → B) → (B → C) → (A → C)
trans f g x = g (f x)

-- Alternative notation using composition operator
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

infixr 9 _∘_

-- Proof that transitivity is associative
trans-assoc : {A B C D : Set}
            → (f : A → B) → (g : B → C) → (h : C → D)
            → (h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f)
trans-assoc f g h = refl
  where
    -- Propositional equality
    data _≡_ {A : Set} (x : A) : A → Set where
      refl : x ≡ x

    infix 4 _≡_

-- Proof that identity is a left identity for composition
id-left : {A B : Set} → (f : A → B) → (id ∘ f) ≡ f
id-left f = refl
  where
    data _≡_ {A : Set} (x : A) : A → Set where
      refl : x ≡ x
    infix 4 _≡_

-- Proof that identity is a right identity for composition
id-right : {A B : Set} → (f : A → B) → (f ∘ id) ≡ f
id-right f = refl
  where
    data _≡_ {A : Set} (x : A) : A → Set where
      refl : x ≡ x
    infix 4 _≡_

--------------------------------------------------------------------------------
-- Additional Basic Combinators
--------------------------------------------------------------------------------

-- The K combinator: constant function
const : {A B : Set} → A → B → A
const x y = x

-- The S combinator: application combinator
S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S f g x = f x (g x)

-- Flip: swaps the order of arguments
flip : {A B C : Set} → (A → B → C) → (B → A → C)
flip f y x = f x y

-- Function application operator (useful for reducing parentheses)
_$_ : {A B : Set} → (A → B) → A → B
f $ x = f x

infixr 0 _$_

--------------------------------------------------------------------------------
-- Proof that basic combinators satisfy certain properties
--------------------------------------------------------------------------------

module CombinatorLaws where
  data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

  infix 4 _≡_

  -- SKK = I (a famous combinator identity)
  SKK : {A : Set} → (x : A) → S const const x ≡ id x
  SKK x = refl

  -- Flip is involutive (applying it twice gets you back where you started)
  flip-involutive : {A B C : Set} → (f : A → B → C)
                  → (x : A) → (y : B)
                  → flip (flip f) x y ≡ f x y
  flip-involutive f x y = refl

--------------------------------------------------------------------------------
-- Curry and Uncurry
--------------------------------------------------------------------------------

-- Product type (pairs)
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

infixr 4 _×_
infixr 5 _,_

-- Curry: convert a function on pairs to a curried function
curry : {A B C : Set} → (A × B → C) → (A → B → C)
curry f x y = f (x , y)

-- Uncurry: convert a curried function to a function on pairs
uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
uncurry f (x , y) = f x y

-- Proof that curry and uncurry are inverses
module CurryUncurryLaws where
  data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

  postulate
    funext : {A B : Set} {f g : A → B}
           → ((x : A) → f x ≡ g x)
           → f ≡ g

  curry-uncurry : {A B C : Set} → (f : A → B → C)
                → curry (uncurry f) ≡ f
  curry-uncurry f = funext λ x → funext λ y → refl

  uncurry-curry : {A B C : Set} → (f : A × B → C)
                → uncurry (curry f) ≡ f
  uncurry-curry f = funext λ { (x , y) → refl }
