-- SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
-- SPDX-License-Identifier: MIT AND Palimpsest-0.6
--
-- Nat.agda - Natural number proofs and arithmetic properties
--
-- This file demonstrates natural number definitions and proofs using induction,
-- including basic arithmetic properties and theorems.

module Nat where

--------------------------------------------------------------------------------
-- Natural Numbers Definition
--------------------------------------------------------------------------------

-- Natural numbers defined inductively
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Pattern synonyms for readability
pattern 1+ n = suc n

--------------------------------------------------------------------------------
-- Propositional Equality
--------------------------------------------------------------------------------

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

-- Symmetry
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Transitivity
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- Congruence
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

-- Substitution
subst : {A : Set} {x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

--------------------------------------------------------------------------------
-- Addition
--------------------------------------------------------------------------------

-- Addition defined by recursion on the first argument
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

infixl 6 _+_

-- Addition is commutative with zero on the right
+-zero : (n : ℕ) → n + zero ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)

-- Addition with successor on the right
+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

-- Addition is commutative
+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero    n = sym (+-zero n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

-- Addition is associative
+-assoc : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero    n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

-- Zero is a left identity
+-identityˡ : (n : ℕ) → zero + n ≡ n
+-identityˡ n = refl

-- Zero is a right identity
+-identityʳ : (n : ℕ) → n + zero ≡ n
+-identityʳ = +-zero

--------------------------------------------------------------------------------
-- Multiplication
--------------------------------------------------------------------------------

-- Multiplication defined by recursion
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

infixl 7 _*_

-- Multiplication by zero
*-zero : (n : ℕ) → n * zero ≡ zero
*-zero zero    = refl
*-zero (suc n) = *-zero n

-- Multiplication by one (right)
*-one : (n : ℕ) → n * 1 ≡ n
*-one zero    = refl
*-one (suc n) = cong suc (*-one n)

-- Distributive property: m * (n + p) ≡ m * n + m * p
*-distribˡ-+ : (m n p : ℕ) → m * (n + p) ≡ m * n + m * p
*-distribˡ-+ zero    n p = refl
*-distribˡ-+ (suc m) n p =
  begin
    (n + p) + m * (n + p)
  ≡⟨ cong ((n + p) +_) (*-distribˡ-+ m n p) ⟩
    (n + p) + (m * n + m * p)
  ≡⟨ sym (+-assoc (n + p) (m * n) (m * p)) ⟩
    ((n + p) + m * n) + m * p
  ≡⟨ cong (_+ m * p) (+-assoc n p (m * n)) ⟩
    (n + (p + m * n)) + m * p
  ≡⟨ cong (λ x → (n + x) + m * p) (+-comm p (m * n)) ⟩
    (n + (m * n + p)) + m * p
  ≡⟨ cong (_+ m * p) (sym (+-assoc n (m * n) p)) ⟩
    ((n + m * n) + p) + m * p
  ≡⟨ +-assoc (n + m * n) p (m * p) ⟩
    (n + m * n) + (p + m * p)
  ∎
  where
    begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
    begin p = p

    _≡⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
    x ≡⟨ p ⟩ q = trans p q

    _∎ : {A : Set} → (x : A) → x ≡ x
    x ∎ = refl

    infix  1 begin_
    infixr 2 _≡⟨_⟩_
    infix  3 _∎

-- Multiplication with successor
*-suc : (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero    n = refl
*-suc (suc m) n =
  cong suc (trans (+-suc n (m * suc n))
                  (trans (cong (suc n +_) (*-suc m n))
                         (sym (+-assoc (suc n) m (m * n)))))

-- Multiplication is commutative
*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm zero    n = sym (*-zero n)
*-comm (suc m) n = trans (cong (n +_) (*-comm m n)) (sym (*-suc n m))

-- Multiplication is associative
*-assoc : (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero    n p = refl
*-assoc (suc m) n p =
  trans (*-distribˡ-+ p n (m * n))
        (cong (p * n +_) (*-assoc m n p))

-- One is a left identity for multiplication
*-identityˡ : (n : ℕ) → 1 * n ≡ n
*-identityˡ n = +-zero n

-- One is a right identity for multiplication
*-identityʳ : (n : ℕ) → n * 1 ≡ n
*-identityʳ = *-one

--------------------------------------------------------------------------------
-- Ordering
--------------------------------------------------------------------------------

-- Less than or equal to
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

-- Reflexivity of ≤
≤-refl : (n : ℕ) → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

-- Transitivity of ≤
≤-trans : {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

-- Antisymmetry of ≤
≤-antisym : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n       z≤n       = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- Zero is the minimum
≤-zero : (n : ℕ) → zero ≤ n
≤-zero n = z≤n

-- n ≤ suc n
≤-step : {n : ℕ} → n ≤ suc n
≤-step {zero}  = z≤n
≤-step {suc n} = s≤s ≤-step

-- Addition preserves ≤
+-mono-≤ : {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ z≤n       p≤q = p≤q
+-mono-≤ (s≤s m≤n) p≤q = s≤s (+-mono-≤ m≤n p≤q)

-- Multiplication preserves ≤
*-mono-≤ : {m n p : ℕ} → m ≤ n → m * p ≤ n * p
*-mono-≤ {p = p} z≤n = z≤n
*-mono-≤ {p = p} (s≤s m≤n) = +-mono-≤ (≤-refl p) (*-mono-≤ m≤n)

--------------------------------------------------------------------------------
-- Subtraction (monus)
--------------------------------------------------------------------------------

-- Truncated subtraction (monus): m ∸ n = max(0, m - n)
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

infixl 6 _∸_

-- Properties of monus
∸-zero : (n : ℕ) → n ∸ zero ≡ n
∸-zero n = refl

zero-∸ : (n : ℕ) → zero ∸ n ≡ zero
zero-∸ zero    = refl
zero-∸ (suc n) = refl

-- m ∸ m ≡ 0
∸-self : (n : ℕ) → n ∸ n ≡ zero
∸-self zero    = refl
∸-self (suc n) = ∸-self n

-- (m + n) ∸ n ≡ m
+-∸-assoc : (m n : ℕ) → (m + n) ∸ n ≡ m
+-∸-assoc m zero    = +-zero m
+-∸-assoc m (suc n) = trans (cong (_∸ suc n) (+-suc m n)) (+-∸-assoc m n)

--------------------------------------------------------------------------------
-- Maximum and Minimum
--------------------------------------------------------------------------------

-- Maximum of two numbers
max : ℕ → ℕ → ℕ
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)

-- Minimum of two numbers
min : ℕ → ℕ → ℕ
min zero    n       = zero
min (suc m) zero    = zero
min (suc m) (suc n) = suc (min m n)

-- max is commutative
max-comm : (m n : ℕ) → max m n ≡ max n m
max-comm zero    zero    = refl
max-comm zero    (suc n) = refl
max-comm (suc m) zero    = refl
max-comm (suc m) (suc n) = cong suc (max-comm m n)

-- min is commutative
min-comm : (m n : ℕ) → min m n ≡ min n m
min-comm zero    zero    = refl
min-comm zero    (suc n) = refl
min-comm (suc m) zero    = refl
min-comm (suc m) (suc n) = cong suc (min-comm m n)

--------------------------------------------------------------------------------
-- Division by 2 (for demonstrating well-founded recursion)
--------------------------------------------------------------------------------

-- Half of a number (rounded down)
half : ℕ → ℕ
half zero          = zero
half (suc zero)    = zero
half (suc (suc n)) = suc (half n)

-- Double of a number
double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

-- double (half n) ≤ n
double-half-≤ : (n : ℕ) → double (half n) ≤ n
double-half-≤ zero              = z≤n
double-half-≤ (suc zero)        = s≤s z≤n
double-half-≤ (suc (suc n))     = s≤s (s≤s (double-half-≤ n))

--------------------------------------------------------------------------------
-- Even and Odd
--------------------------------------------------------------------------------

-- Even numbers
data Even : ℕ → Set where
  even-zero : Even zero
  even-suc  : {n : ℕ} → Even n → Even (suc (suc n))

-- Odd numbers
data Odd : ℕ → Set where
  odd-one : Odd (suc zero)
  odd-suc : {n : ℕ} → Odd n → Odd (suc (suc n))

-- Every number is even or odd
even-or-odd : (n : ℕ) → Even n ⊎ Odd n
even-or-odd zero              = inj₁ even-zero
even-or-odd (suc zero)        = inj₂ odd-one
even-or-odd (suc (suc n))     with even-or-odd n
... | inj₁ even-n = inj₁ (even-suc even-n)
... | inj₂ odd-n  = inj₂ (odd-suc odd-n)
  where
    data _⊎_ (A B : Set) : Set where
      inj₁ : A → A ⊎ B
      inj₂ : B → A ⊎ B

-- Sum of two even numbers is even
even-+ : {m n : ℕ} → Even m → Even n → Even (m + n)
even-+ even-zero     en = en
even-+ (even-suc em) en = even-suc (even-+ em en)

-- Product of two even numbers is even
even-* : {m n : ℕ} → Even m → Even n → Even (m * n)
even-* even-zero     _  = even-zero
even-* (even-suc em) en = even-+ en (even-+ en (even-* em en))

--------------------------------------------------------------------------------
-- Exponentiation
--------------------------------------------------------------------------------

-- Exponentiation: m ^ n
_^_ : ℕ → ℕ → ℕ
m ^ zero  = 1
m ^ suc n = m * (m ^ n)

infixr 8 _^_

-- Any number to the power of 0 is 1
^-zero : (n : ℕ) → n ^ 0 ≡ 1
^-zero n = refl

-- 1 to any power is 1
1-^ : (n : ℕ) → 1 ^ n ≡ 1
1-^ zero    = refl
1-^ (suc n) = 1-^ n

-- Exponentiation distributes over multiplication
^-distribˡ-* : (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-* m zero    p = sym (+-zero (m ^ p))
^-distribˡ-* m (suc n) p =
  trans (cong (m *_) (^-distribˡ-* m n p))
        (sym (*-assoc m (m ^ n) (m ^ p)))
