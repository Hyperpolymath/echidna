-- SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
-- SPDX-License-Identifier: MIT AND Palimpsest-0.6
--
-- List.agda - List data structure proofs
--
-- This file demonstrates list operations and their properties,
-- including append, length, map, filter, and fold operations.

module List where

--------------------------------------------------------------------------------
-- Natural Numbers (for length)
--------------------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

infixl 6 _+_

--------------------------------------------------------------------------------
-- Propositional Equality
--------------------------------------------------------------------------------

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} {x₁ x₂ : A} {y₁ y₂ : B}
      → (f : A → B → C)
      → x₁ ≡ x₂
      → y₁ ≡ y₂
      → f x₁ y₁ ≡ f x₂ y₂
cong₂ f refl refl = refl

--------------------------------------------------------------------------------
-- List Definition
--------------------------------------------------------------------------------

-- Polymorphic list type
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

-- Pattern synonym for single element list
pattern [_] x = x ∷ []

-- Pattern for two element list
pattern [_,_] x y = x ∷ y ∷ []

-- Pattern for three element list
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []

--------------------------------------------------------------------------------
-- Basic List Operations
--------------------------------------------------------------------------------

-- Append (concatenation)
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

-- Length
length : {A : Set} → List A → ℕ
length []       = 0
length (x ∷ xs) = suc (length xs)

-- Map
map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- Filter
filter : {A : Set} → (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false = filter p xs
  where
    data Bool : Set where
      true  : Bool
      false : Bool

-- Reverse (naive, O(n²))
reverse : {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

-- Reverse with accumulator (O(n))
rev-acc : {A : Set} → List A → List A → List A
rev-acc acc []       = acc
rev-acc acc (x ∷ xs) = rev-acc (x ∷ acc) xs

reverse′ : {A : Set} → List A → List A
reverse′ xs = rev-acc [] xs

-- Head (with default)
head : {A : Set} → A → List A → A
head default []      = default
head default (x ∷ _) = x

-- Tail
tail : {A : Set} → List A → List A
tail []       = []
tail (_ ∷ xs) = xs

-- Take first n elements
take : {A : Set} → ℕ → List A → List A
take zero    _        = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

-- Drop first n elements
drop : {A : Set} → ℕ → List A → List A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

--------------------------------------------------------------------------------
-- Fold Operations
--------------------------------------------------------------------------------

-- Fold right
foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr f z []       = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

-- Fold left
foldl : {A B : Set} → (B → A → B) → B → List A → B
foldl f z []       = z
foldl f z (x ∷ xs) = foldl f (f z x) xs

-- Sum (using foldr)
sum : List ℕ → ℕ
sum = foldr _+_ 0

-- Product (using foldr)
product : List ℕ → ℕ
product = foldr _*_ 1
  where
    _*_ : ℕ → ℕ → ℕ
    zero  * n = zero
    suc m * n = n + (m * n)

-- Concatenate list of lists
concat : {A : Set} → List (List A) → List A
concat = foldr _++_ []

--------------------------------------------------------------------------------
-- Append Properties
--------------------------------------------------------------------------------

-- Append with empty list on right is identity
++-identityʳ : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
++-identityʳ []       = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

-- Append with empty list on left is identity
++-identityˡ : {A : Set} → (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

-- Append is associative
++-assoc : {A : Set} → (xs ys zs : List A)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

--------------------------------------------------------------------------------
-- Length Properties
--------------------------------------------------------------------------------

-- Length of append is sum of lengths
length-++ : {A : Set} → (xs ys : List A)
          → length (xs ++ ys) ≡ length xs + length ys
length-++ []       ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

-- Length of reverse equals length of original
length-reverse : {A : Set} → (xs : List A)
               → length (reverse xs) ≡ length xs
length-reverse []       = refl
length-reverse (x ∷ xs) =
  trans (length-++ (reverse xs) [ x ])
        (trans (cong (_+ 1) (length-reverse xs))
               (+-suc (length xs) 0))
  where
    +-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
    +-suc zero    n = refl
    +-suc (suc m) n = cong suc (+-suc m n)

-- Length of map is preserved
length-map : {A B : Set} → (f : A → B) → (xs : List A)
           → length (map f xs) ≡ length xs
length-map f []       = refl
length-map f (x ∷ xs) = cong suc (length-map f xs)

--------------------------------------------------------------------------------
-- Map Properties
--------------------------------------------------------------------------------

-- Map preserves append
map-++ : {A B : Set} → (f : A → B) → (xs ys : List A)
       → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

-- Map composition
map-compose : {A B C : Set} → (f : A → B) → (g : B → C) → (xs : List A)
            → map g (map f xs) ≡ map (λ x → g (f x)) xs
map-compose f g []       = refl
map-compose f g (x ∷ xs) = cong (g (f x) ∷_) (map-compose f g xs)

-- Map with identity is identity
map-id : {A : Set} → (xs : List A) → map (λ x → x) xs ≡ xs
map-id []       = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

--------------------------------------------------------------------------------
-- Reverse Properties
--------------------------------------------------------------------------------

-- Reverse of append
reverse-++ : {A : Set} → (xs ys : List A)
           → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ []       ys = sym (++-identityʳ (reverse ys))
reverse-++ (x ∷ xs) ys =
  trans (cong (_++ [ x ]) (reverse-++ xs ys))
        (++-assoc (reverse ys) (reverse xs) [ x ])

-- Reverse is involutive (reversing twice gives the original)
reverse-involutive : {A : Set} → (xs : List A)
                   → reverse (reverse xs) ≡ xs
reverse-involutive []       = refl
reverse-involutive (x ∷ xs) =
  trans (reverse-++ (reverse xs) [ x ])
        (cong (x ∷_) (reverse-involutive xs))

--------------------------------------------------------------------------------
-- Fold Properties
--------------------------------------------------------------------------------

-- foldr with cons and nil is identity
foldr-id : {A : Set} → (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-id []       = refl
foldr-id (x ∷ xs) = cong (x ∷_) (foldr-id xs)

-- Relationship between foldr and append
foldr-++ : {A B : Set} → (f : A → B → B) → (z : B) → (xs ys : List A)
         → foldr f z (xs ++ ys) ≡ foldr f (foldr f z ys) xs
foldr-++ f z []       ys = refl
foldr-++ f z (x ∷ xs) ys = cong (f x) (foldr-++ f z xs ys)

-- Map can be defined using foldr
map-foldr : {A B : Set} → (f : A → B) → (xs : List A)
          → map f xs ≡ foldr (λ x acc → f x ∷ acc) [] xs
map-foldr f []       = refl
map-foldr f (x ∷ xs) = cong (f x ∷_) (map-foldr f xs)

-- Append can be defined using foldr
++-foldr : {A : Set} → (xs ys : List A)
         → xs ++ ys ≡ foldr _∷_ ys xs
++-foldr []       ys = refl
++-foldr (x ∷ xs) ys = cong (x ∷_) (++-foldr xs ys)

-- Length can be defined using foldr
length-foldr : {A : Set} → (xs : List A)
             → length xs ≡ foldr (λ _ n → suc n) 0 xs
length-foldr []       = refl
length-foldr (x ∷ xs) = cong suc (length-foldr xs)

--------------------------------------------------------------------------------
-- Take and Drop Properties
--------------------------------------------------------------------------------

-- Take and drop partition the list
take-drop : {A : Set} → (n : ℕ) → (xs : List A)
          → take n xs ++ drop n xs ≡ xs
take-drop zero    xs       = refl
take-drop (suc n) []       = refl
take-drop (suc n) (x ∷ xs) = cong (x ∷_) (take-drop n xs)

-- Length of take
length-take : {A : Set} → (n : ℕ) → (xs : List A)
            → length (take n xs) ≤ n
length-take zero    xs       = z≤n
length-take (suc n) []       = z≤n
length-take (suc n) (x ∷ xs) = s≤s (length-take n xs)
  where
    data _≤_ : ℕ → ℕ → Set where
      z≤n : {n : ℕ} → zero ≤ n
      s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

--------------------------------------------------------------------------------
-- All and Any Predicates
--------------------------------------------------------------------------------

-- All elements satisfy a predicate
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

-- At least one element satisfies a predicate
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

-- All is preserved by append
All-++ : {A : Set} {P : A → Set} {xs ys : List A}
       → All P xs → All P ys → All P (xs ++ ys)
All-++ []       pys = pys
All-++ (px ∷ pxs) pys = px ∷ All-++ pxs pys

-- Any distributes over append
Any-++ : {A : Set} {P : A → Set} {xs ys : List A}
       → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
Any-++ {xs = []}     pxsys      = inj₂ pxsys
Any-++ {xs = x ∷ xs} (here px)  = inj₁ (here px)
Any-++ {xs = x ∷ xs} (there pxsys) with Any-++ {xs = xs} pxsys
... | inj₁ pxs = inj₁ (there pxs)
... | inj₂ pys = inj₂ pys
  where
    data _⊎_ (A B : Set) : Set where
      inj₁ : A → A ⊎ B
      inj₂ : B → A ⊎ B

--------------------------------------------------------------------------------
-- Membership
--------------------------------------------------------------------------------

-- Element membership in list
data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

infix 4 _∈_

-- If x ∈ xs and xs ⊆ ys, then x ∈ ys
∈-++-left : {A : Set} {x : A} {xs ys : List A}
          → x ∈ xs → x ∈ (xs ++ ys)
∈-++-left here        = here
∈-++-left (there x∈xs) = there (∈-++-left x∈xs)

∈-++-right : {A : Set} {x : A} {xs ys : List A}
           → x ∈ ys → x ∈ (xs ++ ys)
∈-++-right {xs = []}     x∈ys = x∈ys
∈-++-right {xs = y ∷ xs} x∈ys = there (∈-++-right {xs = xs} x∈ys)

-- Map preserves membership (modulo function application)
∈-map : {A B : Set} {f : A → B} {x : A} {xs : List A}
      → x ∈ xs → f x ∈ map f xs
∈-map here        = here
∈-map (there x∈xs) = there (∈-map x∈xs)

--------------------------------------------------------------------------------
-- Zip
--------------------------------------------------------------------------------

-- Zip two lists together
zip : {A B : Set} → List A → List B → List (A × B)
zip []       _        = []
zip _        []       = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys
  where
    record _×_ (A B : Set) : Set where
      constructor _,_
      field
        fst : A
        snd : B

-- Length of zip is minimum of input lengths
length-zip : {A B : Set} → (xs : List A) → (ys : List B)
           → length (zip xs ys) ≤ min (length xs) (length ys)
length-zip []       _        = z≤n
length-zip _        []       = z≤n
length-zip (x ∷ xs) (y ∷ ys) = s≤s (length-zip xs ys)
  where
    data _≤_ : ℕ → ℕ → Set where
      z≤n : {n : ℕ} → zero ≤ n
      s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

    min : ℕ → ℕ → ℕ
    min zero    _       = zero
    min _       zero    = zero
    min (suc m) (suc n) = suc (min m n)
