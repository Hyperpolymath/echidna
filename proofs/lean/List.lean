/-
SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
SPDX-License-Identifier: MIT

List Proofs in Lean 4

This file demonstrates proofs about lists:
- Append properties
- Length theorems
- Map and fold properties
- Membership and lookup

These serve as test cases for ECHIDNA's Lean backend integration.
-/

namespace ECHIDNA.List

/-! ## Basic List Properties -/

/--
The empty list has length 0.
-/
theorem length_nil {α : Type} : List.length ([] : List α) = 0 := by
  rfl

/--
Length of singleton list.
-/
theorem length_singleton {α : Type} (x : α) : List.length [x] = 1 := by
  rfl

/--
Length of cons.
-/
theorem length_cons {α : Type} (x : α) (xs : List α) :
  List.length (x :: xs) = List.length xs + 1 := by
  rfl


/-! ## Append Properties -/

/--
Appending empty list on the right is identity.
-/
theorem append_nil {α : Type} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.append]
    exact ih

/--
Appending empty list on the left is identity.
-/
theorem nil_append {α : Type} (xs : List α) : [] ++ xs = xs := by
  rfl

/--
Append is associative.
-/
theorem append_assoc {α : Type} (xs ys zs : List α) :
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.append]
    exact ih

/--
Length of append is sum of lengths.
-/
theorem length_append {α : Type} (xs ys : List α) :
  List.length (xs ++ ys) = List.length xs + List.length ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.length, List.append]
    rw [ih]
    omega


/-! ## Reverse Properties -/

/--
Reverse of empty list is empty.
-/
theorem reverse_nil {α : Type} : List.reverse ([] : List α) = [] := by
  rfl

/--
Reverse of singleton is itself.
-/
theorem reverse_singleton {α : Type} (x : α) : List.reverse [x] = [x] := by
  rfl

/--
Reverse is involutive (reversing twice gives original).
-/
theorem reverse_reverse {α : Type} (xs : List α) :
  List.reverse (List.reverse xs) = xs := by
  exact List.reverse_reverse xs

/--
Length is preserved by reverse.
-/
theorem length_reverse {α : Type} (xs : List α) :
  List.length (List.reverse xs) = List.length xs := by
  exact List.length_reverse xs

/--
Reverse distributes over append.
-/
theorem reverse_append {α : Type} (xs ys : List α) :
  List.reverse (xs ++ ys) = List.reverse ys ++ List.reverse xs := by
  exact List.reverse_append xs ys


/-! ## Map Properties -/

/--
Map over empty list is empty.
-/
theorem map_nil {α β : Type} (f : α → β) : List.map f [] = [] := by
  rfl

/--
Map over cons.
-/
theorem map_cons {α β : Type} (f : α → β) (x : α) (xs : List α) :
  List.map f (x :: xs) = f x :: List.map f xs := by
  rfl

/--
Length is preserved by map.
-/
theorem length_map {α β : Type} (f : α → β) (xs : List α) :
  List.length (List.map f xs) = List.length xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.map, List.length]
    exact ih

/--
Map distributes over append.
-/
theorem map_append {α β : Type} (f : α → β) (xs ys : List α) :
  List.map f (xs ++ ys) = List.map f xs ++ List.map f ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.map, List.append]
    exact ih

/--
Map identity is identity.
-/
theorem map_id {α : Type} (xs : List α) : List.map id xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.map, id]
    exact ih

/--
Map composition.
-/
theorem map_map {α β γ : Type} (f : α → β) (g : β → γ) (xs : List α) :
  List.map g (List.map f xs) = List.map (g ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.map, Function.comp]
    exact ih


/-! ## Filter Properties -/

/--
Filter empty list is empty.
-/
theorem filter_nil {α : Type} (p : α → Bool) : List.filter p [] = [] := by
  rfl

/--
Length of filtered list is at most original length.
-/
theorem length_filter_le {α : Type} (p : α → Bool) (xs : List α) :
  List.length (List.filter p xs) ≤ List.length xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.filter]
    cases p x <;> simp <;> omega

/--
Filter distributes over append.
-/
theorem filter_append {α : Type} (p : α → Bool) (xs ys : List α) :
  List.filter p (xs ++ ys) = List.filter p xs ++ List.filter p ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.filter, List.append]
    cases p x <;> simp [List.append, ih]


/-! ## Fold Properties -/

/--
Right fold over empty list.
-/
theorem foldr_nil {α β : Type} (f : α → β → β) (init : β) :
  List.foldr f init [] = init := by
  rfl

/--
Right fold over cons.
-/
theorem foldr_cons {α β : Type} (f : α → β → β) (init : β) (x : α) (xs : List α) :
  List.foldr f init (x :: xs) = f x (List.foldr f init xs) := by
  rfl

/--
Right fold over append.
-/
theorem foldr_append {α β : Type} (f : α → β → β) (init : β) (xs ys : List α) :
  List.foldr f init (xs ++ ys) = List.foldr f (List.foldr f init ys) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.foldr, List.append]
    rw [ih]

/--
Left fold over empty list.
-/
theorem foldl_nil {α β : Type} (f : β → α → β) (init : β) :
  List.foldl f init [] = init := by
  rfl

/--
Left fold over cons.
-/
theorem foldl_cons {α β : Type} (f : β → α → β) (init : β) (x : α) (xs : List α) :
  List.foldl f init (x :: xs) = List.foldl f (f init x) xs := by
  rfl


/-! ## Sum and Product -/

/--
Sum of empty list is 0.
-/
theorem sum_nil : List.sum ([] : List Nat) = 0 := by
  rfl

/--
Sum of cons.
-/
theorem sum_cons (x : Nat) (xs : List Nat) :
  List.sum (x :: xs) = x + List.sum xs := by
  rfl

/--
Sum of append.
-/
theorem sum_append (xs ys : List Nat) :
  List.sum (xs ++ ys) = List.sum xs + List.sum ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.sum, List.append]
    rw [ih]
    omega


/-! ## Membership Properties -/

/--
Nothing is in the empty list.
-/
theorem mem_nil {α : Type} (x : α) : x ∉ ([] : List α) := by
  simp [List.mem_nil_iff]

/--
Element is in list after cons.
-/
theorem mem_cons_self {α : Type} (x : α) (xs : List α) : x ∈ (x :: xs) := by
  exact List.mem_cons_self x xs

/--
Membership in cons (if in tail).
-/
theorem mem_cons_of_mem {α : Type} (x y : α) (xs : List α) :
  x ∈ xs → x ∈ (y :: xs) := by
  intro h
  exact List.mem_cons_of_mem y h

/--
Membership in append (left).
-/
theorem mem_append_left {α : Type} (x : α) (xs ys : List α) :
  x ∈ xs → x ∈ (xs ++ ys) := by
  intro h
  exact List.mem_append_left ys h

/--
Membership in append (right).
-/
theorem mem_append_right {α : Type} (x : α) (xs ys : List α) :
  x ∈ ys → x ∈ (xs ++ ys) := by
  intro h
  exact List.mem_append_right xs h


/-! ## Take and Drop -/

/--
Take 0 elements is empty.
-/
theorem take_zero {α : Type} (xs : List α) : List.take 0 xs = [] := by
  cases xs <;> rfl

/--
Take from empty list is empty.
-/
theorem take_nil {α : Type} (n : Nat) : List.take n ([] : List α) = [] := by
  cases n <;> rfl

/--
Drop 0 elements is identity.
-/
theorem drop_zero {α : Type} (xs : List α) : List.drop 0 xs = xs := by
  cases xs <;> rfl

/--
Drop from empty list is empty.
-/
theorem drop_nil {α : Type} (n : Nat) : List.drop n ([] : List α) = [] := by
  cases n <;> rfl

/--
Take and drop reconstruct the list.
-/
theorem take_append_drop {α : Type} (n : Nat) (xs : List α) :
  List.take n xs ++ List.drop n xs = xs := by
  induction xs generalizing n with
  | nil => cases n <;> rfl
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp [List.take, List.drop, List.append]
      exact ih n


/-! ## Zip Properties -/

/--
Zip with empty list (left).
-/
theorem zip_nil_left {α β : Type} (ys : List β) :
  List.zip ([] : List α) ys = [] := by
  rfl

/--
Zip with empty list (right).
-/
theorem zip_nil_right {α β : Type} (xs : List α) :
  List.zip xs ([] : List β) = [] := by
  cases xs <;> rfl

/--
Length of zip is minimum of lengths.
-/
theorem length_zip {α β : Type} (xs : List α) (ys : List β) :
  List.length (List.zip xs ys) = min (List.length xs) (List.length ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      simp [List.zip, List.length]
      rw [ih]
      omega


/-! ## All and Any -/

/--
All predicate on empty list is true.
-/
theorem all_nil {α : Type} (p : α → Bool) : List.all [] p = true := by
  rfl

/--
Any predicate on empty list is false.
-/
theorem any_nil {α : Type} (p : α → Bool) : List.any [] p = false := by
  rfl

/--
If all elements satisfy predicate, so does any sublist.
-/
theorem all_append {α : Type} (p : α → Bool) (xs ys : List α) :
  List.all (xs ++ ys) p = (List.all xs p && List.all ys p) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.all, List.append]
    rw [ih]
    cases List.all xs p <;> simp


/-! ## Replicate -/

/--
Replicate 0 times is empty.
-/
theorem replicate_zero {α : Type} (x : α) : List.replicate 0 x = [] := by
  rfl

/--
Length of replicate.
-/
theorem length_replicate {α : Type} (n : Nat) (x : α) :
  List.length (List.replicate n x) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate, List.length]
    exact ih


end ECHIDNA.List
