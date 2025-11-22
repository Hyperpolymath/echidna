/-
SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
SPDX-License-Identifier: MIT

Natural Number Proofs in Lean 4

This file demonstrates proofs about natural numbers:
- Basic arithmetic properties
- Induction principles
- Simple number theory
- Ordering properties

These serve as test cases for ECHIDNA's Lean backend integration.
-/

namespace ECHIDNA.Nat

/-! ## Basic Arithmetic Properties -/

/--
Zero is the additive identity (right).
-/
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

/--
Zero is the additive identity (left).
-/
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ]
    rw [ih]

/--
One is the multiplicative identity (right).
-/
theorem mul_one (n : Nat) : n * 1 = n := by
  rw [Nat.mul_one]

/--
One is the multiplicative identity (left).
-/
theorem one_mul (n : Nat) : 1 * n = n := by
  rw [Nat.one_mul]

/--
Zero is the multiplicative annihilator (right).
-/
theorem mul_zero (n : Nat) : n * 0 = 0 := by
  rw [Nat.mul_zero]

/--
Zero is the multiplicative annihilator (left).
-/
theorem zero_mul (n : Nat) : 0 * n = 0 := by
  rw [Nat.zero_mul]


/-! ## Commutativity -/

/--
Addition is commutative.
-/
theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n with
  | zero =>
    rw [Nat.add_zero, zero_add]
  | succ n ih =>
    rw [Nat.add_succ, ← ih, Nat.succ_add]

/--
Multiplication is commutative.
-/
theorem mul_comm (m n : Nat) : m * n = n * m := by
  rw [Nat.mul_comm]


/-! ## Associativity -/

/--
Addition is associative.
-/
theorem add_assoc (m n k : Nat) : (m + n) + k = m + (n + k) := by
  induction k with
  | zero =>
    rfl
  | succ k ih =>
    rw [Nat.add_succ, Nat.add_succ, Nat.add_succ, ih]

/--
Multiplication is associative.
-/
theorem mul_assoc (m n k : Nat) : (m * n) * k = m * (n * k) := by
  rw [Nat.mul_assoc]


/-! ## Distributivity -/

/--
Left distributivity: m * (n + k) = m * n + m * k
-/
theorem left_distrib (m n k : Nat) : m * (n + k) = m * n + m * k := by
  rw [Nat.mul_add]

/--
Right distributivity: (m + n) * k = m * k + n * k
-/
theorem right_distrib (m n k : Nat) : (m + n) * k = m * k + n * k := by
  rw [Nat.add_mul]


/-! ## Induction Examples -/

/--
Sum of first n natural numbers: 0 + 1 + ... + n = n(n+1)/2
Proven using the formula: sum = n * (n + 1) / 2
-/
theorem sum_first_n (n : Nat) : 2 * (Fin.sum n id) = n * (n + 1) := by
  sorry -- Requires more advanced Mathlib setup

/--
Simple induction: n + n = 2 * n
-/
theorem double_add (n : Nat) : n + n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.succ_add, Nat.add_succ, ih]
    rw [Nat.mul_succ, Nat.add_comm]
    rfl

/--
Power of 2 grows: 2^n ≥ n for all n ≥ 1
-/
theorem pow2_ge (n : Nat) : n ≥ 1 → 2^n ≥ n := by
  intro h
  induction n with
  | zero =>
    cases h
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have : n + 1 ≥ 1 := Nat.succ_le_succ (Nat.zero_le n)
      have prev := ih this
      simp [Nat.pow_succ]
      omega


/-! ## Comparison and Ordering -/

/--
Reflexivity of ≤.
-/
theorem le_refl (n : Nat) : n ≤ n := by
  exact Nat.le_refl n

/--
Antisymmetry of ≤.
-/
theorem le_antisymm (m n : Nat) : m ≤ n → n ≤ m → m = n := by
  intro hmn hnm
  exact Nat.le_antisymm hmn hnm

/--
Transitivity of ≤.
-/
theorem le_trans (m n k : Nat) : m ≤ n → n ≤ k → m ≤ k := by
  intro hmn hnk
  exact Nat.le_trans hmn hnk

/--
Successor is greater.
-/
theorem lt_succ_self (n : Nat) : n < n + 1 := by
  exact Nat.lt_succ_self n

/--
Zero is the minimum natural number.
-/
theorem zero_le (n : Nat) : 0 ≤ n := by
  exact Nat.zero_le n


/-! ## Addition Properties -/

/--
Left cancellation for addition: k + m = k + n → m = n
-/
theorem add_left_cancel (k m n : Nat) : k + m = k + n → m = n := by
  intro h
  exact Nat.add_left_cancel h

/--
Right cancellation for addition: m + k = n + k → m = n
-/
theorem add_right_cancel (k m n : Nat) : m + k = n + k → m = n := by
  intro h
  exact Nat.add_right_cancel h

/--
Addition preserves ordering (left).
-/
theorem add_le_add_left (m n k : Nat) : m ≤ n → k + m ≤ k + n := by
  intro h
  exact Nat.add_le_add_left h k

/--
Addition preserves ordering (right).
-/
theorem add_le_add_right (m n k : Nat) : m ≤ n → m + k ≤ n + k := by
  intro h
  exact Nat.add_le_add_right h k


/-! ## Multiplication Properties -/

/--
Multiplication by successor: m * (n + 1) = m * n + m
-/
theorem mul_succ (m n : Nat) : m * (n + 1) = m * n + m := by
  rw [Nat.mul_succ]

/--
Successor times: (m + 1) * n = m * n + n
-/
theorem succ_mul (m n : Nat) : (m + 1) * n = m * n + n := by
  rw [Nat.succ_mul]

/--
Left cancellation for multiplication (when k > 0).
-/
theorem mul_left_cancel (k m n : Nat) : k > 0 → k * m = k * n → m = n := by
  intro hk h
  cases k with
  | zero => cases hk
  | succ k =>
    exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ k) h


/-! ## Subtraction Properties -/

/--
Subtraction of zero.
-/
theorem sub_zero (n : Nat) : n - 0 = n := by
  rfl

/--
Self subtraction.
-/
theorem sub_self (n : Nat) : n - n = 0 := by
  exact Nat.sub_self n

/--
Subtraction and addition (when n ≤ m).
-/
theorem sub_add_cancel (m n : Nat) : n ≤ m → (m - n) + n = m := by
  intro h
  exact Nat.sub_add_cancel h


/-! ## Simple Number Theory -/

/--
Even number definition: n is even if n = 2k for some k.
-/
def is_even (n : Nat) : Prop := ∃ k, n = 2 * k

/--
Odd number definition: n is odd if n = 2k + 1 for some k.
-/
def is_odd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

/--
Zero is even.
-/
theorem zero_is_even : is_even 0 := by
  use 0
  rfl

/--
One is odd.
-/
theorem one_is_odd : is_odd 1 := by
  use 0
  rfl

/--
Two is even.
-/
theorem two_is_even : is_even 2 := by
  use 1
  rfl

/--
Sum of two even numbers is even.
-/
theorem even_add_even (m n : Nat) : is_even m → is_even n → is_even (m + n) := by
  intro ⟨k, hm⟩ ⟨j, hn⟩
  use k + j
  rw [hm, hn]
  ring

/--
Product of any number with an even number is even.
-/
theorem mul_even (m n : Nat) : is_even n → is_even (m * n) := by
  intro ⟨k, hn⟩
  use m * k
  rw [hn]
  ring


/-! ## Division Properties -/

/--
Division by 1 is identity.
-/
theorem div_one (n : Nat) : n / 1 = n := by
  exact Nat.div_one n

/--
Self division (when n > 0).
-/
theorem div_self (n : Nat) : n > 0 → n / n = 1 := by
  intro h
  exact Nat.div_self h


/-! ## Modulo Properties -/

/--
Modulo 1 is always 0.
-/
theorem mod_one (n : Nat) : n % 1 = 0 := by
  exact Nat.mod_one n

/--
Modulo self (when n > 0).
-/
theorem mod_self (n : Nat) : n > 0 → n % n = 0 := by
  intro h
  exact Nat.mod_self n

/--
Modulo is less than divisor (when divisor > 0).
-/
theorem mod_lt (m n : Nat) : n > 0 → m % n < n := by
  intro h
  exact Nat.mod_lt m h


/-! ## GCD Properties -/

/--
GCD is commutative.
-/
theorem gcd_comm (m n : Nat) : Nat.gcd m n = Nat.gcd n m := by
  exact Nat.gcd_comm m n

/--
GCD with zero.
-/
theorem gcd_zero_right (n : Nat) : Nat.gcd n 0 = n := by
  exact Nat.gcd_zero_right n

/--
GCD with self.
-/
theorem gcd_self (n : Nat) : Nat.gcd n n = n := by
  exact Nat.gcd_self n


end ECHIDNA.Nat
