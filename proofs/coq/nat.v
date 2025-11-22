(* ========================================================================= *)
(* ECHIDNA Natural Number Proofs                                             *)
(* Proofs about natural numbers, arithmetic, and induction                   *)
(* ========================================================================= *)

Require Import Arith.
Require Import Lia.

(** * Basic Natural Number Properties *)

(** ** Addition Properties *)

(** *** Addition is Commutative: n + m = m + n

    This proof uses induction on n and the built-in rewrite tactic.
*)
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IH].
  - (* Base case: 0 + m = m + 0 *)
    simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - (* Inductive case: S n' + m = m + S n' *)
    simpl.
    rewrite IH.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

(** *** Addition is Associative: (n + m) + p = n + (m + p) *)
Theorem plus_assoc : forall n m p : nat,
  (n + m) + p = n + (m + p).
Proof.
  intros n m p.
  induction n as [| n' IH].
  - (* Base case: (0 + m) + p = 0 + (m + p) *)
    simpl.
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** *** Zero is the Right Identity for Addition: n + 0 = n *)
Theorem plus_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intro n.
  induction n as [| n' IH].
  - (* Base case: 0 + 0 = 0 *)
    reflexivity.
  - (* Inductive case: S n' + 0 = S n' *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** *** Successor on the Right: n + S m = S (n + m) *)
Theorem plus_succ_r : forall n m : nat,
  n + S m = S (n + m).
Proof.
  intros n m.
  induction n as [| n' IH].
  - (* Base case: 0 + S m = S (0 + m) *)
    simpl.
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** ** Multiplication Properties *)

(** *** Multiplication by Zero: n * 0 = 0 *)
Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intro n.
  induction n as [| n' IH].
  - (* Base case: 0 * 0 = 0 *)
    reflexivity.
  - (* Inductive case: S n' * 0 = 0 *)
    simpl.
    exact IH.
Qed.

(** *** Multiplication is Commutative: n * m = m * n *)
Theorem mult_comm : forall n m : nat,
  n * m = m * n.
Proof.
  intros n m.
  induction n as [| n' IH].
  - (* Base case: 0 * m = m * 0 *)
    simpl.
    rewrite mult_0_r.
    reflexivity.
  - (* Inductive case: S n' * m = m * S n' *)
    simpl.
    rewrite IH.
    rewrite <- mult_n_Sm.
    reflexivity.
Qed.

(** *** Distribution: n * (m + p) = n * m + n * p *)
Theorem mult_plus_distr_l : forall n m p : nat,
  n * (m + p) = n * m + n * p.
Proof.
  intros n m p.
  induction n as [| n' IH].
  - (* Base case: 0 * (m + p) = 0 * m + 0 * p *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite IH.
    (* Now we need: (m + p) + (n' * m + n' * p) = m + n' * m + (p + n' * p) *)
    rewrite plus_assoc.
    rewrite plus_assoc.
    (* Rearrange the middle terms *)
    assert (H: forall a b c d : nat, a + (b + c) + d = a + b + (c + d)).
    { intros. lia. }
    rewrite <- H.
    rewrite <- plus_assoc.
    rewrite (plus_comm p (n' * m)).
    reflexivity.
Qed.

(** *** Multiplication is Associative: (n * m) * p = n * (m * p) *)
Theorem mult_assoc : forall n m p : nat,
  (n * m) * p = n * (m * p).
Proof.
  intros n m p.
  induction n as [| n' IH].
  - (* Base case *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite mult_plus_distr_l.
    rewrite IH.
    reflexivity.
Qed.

(** ** Comparison Properties *)

(** *** Less Than or Equal is Reflexive: n ≤ n *)
Theorem le_refl : forall n : nat,
  n <= n.
Proof.
  intro n.
  induction n as [| n' IH].
  - (* Base case: 0 ≤ 0 *)
    apply le_n.
  - (* Inductive case: S n' ≤ S n' *)
    apply le_n.
Qed.

(** *** Less Than or Equal is Transitive: n ≤ m → m ≤ p → n ≤ p *)
Theorem le_trans : forall n m p : nat,
  n <= m -> m <= p -> n <= p.
Proof.
  intros n m p H_nm H_mp.
  induction H_mp as [| p' H_mp' IH].
  - (* Case: m = p *)
    exact H_nm.
  - (* Case: m ≤ p' and p = S p' *)
    apply le_S.
    exact IH.
Qed.

(** *** Addition Preserves Order: n ≤ m → n + p ≤ m + p *)
Theorem plus_le_compat_r : forall n m p : nat,
  n <= m -> n + p <= m + p.
Proof.
  intros n m p H.
  induction H as [| m' H' IH].
  - (* Case: n = m *)
    apply le_refl.
  - (* Case: n ≤ m' *)
    rewrite <- plus_n_Sm.
    apply le_S.
    exact IH.
Qed.

(** ** Induction Examples *)

(** *** Sum of First n Natural Numbers: sum(n) = n * (n + 1) / 2

    We'll prove: 2 * sum(n) = n * (n + 1)
    where sum(n) = 0 + 1 + 2 + ... + n
*)

Fixpoint sum_n (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + sum_n n'
  end.

Theorem sum_formula : forall n : nat,
  2 * sum_n n = n * (n + 1).
Proof.
  intro n.
  induction n as [| n' IH].
  - (* Base case: n = 0 *)
    reflexivity.
  - (* Inductive case: n = S n' *)
    simpl.
    rewrite mult_plus_distr_l.
    rewrite IH.
    (* Need to show: 2 * S n' + n' * (n' + 1) = S n' * (S n' + 1) *)
    simpl.
    ring.  (* The ring tactic solves polynomial equalities *)
Qed.

(** *** Powers of 2 Grow Exponentially *)

Fixpoint power_of_2 (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => 2 * power_of_2 n'
  end.

Theorem power_of_2_positive : forall n : nat,
  power_of_2 n >= 1.
Proof.
  intro n.
  induction n as [| n' IH].
  - (* Base case *)
    simpl.
    apply le_n.
  - (* Inductive case *)
    simpl.
    (* Need: 2 * power_of_2 n' >= 1 *)
    (* Since power_of_2 n' >= 1, we have 2 * power_of_2 n' >= 2 *)
    lia.
Qed.

Theorem power_of_2_grows : forall n : nat,
  power_of_2 (S n) = 2 * power_of_2 n.
Proof.
  intro n.
  reflexivity.
Qed.

(** *** Factorial is Always Positive *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => S n' * factorial n'
  end.

Theorem factorial_positive : forall n : nat,
  factorial n >= 1.
Proof.
  intro n.
  induction n as [| n' IH].
  - (* Base case: factorial 0 = 1 *)
    simpl.
    apply le_n.
  - (* Inductive case *)
    simpl.
    (* factorial (S n') = S n' * factorial n' *)
    (* Since factorial n' >= 1 and S n' >= 1, result >= 1 *)
    apply Nat.le_trans with (m := factorial n').
    + exact IH.
    + apply Nat.le_trans with (m := 1 * factorial n').
      * simpl. apply le_refl.
      * apply mult_le_compat_r.
        apply le_S.
        apply le_0_n.
Qed.

(** *** Factorial Grows Faster Than Powers of 2 *)

Theorem factorial_ge_power_of_2 : forall n : nat,
  n >= 4 -> factorial n >= power_of_2 n.
Proof.
  intro n.
  induction n as [| n' IH].
  - (* Base case: impossible since 0 < 4 *)
    intro H.
    inversion H.
  - (* Inductive case *)
    intro H.
    destruct n' as [| [| [| [| n'']]]].
    + (* n' = 0, so n = 1 < 4: contradiction *)
      inversion H.
    + (* n' = 1, so n = 2 < 4: contradiction *)
      inversion H. inversion H1.
    + (* n' = 2, so n = 3 < 4: contradiction *)
      inversion H. inversion H1. inversion H3.
    + (* n' = 3, so n = 4: base case *)
      simpl.
      lia.
    + (* n' >= 4: use induction *)
      assert (H_ge: S n'' >= 4).
      { lia. }
      assert (H_IH := IH (Nat.le_trans _ _ _ (le_S _ _ (le_S _ _ (le_S _ _ (le_S _ _ (le_0_n n''))))) H)).
      simpl.
      (* factorial (S (S (S (S n'')))) = S (S (S (S n''))) * factorial (S (S (S n''))) *)
      (* power_of_2 (S (S (S (S n'')))) = 2 * power_of_2 (S (S (S n''))) *)
      (* Need: 5 + n'' * factorial ... >= 2 * power_of_2 ... *)
      (* Since n'' + 4 >= 4 and factorial grows faster, this holds *)
      lia.
Qed.

(** ** Even and Odd Numbers *)

(** *** Definition of Even and Odd *)
Inductive even : nat -> Prop :=
  | even_0 : even 0
  | even_SS : forall n, even n -> even (S (S n)).

Inductive odd : nat -> Prop :=
  | odd_1 : odd 1
  | odd_SS : forall n, odd n -> odd (S (S n)).

(** *** Every Number is Either Even or Odd *)
Theorem even_or_odd : forall n : nat,
  even n \/ odd n.
Proof.
  intro n.
  induction n as [| n' IH].
  - (* Base case: 0 is even *)
    left.
    apply even_0.
  - (* Inductive case *)
    destruct IH as [H_even | H_odd].
    + (* n' is even, so S n' is odd *)
      right.
      destruct n' as [| n''].
      * apply odd_1.
      * inversion H_even.
        apply odd_SS.
        assumption.
    + (* n' is odd, so S n' is even *)
      left.
      destruct n' as [| n''].
      * inversion H_odd.
      * inversion H_odd.
        apply even_SS.
        assumption.
Qed.

(** *** Sum of Two Even Numbers is Even *)
Theorem even_plus_even : forall n m : nat,
  even n -> even m -> even (n + m).
Proof.
  intros n m H_n H_m.
  induction H_n as [| n' H_n' IH].
  - (* n = 0 *)
    simpl.
    exact H_m.
  - (* n = S (S n') *)
    simpl.
    apply even_SS.
    exact IH.
Qed.

(* ========================================================================= *)
(* End of nat.v                                                              *)
(* ========================================================================= *)
