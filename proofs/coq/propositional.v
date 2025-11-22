(* ========================================================================= *)
(* ECHIDNA Propositional Logic Proofs                                        *)
(* Advanced propositional logic including classical reasoning                *)
(* ========================================================================= *)

(** * Propositional Logic Theorems *)

(** ** De Morgan's Laws
    These laws relate conjunction, disjunction, and negation.
    They are fundamental in both classical and constructive logic.
*)

(** *** De Morgan's Law 1: ¬(A ∨ B) ↔ (¬A ∧ ¬B)
    "Not (A or B)" is equivalent to "(not A) and (not B)"

    This direction is constructively valid.
*)
Theorem de_morgan_1 : forall A B : Prop,
  ~(A \/ B) -> (~A /\ ~B).
Proof.
  intros A B H_not_or.
  split.
  - (* Prove ¬A *)
    intro H_a.
    apply H_not_or.
    left.
    exact H_a.
  - (* Prove ¬B *)
    intro H_b.
    apply H_not_or.
    right.
    exact H_b.
Qed.

(** *** De Morgan's Law 1 (Reverse): (¬A ∧ ¬B) → ¬(A ∨ B)
    This direction is also constructively valid.
*)
Theorem de_morgan_1_rev : forall A B : Prop,
  (~A /\ ~B) -> ~(A \/ B).
Proof.
  intros A B H_and H_or.
  destruct H_and as [H_not_a H_not_b].
  destruct H_or as [H_a | H_b].
  - (* Case: A is true *)
    apply H_not_a.
    exact H_a.
  - (* Case: B is true *)
    apply H_not_b.
    exact H_b.
Qed.

(** *** De Morgan's Law 2: ¬(A ∧ B) → (¬A ∨ ¬B)
    "Not (A and B)" implies "(not A) or (not B)"

    Note: This requires classical logic (excluded middle).
    In constructive logic, we can only prove the reverse direction.
*)

(** First, let's prove the constructively valid direction *)
Theorem de_morgan_2_constructive : forall A B : Prop,
  (~A \/ ~B) -> ~(A /\ B).
Proof.
  intros A B H_or H_and.
  destruct H_and as [H_a H_b].
  destruct H_or as [H_not_a | H_not_b].
  - (* Case: ¬A *)
    apply H_not_a.
    exact H_a.
  - (* Case: ¬B *)
    apply H_not_b.
    exact H_b.
Qed.

(** For the classical direction, we need the law of excluded middle *)
Require Import Classical.

Theorem de_morgan_2_classical : forall A B : Prop,
  ~(A /\ B) -> (~A \/ ~B).
Proof.
  intros A B H_not_and.
  (* Use excluded middle on A *)
  destruct (classic A) as [H_a | H_not_a].
  - (* Case: A is true *)
    right.
    intro H_b.
    apply H_not_and.
    split; assumption.
  - (* Case: ¬A is true *)
    left.
    exact H_not_a.
Qed.

(** ** Double Negation *)

(** *** Double Negation Introduction
    This is constructively valid: A → ¬¬A
*)
Theorem double_negation_intro : forall A : Prop,
  A -> ~~A.
Proof.
  intros A H_a H_not_a.
  apply H_not_a.
  exact H_a.
Qed.

(** *** Double Negation Elimination (Classical)
    This requires classical logic: ¬¬A → A

    This is one of the key differences between classical and
    constructive logic.
*)
Theorem double_negation_elim : forall A : Prop,
  ~~A -> A.
Proof.
  intros A H_not_not_a.
  destruct (classic A) as [H_a | H_not_a].
  - exact H_a.
  - (* This is a contradiction *)
    exfalso.
    apply H_not_not_a.
    exact H_not_a.
Qed.

(** ** Law of Excluded Middle and Related Theorems *)

(** *** Excluded Middle Implies Double Negation Elimination
    If we have A ∨ ¬A for all A, then we can eliminate double negation.
*)
Theorem lem_implies_dne :
  (forall A : Prop, A \/ ~A) -> (forall B : Prop, ~~B -> B).
Proof.
  intros H_lem B H_not_not_b.
  destruct (H_lem B) as [H_b | H_not_b].
  - exact H_b.
  - exfalso.
    apply H_not_not_b.
    exact H_not_b.
Qed.

(** *** Peirce's Law (Classical)
    ((A → B) → A) → A

    This is a classical tautology that's not provable constructively.
*)
Theorem peirce_law : forall A B : Prop,
  ((A -> B) -> A) -> A.
Proof.
  intros A B H.
  destruct (classic A) as [H_a | H_not_a].
  - exact H_a.
  - apply H.
    intro H_a.
    exfalso.
    apply H_not_a.
    exact H_a.
Qed.

(** ** Implication Properties *)

(** *** Contrapositive
    (A → B) → (¬B → ¬A)

    This is constructively valid.
*)
Theorem contrapositive : forall A B : Prop,
  (A -> B) -> (~B -> ~A).
Proof.
  intros A B H_imp H_not_b H_a.
  apply H_not_b.
  apply H_imp.
  exact H_a.
Qed.

(** *** Contrapositive Reverse (Classical)
    (¬B → ¬A) → (A → B)

    This requires classical logic.
*)
Theorem contrapositive_reverse : forall A B : Prop,
  (~B -> ~A) -> (A -> B).
Proof.
  intros A B H_contra H_a.
  destruct (classic B) as [H_b | H_not_b].
  - exact H_b.
  - exfalso.
    apply (H_contra H_not_b).
    exact H_a.
Qed.

(** ** Disjunction Properties *)

(** *** Disjunction Commutativity
    A ∨ B → B ∨ A
*)
Theorem or_commutative : forall A B : Prop,
  A \/ B -> B \/ A.
Proof.
  intros A B H.
  destruct H as [H_a | H_b].
  - right; exact H_a.
  - left; exact H_b.
Qed.

(** *** Disjunction Associativity
    (A ∨ B) ∨ C → A ∨ (B ∨ C)
*)
Theorem or_associative : forall A B C : Prop,
  (A \/ B) \/ C -> A \/ (B \/ C).
Proof.
  intros A B C H.
  destruct H as [[H_a | H_b] | H_c].
  - left; exact H_a.
  - right; left; exact H_b.
  - right; right; exact H_c.
Qed.

(** ** Conjunction Properties *)

(** *** Conjunction Associativity
    (A ∧ B) ∧ C ↔ A ∧ (B ∧ C)
*)
Theorem and_associative : forall A B C : Prop,
  (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
  intros A B C H.
  destruct H as [[H_a H_b] H_c].
  split.
  - exact H_a.
  - split.
    + exact H_b.
    + exact H_c.
Qed.

Theorem and_associative_rev : forall A B C : Prop,
  A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  intros A B C H.
  destruct H as [H_a [H_b H_c]].
  split.
  - split.
    + exact H_a.
    + exact H_b.
  - exact H_c.
Qed.

(** ** Distribution Laws *)

(** *** Conjunction Distributes Over Disjunction
    A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C)
*)
Theorem and_distributes_over_or : forall A B C : Prop,
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
  intros A B C H.
  destruct H as [H_a H_or].
  destruct H_or as [H_b | H_c].
  - left; split; assumption.
  - right; split; assumption.
Qed.

Theorem and_distributes_over_or_rev : forall A B C : Prop,
  (A /\ B) \/ (A /\ C) -> A /\ (B \/ C).
Proof.
  intros A B C H.
  destruct H as [[H_a H_b] | [H_a H_c]].
  - split.
    + exact H_a.
    + left; exact H_b.
  - split.
    + exact H_a.
    + right; exact H_c.
Qed.

(** *** Disjunction Distributes Over Conjunction
    A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C)
*)
Theorem or_distributes_over_and : forall A B C : Prop,
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
  intros A B C H.
  destruct H as [H_a | [H_b H_c]].
  - split.
    + left; exact H_a.
    + left; exact H_a.
  - split.
    + right; exact H_b.
    + right; exact H_c.
Qed.

(** ** Reductio ad Absurdum (Proof by Contradiction) *)

(** *** Classical proof by contradiction
    If assuming ¬A leads to a contradiction, then A must be true.

    This requires classical logic.
*)
Theorem proof_by_contradiction : forall A : Prop,
  (~A -> False) -> A.
Proof.
  intros A H.
  destruct (classic A) as [H_a | H_not_a].
  - exact H_a.
  - exfalso.
    apply H.
    exact H_not_a.
Qed.

(** ** Ex Falso Quodlibet *)

(** *** From False, Anything Follows
    This is constructively valid.
*)
Theorem ex_falso : forall A : Prop,
  False -> A.
Proof.
  intros A H_false.
  exfalso.
  exact H_false.
Qed.

(* ========================================================================= *)
(* End of propositional.v                                                    *)
(* ========================================================================= *)
