(* ========================================================================= *)
(* ECHIDNA Basic Coq Proofs                                                  *)
(* Simple logical proofs demonstrating fundamental tactics                   *)
(* ========================================================================= *)

(** * Identity and Basic Implication *)

(** ** Theorem: Identity
    For any proposition A, if A is true, then A is true.
    This is the most fundamental theorem in logic.

    Tactics used:
    - intro: Introduce the hypothesis into the context
*)
Theorem identity : forall A : Prop, A -> A.
Proof.
  intros A H.  (* Introduce the proposition A and hypothesis H : A *)
  exact H.     (* The goal is exactly H *)
Qed.

(** Alternative proof using apply *)
Theorem identity' : forall A : Prop, A -> A.
Proof.
  intros A H.
  apply H.
Qed.

(** ** Theorem: Modus Ponens
    If we have "A implies B" and we have A, then we can conclude B.
    This is one of the most fundamental rules of inference.

    Tactics used:
    - intro: Introduce hypotheses
    - apply: Apply a function/implication to prove the goal
*)
Theorem modus_ponens : forall A B : Prop, (A -> B) -> A -> B.
Proof.
  intros A B H_imp H_a.  (* Introduce propositions and hypotheses *)
                          (* H_imp : A -> B *)
                          (* H_a : A *)
  apply H_imp.            (* Apply the implication to prove B *)
  exact H_a.              (* Provide A as the argument *)
Qed.

(** Shorter proof *)
Theorem modus_ponens' : forall A B : Prop, (A -> B) -> A -> B.
Proof.
  intros A B H_imp H_a.
  apply H_imp.
  assumption.  (* Find and use H_a automatically *)
Qed.

(** Even shorter using auto *)
Theorem modus_ponens'' : forall A B : Prop, (A -> B) -> A -> B.
Proof.
  auto.  (* Coq can prove this automatically *)
Qed.

(** ** Theorem: Transitivity of Implication
    If A implies B, and B implies C, then A implies C.
    This allows us to chain implications together.

    Tactics used:
    - intro: Introduce hypotheses
    - apply: Apply implications
*)
Theorem transitivity : forall A B C : Prop,
  (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C H_ab H_bc.  (* H_ab : A -> B, H_bc : B -> C *)
  intro H_a.                (* H_a : A *)
  apply H_bc.               (* To prove C, we prove B *)
  apply H_ab.               (* To prove B, we prove A *)
  exact H_a.                (* We have A *)
Qed.

(** Shorter proof showing the flow *)
Theorem transitivity' : forall A B C : Prop,
  (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C H_ab H_bc H_a.
  apply H_bc, H_ab.  (* Apply both implications in sequence *)
  assumption.
Qed.

(** ** Theorem: Conjunction Introduction
    If we have A and we have B, then we have A ∧ B.
*)
Theorem and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B H_a H_b.
  split.            (* Split the conjunction into two goals *)
  - exact H_a.      (* Prove A *)
  - exact H_b.      (* Prove B *)
Qed.

(** ** Theorem: Conjunction Elimination (Left)
    If we have A ∧ B, then we have A.
*)
Theorem and_elim_left : forall A B : Prop, A /\ B -> A.
Proof.
  intros A B H.
  destruct H as [H_a H_b].  (* Destruct the conjunction *)
  exact H_a.
Qed.

(** ** Theorem: Conjunction Elimination (Right)
    If we have A ∧ B, then we have B.
*)
Theorem and_elim_right : forall A B : Prop, A /\ B -> B.
Proof.
  intros A B H.
  destruct H as [H_a H_b].
  exact H_b.
Qed.

(** ** Theorem: Conjunction Commutativity
    A ∧ B is equivalent to B ∧ A.
*)
Theorem and_commutative : forall A B : Prop, A /\ B -> B /\ A.
Proof.
  intros A B H.
  destruct H as [H_a H_b].
  split.
  - exact H_b.
  - exact H_a.
Qed.

(** ** Theorem: Disjunction Introduction (Left)
    If we have A, then we have A ∨ B.
*)
Theorem or_intro_left : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B H_a.
  left.  (* Choose the left side of the disjunction *)
  exact H_a.
Qed.

(** ** Theorem: Disjunction Introduction (Right)
    If we have B, then we have A ∨ B.
*)
Theorem or_intro_right : forall A B : Prop, B -> A \/ B.
Proof.
  intros A B H_b.
  right.  (* Choose the right side of the disjunction *)
  exact H_b.
Qed.

(** ** Theorem: Disjunction Elimination
    If we have A ∨ B, and both A and B imply C, then we have C.
*)
Theorem or_elim : forall A B C : Prop,
  A \/ B -> (A -> C) -> (B -> C) -> C.
Proof.
  intros A B C H_or H_ac H_bc.
  destruct H_or as [H_a | H_b].
  - (* Case: A is true *)
    apply H_ac.
    exact H_a.
  - (* Case: B is true *)
    apply H_bc.
    exact H_b.
Qed.

(** ** Theorem: Curry
    Convert a function taking a pair to a curried function.
    (A ∧ B) → C is equivalent to A → (B → C).
*)
Theorem curry : forall A B C : Prop,
  ((A /\ B) -> C) -> (A -> B -> C).
Proof.
  intros A B C H_and_imp H_a H_b.
  apply H_and_imp.
  split.
  - exact H_a.
  - exact H_b.
Qed.

(** ** Theorem: Uncurry
    Convert a curried function to one taking a pair.
*)
Theorem uncurry : forall A B C : Prop,
  (A -> B -> C) -> ((A /\ B) -> C).
Proof.
  intros A B C H_curry H_and.
  destruct H_and as [H_a H_b].
  apply H_curry.
  - exact H_a.
  - exact H_b.
Qed.

(* ========================================================================= *)
(* End of basic.v                                                            *)
(* ========================================================================= *)
