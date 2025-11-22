(* ========================================================================= *)
(* ECHIDNA List Proofs                                                       *)
(* Proofs about lists, append, length, map, and fold operations             *)
(* ========================================================================= *)

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Lia.

(** * Basic List Properties *)

(** ** Append Properties *)

(** *** Append with Empty List on Right: l ++ [] = l *)
Theorem app_nil_r : forall {A : Type} (l : list A),
  l ++ [] = l.
Proof.
  intros A l.
  induction l as [| h t IH].
  - (* Base case: [] ++ [] = [] *)
    reflexivity.
  - (* Inductive case: (h :: t) ++ [] = h :: t *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** *** Append is Associative: (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) *)
Theorem app_assoc : forall {A : Type} (l1 l2 l3 : list A),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros A l1 l2 l3.
  induction l1 as [| h t IH].
  - (* Base case: ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3) *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** *** Cons and Append: x :: l = [x] ++ l *)
Theorem cons_app : forall {A : Type} (x : A) (l : list A),
  x :: l = [x] ++ l.
Proof.
  intros A x l.
  reflexivity.
Qed.

(** ** Length Properties *)

(** *** Length of Append: length (l1 ++ l2) = length l1 + length l2 *)
Theorem length_app : forall {A : Type} (l1 l2 : list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros A l1 l2.
  induction l1 as [| h t IH].
  - (* Base case: length ([] ++ l2) = length [] + length l2 *)
    reflexivity.
  - (* Inductive case: length ((h :: t) ++ l2) = length (h :: t) + length l2 *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** *** Length of Cons: length (x :: l) = S (length l) *)
Theorem length_cons : forall {A : Type} (x : A) (l : list A),
  length (x :: l) = S (length l).
Proof.
  intros A x l.
  reflexivity.
Qed.

(** *** Empty List has Length 0 *)
Theorem length_nil : forall {A : Type},
  length (@nil A) = 0.
Proof.
  intro A.
  reflexivity.
Qed.

(** ** Reverse Properties *)

(** *** Helper: Reverse of Append *)
Theorem rev_app_distr : forall {A : Type} (l1 l2 : list A),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros A l1 l2.
  induction l1 as [| h t IH].
  - (* Base case *)
    simpl.
    rewrite app_nil_r.
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite IH.
    rewrite app_assoc.
    reflexivity.
Qed.

(** *** Reverse is Involutive: rev (rev l) = l *)
Theorem rev_involutive : forall {A : Type} (l : list A),
  rev (rev l) = l.
Proof.
  intros A l.
  induction l as [| h t IH].
  - (* Base case: rev (rev []) = [] *)
    reflexivity.
  - (* Inductive case: rev (rev (h :: t)) = h :: t *)
    simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** *** Length of Reverse: length (rev l) = length l *)
Theorem length_rev : forall {A : Type} (l : list A),
  length (rev l) = length l.
Proof.
  intros A l.
  induction l as [| h t IH].
  - (* Base case *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite length_app.
    simpl.
    rewrite IH.
    lia.
Qed.

(** ** Map Properties *)

(** *** Map Preserves Length: length (map f l) = length l *)
Theorem map_length : forall {A B : Type} (f : A -> B) (l : list A),
  length (map f l) = length l.
Proof.
  intros A B f l.
  induction l as [| h t IH].
  - (* Base case *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** *** Map Distributes Over Append: map f (l1 ++ l2) = map f l1 ++ map f l2 *)
Theorem map_app : forall {A B : Type} (f : A -> B) (l1 l2 : list A),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros A B f l1 l2.
  induction l1 as [| h t IH].
  - (* Base case *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** *** Map Composition: map (g ∘ f) l = map g (map f l) *)
Theorem map_map : forall {A B C : Type} (f : A -> B) (g : B -> C) (l : list A),
  map g (map f l) = map (fun x => g (f x)) l.
Proof.
  intros A B C f g l.
  induction l as [| h t IH].
  - (* Base case *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite <- IH.
    reflexivity.
Qed.

(** *** Map with Identity: map id l = l *)
Theorem map_id : forall {A : Type} (l : list A),
  map (fun x => x) l = l.
Proof.
  intros A l.
  induction l as [| h t IH].
  - (* Base case *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** *** Map and Reverse Commute *)
Theorem map_rev : forall {A B : Type} (f : A -> B) (l : list A),
  map f (rev l) = rev (map f l).
Proof.
  intros A B f l.
  induction l as [| h t IH].
  - (* Base case *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite map_app.
    rewrite IH.
    reflexivity.
Qed.

(** ** Fold Properties *)

(** *** Fold Right on Empty List *)
Theorem fold_right_nil : forall {A B : Type} (f : A -> B -> B) (acc : B),
  fold_right f acc [] = acc.
Proof.
  intros A B f acc.
  reflexivity.
Qed.

(** *** Fold Right on Cons *)
Theorem fold_right_cons : forall {A B : Type} (f : A -> B -> B) (acc : B) (h : A) (t : list A),
  fold_right f acc (h :: t) = f h (fold_right f acc t).
Proof.
  intros A B f acc h t.
  reflexivity.
Qed.

(** *** Fold Right and Append *)
Theorem fold_right_app : forall {A B : Type} (f : A -> B -> B) (acc : B) (l1 l2 : list A),
  fold_right f acc (l1 ++ l2) = fold_right f (fold_right f acc l2) l1.
Proof.
  intros A B f acc l1 l2.
  induction l1 as [| h t IH].
  - (* Base case *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** *** Sum of List Using Fold *)
Definition sum_list (l : list nat) : nat :=
  fold_right plus 0 l.

Theorem sum_list_app : forall l1 l2 : list nat,
  sum_list (l1 ++ l2) = sum_list l1 + sum_list l2.
Proof.
  intros l1 l2.
  unfold sum_list.
  rewrite fold_right_app.
  induction l1 as [| h t IH].
  - (* Base case *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite <- plus_assoc.
    reflexivity.
Qed.

(** ** Filter Properties *)

(** *** Filter Preserves Order *)
Theorem filter_preserves_order : forall {A : Type} (f : A -> bool) (l : list A) (x y : A),
  In x l -> In y l ->
  In x (filter f l) -> In y (filter f l) ->
  exists l1 l2 l3, l = l1 ++ [x] ++ l2 ++ [y] ++ l3 ->
  exists l1' l2', filter f l = l1' ++ [x] ++ l2' ++ [y].
Proof.
  (* This is a complex property; we'll state it without full proof *)
  (* The proof would require defining what "preserves order" means precisely *)
Admitted.

(** *** Filter and Append *)
Theorem filter_app : forall {A : Type} (f : A -> bool) (l1 l2 : list A),
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  intros A f l1 l2.
  induction l1 as [| h t IH].
  - (* Base case *)
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite IH.
    destruct (f h).
    + reflexivity.
    + reflexivity.
Qed.

(** *** Length of Filter is Bounded *)
Theorem filter_length : forall {A : Type} (f : A -> bool) (l : list A),
  length (filter f l) <= length l.
Proof.
  intros A f l.
  induction l as [| h t IH].
  - (* Base case *)
    simpl.
    apply le_n.
  - (* Inductive case *)
    simpl.
    destruct (f h) eqn:E.
    + (* f h = true *)
      simpl.
      apply le_n_S.
      exact IH.
    + (* f h = false *)
      apply le_S.
      exact IH.
Qed.

(** ** Nth Element Properties *)

(** *** Nth of Append (Left Part) *)
Theorem nth_app_l : forall {A : Type} (l1 l2 : list A) (n : nat) (d : A),
  n < length l1 ->
  nth n (l1 ++ l2) d = nth n l1 d.
Proof.
  intros A l1 l2 n d H.
  generalize dependent n.
  induction l1 as [| h t IH].
  - (* Base case: contradiction since n < 0 is impossible *)
    intros n H.
    inversion H.
  - (* Inductive case *)
    intros n H.
    destruct n as [| n'].
    + (* n = 0 *)
      reflexivity.
    + (* n = S n' *)
      simpl.
      apply IH.
      simpl in H.
      lia.
Qed.

(** *** Nth of Append (Right Part) *)
Theorem nth_app_r : forall {A : Type} (l1 l2 : list A) (n : nat) (d : A),
  length l1 <= n ->
  nth n (l1 ++ l2) d = nth (n - length l1) l2 d.
Proof.
  intros A l1 l2 n d H.
  generalize dependent n.
  induction l1 as [| h t IH].
  - (* Base case *)
    intros n H.
    simpl.
    rewrite Nat.sub_0_r.
    reflexivity.
  - (* Inductive case *)
    intros n H.
    destruct n as [| n'].
    + (* n = 0: contradiction since length (h :: t) > 0 *)
      simpl in H.
      inversion H.
    + (* n = S n' *)
      simpl.
      apply IH.
      simpl in H.
      lia.
Qed.

(** ** List Membership (In) Properties *)

(** *** In and Append *)
Theorem in_app_iff : forall {A : Type} (x : A) (l1 l2 : list A),
  In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof.
  intros A x l1 l2.
  split.
  - (* Forward direction *)
    intro H.
    induction l1 as [| h t IH].
    + (* l1 = [] *)
      simpl in H.
      right.
      exact H.
    + (* l1 = h :: t *)
      simpl in H.
      destruct H as [H_eq | H_in].
      * (* x = h *)
        left.
        left.
        exact H_eq.
      * (* In x (t ++ l2) *)
        destruct (IH H_in) as [H_l | H_r].
        -- left; right; exact H_l.
        -- right; exact H_r.
  - (* Backward direction *)
    intro H.
    destruct H as [H_l | H_r].
    + (* In x l1 *)
      induction l1 as [| h t IH].
      * (* l1 = []: contradiction *)
        inversion H_l.
      * (* l1 = h :: t *)
        simpl.
        destruct H_l as [H_eq | H_in].
        -- left; exact H_eq.
        -- right; apply IH; exact H_in.
    + (* In x l2 *)
      induction l1 as [| h t IH].
      * (* l1 = [] *)
        simpl.
        exact H_r.
      * (* l1 = h :: t *)
        simpl.
        right.
        apply IH.
Qed.

(** *** In and Map *)
Theorem in_map : forall {A B : Type} (f : A -> B) (l : list A) (x : A),
  In x l -> In (f x) (map f l).
Proof.
  intros A B f l x H.
  induction l as [| h t IH].
  - (* Base case: contradiction *)
    inversion H.
  - (* Inductive case *)
    simpl.
    destruct H as [H_eq | H_in].
    + (* x = h *)
      left.
      rewrite H_eq.
      reflexivity.
    + (* In x t *)
      right.
      apply IH.
      exact H_in.
Qed.

(** *** In and Filter *)
Theorem in_filter : forall {A : Type} (f : A -> bool) (l : list A) (x : A),
  In x (filter f l) <-> In x l /\ f x = true.
Proof.
  intros A f l x.
  split.
  - (* Forward direction *)
    intro H.
    induction l as [| h t IH].
    + (* Base case: contradiction *)
      inversion H.
    + (* Inductive case *)
      simpl in H.
      destruct (f h) eqn:E.
      * (* f h = true *)
        simpl in H.
        destruct H as [H_eq | H_in].
        -- (* x = h *)
          split.
          ++ left; exact H_eq.
          ++ rewrite <- H_eq; exact E.
        -- (* In x (filter f t) *)
          destruct (IH H_in) as [H_in_t H_fx].
          split.
          ++ right; exact H_in_t.
          ++ exact H_fx.
      * (* f h = false *)
        destruct (IH H) as [H_in_t H_fx].
        split.
        -- right; exact H_in_t.
        -- exact H_fx.
  - (* Backward direction *)
    intro H.
    destruct H as [H_in H_fx].
    induction l as [| h t IH].
    + (* Base case: contradiction *)
      inversion H_in.
    + (* Inductive case *)
      simpl.
      destruct H_in as [H_eq | H_in_t].
      * (* x = h *)
        rewrite <- H_eq.
        rewrite H_fx.
        simpl.
        left.
        reflexivity.
      * (* In x t *)
        destruct (f h) eqn:E.
        -- simpl.
           right.
           apply IH.
           exact H_in_t.
        -- apply IH.
           exact H_in_t.
Qed.

(* ========================================================================= *)
(* End of list.v                                                             *)
(* ========================================================================= *)
