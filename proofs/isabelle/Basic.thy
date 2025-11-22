(*
  Basic.thy - Simple Isabelle/HOL Proofs

  This theory demonstrates basic proof techniques in Isabelle/HOL:
  - Identity proofs
  - Modus ponens
  - Transitivity
  - Simple implication chains

  Part of the ECHIDNA theorem proving platform
  Tier 1 Prover: Isabelle/HOL
*)

theory Basic
  imports Main
begin

section \<open>Basic Identity Proofs\<close>

text \<open>
  The simplest possible proof: anything implies itself.
  This demonstrates the identity law of propositional logic.
\<close>

lemma identity:
  "A \<longrightarrow> A"
  by simp

lemma identity_meta:
  "A \<Longrightarrow> A"
  by assumption

text \<open>
  More explicit proof of identity using apply-style tactics.
\<close>

lemma identity_explicit:
  shows "A \<longrightarrow> A"
proof -
  show "A \<longrightarrow> A" by simp
qed

section \<open>Modus Ponens\<close>

text \<open>
  Modus ponens is the fundamental rule of inference:
  If we have A ⟹ B and we have A, then we can derive B.
\<close>

lemma modus_ponens:
  "(A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> B"
  by simp

lemma modus_ponens_meta:
  "(A \<Longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B"
  by assumption

text \<open>
  Applied version: given the premises, derive the conclusion.
\<close>

lemma modus_ponens_applied:
  assumes "A \<Longrightarrow> B" and "A"
  shows "B"
  using assms by simp

section \<open>Transitivity\<close>

text \<open>
  Transitivity of implication: if A implies B and B implies C,
  then A implies C.
\<close>

lemma implication_transitivity:
  "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)"
  by auto

lemma implication_transitivity_meta:
  assumes "A \<Longrightarrow> B" and "B \<Longrightarrow> C"
  shows "A \<Longrightarrow> C"
  using assms by simp

text \<open>
  Explicit proof showing the reasoning steps.
\<close>

lemma transitivity_explicit:
  assumes ab: "A \<Longrightarrow> B"
      and bc: "B \<Longrightarrow> C"
      and a: "A"
  shows "C"
proof -
  have "B" using ab a by simp
  then show "C" using bc by simp
qed

section \<open>Basic Conjunction Properties\<close>

text \<open>
  Conjunction is commutative.
\<close>

lemma conj_commute:
  "A \<and> B \<longrightarrow> B \<and> A"
  by simp

lemma conj_commute_meta:
  assumes "A" and "B"
  shows "B \<and> A"
  using assms by simp

text \<open>
  Conjunction elimination (projection).
\<close>

lemma conj_elim_left:
  "A \<and> B \<Longrightarrow> A"
  by simp

lemma conj_elim_right:
  "A \<and> B \<Longrightarrow> B"
  by simp

section \<open>Basic Disjunction Properties\<close>

text \<open>
  Disjunction is commutative.
\<close>

lemma disj_commute:
  "A \<or> B \<longrightarrow> B \<or> A"
  by simp

text \<open>
  Disjunction introduction.
\<close>

lemma disj_intro_left:
  "A \<Longrightarrow> A \<or> B"
  by simp

lemma disj_intro_right:
  "B \<Longrightarrow> A \<or> B"
  by simp

section \<open>Simple Implication Chains\<close>

text \<open>
  Chaining multiple implications together.
\<close>

lemma chain_two:
  assumes "A" and "A \<Longrightarrow> B"
  shows "B"
  using assms by simp

lemma chain_three:
  assumes "A" and "A \<Longrightarrow> B" and "B \<Longrightarrow> C"
  shows "C"
  using assms by simp

lemma chain_four:
  assumes "A" and "A \<Longrightarrow> B" and "B \<Longrightarrow> C" and "C \<Longrightarrow> D"
  shows "D"
  using assms by simp

text \<open>
  Hypothetical syllogism: combining two implications.
\<close>

lemma hypothetical_syllogism:
  assumes "A \<longrightarrow> B" and "B \<longrightarrow> C"
  shows "A \<longrightarrow> C"
  using assms by auto

section \<open>Negation Basics\<close>

text \<open>
  Double negation elimination (classical).
\<close>

lemma double_negation:
  "\<not>\<not>A \<longrightarrow> A"
  by simp

text \<open>
  Contrapositive: if A implies B, then not B implies not A.
\<close>

lemma contrapositive:
  "(A \<longrightarrow> B) \<longrightarrow> (\<not>B \<longrightarrow> \<not>A)"
  by auto

lemma contrapositive_applied:
  assumes "A \<Longrightarrow> B" and "\<not>B"
  shows "\<not>A"
  using assms by auto

text \<open>
  Law of excluded middle (classical logic).
\<close>

lemma excluded_middle:
  "A \<or> \<not>A"
  by simp

end
