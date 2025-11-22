(*
  Propositional.thy - Propositional Logic in Isabelle/HOL

  This theory demonstrates propositional logic reasoning:
  - De Morgan's laws
  - Classical logic principles
  - Distribution laws
  - HOL reasoning techniques

  Part of the ECHIDNA theorem proving platform
  Tier 1 Prover: Isabelle/HOL
*)

theory Propositional
  imports Main
begin

section \<open>De Morgan's Laws\<close>

text \<open>
  De Morgan's laws relate conjunction, disjunction, and negation.
  These are fundamental principles of classical logic.
\<close>

lemma de_morgan_conj_to_disj:
  "\<not>(A \<and> B) \<longleftrightarrow> (\<not>A \<or> \<not>B)"
  by auto

lemma de_morgan_disj_to_conj:
  "\<not>(A \<or> B) \<longleftrightarrow> (\<not>A \<and> \<not>B)"
  by auto

text \<open>
  De Morgan's laws with explicit proofs using apply-style tactics.
\<close>

lemma de_morgan_conj_explicit:
  shows "\<not>(A \<and> B) \<longleftrightarrow> (\<not>A \<or> \<not>B)"
proof
  assume "\<not>(A \<and> B)"
  then show "\<not>A \<or> \<not>B" by auto
next
  assume "\<not>A \<or> \<not>B"
  then show "\<not>(A \<and> B)" by auto
qed

lemma de_morgan_disj_explicit:
  shows "\<not>(A \<or> B) \<longleftrightarrow> (\<not>A \<and> \<not>B)"
proof
  assume "\<not>(A \<or> B)"
  then show "\<not>A \<and> \<not>B" by auto
next
  assume "\<not>A \<and> \<not>B"
  then show "\<not>(A \<or> B)" by auto
qed

section \<open>Classical Logic Principles\<close>

text \<open>
  The law of excluded middle: for any proposition A,
  either A is true or its negation is true.
\<close>

lemma lem:
  "A \<or> \<not>A"
  by simp

text \<open>
  Double negation elimination: ¬¬A is equivalent to A.
  This is a characteristic principle of classical (vs. intuitionistic) logic.
\<close>

lemma double_neg_elim:
  "\<not>\<not>A \<longleftrightarrow> A"
  by auto

lemma double_neg_intro:
  "A \<Longrightarrow> \<not>\<not>A"
  by simp

text \<open>
  Proof by contradiction (reductio ad absurdum).
  If assuming ¬A leads to a contradiction, then A must be true.
\<close>

lemma contradiction_implies_anything:
  "False \<Longrightarrow> A"
  by simp

lemma proof_by_contradiction:
  "(\<not>A \<Longrightarrow> False) \<Longrightarrow> A"
  by auto

text \<open>
  Peirce's law: a characteristic classical tautology.
\<close>

lemma peirce:
  "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
  by auto

section \<open>Distribution Laws\<close>

text \<open>
  Conjunction distributes over disjunction.
\<close>

lemma conj_distrib_disj:
  "A \<and> (B \<or> C) \<longleftrightarrow> (A \<and> B) \<or> (A \<and> C)"
  by auto

text \<open>
  Disjunction distributes over conjunction.
\<close>

lemma disj_distrib_conj:
  "A \<or> (B \<and> C) \<longleftrightarrow> (A \<or> B) \<and> (A \<or> C)"
  by auto

text \<open>
  Explicit proof of distribution using structured proof.
\<close>

lemma conj_distrib_explicit:
  shows "A \<and> (B \<or> C) \<longleftrightarrow> (A \<and> B) \<or> (A \<and> C)"
proof
  assume "A \<and> (B \<or> C)"
  then show "(A \<and> B) \<or> (A \<and> C)"
  proof (cases "B")
    case True
    with \<open>A \<and> (B \<or> C)\<close> show ?thesis by simp
  next
    case False
    with \<open>A \<and> (B \<or> C)\<close> show ?thesis by auto
  qed
next
  assume "(A \<and> B) \<or> (A \<and> C)"
  then show "A \<and> (B \<or> C)" by auto
qed

section \<open>Implication Properties\<close>

text \<open>
  Implication can be expressed using disjunction and negation.
\<close>

lemma impl_as_disj:
  "(A \<longrightarrow> B) \<longleftrightarrow> (\<not>A \<or> B)"
  by auto

text \<open>
  Implication is transitive (hypothetical syllogism).
\<close>

lemma impl_transitive:
  "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)"
  by auto

text \<open>
  Exportation law: converting curried implications.
\<close>

lemma exportation:
  "((A \<and> B) \<longrightarrow> C) \<longleftrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
  by auto

text \<open>
  Contrapositive forms.
\<close>

lemma contrapositive_simple:
  "(A \<longrightarrow> B) \<longleftrightarrow> (\<not>B \<longrightarrow> \<not>A)"
  by auto

lemma contrapositive_double_neg:
  "(A \<longrightarrow> \<not>B) \<longleftrightarrow> (B \<longrightarrow> \<not>A)"
  by auto

section \<open>Equivalence Properties\<close>

text \<open>
  Logical equivalence is symmetric, reflexive, and transitive.
\<close>

lemma equiv_refl:
  "A \<longleftrightarrow> A"
  by simp

lemma equiv_symm:
  "(A \<longleftrightarrow> B) \<Longrightarrow> (B \<longleftrightarrow> A)"
  by auto

lemma equiv_trans:
  assumes "A \<longleftrightarrow> B" and "B \<longleftrightarrow> C"
  shows "A \<longleftrightarrow> C"
  using assms by auto

text \<open>
  Equivalence can be decomposed into two implications.
\<close>

lemma equiv_as_impl:
  "(A \<longleftrightarrow> B) \<longleftrightarrow> ((A \<longrightarrow> B) \<and> (B \<longrightarrow> A))"
  by auto

section \<open>Absorption Laws\<close>

text \<open>
  Absorption laws simplify compound propositions.
\<close>

lemma absorption_conj:
  "A \<or> (A \<and> B) \<longleftrightarrow> A"
  by auto

lemma absorption_disj:
  "A \<and> (A \<or> B) \<longleftrightarrow> A"
  by auto

section \<open>Idempotence Laws\<close>

text \<open>
  Conjunction and disjunction are idempotent.
\<close>

lemma conj_idemp:
  "A \<and> A \<longleftrightarrow> A"
  by simp

lemma disj_idemp:
  "A \<or> A \<longleftrightarrow> A"
  by simp

section \<open>Associativity and Commutativity\<close>

text \<open>
  Conjunction is associative and commutative.
\<close>

lemma conj_assoc:
  "(A \<and> B) \<and> C \<longleftrightarrow> A \<and> (B \<and> C)"
  by auto

lemma conj_comm:
  "A \<and> B \<longleftrightarrow> B \<and> A"
  by auto

text \<open>
  Disjunction is associative and commutative.
\<close>

lemma disj_assoc:
  "(A \<or> B) \<or> C \<longleftrightarrow> A \<or> (B \<or> C)"
  by auto

lemma disj_comm:
  "A \<or> B \<longleftrightarrow> B \<or> A"
  by auto

section \<open>Material Implication Theorems\<close>

text \<open>
  Various theorems involving material implication.
\<close>

lemma impl_self:
  "A \<longrightarrow> A"
  by simp

lemma true_impl_anything:
  "True \<longrightarrow> A \<longleftrightarrow> A"
  by simp

lemma anything_impl_true:
  "A \<longrightarrow> True"
  by simp

lemma false_impl_anything:
  "False \<longrightarrow> A"
  by simp

lemma anything_impl_false:
  "A \<longrightarrow> False \<longleftrightarrow> \<not>A"
  by auto

section \<open>Complex Tautologies\<close>

text \<open>
  More complex tautologies demonstrating HOL reasoning.
\<close>

lemma complex_tautology_1:
  "((A \<longrightarrow> B) \<and> (C \<longrightarrow> D) \<and> (A \<or> C)) \<longrightarrow> (B \<or> D)"
  by auto

lemma complex_tautology_2:
  "((A \<or> B) \<and> (A \<longrightarrow> C) \<and> (B \<longrightarrow> D)) \<longrightarrow> (C \<or> D)"
  by auto

lemma complex_tautology_3:
  "(A \<longrightarrow> (B \<longrightarrow> C)) \<longleftrightarrow> ((A \<and> B) \<longrightarrow> C)"
  by auto

lemma complex_tautology_4:
  "((A \<longrightarrow> B) \<and> (\<not>A \<longrightarrow> B)) \<longleftrightarrow> B"
  by auto

text \<open>
  Case analysis using disjunction.
\<close>

lemma case_analysis:
  assumes "A \<or> B" and "A \<Longrightarrow> C" and "B \<Longrightarrow> C"
  shows "C"
  using assms by auto

text \<open>
  Disjunctive syllogism.
\<close>

lemma disjunctive_syllogism:
  assumes "A \<or> B" and "\<not>A"
  shows "B"
  using assms by auto

end
