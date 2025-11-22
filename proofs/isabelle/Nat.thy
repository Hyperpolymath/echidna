(*
  Nat.thy - Natural Number Proofs in Isabelle/HOL

  This theory demonstrates reasoning about natural numbers:
  - Arithmetic properties (addition, multiplication)
  - Induction proofs
  - Ordering properties
  - Recursive function definitions

  Part of the ECHIDNA theorem proving platform
  Tier 1 Prover: Isabelle/HOL
*)

theory Nat
  imports Main
begin

section \<open>Basic Arithmetic Properties\<close>

text \<open>
  Addition with zero.
\<close>

lemma add_zero_left:
  "0 + n = n"
  by simp

lemma add_zero_right:
  "n + 0 = n"
  by simp

text \<open>
  Addition is commutative.
\<close>

lemma add_comm:
  "m + n = n + m"
  by simp

text \<open>
  Addition is associative.
\<close>

lemma add_assoc:
  "(m + n) + p = m + (n + p)"
  by simp

text \<open>
  Explicit inductive proof of right zero for addition.
\<close>

lemma add_zero_right_inductive:
  shows "n + 0 = n"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

section \<open>Multiplication Properties\<close>

text \<open>
  Multiplication with zero.
\<close>

lemma mult_zero_left:
  "0 * n = 0"
  by simp

lemma mult_zero_right:
  "n * 0 = 0"
  by simp

text \<open>
  Multiplication with one (identity).
\<close>

lemma mult_one_left:
  "1 * n = n"
  by simp

lemma mult_one_right:
  "n * 1 = n"
  by simp

text \<open>
  Multiplication is commutative.
\<close>

lemma mult_comm:
  "m * n = n * m"
  by simp

text \<open>
  Multiplication is associative.
\<close>

lemma mult_assoc:
  "(m * n) * p = m * (n * p)"
  by simp

text \<open>
  Distributive law: multiplication distributes over addition.
\<close>

lemma mult_distrib_left:
  "m * (n + p) = m * n + m * p"
  by (simp add: ring_distribs)

lemma mult_distrib_right:
  "(m + n) * p = m * p + n * p"
  by (simp add: ring_distribs)

section \<open>Induction Examples\<close>

text \<open>
  Sum of first n natural numbers: 0 + 1 + 2 + ... + n = n*(n+1)/2
  We prove the equivalent form: 2 * sum = n * (n + 1)
\<close>

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = Suc n + sum_upto n"

lemma sum_formula:
  "2 * sum_upto n = n * (n + 1)"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "2 * sum_upto (Suc n) = 2 * (Suc n + sum_upto n)"
    by simp
  also have "... = 2 * Suc n + 2 * sum_upto n"
    by simp
  also have "... = 2 * Suc n + n * (n + 1)"
    using Suc.IH by simp
  also have "... = 2 * (n + 1) + n * (n + 1)"
    by simp
  also have "... = (2 + n) * (n + 1)"
    by (simp add: ring_distribs)
  also have "... = Suc n * (Suc n + 1)"
    by simp
  finally show ?case .
qed

text \<open>
  Factorial function and basic properties.
\<close>

fun factorial :: "nat \<Rightarrow> nat" where
  "factorial 0 = 1" |
  "factorial (Suc n) = Suc n * factorial n"

lemma factorial_positive:
  "factorial n > 0"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "factorial (Suc n) = Suc n * factorial n"
    by simp
  also have "... > 0"
    using Suc.IH by simp
  finally show ?case .
qed

lemma factorial_monotone:
  "n > 0 \<Longrightarrow> factorial n \<ge> n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    have "factorial (Suc n) = Suc n * factorial n"
      by simp
    also have "... \<ge> Suc n * 1"
      using factorial_positive[of n] by simp
    also have "... = Suc n"
      by simp
    finally show ?thesis .
  qed
qed

section \<open>Power Function\<close>

text \<open>
  Properties of exponentiation.
\<close>

lemma power_zero:
  "n ^ 0 = 1"
  by simp

lemma power_one:
  "n ^ 1 = n"
  by simp

lemma power_add:
  "n ^ (m + p) = n ^ m * n ^ p"
  by (simp add: power_add)

lemma power_mult:
  "n ^ (m * p) = (n ^ m) ^ p"
  by (simp add: power_mult)

text \<open>
  Explicit inductive proof for power addition law.
\<close>

lemma power_add_inductive:
  shows "n ^ (m + p) = n ^ m * n ^ p"
proof (induction m)
  case 0
  show ?case by simp
next
  case (Suc m)
  have "n ^ (Suc m + p) = n ^ Suc (m + p)"
    by simp
  also have "... = n * n ^ (m + p)"
    by simp
  also have "... = n * (n ^ m * n ^ p)"
    using Suc.IH by simp
  also have "... = (n * n ^ m) * n ^ p"
    by simp
  also have "... = n ^ Suc m * n ^ p"
    by simp
  finally show ?case .
qed

section \<open>Ordering Properties\<close>

text \<open>
  Less than or equal is reflexive, transitive, and antisymmetric.
\<close>

lemma le_refl:
  "n \<le> n"
  by simp

lemma le_trans:
  "m \<le> n \<Longrightarrow> n \<le> p \<Longrightarrow> m \<le> p"
  by simp

lemma le_antisym:
  "m \<le> n \<Longrightarrow> n \<le> m \<Longrightarrow> m = n"
  by simp

text \<open>
  Strict ordering properties.
\<close>

lemma less_irrefl:
  "\<not>(n < n)"
  by simp

lemma less_trans:
  "m < n \<Longrightarrow> n < p \<Longrightarrow> m < p"
  by simp

lemma less_imp_le:
  "m < n \<Longrightarrow> m \<le> n"
  by simp

text \<open>
  Successor properties.
\<close>

lemma suc_greater:
  "n < Suc n"
  by simp

lemma suc_le_eq:
  "Suc m \<le> Suc n \<longleftrightarrow> m \<le> n"
  by simp

lemma suc_less_eq:
  "Suc m < Suc n \<longleftrightarrow> m < n"
  by simp

section \<open>Addition and Ordering\<close>

text \<open>
  Addition preserves ordering.
\<close>

lemma add_le_mono:
  "m \<le> n \<Longrightarrow> m + p \<le> n + p"
  by simp

lemma add_less_mono:
  "m < n \<Longrightarrow> m + p < n + p"
  by simp

text \<open>
  Cancellation laws for addition.
\<close>

lemma add_left_cancel:
  "p + m = p + n \<longleftrightarrow> m = n"
  by simp

lemma add_right_cancel:
  "m + p = n + p \<longleftrightarrow> m = n"
  by simp

section \<open>Division and Modulo\<close>

text \<open>
  Basic properties of division and modulo.
\<close>

lemma div_mult_self:
  "n > 0 \<Longrightarrow> (m * n) div n = m"
  by simp

lemma mod_mult_self:
  "n > 0 \<Longrightarrow> (m * n) mod n = 0"
  by simp

lemma div_less:
  "m < n \<Longrightarrow> n > 0 \<Longrightarrow> m div n = 0"
  by simp

lemma mod_less:
  "m < n \<Longrightarrow> n > 0 \<Longrightarrow> m mod n = m"
  by simp

text \<open>
  Division-modulo identity.
\<close>

lemma div_mod_equality:
  "n > 0 \<Longrightarrow> (m div n) * n + m mod n = m"
  by simp

section \<open>Even and Odd\<close>

text \<open>
  Definition and properties of even numbers.
\<close>

lemma even_zero:
  "even 0"
  by simp

lemma even_double:
  "even (2 * n)"
  by simp

lemma even_succ_succ:
  "even n \<longleftrightarrow> even (Suc (Suc n))"
  by simp

text \<open>
  Sum of two even numbers is even.
\<close>

lemma even_add:
  "even m \<Longrightarrow> even n \<Longrightarrow> even (m + n)"
  by simp

text \<open>
  Product involving an even number is even.
\<close>

lemma even_mult:
  "even m \<or> even n \<Longrightarrow> even (m * n)"
  by auto

section \<open>Strong Induction\<close>

text \<open>
  Example of strong induction (course-of-values induction).
  We prove that every number >= 2 can be expressed as a product of primes.
  This is a simplified version demonstrating the principle.
\<close>

lemma strong_induction_example:
  assumes "\<And>n. (\<forall>m. m < n \<longrightarrow> P m) \<Longrightarrow> P n"
  shows "P n"
proof -
  have "\<forall>m. m \<le> n \<longrightarrow> P m"
  proof (induction n)
    case 0
    show ?case using assms by simp
  next
    case (Suc n)
    show ?case
    proof (intro allI impI)
      fix m
      assume "m \<le> Suc n"
      show "P m"
      proof (cases "m \<le> n")
        case True
        then show ?thesis using Suc.IH by simp
      next
        case False
        then have "m = Suc n" using \<open>m \<le> Suc n\<close> by simp
        moreover have "P (Suc n)"
          using assms[of "Suc n"] Suc.IH by simp
        ultimately show ?thesis by simp
      qed
    qed
  qed
  then show ?thesis by simp
qed

end
