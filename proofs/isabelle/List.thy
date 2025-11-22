(*
  List.thy - List Proofs in Isabelle/HOL

  This theory demonstrates reasoning about lists:
  - Append properties
  - Length properties
  - Map, filter, and other list functions
  - Induction on lists
  - Structural properties

  Part of the ECHIDNA theorem proving platform
  Tier 1 Prover: Isabelle/HOL
*)

theory List
  imports Main
begin

section \<open>Basic List Properties\<close>

text \<open>
  Lists are defined inductively:
  - [] is the empty list
  - x # xs is a list with head x and tail xs
\<close>

lemma empty_list_length:
  "length [] = 0"
  by simp

lemma cons_length:
  "length (x # xs) = Suc (length xs)"
  by simp

section \<open>Append Properties\<close>

text \<open>
  Append is written as @ in Isabelle.
  It concatenates two lists.
\<close>

lemma append_nil_left:
  "[] @ xs = xs"
  by simp

lemma append_nil_right:
  "xs @ [] = xs"
  by simp

text \<open>
  Append is associative.
\<close>

lemma append_assoc:
  "(xs @ ys) @ zs = xs @ (ys @ zs)"
  by simp

text \<open>
  Explicit inductive proof of right identity for append.
\<close>

lemma append_nil_right_inductive:
  shows "xs @ [] = xs"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have "(x # xs) @ [] = x # (xs @ [])"
    by simp
  also have "... = x # xs"
    using Cons.IH by simp
  finally show ?case .
qed

text \<open>
  Append and cons relationship.
\<close>

lemma append_cons:
  "xs @ (y # ys) = (xs @ [y]) @ ys"
  by simp

lemma cons_append:
  "(x # xs) @ ys = x # (xs @ ys)"
  by simp

section \<open>Length Properties\<close>

text \<open>
  Length of append is sum of lengths.
\<close>

lemma length_append:
  "length (xs @ ys) = length xs + length ys"
  by simp

text \<open>
  Explicit inductive proof.
\<close>

lemma length_append_inductive:
  shows "length (xs @ ys) = length xs + length ys"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have "length ((x # xs) @ ys) = length (x # (xs @ ys))"
    by simp
  also have "... = Suc (length (xs @ ys))"
    by simp
  also have "... = Suc (length xs + length ys)"
    using Cons.IH by simp
  also have "... = Suc (length xs) + length ys"
    by simp
  also have "... = length (x # xs) + length ys"
    by simp
  finally show ?case .
qed

text \<open>
  Length equals zero iff list is empty.
\<close>

lemma length_zero_iff_nil:
  "length xs = 0 \<longleftrightarrow> xs = []"
  by simp

lemma length_positive_iff_cons:
  "length xs > 0 \<longleftrightarrow> (\<exists>y ys. xs = y # ys)"
  by (cases xs; simp)

section \<open>Map Function\<close>

text \<open>
  Map applies a function to every element of a list.
\<close>

lemma map_nil:
  "map f [] = []"
  by simp

lemma map_cons:
  "map f (x # xs) = f x # map f xs"
  by simp

text \<open>
  Map preserves length.
\<close>

lemma length_map:
  "length (map f xs) = length xs"
  by simp

text \<open>
  Map composition: mapping twice is the same as mapping the composition.
\<close>

lemma map_compose:
  "map f (map g xs) = map (f \<circ> g) xs"
  by simp

text \<open>
  Map and append commute.
\<close>

lemma map_append:
  "map f (xs @ ys) = map f xs @ map f ys"
  by simp

text \<open>
  Explicit inductive proof.
\<close>

lemma map_append_inductive:
  shows "map f (xs @ ys) = map f xs @ map f ys"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have "map f ((x # xs) @ ys) = map f (x # (xs @ ys))"
    by simp
  also have "... = f x # map f (xs @ ys)"
    by simp
  also have "... = f x # (map f xs @ map f ys)"
    using Cons.IH by simp
  also have "... = (f x # map f xs) @ map f ys"
    by simp
  also have "... = map f (x # xs) @ map f ys"
    by simp
  finally show ?case .
qed

text \<open>
  Identity map.
\<close>

lemma map_ident:
  "map (\<lambda>x. x) xs = xs"
  by simp

section \<open>Reverse Function\<close>

text \<open>
  Reverse reverses the order of list elements.
\<close>

lemma rev_nil:
  "rev [] = []"
  by simp

lemma rev_cons:
  "rev (x # xs) = rev xs @ [x]"
  by simp

text \<open>
  Reverse is involutive (reversing twice gives the original).
\<close>

lemma rev_rev:
  "rev (rev xs) = xs"
  by simp

text \<open>
  Reverse and append.
\<close>

lemma rev_append:
  "rev (xs @ ys) = rev ys @ rev xs"
  by simp

text \<open>
  Length is preserved by reverse.
\<close>

lemma length_rev:
  "length (rev xs) = length xs"
  by simp

text \<open>
  Map and reverse commute.
\<close>

lemma map_rev:
  "map f (rev xs) = rev (map f xs)"
  by simp

section \<open>Filter Function\<close>

text \<open>
  Filter keeps only elements satisfying a predicate.
\<close>

lemma filter_nil:
  "filter P [] = []"
  by simp

lemma filter_cons_true:
  "P x \<Longrightarrow> filter P (x # xs) = x # filter P xs"
  by simp

lemma filter_cons_false:
  "\<not>P x \<Longrightarrow> filter P (x # xs) = filter P xs"
  by simp

text \<open>
  Filter and append.
\<close>

lemma filter_append:
  "filter P (xs @ ys) = filter P xs @ filter P ys"
  by simp

text \<open>
  Filtering with a constant true predicate.
\<close>

lemma filter_true:
  "filter (\<lambda>x. True) xs = xs"
  by simp

text \<open>
  Filtering with a constant false predicate.
\<close>

lemma filter_false:
  "filter (\<lambda>x. False) xs = []"
  by simp

text \<open>
  Length of filtered list is at most original length.
\<close>

lemma length_filter_le:
  "length (filter P xs) \<le> length xs"
  by simp

section \<open>Take and Drop\<close>

text \<open>
  Take and drop split a list at a given position.
\<close>

lemma take_nil:
  "take n [] = []"
  by simp

lemma drop_nil:
  "drop n [] = []"
  by simp

text \<open>
  Take and drop complement each other.
\<close>

lemma take_drop_append:
  "take n xs @ drop n xs = xs"
  by simp

text \<open>
  Length properties.
\<close>

lemma length_take:
  "length (take n xs) = min n (length xs)"
  by simp

lemma length_drop:
  "length (drop n xs) = length xs - n"
  by simp

section \<open>Membership and Element Access\<close>

text \<open>
  List membership.
\<close>

lemma in_nil:
  "x \<in> set [] \<longleftrightarrow> False"
  by simp

lemma in_cons:
  "x \<in> set (y # ys) \<longleftrightarrow> x = y \<or> x \<in> set ys"
  by simp

text \<open>
  Membership and append.
\<close>

lemma in_append:
  "x \<in> set (xs @ ys) \<longleftrightarrow> x \<in> set xs \<or> x \<in> set ys"
  by simp

text \<open>
  Membership is preserved by reverse.
\<close>

lemma in_rev:
  "x \<in> set (rev xs) \<longleftrightarrow> x \<in> set xs"
  by simp

text \<open>
  If all elements satisfy P and x is in the list, then P x.
\<close>

lemma all_in_set:
  assumes "x \<in> set xs" and "\<forall>y \<in> set xs. P y"
  shows "P x"
  using assms by simp

section \<open>Fold Functions\<close>

text \<open>
  Left fold (foldl) and right fold (foldr).
\<close>

lemma foldl_nil:
  "foldl f acc [] = acc"
  by simp

lemma foldl_cons:
  "foldl f acc (x # xs) = foldl f (f acc x) xs"
  by simp

lemma foldr_nil:
  "foldr f [] acc = acc"
  by simp

lemma foldr_cons:
  "foldr f (x # xs) acc = f x (foldr f xs acc)"
  by simp

text \<open>
  Foldr and append.
\<close>

lemma foldr_append:
  "foldr f (xs @ ys) acc = foldr f xs (foldr f ys acc)"
  by simp

section \<open>List Induction Examples\<close>

text \<open>
  Sum of list elements (using foldr).
\<close>

definition sum_list :: "nat list \<Rightarrow> nat" where
  "sum_list xs = foldr (+) xs 0"

lemma sum_nil:
  "sum_list [] = 0"
  unfolding sum_list_def by simp

lemma sum_cons:
  "sum_list (x # xs) = x + sum_list xs"
  unfolding sum_list_def by simp

lemma sum_append:
  "sum_list (xs @ ys) = sum_list xs + sum_list ys"
proof (induction xs)
  case Nil
  show ?case
    unfolding sum_list_def by simp
next
  case (Cons x xs)
  have "sum_list ((x # xs) @ ys) = sum_list (x # (xs @ ys))"
    by simp
  also have "... = x + sum_list (xs @ ys)"
    by (simp add: sum_cons)
  also have "... = x + (sum_list xs + sum_list ys)"
    using Cons.IH by simp
  also have "... = (x + sum_list xs) + sum_list ys"
    by simp
  also have "... = sum_list (x # xs) + sum_list ys"
    by (simp add: sum_cons)
  finally show ?case .
qed

text \<open>
  Length using foldr.
\<close>

lemma length_as_foldr:
  "length xs = foldr (\<lambda>x n. Suc n) xs 0"
  by (induction xs; simp)

text \<open>
  Map using foldr.
\<close>

lemma map_as_foldr:
  "map f xs = foldr (\<lambda>x ys. f x # ys) xs []"
  by (induction xs; simp)

section \<open>List Comprehension Properties\<close>

text \<open>
  Concat flattens a list of lists.
\<close>

lemma concat_nil:
  "concat [] = []"
  by simp

lemma concat_cons:
  "concat (xs # xss) = xs @ concat xss"
  by simp

lemma concat_append:
  "concat (xss @ yss) = concat xss @ concat yss"
  by simp

text \<open>
  Length of concat.
\<close>

lemma length_concat:
  "length (concat xss) = sum_list (map length xss)"
  by (induction xss; simp add: sum_list_def)

section \<open>All and Exists\<close>

text \<open>
  Universal quantification over lists.
\<close>

lemma list_all_nil:
  "list_all P []"
  by simp

lemma list_all_cons:
  "list_all P (x # xs) \<longleftrightarrow> P x \<and> list_all P xs"
  by simp

text \<open>
  Existential quantification over lists.
\<close>

lemma list_ex_nil:
  "\<not>list_ex P []"
  by simp

lemma list_ex_cons:
  "list_ex P (x # xs) \<longleftrightarrow> P x \<or> list_ex P xs"
  by simp

text \<open>
  Relationship between list_all and filter.
\<close>

lemma list_all_filter:
  "list_all P xs \<longleftrightarrow> filter P xs = xs"
  by (induction xs; auto)

end
