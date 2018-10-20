---
layout: post
title:  "Kitty Grundman's self referential puzzle"
date:   2018-10-22
---

Linked from [James Propp's self-referential aptitude test]({% post_url
2018-10-21-self-referential-aptitude-test %}) is [another delightfully
self-referential puzzle attributed to Kitty
Grundman](http://faculty.uml.edu/jpropp/kitty.txt), [Helen
Grundman](https://www.brynmawr.edu/people/helen-g-grundman)'s cat:

----

Below are ten statements concerning X, a whole number between 1 and 10
(inclusive).  Not all of the statements are true, but not all of them are false
either.  What number is X?

1. X equals the sum of the statement numbers of the false statements in this
list.

2. X is less than the number of false statements in this list, and statement 10
is true.

3. There are exactly three true statements in this list, or statement 1 is
false, but not both.

4. The previous three statements are all false, or statement 9 is true, or
both.

5. Either X is odd, or statement 7 is true, but not both.

6. Exactly two of the odd-numbered statements are false.

7. X is the number of a true statement.

8. The even-numbered statements are either all true or all false.

9. X equals three times the statement number of the first true statement in
this list, or statement 4 is false, or both.

10. X is even, or statement 6 is true, or both.

----

**There's spoilers throughout this article**, so you should stop reading now if
you want to try this puzzle yourself instead.

The killer feature here is the fact that we don't even know which statements
are true up front, and this gets deeply confusing and makes it very difficult
to see what the next step might be. A perfect opportunity for formalisation.
Although it doesn't say so, it turns out that the truth or falsehood of each
statement is uniquely determined too.

## Modelling the puzzle

We start by defining the set of statement numbers.

    definition statementNumber :: "nat set" where "statementNumber ≡ {1..10}"

It's occasionally handy to be able to do a case split on a statement number,
which this lemma enables.

    lemma statementNumber_cases[consumes 1]:
      assumes q: "n ∈ statementNumber"
      assumes "n = 1 ⟹ P"
      assumes "n = 2 ⟹ P"
      assumes "n = 3 ⟹ P"
      assumes "n = 4 ⟹ P"
      assumes "n = 5 ⟹ P"
      assumes "n = 6 ⟹ P"
      assumes "n = 7 ⟹ P"
      assumes "n = 8 ⟹ P"
      assumes "n = 9 ⟹ P"
      assumes "n = 10 ⟹ P"
      shows P
    proof -
      note q
      also have "statementNumber = set [1..<11]" unfolding atLeastAtMost_upt statementNumber_def by simp
      also have "… = set [1,2,3,4,5,6,7,8,9,10]"
        apply (intro cong [OF refl, where f = set])
        by (simp add: upt_rec)
      finally show P using assms by auto
    qed

It's also useful later on to have a type that comprises just the valid
statement numbers.

    typedef Statement = statementNumber unfolding statementNumber_def by auto

The puzzle itself is defined in a locale, which starts by introducing the two
free variables in the problem:

    locale Kitty =
      fixes X :: nat
      assumes X_bounds: "1 ≤ X" "X ≤ 10"
      fixes isTrueStatement :: "Statement ⇒ bool"

It's a lot more useful to be able to talk about the truth of statements
directly in terms of their numbers so we also define some helper functions:

      fixes isTrue :: "nat ⇒ bool"
      defines "isTrue ≡ isTrueStatement ∘ Abs_Statement"
      fixes isFalse :: "nat ⇒ bool"
      defines "isFalse ≡ (op = False) ∘ isTrue"
      fixes trueStatements :: "nat set"
      defines "trueStatements ≡ {n ∈ statementNumber. isTrue n}"
      fixes falseStatements :: "nat set"
      defines "falseStatements ≡ {n ∈ statementNumber. isFalse n}"

The preamble to the puzzle tells us that `trueStatements` and `falseStatements`
are nonempty but in fact we do not need this information so it's omitted from
the model. The statements themselves follow.

        (* 1. X equals the sum of the statement numbers of the false statements in this list. *)
      assumes s1: "isTrue 1 = (X = ∑falseStatements)"
        (* 2. X is less than the number of false statements in this list, and statement 10 is true. *)
      assumes s2: "isTrue 2 = (X < card falseStatements ∧ isTrue 10)"
        (* 3. There are exactly three true statements in this list, or statement 1 is false, but not both. *)
      assumes s3: "isTrue 3 = ((card trueStatements = 3) ≠ (isFalse 1))"
        (* 4. The previous three statements are all false, or statement 9 is true, or both. *)
      assumes s4: "isTrue 4 = ({1,2,3} ⊆ falseStatements ∨ isTrue 9)"
        (* 5. Either X is odd, or statement 7 is true, but not both. *)
      assumes s5: "isTrue 5 = (odd X ≠ isTrue 7)"
        (* 6. Exactly two of the odd-numbered statements are false. *)
      assumes s6: "isTrue 6 = (card (falseStatements ∩ Collect odd) = 2)"
        (* 7. X is the number of a true statement. *)
      assumes s7: "isTrue 7 = isTrue X"
        (* 8. The even-numbered statements are either all true or all false. *)
      assumes s8: "isTrue 8 = (falseStatements ∩ Collect even = {} ∨ trueStatements ∩ Collect even = {})"
        (* 9. X equals three times the statement number of the first true statement in this list, or statement 4 is false, or both. *)
      assumes s9: "isTrue 9 = (X = 3 * (LEAST n. n ∈ trueStatements) ∨ isFalse 4)"
        (* 10. X is even, or statement 6 is true, or both. *)
      assumes s10: "isTrue 10 = (even X ∨ isTrue 6)"

This is mostly straightforward but there are a couple of things worth pointing
out. Firstly, two of the statements are of the form "A or B but not both", i.e.
an exclusive disjunction, which is written `≠`. This wasn't obvious to me at
first but it makes sense if you draw some truth tables.  Secondly, `Collect
even` means the same as `{n. even n}`; writing `falseStatements ∩ Collect even`
instead of `{n.  isFalse n ∧ even n}` seemed to play more nicely with the proof
automation.

## Solving the puzzle

We start with some basic statements about cardinalities:

    lemma card_statementNumber: "card statementNumber = 10"
    proof -
      have p: "statementNumber = {1,2,3,4,5,6,7,8,9,10}"
      proof (intro cong [OF refl, where f = card] subsetI equalityI)
        fix x assume "x ∈ statementNumber" thus "x ∈ {1,2,3,4,5,6,7,8,9,10}" by (cases rule: statementNumber_cases, auto)
      qed (auto simp add: statementNumber_def)
      show ?thesis unfolding p by simp
    qed

    lemma card_trueFalse: "card trueStatements + card falseStatements = 10"
    proof -
      have "card statementNumber = card (trueStatements ∪ falseStatements)"
        by (intro cong [OF refl, where f = card], auto simp add: falseStatements_def trueStatements_def isFalse_def)
      also have "… = card trueStatements + card falseStatements"
        by (intro card_Un_disjoint, auto simp add: trueStatements_def falseStatements_def isFalse_def statementNumber_def)
      finally show ?thesis using card_statementNumber by simp
    qed

The first step of the puzzle is quite straightforward: if statement 4 is false
then statement 9 is true, which implies that statement 4 is true, a
contradiction. Therefore statement 4 must be true:

    lemma true4: "isTrue 4"
    proof (cases "isTrue 4")
      case False
      hence "isFalse 4" by (simp add: isFalse_def)
      with s9 have "isTrue 9" by simp
      with s4 show "isTrue 4" by simp
    qed simp

Statement 9 discusses the lowest-numbered true statement, and since we have
found a true statement we know that the lowest-numbered one is well-defined:

    lemma leastTrue: "(LEAST n. n ∈ trueStatements) ∈ trueStatements"
    proof -
      from true4 have "4 ∈ trueStatements" by (auto simp add: trueStatements_def statementNumber_def)
      thus ?thesis by (intro LeastI)
    qed

The next step is a bit of a pig, but it turns out that we can now show that
statement 2 is false. The proof is by contradiction and runs as follows.
Suppose statement 2 were true. Then:

- statement 10 is true.
- statement 4 (already known to be true) tells us that statement 9 is true.
- statement 9 tells us that X is 3 or 6 since the first true statement is
  either 1 or 2.
- if X were 6 then according to statement 2 there are ≥ 7 false statements in
  the list; however we have found 4 true statements (2, 4, 9 and 10) so this
  cannot be; therefore X is 3 and the first true statement is 1.
- statement 1 tells us that X (i.e. 3) is the sum of the numbers of the false
  statements; statements 1 and 2 are true which means that the only false
  statement can be number 3.
- this means that in particular statement 7 is true, which says that statement
  3 is true, which is a contradiction 🎉

Here's the formal version of this argument:

    lemma false2: "isFalse 2"
    proof (rule ccontr)
      assume "¬ ?thesis"
      hence true2: "isTrue 2" by (auto simp add: isFalse_def)

      with s4 true2 true4 have true9: "isTrue 9" by (auto simp add: falseStatements_def isFalse_def)
      with s9 true4 have X_3_min: "X = 3 * (LEAST n. n ∈ trueStatements)" by (simp add: isFalse_def)

      from s2 true2 have true10: "isTrue 10" by simp

      from true2 have "(LEAST n. n ∈ trueStatements) ≤ 2"
        by (intro Least_le, simp add: trueStatements_def statementNumber_def)

      with leastTrue have "(LEAST n. n ∈ trueStatements) ∈ {1,2}" by (auto simp add: trueStatements_def statementNumber_def)
      hence least1: "(LEAST n. n ∈ trueStatements) = 1"
      proof (elim insertE)
        assume 2: "(LEAST n. n ∈ trueStatements) = 2"
        with X_3_min true2 s2 have "6 < card falseStatements" by simp
        also have "… = 10 - card trueStatements" using card_trueFalse by simp
        also have "… ≤ 10 - card {2,4,9,10::nat}"
          using true2 true4 true9 true10 by (intro diff_le_mono2 card_mono, auto simp add: trueStatements_def statementNumber_def)
        also have "… = 6" by simp
        finally show ?thesis by simp
      qed simp_all
      from X_3_min least1 have X3: "X = 3" by simp
      from least1 leastTrue have true1: "isTrue 1" by (simp add: trueStatements_def)

      have falseStatements_3: "falseStatements ⊆ {3}"
      proof (intro subsetI)
        fix f assume f: "f ∈ falseStatements"
        from true1 s1 X3 have "3 = sum id falseStatements" by simp
        also from f have "… = sum id (insert f falseStatements)" by (intro cong [OF refl, where f = "sum id"], auto)
        also have "… = id f + sum id (falseStatements - {f})" by (intro sum.insert_remove, auto simp add: falseStatements_def statementNumber_def)
        also have "… ≥ f" by simp
        finally have f3: "f ≤ 3" .
        from f have "f ∈ statementNumber" "isFalse f" unfolding falseStatements_def by auto
        from this f3 true1 true2 show "f ∈ {3}" by (cases rule: statementNumber_cases, auto simp add: isFalse_def)
      qed
      hence trueNot3: "⋀n. n ∈ statementNumber ⟹ n ≠ 3 ⟹ isTrue n"
        by (auto simp add: falseStatements_def isFalse_def statementNumber_def)
      have "isTrue 7" by (intro trueNot3, auto simp add: statementNumber_def)
      with s7 X3 have true3: "isTrue 3" by simp

      from s2 true2 X_bounds have "card falseStatements ≠ 0" by simp
      then obtain f where f: "f ∈ falseStatements" by (cases "falseStatements = {}", auto)
      with falseStatements_3 have "f = 3" by auto
      with f true3 show False by (auto simp add: falseStatements_def isFalse_def)
    qed

Phew. After this we get a few easy wins. Firstly, statement 8 is false because
we've found even-numbered statements that are both true and false:

    lemma false8: "isFalse 8"
    proof (rule ccontr)
      assume "¬ isFalse 8" hence true8: "isTrue 8" by (simp add: isFalse_def)
      moreover from false2 have "2 ∈ falseStatements ∩ Collect even" by (auto simp add: falseStatements_def statementNumber_def)
      moreover from true4 have "4 ∈ trueStatements ∩ Collect even" by (auto simp add: trueStatements_def statementNumber_def)
      ultimately show False using s8 by auto
    qed

This lets us deduce that statement 1 cannot be true, because if it were true
then X ≤ 10 would be equal to the sum of the numbers of the false statements; 2
and 8 are both false and add up to 10, so all the other statements are true.
This contradicts all sorts of things, for instance statement 6 (also statements
3 and 9) so we know that the first statement is false:

    lemma false1: "isFalse 1"
    proof (rule ccontr)
      assume "¬ isFalse 1" hence true1: "isTrue 1" by (simp add: isFalse_def)
      with s1 have "X = sum id falseStatements" by simp
      also from false8 have "… = sum id (insert 8 falseStatements)"
        by (intro cong [OF refl, where f = "sum id"], auto simp add: falseStatements_def statementNumber_def)
      also have "… = id 8 + sum id (falseStatements - {8})"
        by (intro sum.insert_remove, auto simp add: falseStatements_def statementNumber_def)
      finally have lt2: "∑ (falseStatements - {8}) ≤ 2" using X_bounds by simp

      have finf: "finite falseStatements" by (auto simp add: falseStatements_def statementNumber_def)

      note true1
      with s1 have "X = sum id falseStatements" by simp
      also from false2 false8 have "… = sum id (insert 2 (insert 8 falseStatements))"
        by (intro cong [OF refl, where f = "sum id"], auto simp add: falseStatements_def statementNumber_def)
      also have "… = id 2 + sum id (insert 8 falseStatements - {2})"
        using finf by (intro sum.insert_remove, auto)
      also have "… = id 2 + sum id (insert 8 (falseStatements - {2}))"
        by (intro cong [OF refl, where f = "op + (id 2)"] cong [OF refl, where f = "sum id"], auto)
      also have "… = id 2 + (id 8 + sum id (falseStatements - {2} - {8}))"
        using finf by (intro cong [OF refl sum.insert_remove, where f = "op + (id 2)"], auto)
      also have "… = 10 + sum id (falseStatements - {2} - {8})" by simp
      finally have "sum id (falseStatements - {2} - {8}) = 0" using X_bounds by simp
      with finf have "∀n ∈ (falseStatements - {2} - {8}). id n = 0"
        by (intro iffD1 [OF sum_eq_0_iff], auto)
      with false2 false8 have onlyFalse: "falseStatements = {2,8}" by (auto simp add: falseStatements_def statementNumber_def)

      have "isFalse 6" by (simp add: isFalse_def s6 onlyFalse)
      hence "6 ∈ falseStatements" by (simp add: falseStatements_def statementNumber_def)
      with onlyFalse show False by simp
    qed

The next step took quite some exploration, but it now turns out we can work out
the truth of statement 3 as follows.

Suppose for a contradiction that statement 3 were false. Since we know that
statement 1 is also false this means that (with a bit of boolean algebra) there
are exactly three true statements in the list. Also statement 9 must be false
since the first true statement in the list is at least statement 4, which is
too large. This means there are at least three odd-numbered false statements
(1, 3 and 9) which means that statement 6 is also false. The remaining
statements are numbers 5, 7 and 10:

        (* 5. Either X is odd, or statement 7 is true, but not both. *)
      assumes s5: "isTrue 5 = (odd X ≠ isTrue 7)"
        (* 7. X is the number of a true statement. *)
      assumes s7: "isTrue 7 = isTrue X"
        (* 10. X is even, or statement 6 is true, or both. *)
      assumes s10: "isTrue 10 = (even X ∨ isTrue 6)"

We can simplify these a bit: since statement 6 is false, statement 10 is just
"X is even", and this means that

    isTrue 5 = (even X    = isTrue 7)
             = (isTrue 10 = isTrue 7).

The equality signs here are really bi-implications, which is an associative and
commutative operation, so we could just as well write this:

    isTrue 5 = isTrue 7 = isTrue 10

However a chain of bi-implications like this is a pretty weird operation: in
general an expression like

    A = B = C = ... = Z

is true iff it has an even number of false components. Since in this case we
have three components, this means that an odd number of them must be true. The
only other true statement is number 4, so all told this means that there is an
even number of true statements in the list. But we already knew that there are
three true statements in the list, which is odd, giving us a contradiction.
Hurrah! 🎉 Formally:

    lemma true3: "isTrue 3"
    proof (rule ccontr)
      assume "¬ isTrue 3" hence false3: "isFalse 3" by (simp add: isFalse_def)
      from false3 false1 s3 have threeTruths: "card trueStatements = 3" by (simp add: isFalse_def)
      from leastTrue have
        "(LEAST n. n ∈ trueStatements) ∈ statementNumber"
        "isTrue (LEAST n. n ∈ trueStatements)"
        by (auto simp add: trueStatements_def)
      from this false1 false2 false3 have "4 ≤ (LEAST n. n ∈ trueStatements)"
        by (cases rule: statementNumber_cases, auto simp add: isFalse_def)
      with s9 true4 X_bounds have false9: "isFalse 9" by (auto simp add: isFalse_def)

      have "3 = card {1,3,9::nat}" by simp
      also from false1 false3 false9 have "… ≤ card (falseStatements ∩ {a. odd a})"
        by (intro card_mono, auto simp add: falseStatements_def statementNumber_def)
      finally have false6: "isFalse 6" using s6 by (auto simp add: isFalse_def)

      note known = false1 false2 false3 true4 false6 false8 false9
      define whenTrue :: "nat ⇒ nat set" where "⋀n. whenTrue n ≡ {n} ∩ (if isTrue n then UNIV else {})"

      have ts: "trueStatements = (whenTrue 5) ∪ (whenTrue 7) ∪ (whenTrue 10) ∪ {4}"
        (is "?LHS = ?RHS")
      proof (intro equalityI subsetI)
        fix n assume "n ∈ ?LHS" hence "n ∈ statementNumber" "isTrue n" by (auto simp add: trueStatements_def)
        from this known show "n ∈ ?RHS"
          by (cases rule: statementNumber_cases, auto simp add: trueStatements_def statementNumber_def isFalse_def whenTrue_def)
      next
        fix n assume "n ∈ ?RHS" with true4 show "n ∈ ?LHS"
          apply (cases "isTrue 5", auto simp add: trueStatements_def statementNumber_def whenTrue_def)
          by (meson empty_iff)+
      qed

      from s5 s10 false6 have "isTrue 5 = isTrue 7 = isTrue 10" by (auto simp add: isFalse_def)
      then consider
        (5) "isTrue 5" "isFalse 7" "isFalse 10"
        | (7) "isFalse 5" "isTrue 7" "isFalse 10"
        | (10) "isFalse 5" "isFalse 7" "isTrue 10"
        | (all) "isTrue 5" "isTrue 7" "isTrue 10" by (auto simp add: isFalse_def)
      hence "even (card trueStatements)"
        unfolding ts by (cases, auto simp add: whenTrue_def isFalse_def)

      with threeTruths show False by simp
    qed

This means that the first disjunct of statement 4 is false, so the second is
true:

    lemma true9: "isTrue 9"
      using true3 true4 false1 false2 s4 by (auto simp add: falseStatements_def isFalse_def)

And statement 9 tells us what X is:

    lemma X9: "X = 9"
    proof -
      from true9 true4 s9 have X_3_least: "X = 3 * (LEAST n. n ∈ trueStatements)" by (simp add: isFalse_def)

      from leastTrue have
        "(LEAST n. n ∈ trueStatements) ∈ statementNumber"
        "isTrue (LEAST n. n ∈ trueStatements)"
        by (auto simp add: trueStatements_def)
      moreover from true3 have "(LEAST n. n ∈ trueStatements) ≤ 3"
        by (intro Least_le, auto simp add: trueStatements_def statementNumber_def)
      ultimately have "(LEAST n. n ∈ trueStatements) = 3" using false1 false2
        by (cases rule: statementNumber_cases, auto simp add: isFalse_def)
      with X_3_least show X9: "X = 9" by simp
    qed

From this point on it's quite simple to resolve the truths of the remaining
statements:

    lemma true7: "isTrue 7" using X9 true9 s7 by simp
    lemma false5: "isFalse 5" using X9 true7 s5 by (simp add: isFalse_def)

    lemma true6: "isTrue 6"
    proof -
      have "falseStatements ∩ Collect odd = {1,5}"
      proof (intro equalityI subsetI)
        fix n::nat assume "n ∈ {1,5}"
        with false1 false5 show "n ∈ falseStatements ∩ {a. odd a}"
          by (auto simp add: falseStatements_def statementNumber_def)
      next
        fix n assume "n ∈ falseStatements ∩ {a. odd a}"
        hence "n ∈ statementNumber" "isFalse n" "odd n" by (auto simp add: falseStatements_def)
        from this true3 true7 true9 show "n ∈ {1,5}"
          by (cases rule: statementNumber_cases, auto simp add: isFalse_def)
      qed
      with s6 show "isTrue 6" by auto
    qed

    lemma true10: "isTrue 10" using s10 true6 by simp

It remains to validate that this solution really does satisfy the problem
statement, and that the whole puzzle didn't contain a contradiction. We do this
by showing that we have really found a model for this locale:

    definition solvedTrueStatement :: "Statement ⇒ bool"
      where "solvedTrueStatement s ≡ Rep_Statement s ∈ {3,4,6,7,9,10}"

    lemma "Kitty 9 solvedTrueStatement"
    proof -
      have "(LEAST n. n ∈ {3, 4, 6, 7, 9, 10}) = (3::nat)" by (intro Least_equality, auto)

      moreover have p: "⋀n. 1 ≤ n ⟹ n ≤ 10 ⟹ (solvedTrueStatement ∘ Abs_Statement) n = (n ∈ {3,4,6,7,9,10})"
      proof -
        fix n::nat assume "1 ≤ n" "n ≤ 10" hence "n ∈ statementNumber" by (simp add: statementNumber_def)
        from Abs_Statement_inverse [OF this] show "(solvedTrueStatement ∘ Abs_Statement) n = (n ∈ {3,4,6,7,9,10})"
          by (simp add: solvedTrueStatement_def)
      qed

      hence
        "(solvedTrueStatement ∘ Abs_Statement) 8  = False"
        "{n ∈ statementNumber. (solvedTrueStatement ∘ Abs_Statement) n} = {3,4,6,7,9,10}"
        by (auto simp add: statementNumber_def)

      moreover have "{n ∈ statementNumber. (op = False ∘ (solvedTrueStatement ∘ Abs_Statement)) n} = {1,2,5,8}"
        using p
      proof (intro equalityI subsetI)
        fix x assume a: "x ∈ {n ∈ statementNumber. (op = False ∘ (solvedTrueStatement ∘ Abs_Statement)) n}"
        hence "x ∈ statementNumber" by simp
        from this a p show "x ∈ {1,2,5,8}" by (cases rule: statementNumber_cases, auto)
      qed (auto simp add: statementNumber_def)

      ultimately show ?thesis apply unfold_locales by auto
    qed

Finally, we can show that the solution is unique:

    lemma (in Kitty) "isTrueStatement = solvedTrueStatement"
    proof (intro ext)
      fix x
      have "isTrueStatement x = isTrue (Rep_Statement x)"
        by (simp add: isTrue_def Rep_Statement_inverse)

      also from Rep_Statement [of x] false1 false2 true3 true4 false5 true6 true7 false8 true9 true10
      have "isTrue (Rep_Statement x) = solvedTrueStatement x"
        by (cases rule: statementNumber_cases, auto simp add: solvedTrueStatement_def isFalse_def)

      finally show "isTrueStatement x = solvedTrueStatement x".
    qed

## Conclusion

Somewhat surprisingly, we didn't need to know that there was at least one true
and at least one false statement in the list; moreover we didn't need to work
out the truth of every statement in order to find X. Despite this, there is in
fact only one way to assign the truths of the statements. I found there to be a
couple of very tricky steps along the way, in which you had to follow a chain
of reasoning for quite some distance before it yielded a contradiction. It was
often hard to see which path to take next, and it was fun to explore all the
possibilities.

I'm impressed by how well-crafted this puzzle is. It all fits together very
elegantly.

