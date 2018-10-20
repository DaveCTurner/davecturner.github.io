---
layout: post
title:  "The self-referential aptitude test"
date:   2018-10-21
---

I stumbled across [James Propp's self-referential aptitude
test](http://faculty.uml.edu/jpropp/srat-Q.txt) the other day and thought it'd
be fun to formalise it and its solution in
[Isabelle/HOL](https://isabelle.in.tum.de) to make sure I wasn't making any
invalid logical leaps.

The first half of this post models the test itself (without many spoilers) and
the second half develops the solution (which necessarily contains a lot of
spoilers.) However if you want to experience the test in its full glory it's
probably best to stop reading now and go and [read the
original](http://faculty.uml.edu/jpropp/srat-Q.txt).

## Modelling the test

The test comprises twenty multiple-choice questions, many of which refer to the
other questions by number in some way:

    definition questionNumber :: "nat set" where "questionNumber ≡ {1..20}"

My first attempt defined this as an algebraic datatype:

    datatype Question = Q1 | Q2 | ...

This gave me some useful properties, like the ability to prove things by simply
enumerating all the cases and checking them one-by-one, but also lost the
ability to easily talk about "odd-numbered questions" or "questions preceding
11".  We could develop the theory needed for that, of course, but here it's
simpler to model them as a subset of the natural numbers. We can regain the
ability to enumerate all the cases using this lemma:

    lemma questionNumber_cases[consumes 1]:
      assumes q: "n ∈ questionNumber"
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
      assumes "n = 11 ⟹ P"
      assumes "n = 12 ⟹ P"
      assumes "n = 13 ⟹ P"
      assumes "n = 14 ⟹ P"
      assumes "n = 15 ⟹ P"
      assumes "n = 16 ⟹ P"
      assumes "n = 17 ⟹ P"
      assumes "n = 18 ⟹ P"
      assumes "n = 19 ⟹ P"
      assumes "n = 20 ⟹ P"
      shows P
    proof -
      note q
      also have "questionNumber = set [1..<21]" unfolding atLeastAtMost_upt questionNumber_def by simp
      also have "… = set [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]"
        apply (intro cong [OF refl, where f = set])
        by (simp add: upt_rec)
      finally show P using assms by auto
    qed

It's also useful to have a datatype that comprises _just_ the question numbers:

    typedef Question = "questionNumber" unfolding questionNumber_def by auto

Each question has 5 answers, which is appropriate to model as an algebraic
datatype:

    datatype Answer = A | B | C | D | E

We model the questions themselves as logical statements in a locale, with a
single free variable `f` which assigns an answer to each question.

    locale Test =
      fixes f :: "Question ⇒ Answer"

In fact it's way more useful to consider the question numbers as numbers, so we
define an auxiliary function `nat ⇒ Answer` in terms of `f`:

      fixes answer :: "nat ⇒ Answer"
      defines "answer n ≡ f (Abs_Question n)"

### Question 1

        (*
     1. The first question whose answer is B is question
        (A) 1
        (B) 2
        (C) 3
        (D) 4
        (E) 5
    *)
      fixes firstQuestionWithAnswerB :: nat
      defines "firstQuestionWithAnswerB ≡ LEAST n. 1 ≤ n ∧ answer n = B"
      assumes q1a: "(answer 1 = A) = (firstQuestionWithAnswerB = 1)"
      assumes q1b: "(answer 1 = B) = (firstQuestionWithAnswerB = 2)"
      assumes q1c: "(answer 1 = C) = (firstQuestionWithAnswerB = 3)"
      assumes q1d: "(answer 1 = D) = (firstQuestionWithAnswerB = 4)"
      assumes q1e: "(answer 1 = E) = (firstQuestionWithAnswerB = 5)"

This isn't quite the full story for this question, because of [how Isabelle
models ill-defined things]({% post_url 2018-04-09-partial-functions-isabelle
%}). The problem is that if there is no `n ≥ 1` with `answer n = B` then
`firstQuestionWithAnswerB` is not well-defined, so it could be anything, and
strictly speaking the question also tells us there is such a question so that
we can exclude this situation. It turns out not to be necessary to model this
extra fact here.

### Question 2

        (*
     2. The only two consecutive questions with identical answers are questions
        (A) 6 and 7
        (B) 7 and 8
        (C) 8 and 9
        (D) 9 and 10
        (E) 10 and 11
    *)
      fixes questionsWithSameAnswerAsNext :: "nat set"
      defines "questionsWithSameAnswerAsNext ≡ { n. n ∈ questionNumber ∧ Suc n ∈ questionNumber ∧ answer n = answer (Suc n) }"
      assumes q2a: "(answer 2 = A) = (questionsWithSameAnswerAsNext = {6})"
      assumes q2b: "(answer 2 = B) = (questionsWithSameAnswerAsNext = {7})"
      assumes q2c: "(answer 2 = C) = (questionsWithSameAnswerAsNext = {8})"
      assumes q2d: "(answer 2 = D) = (questionsWithSameAnswerAsNext = {9})"
      assumes q2e: "(answer 2 = E) = (questionsWithSameAnswerAsNext = {10})"

This is quite a useful question: even without knowing its answer, it tells us
that many of the questions definitely have different answers from their
neighbours.

### Question 3

        (*
     3. The number of questions with the answer E is
        (A) 0
        (B) 1
        (C) 2
        (D) 3
        (E) 4
    *)
      fixes numberOfQuestionsWithAnswersIn :: "Answer set ⇒ nat"
      defines "numberOfQuestionsWithAnswersIn S ≡ card { n ∈ questionNumber. answer n ∈ S }"
      assumes q3a: "(answer 3 = A) = (numberOfQuestionsWithAnswersIn {E} = 0)"
      assumes q3b: "(answer 3 = B) = (numberOfQuestionsWithAnswersIn {E} = 1)"
      assumes q3c: "(answer 3 = C) = (numberOfQuestionsWithAnswersIn {E} = 2)"
      assumes q3d: "(answer 3 = D) = (numberOfQuestionsWithAnswersIn {E} = 3)"
      assumes q3e: "(answer 3 = E) = (numberOfQuestionsWithAnswersIn {E} = 4)"

There are quite a few questions that talk about the number of questions with
particular answers, so we introduce the `numberOfQuestionsWithAnswersIn`
function.

### Question 4

        (*
     4. The number of questions with the answer A is
        (A) 4
        (B) 5
        (C) 6
        (D) 7
        (E) 8
    *)
      assumes q4a: "(answer 4 = A) = (numberOfQuestionsWithAnswersIn {A} = 4)"
      assumes q4b: "(answer 4 = B) = (numberOfQuestionsWithAnswersIn {A} = 5)"
      assumes q4c: "(answer 4 = C) = (numberOfQuestionsWithAnswersIn {A} = 6)"
      assumes q4d: "(answer 4 = D) = (numberOfQuestionsWithAnswersIn {A} = 7)"
      assumes q4e: "(answer 4 = E) = (numberOfQuestionsWithAnswersIn {A} = 8)"

### Question 5

        (*
     5. The answer to this question is the same as the answer to question
        (A) 1
        (B) 2
        (C) 3
        (D) 4
        (E) 5
    *)
      assumes q5a: "(answer 5 = A) = (answer 5 = answer 1)"
      assumes q5b: "(answer 5 = B) = (answer 5 = answer 2)"
      assumes q5c: "(answer 5 = C) = (answer 5 = answer 3)"
      assumes q5d: "(answer 5 = D) = (answer 5 = answer 4)"
      assumes q5e: "(answer 5 = E) = (answer 5 = answer 5)"

This question is one of the more mindbending ones, at least partly because
unlike the preceding questions the answers are not inherently mutually
exclusive. However, the nature of this kind of puzzle is that the answers _are_
all mutually exclusive, which this model captures: for instance if `answer 5 =
answer 1` then `answer 5 = A` and therefore `answer 5 ≠ B` so `answer 5 ≠
answer 2` as well.

### Question 6

        (*
     6. The answer to question 17 is
        (A) C
        (B) D
        (C) E
        (D) none of the above
        (E) all of the above
    *)
      assumes q6a: "(answer 6 = A) = (answer 17 = C)"
      assumes q6b: "(answer 6 = B) = (answer 17 = D)"
      assumes q6c: "(answer 6 = C) = (answer 17 = E)"
      assumes q6d: "(answer 6 = D) = (answer 17 ∉ {C,D,E})"
      assumes q6e: "(answer 6 = E) = (answer 17 = C ∧ answer 17 = D ∧ answer 17 = E ∧ answer 17 ∉ {C,D,E})"

I like that there's a bit of self-reference in the options to this question
here, although it's quite easy to untangle it.

### Question 7

        (*
     7. Alphabetically, the answer to this question and the answer to the
        following question are
        (A) 4 apart
        (B) 3 apart
        (C) 2 apart
        (D) 1 apart
        (E) the same
    *)
      assumes q7a: "(answer 7 = A) = ({answer 7, answer 8} ∈ { {A,E} })"
      assumes q7b: "(answer 7 = B) = ({answer 7, answer 8} ∈ { {A,D},{B,E} })"
      assumes q7c: "(answer 7 = C) = ({answer 7, answer 8} ∈ { {A,C},{B,D},{C,E} })"
      assumes q7d: "(answer 7 = D) = ({answer 7, answer 8} ∈ { {A,B},{B,C},{C,D},{D,E} })"
      assumes q7e: "(answer 7 = E) = (answer 7 = answer 8)"

I couldn't think of a slicker way to model this question than simply
enumerating all the possibilities. If there were many questions of this form
then perhaps it'd make more sense to develop more machinery on top of the
`Answer` type, but there aren't so I didn't.

### Question 8

        (*
     8. The number of questions whose answers are vowels is
        (A) 4
        (B) 5
        (C) 6
        (D) 7
        (E) 8
    *)
      assumes q8a: "(answer 8 = A) = (numberOfQuestionsWithAnswersIn {A,E} = 4)"
      assumes q8b: "(answer 8 = B) = (numberOfQuestionsWithAnswersIn {A,E} = 5)"
      assumes q8c: "(answer 8 = C) = (numberOfQuestionsWithAnswersIn {A,E} = 6)"
      assumes q8d: "(answer 8 = D) = (numberOfQuestionsWithAnswersIn {A,E} = 7)"
      assumes q8e: "(answer 8 = E) = (numberOfQuestionsWithAnswersIn {A,E} = 8)"

Similarly to question 7, it's simplest to just enumerate the vowels.

### Question 9

        (*
     9. The next question with the same answer as this one is question
        (A) 10
        (B) 11
        (C) 12
        (D) 13
        (E) 14
    *)
      assumes q9a: "(answer 9 = A) = ((LEAST n. 9 < n ∧ answer n = answer 9) = 10)"
      assumes q9b: "(answer 9 = B) = ((LEAST n. 9 < n ∧ answer n = answer 9) = 11)"
      assumes q9c: "(answer 9 = C) = ((LEAST n. 9 < n ∧ answer n = answer 9) = 12)"
      assumes q9d: "(answer 9 = D) = ((LEAST n. 9 < n ∧ answer n = answer 9) = 13)"
      assumes q9e: "(answer 9 = E) = ((LEAST n. 9 < n ∧ answer n = answer 9) = 14)"

Similarly to question 1, this model omits the fact that there _is_ a later
question with the same answer, but this turns out not to be necessary.

### Question 10

        (*
    10. The answer to question 16 is
        (A) D
        (B) A
        (C) E
        (D) B
        (E) C
    *)
      assumes q10a: "(answer 10 = A) = (answer 16 = D)"
      assumes q10b: "(answer 10 = B) = (answer 16 = A)"
      assumes q10c: "(answer 10 = C) = (answer 16 = E)"
      assumes q10d: "(answer 10 = D) = (answer 16 = B)"
      assumes q10e: "(answer 10 = E) = (answer 16 = C)"

### Question 11

        (*
    11. The number of questions preceding this one with the answer B is
        (A) 0
        (B) 1
        (C) 2
        (D) 3
        (E) 4
    *)
      assumes q11a: "(answer 11 = A) = (card { n ∈ questionNumber. n < 11 ∧ answer n = B } = 0)"
      assumes q11b: "(answer 11 = B) = (card { n ∈ questionNumber. n < 11 ∧ answer n = B } = 1)"
      assumes q11c: "(answer 11 = C) = (card { n ∈ questionNumber. n < 11 ∧ answer n = B } = 2)"
      assumes q11d: "(answer 11 = D) = (card { n ∈ questionNumber. n < 11 ∧ answer n = B } = 3)"
      assumes q11e: "(answer 11 = E) = (card { n ∈ questionNumber. n < 11 ∧ answer n = B } = 4)"

### Question 12

        (*
    12. The number of questions whose answer is a consonant is
        (A) an even number
        (B) an odd number
        (C) a perfect square
        (D) a prime
        (E) divisible by 5
    *)
      assumes q12a: "(answer 12 = A) = (even (numberOfQuestionsWithAnswersIn {B,C,D}))"
      assumes q12b: "(answer 12 = B) = (odd  (numberOfQuestionsWithAnswersIn {B,C,D}))"
      assumes q12c: "(answer 12 = C) = (numberOfQuestionsWithAnswersIn {B,C,D} ∈ {1,4,9,16})"
      assumes q12d: "(answer 12 = D) = (numberOfQuestionsWithAnswersIn {B,C,D} ∈ {2,3,5,7,11,13,17,19})"
      assumes q12e: "(answer 12 = E) = (numberOfQuestionsWithAnswersIn {B,C,D} ∈ {5,10,15,20})"

I could have encoded the properties "a perfect square", "prime" and "divisible
by 5" more faithfully, but there's only 20 questions so enumerating the
possibilities by hand was much quicker.

### Question 13

        (*
    13. The only odd-numbered problem with answer A is
        (A) 9
        (B) 11
        (C) 13
        (D) 15
        (E) 17
    *)
      assumes q13a: "(answer 13 = A) = ({n ∈ questionNumber. odd n ∧ answer n = A} = {9})"
      assumes q13b: "(answer 13 = B) = ({n ∈ questionNumber. odd n ∧ answer n = A} = {11})"
      assumes q13c: "(answer 13 = C) = ({n ∈ questionNumber. odd n ∧ answer n = A} = {13})"
      assumes q13d: "(answer 13 = D) = ({n ∈ questionNumber. odd n ∧ answer n = A} = {15})"
      assumes q13e: "(answer 13 = E) = ({n ∈ questionNumber. odd n ∧ answer n = A} = {17})"

This immediately tells us that many odd-numbered problems do _not_ have the
answer A, which could be quite useful.

### Question 14

        (*
    14. The number of questions with answer D is
        (A) 6
        (B) 7
        (C) 8
        (D) 9
        (E) 10
    *)
      assumes q14a: "(answer 14 = A) = (numberOfQuestionsWithAnswersIn {D} = 6)"
      assumes q14b: "(answer 14 = B) = (numberOfQuestionsWithAnswersIn {D} = 7)"
      assumes q14c: "(answer 14 = C) = (numberOfQuestionsWithAnswersIn {D} = 8)"
      assumes q14d: "(answer 14 = D) = (numberOfQuestionsWithAnswersIn {D} = 9)"
      assumes q14e: "(answer 14 = E) = (numberOfQuestionsWithAnswersIn {D} = 10)"

### Question 15

        (*
    15. The answer to question 12 is
        (A) A
        (B) B
        (C) C
        (D) D
        (E) E
    *)
      assumes q15a: "(answer 15 = A) = (answer 12 = A)"
      assumes q15b: "(answer 15 = B) = (answer 12 = B)"
      assumes q15c: "(answer 15 = C) = (answer 12 = C)"
      assumes q15d: "(answer 15 = D) = (answer 12 = D)"
      assumes q15e: "(answer 15 = E) = (answer 12 = E)"

### Question 16

        (*
    16. The answer to question 10 is
        (A) D
        (B) C
        (C) B
        (D) A
        (E) E
    *)
      assumes q16a: "(answer 16 = A) = (answer 10 = D)"
      assumes q16b: "(answer 16 = B) = (answer 10 = C)"
      assumes q16c: "(answer 16 = C) = (answer 10 = B)"
      assumes q16d: "(answer 16 = D) = (answer 10 = A)"
      assumes q16e: "(answer 16 = E) = (answer 10 = E)"

### Question 17

        (*
    17. The answer to question 6 is
        (A) C
        (B) D
        (C) E
        (D) none of the above
        (E) all of the above
    *)
      assumes q17a: "(answer 17 = A) = (answer 6 = C)"
      assumes q17b: "(answer 17 = B) = (answer 6 = D)"
      assumes q17c: "(answer 17 = C) = (answer 6 = E)"
      assumes q17d: "(answer 17 = D) = (answer 6 ∉ {C,D,E})"
      assumes q17e: "(answer 17 = E) = (answer 6 = C ∧ answer 6 = D ∧ answer 6 = E ∧ answer 6 ∉ {C,D,E})"

### Question 18

        (*
    18. The number of questions with answer A equals the number of questions
        with answer
        (A) B
        (B) C
        (C) D
        (D) E
        (E) none of the above
    *)
      assumes q18a: "(answer 18 = A) = (numberOfQuestionsWithAnswersIn {A} = numberOfQuestionsWithAnswersIn {B})"
      assumes q18b: "(answer 18 = B) = (numberOfQuestionsWithAnswersIn {A} = numberOfQuestionsWithAnswersIn {C})"
      assumes q18c: "(answer 18 = C) = (numberOfQuestionsWithAnswersIn {A} = numberOfQuestionsWithAnswersIn {D})"
      assumes q18d: "(answer 18 = D) = (numberOfQuestionsWithAnswersIn {A} = numberOfQuestionsWithAnswersIn {E})"
      assumes q18e: "(answer 18 = E) = (numberOfQuestionsWithAnswersIn {A} ∉ numberOfQuestionsWithAnswersIn `{ {B},{C},{D},{E} })"

### Question 19

        (*
    19. The answer to this question is:
        (A) A
        (B) B
        (C) C
        (D) D
        (E) E
    *)
      assumes q19a: "(answer 19 = A) = (answer 19 = A)"
      assumes q19b: "(answer 19 = B) = (answer 19 = B)"
      assumes q19c: "(answer 19 = C) = (answer 19 = C)"
      assumes q19d: "(answer 19 = D) = (answer 19 = D)"
      assumes q19e: "(answer 19 = E) = (answer 19 = E)"

All of the options here are tautologies, but I wrote them out anyway.

### Question 20

        (*
    20. Standardized test is to intelligence as barometer is to
        (A) temperature (only)
        (B) wind-velocity (only)
        (C) latitude (only)
        (D) longitude (only)
        (E) temperature, wind-velocity, latitude, and longitude
    *)
      assumes q20: "answer 20 = E"

This didn't fit into the model so I just wrote down the answer.

## The solution (spoilers below)

Now we can start to answer the questions by proving lemmas within the locale
we've just defined:

    context Test
    begin

First up, an easy one:

    lemma q5: "answer 5 = E" using q5e by auto

Next, questions 10 and 16 refer to each other's answers, and there are some
obviously inconsistent answers (e.g. `10C ⟹ 16E ⟹ 10E`). I wondered if these
two questions alone determined their answers so I tried simply throwing all the
facts into the pot and doing a case split and it worked:

    lemma q10: "answer 10 = A" using q10c q10d q10e q16b q16c q16d q16e by (cases "answer 10", metis+)
    lemma q16: "answer 16 = D" using q10a q10 by simp

There's a similar relationship between questions 6 and 17. We can easily rule
out either of these being `A`, `C` and `E`, so either 6 is `D` and 17 is `B` or
vice versa. Question 2 tells us that neither question should have the same
answer as either of its neighbours, so since we know that the answer to
question 16 is `D` it can't be that 17 is also `D`, so it must be the following:

    lemma q6: "answer 6 = D"
      using q6e q17b q6c q17e q6b q6a q17c
    proof (cases "answer 6")
      case B
      with q17d have "answer (Suc 16) = D" by simp
      with q16 have "16 ∈ questionsWithSameAnswerAsNext"
        unfolding questionsWithSameAnswerAsNext_def questionNumber_def by auto
      with q2a q2b q2c q2d q2e show ?thesis by (cases "answer 2", auto)
    qed auto

    lemma q17: "answer 17 = B" using q17b q6 by simp

Next up is question 12, and again we can use the fact that the answers are all
mutually exclusive to good effect.  Firstly, every number is either even or odd
so the answer must be one of the first two, and therefore none of the remaining
three, so we need to think about the numbers which are not prime or square or
multiples of five, and this only leaves a few possibilities:

    lemma nqs_BCD: "numberOfQuestionsWithAnswersIn {B,C,D} ∈ {6,8,12,14,18}"
    proof -
      have nz: "0 < numberOfQuestionsWithAnswersIn {B,C,D}"
        unfolding numberOfQuestionsWithAnswersIn_def card_gt_0_iff
      proof (intro conjI)
        have "6 ∈ questionNumber" by (simp add: questionNumber_def)
        with q6 show "{n ∈ questionNumber. answer n ∈ {B, C, D}} ≠ {}" by auto
        have fqs: "finite questionNumber" unfolding questionNumber_def by simp
        show "finite {n ∈ questionNumber. answer n ∈ {B, C, D}}" by (intro finite_subset [OF _ fqs], auto)
      qed

      have "numberOfQuestionsWithAnswersIn {B,C,D} ≤ card questionNumber"
        unfolding numberOfQuestionsWithAnswersIn_def by (intro card_mono, auto simp add: questionNumber_def)
      also have "… = 20" unfolding questionNumber_def card_atLeastAtMost by simp
      finally have "numberOfQuestionsWithAnswersIn {B,C,D} ∈ set [0..<21]" by simp
      also have "… = set [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]"
        apply (intro cong [OF refl, where f = set]) by (simp add: upt_rec)
      finally show ?thesis
        using nz q12a q12b q12c q12d q12e by (cases "answer 12", auto)
    qed

The trick here was simply to enumerate the possibilities, which forced a case
split that eliminated all the unwanted ones in the last line. All of the
possibilities are even so this gives us two more answers:

    lemma q12: "answer 12 = A" using nqs_BCD q12a by auto
    lemma q15: "answer 15 = A" using q15a q12 by auto

We've found an odd-numbered question with answer `A` so that resolves question
13:

    lemma q13: "answer 13 = D"
    proof -
      from q13a q13b q13c q13d q13e
      obtain q where q: "{n ∈ questionNumber. odd n ∧ answer n = A} = {q}" by (cases "answer 13", auto)
      from q15 have "15 ∈ {n ∈ questionNumber. odd n ∧ answer n = A}" by (auto simp add: questionNumber_def)
      with q q13d show ?thesis by simp
    qed

Since we have narrowed down the possibilities for the number of questions with
an answer that is a consonant, we also know the possibilities for questions
whose answer is a vowel, which affects questions 3, 4 and 8. Firstly a couple
of results about doing calculations with `numberOfQuestionsWithAnswersIn`:

    lemma nqs_disjoint:
      assumes "S1 ∩ S2 = {}"
      shows "numberOfQuestionsWithAnswersIn (S1 ∪ S2) = numberOfQuestionsWithAnswersIn S1 + numberOfQuestionsWithAnswersIn S2"
    proof -
      have "card {n ∈ questionNumber. answer n ∈ S1 ∪ S2}
        = card ({n ∈ questionNumber. answer n ∈ S1} ∪ {n ∈ questionNumber. answer n ∈ S2})"
        by (intro cong [OF refl, where f = card], auto)
      also have "… = card {n ∈ questionNumber. answer n ∈ S1} + card {n ∈ questionNumber. answer n ∈ S2}"
      proof (intro card_Un_disjoint)
        from assms show "{n ∈ questionNumber. answer n ∈ S1} ∩ {n ∈ questionNumber. answer n ∈ S2} = {}" by auto
        have "finite questionNumber" unfolding questionNumber_def by simp
        thus "finite {n ∈ questionNumber. answer n ∈ S1}" "finite {n ∈ questionNumber. answer n ∈ S2}" by auto
      qed
      finally show ?thesis
        unfolding numberOfQuestionsWithAnswersIn_def by simp
    qed

    lemma nqs_insert:
      assumes "ans ∉ S"
      shows "numberOfQuestionsWithAnswersIn (insert ans S) = numberOfQuestionsWithAnswersIn {ans} + numberOfQuestionsWithAnswersIn S"
    proof -
      have "numberOfQuestionsWithAnswersIn (insert ans S) = numberOfQuestionsWithAnswersIn ({ans} ∪ S)"
        by (intro cong [OF refl, where f = numberOfQuestionsWithAnswersIn], auto)
      also have "… = numberOfQuestionsWithAnswersIn {ans} + numberOfQuestionsWithAnswersIn S"
        using assms by (intro nqs_disjoint, auto)
      finally show ?thesis .
    qed

We can use this to divide the 20 questions into those with vowel answers and
those with consonant answers:

    lemma nqs_AE_BCD: "numberOfQuestionsWithAnswersIn {A,E} + numberOfQuestionsWithAnswersIn {B,C,D} = 20"
    proof -
      have "20 = card questionNumber" unfolding questionNumber_def by simp
      also have "… = numberOfQuestionsWithAnswersIn UNIV" unfolding numberOfQuestionsWithAnswersIn_def by auto
      also have "… = numberOfQuestionsWithAnswersIn ({A,E} ∪ {B,C,D})"
        apply (intro cong [OF refl, where f = numberOfQuestionsWithAnswersIn]) using Answer.exhaust by blast
      also have "… = numberOfQuestionsWithAnswersIn {A,E} + numberOfQuestionsWithAnswersIn {B,C,D}"
        by (intro nqs_disjoint, auto)
      finally show ?thesis by simp
    qed

Question 8 and `nqs_BCD` above together narrow down the possibilities a lot:

    lemma nqs_AE: "numberOfQuestionsWithAnswersIn {A,E} ∈ {6,8}"
    proof -
      have "numberOfQuestionsWithAnswersIn {A,E} ∈ {2,6,8,12,14}" using nqs_BCD nqs_AE_BCD by auto
      with q8a q8b q8c q8d q8e show ?thesis by (cases "answer 8", auto)
    qed

This means that the answers to question 3 and 4 must add up to either 6 or 8:

    lemma nqs_AE_sum: "numberOfQuestionsWithAnswersIn {A,E} = numberOfQuestionsWithAnswersIn {A} + numberOfQuestionsWithAnswersIn {E}"
      by (intro nqs_insert, simp)

Question 1 tells us more about questions 3 and 4 too. With a bit of effort we
can narrow down question 1 to either `C` or `D`: `A` and `B` are both
contradictory, and question 5 rules out `E`:

    lemma firstQuestionWithAnswerB_properties:
      "1 ≤ firstQuestionWithAnswerB" "answer firstQuestionWithAnswerB = B"
      "⋀n. ⟦ 1 ≤ n; n < firstQuestionWithAnswerB ⟧ ⟹ answer n ≠ B"
    proof -
      define P where "⋀n. P n ≡ 1 ≤ n ∧ answer n = B"
      have 1: "firstQuestionWithAnswerB = Least P" unfolding P_def firstQuestionWithAnswerB_def by simp
      have "P firstQuestionWithAnswerB"
        unfolding 1
      proof (intro LeastI)
        from q17 show "P 17" unfolding P_def by auto
      qed
      thus "1 ≤ firstQuestionWithAnswerB" "answer firstQuestionWithAnswerB = B" unfolding P_def by auto

      fix k
      assume k1: "1 ≤ k" and k_lt: "k < firstQuestionWithAnswerB"
      from k_lt have "¬ P k"
        by (intro not_less_Least, simp add: P_def firstQuestionWithAnswerB_def)
      with k1 show "answer k ≠ B" unfolding P_def by auto
    qed

    lemma q1_CD: "answer 1 ∈ {C,D}"
    proof (cases "answer 1")
      case A with q1a firstQuestionWithAnswerB_properties show ?thesis by simp
    next
      case B
      with q1b have fq: "firstQuestionWithAnswerB = 2" by simp
      hence "answer 1 ≠ B" by (intro firstQuestionWithAnswerB_properties(3), simp_all)
      with B show ?thesis by simp
    next
      case E with q5 q5a show ?thesis by simp
    qed auto

That means that either 3's answer or 4's answer is `B`. Moreover, the other one
of them is `D`: they must add up to either 6 or 8, and they cannot be equal
since they are neighbouring questions:

    lemma q34_BD: "{answer 3, answer 4} = {B,D}"
      using q1_CD
    proof (elim insertE)
      from nqs_AE_sum nqs_AE
      have nqs_A_E: "numberOfQuestionsWithAnswersIn {A} + numberOfQuestionsWithAnswersIn {E} ∈ {6,8}" by simp

      have answer34_distinct: "answer 3 ≠ answer 4"
      proof (intro notI)
        assume "answer 3 = answer 4"
        hence "3 ∈ questionsWithSameAnswerAsNext"
          unfolding questionsWithSameAnswerAsNext_def questionNumber_def by auto
        with q2a q2b q2c q2d q2e show False by (cases "answer 2", auto)
      qed

      {
        assume "answer 1 = D"
        with q1d have "firstQuestionWithAnswerB = 4" by simp
        with firstQuestionWithAnswerB_properties have q4: "answer 4 = B" by simp
        from q4 q4b nqs_A_E have "numberOfQuestionsWithAnswersIn {E} ∈ {1, 3}" by auto
        with q3b q3d answer34_distinct q4 show ?thesis by auto
      next
        assume "answer 1 = C"
        with q1c have "firstQuestionWithAnswerB = 3" by simp
        with firstQuestionWithAnswerB_properties have q3: "answer 3 = B" by simp
        from q3 q3b nqs_A_E have "numberOfQuestionsWithAnswersIn {A} ∈ {5, 7}" by auto
        with q3 q4b q4d answer34_distinct show ?thesis by auto
      }
    qed simp

This means that the number of questions whose answers are a vowel is either 1+7
or 3+5 and is therefore 8:

    lemma q8: "answer 8 = E"
    proof -
      from nqs_AE_sum nqs_AE
      have nqs_A_E: "numberOfQuestionsWithAnswersIn {A} + numberOfQuestionsWithAnswersIn {E} ∈ {6,8}" by simp
      with q34_BD q8e q3b q3d q4b q4d nqs_AE_sum
      show ?thesis unfolding doubleton_eq_iff by auto
    qed

This means there are at least two questions whose answer is `E` (5 and 8) and
we already worked out that there are either one or three of them, so there must
be three, and therefore there's five with answer `A`.

    lemma q3: "answer 3 = D"
      using q34_BD unfolding doubleton_eq_iff
    proof (elim disjE conjE)
      assume "answer 3 = B"
      with q3b have "card {n ∈ questionNumber. answer n ∈ {E}} = 1"
        unfolding numberOfQuestionsWithAnswersIn_def by simp
      then obtain q where q: "{n ∈ questionNumber. answer n ∈ {E}} = {q}" by (elim card_1_singletonE, auto)
      moreover from q5 have "5 ∈ {n ∈ questionNumber. answer n ∈ {E}}" unfolding questionNumber_def by auto
      moreover from q8 have "8 ∈ {n ∈ questionNumber. answer n ∈ {E}}" unfolding questionNumber_def by auto
      ultimately show ?thesis by simp
    qed

    lemma q4: "answer 4 = B" using q34_BD q3 unfolding doubleton_eq_iff by simp

This finally resolves question 1:

    lemma q1: "answer 1 = D"
      using q1_CD
    proof (elim insertE)
      assume "answer 1 = C" with q1c firstQuestionWithAnswerB_properties q3 show ?thesis by simp
    qed auto

This was as far as I could get without using the answer to question 20, which
is also `E`, so that's all three of them:

    lemma Es: "{n ∈ questionNumber. answer n = E} = {5,8,20}"
    proof (intro sym [OF card_seteq])
      from q5 q8 q20 show "{5, 8, 20} ⊆ {n ∈ questionNumber. answer n = E}" by (auto simp add: questionNumber_def)
      have "finite {8,20::nat}" by simp
      from card_insert_if [OF this, where x = 5] have "card {5,8,20::nat} = Suc (card {8,20::nat})" by simp
      also have "… = 3" by simp
      also from q3 q3d have "3 = card {n ∈ questionNumber. answer n = E}" by (simp add: numberOfQuestionsWithAnswersIn_def)
      finally show "card {n ∈ questionNumber. answer n = E} ≤ card {5, 8, 20::nat}" by simp
      have "finite questionNumber" by (simp add: questionNumber_def)
      thus "finite {n ∈ questionNumber. answer n = E}" by simp
    qed

This resolves question 2: none of the other questions can have answer `E`, so
in particular neither of 8's neighbours are `E`; moreover 9 and 10 cannot share
an answer since that answer would be `A` and we already found that 15 is an
odd-numbered question with answer `A`, which question 13 tells us to be unique:

    lemma q2: "answer 2 = A"
    proof (cases "answer 2")
      case B with q2b have "7 ∈ questionsWithSameAnswerAsNext" by simp
      with q8 have "7 ∈ {n ∈ questionNumber. answer n = E}" unfolding questionsWithSameAnswerAsNext_def by auto
      with Es show ?thesis by simp
    next
      case C with q2c have "8 ∈ questionsWithSameAnswerAsNext" by simp
      with q8 have "9 ∈ {n ∈ questionNumber. answer n = E}" unfolding questionsWithSameAnswerAsNext_def by auto
      with Es show ?thesis by simp
    next
      case D with q2d have "9 ∈ questionsWithSameAnswerAsNext" by simp
      with q10 have "9 ∈ {n ∈ questionNumber. odd n ∧ answer n = A}" unfolding questionsWithSameAnswerAsNext_def by auto
      with q13 q13d show ?thesis by simp
    next
      case E hence "2 ∈ {n ∈ questionNumber. answer n = E}" unfolding questionNumber_def by auto
      with Es show ?thesis by simp
    qed

We already know the answer to question 6, so this tells us the answer to
question 7 too:

    lemma q7: "answer 7 = D"
    proof -
      from q2 q2a have "6 ∈ questionsWithSameAnswerAsNext" by simp
      with q6 show ?thesis unfolding questionsWithSameAnswerAsNext_def by auto
    qed

We can also resolve question 18. We know there are 5 questions with answer `A`.
Question 14 tells us that the number of questions with answer `D` is at least 6
so that rules out `C`. There are 3 questions with answer `E` so that rules out
`D`. We already know all the questions with answer `E`, and `B` is forbidden
since that's the answer to neighbouring question 17, which leaves `A`:

    lemma q18: "answer 18 = A"
    proof (cases "answer 18")
      case B
      with q17 have "17 ∈ questionsWithSameAnswerAsNext" unfolding questionsWithSameAnswerAsNext_def questionNumber_def by auto
      with q2 q2a show ?thesis by simp
    next
      case C
      with q18c q4 q4b have "numberOfQuestionsWithAnswersIn {D} = 5" by simp
      with q14a q14b q14c q14d q14e show ?thesis by (cases "answer 14", auto)
    next
      case D
      with q18d q4 q4b q3 q3d show ?thesis by simp
    next
      case E hence "18 ∈ {n ∈ questionNumber. answer n = E}" unfolding questionNumber_def by auto
      with Es show ?thesis by simp
    qed

In other words, there are 5 questions with answer `B`:

    lemma cardDs5: "numberOfQuestionsWithAnswersIn {B} = 5" using q18 q18a q4b q4 by simp

Since there are only 12 questions whose answer is a consonant, 5 of which are
`B`, and question 14 tells us that there are at least 6 with answer `D`, this
rules out a lot of possibilities. Also the answer to question 14 cannot be `A`
since that's the answer to neighbouring question 15, so this means there must
be 7 questions with answer `D` and none at all with answer `C`:

    lemma q14: "answer 14 = B" and no_C: "⋀n. n ∈ questionNumber ⟹ answer n ≠ C"
    proof -
      from nqs_AE_BCD q8 q8e have "12 = numberOfQuestionsWithAnswersIn {B,C,D}" by simp
      also have "numberOfQuestionsWithAnswersIn {B,C,D} = numberOfQuestionsWithAnswersIn {B} + numberOfQuestionsWithAnswersIn {C,D}"
        by (intro nqs_insert, simp)
      also have "… = numberOfQuestionsWithAnswersIn {B} + (numberOfQuestionsWithAnswersIn {C} + numberOfQuestionsWithAnswersIn {D})"
        by (intro cong [OF refl, where f = "(op +) (numberOfQuestionsWithAnswersIn {B})"] nqs_insert, simp)
      also from cardDs5 have "… = 5 + numberOfQuestionsWithAnswersIn {C} + numberOfQuestionsWithAnswersIn {D}" by simp
      finally have CD_7: "numberOfQuestionsWithAnswersIn {C} + numberOfQuestionsWithAnswersIn {D} = 7" by simp

      from CD_7 have "numberOfQuestionsWithAnswersIn {D} ≤ 7" by auto
      with q14c q14d q14e show "answer 14 = B"
      proof (cases "answer 14")
        case A with q15 have "14 ∈ questionsWithSameAnswerAsNext" unfolding questionsWithSameAnswerAsNext_def questionNumber_def by auto
        with q2 q2a show ?thesis by simp
      qed auto
      with q14b CD_7 have "numberOfQuestionsWithAnswersIn {C} = 0" by simp
      moreover have "finite questionNumber" unfolding questionNumber_def by simp
      hence "finite {n ∈ questionNumber. answer n = C}" by simp
      ultimately have "{n ∈ questionNumber. answer n = C} = {}"
        unfolding numberOfQuestionsWithAnswersIn_def by (intro iffD1 [OF card_0_eq], simp_all)
      thus "⋀n. n ∈ questionNumber ⟹ answer n ≠ C" by simp
    qed

This narrows down the possibilities for question 9: it cannot be `A` (thanks to
question 13) or `C`, and we've found all the `E`s, so it must be `B` or `D`:

    lemma q9_BD: "answer 9 ∈ {B,D}"
    proof (cases "answer 9")
      case A
      hence "9 ∈ {n ∈ questionNumber. odd n ∧ answer n = A}" unfolding questionNumber_def by simp
      with q13 q13d show ?thesis by simp
    next
      case C have "9 ∈ questionNumber" by (simp add: questionNumber_def) with no_C C show ?thesis by simp
    next
      case E hence "9 ∈ {n ∈ questionNumber. answer n = E}" unfolding questionNumber_def by auto
      with Es show ?thesis by simp
    qed auto

In either case the answer to question 11 is `B`: if 9's answer is `B` then this
is clear; if 9's answer is `D` then 11's answer cannot be `D`, but by the same
reasoning as for question 9 it also cannot be `A`, `C` or `E`, so it is `B` in
both cases.

    lemma q11: "answer 11 = B"
      using q9_BD
    proof (elim insertE)
      assume "answer 9 = B"
      with q9b have p: "(LEAST n. 9 < n ∧ answer n = B) = 11" by simp
      define P where "P ≡ λn. 9 < n ∧ answer n = B"
      have "P (Least P)"
      proof (intro LeastI)
        from q14 show "P 14" by (simp add: P_def)
      qed
      with p show ?thesis by (simp add: P_def)
    next
      assume "answer 9 = D"
      with q9d have p: "(LEAST n. 9 < n ∧ answer n = D) = 13" by simp
      define P where "P ≡ λn. 9 < n ∧ answer n = D"
      have "¬ P 11" using p by (intro not_less_Least, auto simp add: P_def)
      hence not_D: "answer 11 ≠ D" by (simp add: P_def)
      thus ?thesis
      proof (cases "answer 11")
        case A
        hence "11 ∈ {n ∈ questionNumber. odd n ∧ answer n = A}" unfolding questionNumber_def by simp
        with q13 q13d show ?thesis by simp
      next
        case C have "11 ∈ questionNumber" by (simp add: questionNumber_def) with no_C C show ?thesis by simp
      next
        case E hence "11 ∈ {n ∈ questionNumber. answer n = E}" unfolding questionNumber_def by auto
        with Es show ?thesis by simp
      qed auto
    qed simp

This means there is only one question with answer `B` below 11, which is
question 4, so question 9's answer must be `D`:

    lemma q9: "answer 9 = D"
      using q9_BD
    proof (elim insertE)
      from q11 q11b have "is_singleton {n ∈ questionNumber. n < 11 ∧ answer n = B}" unfolding is_singleton_altdef by simp
      then obtain q where "{n ∈ questionNumber. n < 11 ∧ answer n = B} = {q}" by (elim is_singletonE)
      moreover assume "answer 9 = B" hence "9 ∈ {n ∈ questionNumber. n < 11 ∧ answer n = B}" by (simp add: questionNumber_def)
      moreover from q4 have "4 ∈ {n ∈ questionNumber. n < 11 ∧ answer n = B}" by (simp add: questionNumber_def)
      ultimately show ?thesis by simp
    qed simp_all

We have only found four `B`s and we know there to be five, so the remaining
question, number 19, must also have answer `B`:

    lemma q19: "answer 19 = B"
    proof -
      have "{ n ∈ questionNumber. answer n = B } = {4,11,14,17,19}"
      proof (intro card_seteq finite.insertI finite.emptyI subsetI, elim CollectE conjE)
        have "card {4, 11, 14, 17, 19::nat} = 5" by simp
        moreover from cardDs5 have "card {n ∈ questionNumber. answer n = B} = 5"
          unfolding numberOfQuestionsWithAnswersIn_def by simp
        ultimately show "card {4, 11, 14, 17, 19::nat} ≤ card {n ∈ questionNumber. answer n = B}" by simp

        fix n assume "n ∈ questionNumber" "answer n = B"
        thus "n ∈ {4, 11, 14, 17, 19}"
          using q1 q2 q3 q5 q6 q7 q8 q9 q10 q12 q13 q15 q16 q18 q20
          by (cases n rule: questionNumber_cases, simp_all)
      qed
      thus ?thesis by auto
    qed

## Validation

At this point it seems we have found an answer to every question, but it
remains to show that these answers are all consistent with the questions. To do
this we can define a function `Question ⇒ Answer` with the answers we have
found and show that it satisfies all the assumptions of the locale.

    definition answers :: "Answer list" where "answers ≡ [D,A,D,B,E,  D,D,E,D,A,  B,A,D,B,A,  D,B,A,B,E]"

    definition ans :: "Question ⇒ Answer" where "ans q = answers ! (Rep_Question q - 1)"

It's useful to spell out all the answers individually too for the benefit of
the simplifier:

    lemma ans_simps:
      "ans (Abs_Question 1) = D"
      "ans (Abs_Question (Suc 0)) = D"
      "ans (Abs_Question 2) = A"
      "ans (Abs_Question (Suc (Suc 0))) = A"
      "ans (Abs_Question 3) = D"
      "ans (Abs_Question 4) = B"
      "ans (Abs_Question 5) = E"
      "ans (Abs_Question 6) = D"
      "ans (Abs_Question 7) = D"
      "ans (Abs_Question 8) = E"
      "ans (Abs_Question 9) = D"
      "ans (Abs_Question 10) = A"
      "ans (Abs_Question 11) = B"
      "ans (Abs_Question 12) = A"
      "ans (Abs_Question 13) = D"
      "ans (Abs_Question 14) = B"
      "ans (Abs_Question 15) = A"
      "ans (Abs_Question 16) = D"
      "ans (Abs_Question 17) = B"
      "ans (Abs_Question 18) = A"
      "ans (Abs_Question 19) = B"
      "ans (Abs_Question 20) = E"
      using Abs_Question_inverse unfolding ans_def answers_def questionNumber_def by simp_all

This particular simplification is quite useful up-front:

    lemma refl_eq_iff: "((a = a) = P) = P" by simp

Here's the proof that `ans` satisfies all the assumptions of the locale:

    lemma answer_valid: "Test ans"
    proof (unfold_locales, unfold ans_simps refl_eq_iff)

At this point there are 96 subgoals, one for each assumption defined above (19
questions multiplied by 5 answers, plus the unique answer to question 20). The
proof just works through them all one-by-one.

### Question 1

      show "(LEAST n. 1 ≤ n ∧ ans (Abs_Question n) = B) = 4"
      proof (intro Least_equality conjI, simp_all add: ans_simps, elim conjE)
        fix n assume n: "Suc 0 ≤ n" "ans (Abs_Question n) = B"
        show "4 ≤ n"
        proof (rule ccontr)
          assume "¬ 4 ≤ n" with n have "n ∈ {1,2,3}" by auto
          with n show False by (auto simp add: ans_simps)
        qed
      qed
      thus "(D = A) = ((LEAST n. 1 ≤ n ∧ ans (Abs_Question n) = B) = 1)"
        "(D = B) = ((LEAST n. 1 ≤ n ∧ ans (Abs_Question n) = B) = 2)"
        "(D = C) = ((LEAST n. 1 ≤ n ∧ ans (Abs_Question n) = B) = 3)"
        "(D = E) = ((LEAST n. 1 ≤ n ∧ ans (Abs_Question n) = B) = 5)" by simp_all

### Question 2

      show "{n ∈ questionNumber. Suc n ∈ questionNumber ∧ ans (Abs_Question n) = ans (Abs_Question (Suc n))} = {6}"
      proof (intro equalityI subsetI)
        fix n :: nat assume "n ∈ {6}" thus "n ∈ {n ∈ questionNumber. Suc n ∈ questionNumber ∧ ans (Abs_Question n) = ans (Abs_Question (Suc n))}"
          by (auto simp add: ans_simps questionNumber_def)
      next
        fix n assume "n ∈ {n ∈ questionNumber. Suc n ∈ questionNumber ∧ ans (Abs_Question n) = ans (Abs_Question (Suc n))}"
        hence n: "n ∈ questionNumber" "n ≤ 19" "ans (Abs_Question n) = ans (Abs_Question (Suc n))" by (auto simp add: questionNumber_def)
        thus "n ∈ {6}" by (cases n rule: questionNumber_cases, auto simp add: ans_simps)
      qed
      thus "(A = B) = ({n ∈ questionNumber. Suc n ∈ questionNumber ∧ ans (Abs_Question n) = ans (Abs_Question (Suc n))} = {7})"
        "(A = C) = ({n ∈ questionNumber. Suc n ∈ questionNumber ∧ ans (Abs_Question n) = ans (Abs_Question (Suc n))} = {8})"
        "(A = D) = ({n ∈ questionNumber. Suc n ∈ questionNumber ∧ ans (Abs_Question n) = ans (Abs_Question (Suc n))} = {9})"
        "(A = E) = ({n ∈ questionNumber. Suc n ∈ questionNumber ∧ ans (Abs_Question n) = ans (Abs_Question (Suc n))} = {10})" by simp_all

### Question 3

There are quite a few properties for which we need to know exactly which
questions have a particular answer. Here's the questions with answer `E`, which
answers question 3.

      have Es: "{n ∈ questionNumber. ans (Abs_Question n) ∈ {E}} = {5,8,20}"
      proof (intro equalityI subsetI CollectI conjI)
        fix n :: nat assume "n ∈ {5,8,20}" thus "n ∈ questionNumber" "ans (Abs_Question n) ∈ {E}" by (auto simp add: ans_simps questionNumber_def)
      next
        fix n assume "n ∈ {n ∈ questionNumber. ans (Abs_Question n) ∈ {E}}"
        hence n: "n ∈ questionNumber" "ans (Abs_Question n) = E" by (auto simp add: questionNumber_def)
        thus "n ∈ {5,8,20}" by (cases n rule: questionNumber_cases, auto simp add: ans_simps)
      qed
      thus "card {n ∈ questionNumber. ans (Abs_Question n) ∈ {E}} = 3" by auto
      thus "(D = A) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {E}} = 0)"
        "(D = B) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {E}} = 1)"
        "(D = C) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {E}} = 2)"
        "(D = E) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {E}} = 4)" by simp_all

### Question 4

Similarly to question 3, we enumerate the questions have answer `A` using the
same proof, which answers question 4.

      have As: "{n ∈ questionNumber. ans (Abs_Question n) ∈ {A}} = {2,10,12,15,18}"
      proof (intro equalityI subsetI CollectI conjI)
        fix n :: nat assume "n ∈ {2,10,12,15,18}" thus "n ∈ questionNumber" "ans (Abs_Question n) ∈ {A}" by (auto simp add: ans_simps questionNumber_def)
      next
        fix n assume "n ∈ {n ∈ questionNumber. ans (Abs_Question n) ∈ {A}}"
        hence n: "n ∈ questionNumber" "ans (Abs_Question n) = A" by (auto simp add: questionNumber_def)
        thus "n ∈ {2,10,12,15,18}" by (cases n rule: questionNumber_cases, auto simp add: ans_simps)
      qed
      thus "card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A}} = 5" by auto
      thus "(B = A) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A}} = 4)"
        "(B = C) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A}} = 6)"
        "(B = D) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A}} = 7)"
        "(B = E) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A}} = 8)" by simp_all

### Questions 5-7

The proof obligations from these questions are easy to discharge `by auto`:

      show
        "(E = A) = (E = D)"
        "(E = B) = (E = A)"
        "(E = C) = (E = D)"
        "(E = D) = (E = B)"
        "(E = E)"
        "(D = A) = (B = C)"
        "(D = B) = (B = D)"
        "(D = C) = (B = E)"
        "B ∉ {C, D, E}"
        "(D = E) = (B = C ∧ B = D ∧ B = E ∧ B ∉ {C, D, E})"
        "(D = A) = ({D, E} ∈ { {A, E} })"
        "(D = B) = ({D, E} ∈ { {A, D}, {B, E} })"
        "(D = C) = ({D, E} ∈ { {A, C}, {B, D}, {C, E} })"
        "({D, E} ∈ { {A, B}, {B, C}, {C, D}, {D, E} })"
        "(D = E) = (D = E)" by auto

### Question 8

We already enumerated the `A`s and the `E`s so this is easy to prove.

      have "{n ∈ questionNumber. ans (Abs_Question n) ∈ {A, E}} = {2,5,8,10,12,15,18,20}" using As Es by auto
      thus "card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A, E}} = 8" by auto
      thus "(E = A) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A, E}} = 4)"
        "(E = B) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A, E}} = 5)"
        "(E = C) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A, E}} = 6)"
        "(E = D) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A, E}} = 7)" by simp_all

### Question 9

The tricky bit of this proof is showing that the 13 is the _first_ question
after 9 with which it shares an answer. The trick was to use contradiction
(`rule ccontr`) to get the goal into a form where we can automatically reduce
it to the three cases `10`, `11` and `12`.

      show "(LEAST n. 9 < n ∧ ans (Abs_Question n) = D) = 13"
      proof (intro Least_equality conjI, simp_all add: ans_simps, elim conjE, rule ccontr)
        fix n assume "9 < n" "¬ 13 ≤ n" "ans (Abs_Question n) = D"
        hence "n ∈ {10,11,12}" "ans (Abs_Question n) = D" by auto
        thus False by (auto simp add: ans_simps)
      qed
      thus "(D = A) = ((LEAST n. 9 < n ∧ ans (Abs_Question n) = D) = 10)"
        "(D = B) = ((LEAST n. 9 < n ∧ ans (Abs_Question n) = D) = 11)"
        "(D = C) = ((LEAST n. 9 < n ∧ ans (Abs_Question n) = D) = 12)"
        "(D = E) = ((LEAST n. 9 < n ∧ ans (Abs_Question n) = D) = 14)" by simp_all

### Question 10

This question's obligations are easy to discharge:

      show "D = D"
        "(A = B) = (D = A)"
        "(A = C) = (D = E)"
        "(A = D) = (D = B)"
        "(A = E) = (D = C)" by simp_all

### Question 11

By enumerating all the questions below question 11 (`cases n rule:
questionNumber_cases`) it's easy to check that only one of them has answer `B`:

      have "{n ∈ questionNumber. n < 11 ∧ ans (Abs_Question n) = B} = {4}"
      proof (intro equalityI subsetI CollectI conjI)
        fix n :: nat assume "n ∈ {4}" thus "n ∈ questionNumber" "n < 11" "ans (Abs_Question n) = B" by (auto simp add: ans_simps questionNumber_def)
      next
        fix n assume "n ∈ {n ∈ questionNumber. n < 11 ∧ ans (Abs_Question n) = B}"
        hence n: "n ∈ questionNumber" "n < 11" "ans (Abs_Question n) = B" by (auto)
        thus "n ∈ {4}" by (cases n rule: questionNumber_cases, auto simp add: ans_simps)
      qed
      thus "card {n ∈ questionNumber. n < 11 ∧ ans (Abs_Question n) = B} = 1" by simp
      thus "(B = A) = (card {n ∈ questionNumber. n < 11 ∧ ans (Abs_Question n) = B} = 0)"
        "(B = C) = (card {n ∈ questionNumber. n < 11 ∧ ans (Abs_Question n) = B} = 2)"
        "(B = D) = (card {n ∈ questionNumber. n < 11 ∧ ans (Abs_Question n) = B} = 3)"
        "(B = E) = (card {n ∈ questionNumber. n < 11 ∧ ans (Abs_Question n) = B} = 4)" by simp_all

### Question 12

Similarly to in questions 3 and 4, we start by enumerating all the questions
with answer `B`, `C` and `D`:

      have Bs: "{n ∈ questionNumber. ans (Abs_Question n) ∈ {B}} = {4,11,14,17,19}"
      proof (intro equalityI subsetI CollectI conjI)
        fix n :: nat assume "n ∈ {4,11,14,17,19}" thus "n ∈ questionNumber" "ans (Abs_Question n) ∈ {B}" by (auto simp add: ans_simps questionNumber_def)
      next
        fix n assume "n ∈ {n ∈ questionNumber. ans (Abs_Question n) ∈ {B}}"
        hence n: "n ∈ questionNumber" "ans (Abs_Question n) = B" by (auto simp add: questionNumber_def)
        thus "n ∈ {4,11,14,17,19}" by (cases n rule: questionNumber_cases, auto simp add: ans_simps)
      qed
      have Cs: "{n ∈ questionNumber. ans (Abs_Question n) ∈ {C}} = {}"
      proof (intro equalityI subsetI CollectI conjI)
        fix n assume "n ∈ {n ∈ questionNumber. ans (Abs_Question n) ∈ {C}}"
        hence n: "n ∈ questionNumber" "ans (Abs_Question n) = C" by (auto simp add: questionNumber_def)
        thus "n ∈ {}" by (cases n rule: questionNumber_cases, auto simp add: ans_simps)
      qed simp_all
      have Ds: "{n ∈ questionNumber. ans (Abs_Question n) ∈ {D}} = {1,3,6,7,9,13,16}"
      proof (intro equalityI subsetI CollectI conjI)
        fix n :: nat assume "n ∈ {1,3,6,7,9,13,16}" thus "n ∈ questionNumber" "ans (Abs_Question n) ∈ {D}" by (auto simp add: ans_simps questionNumber_def)
      next
        fix n assume "n ∈ {n ∈ questionNumber. ans (Abs_Question n) ∈ {D}}"
        hence n: "n ∈ questionNumber" "ans (Abs_Question n) = D" by (auto simp add: questionNumber_def)
        thus "n ∈ {1,3,6,7,9,13,16}" by (cases n rule: questionNumber_cases, auto simp add: ans_simps)
      qed
      have "{n ∈ questionNumber. ans (Abs_Question n) ∈ {B, C, D}} = {1,3,6,7,9,13,16,4,11,14,17,19}" using Bs Cs Ds by auto
      hence "card {n ∈ questionNumber. ans (Abs_Question n) ∈ {B, C, D}} = 12" by simp
      thus "even (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {B, C, D}})"
        "(A = B) = odd (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {B, C, D}})"
        "(A = C) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {B, C, D}} ∈ {1, 4, 9, 16})"
        "(A = D) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {B, C, D}} ∈ {2, 3, 5, 7, 11, 13, 17, 19})"
        "(A = E) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {B, C, D}} ∈ {5, 10, 15, 20})" by simp_all

### Question 13

This question follows by enumerating all the questions (`cases n rule:
questionNumber_cases`) too.

      show "{n ∈ questionNumber. odd n ∧ ans (Abs_Question n) = A} = {15}"
      proof (intro equalityI subsetI CollectI conjI)
        fix n :: nat assume "n ∈ {15}" thus "n ∈ questionNumber" "odd n" "ans (Abs_Question n) = A" by (auto simp add: ans_simps questionNumber_def)
      next
        fix n assume "n ∈ {n ∈ questionNumber. odd n ∧ ans (Abs_Question n) = A}"
        hence n: "n ∈ questionNumber" "odd n" "ans (Abs_Question n) = A" by (auto simp add: questionNumber_def)
        thus "n ∈ {15}" by (cases n rule: questionNumber_cases, auto simp add: ans_simps)
      qed
      thus "(D = A) = ({n ∈ questionNumber. odd n ∧ ans (Abs_Question n) = A} = {9})"
        "(D = B) = ({n ∈ questionNumber. odd n ∧ ans (Abs_Question n) = A} = {11})"
        "(D = C) = ({n ∈ questionNumber. odd n ∧ ans (Abs_Question n) = A} = {13})"
        "(D = E) = ({n ∈ questionNumber. odd n ∧ ans (Abs_Question n) = A} = {17})" by simp_all

### Question 14

We already enumerated all the questions whose answer is `D`, and there are 7 of
them:

      show "card {n ∈ questionNumber. ans (Abs_Question n) ∈ {D}} = 7" using Ds by auto
      thus "(B = A) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {D}} = 6)"
        "(B = C) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {D}} = 8)"
        "(B = D) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {D}} = 9)"
        "(B = E) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {D}} = 10)" by simp_all

### Questions 15-17

The obligations for these questions are easy to discharge:

      show "A = A"
        "(A = B) = (A = B)"
        "(A = C) = (A = C)"
        "(A = D) = (A = D)"
        "(A = E) = (A = E)"
        "(D = A) = (A = D)"
        "(D = B) = (A = C)"
        "(D = C) = (A = B)"
        "A = A"
        "(D = E) = (A = E)"
        "(B = A) = (D = C)"
        "D = D"
        "(B = C) = (D = E)"
        "(B = D) = (D ∉ {C, D, E})"
        "(B = E) = (D = C ∧ D = D ∧ D = E ∧ D ∉ {C, D, E})" by simp_all

### Question 18

Since we have already calculated the sets of questions with each answer, these
obligations are easy to discharge as long as we are careful to unfold the right
definitions first.

      show            "card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A}} = card {n ∈ questionNumber. ans (Abs_Question n) ∈ {B}}"  unfolding As Bs by simp
      show "(A = B) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A}} = card {n ∈ questionNumber. ans (Abs_Question n) ∈ {C}})" unfolding As Cs by simp
      show "(A = C) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A}} = card {n ∈ questionNumber. ans (Abs_Question n) ∈ {D}})" unfolding As Ds by simp
      show "(A = D) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A}} = card {n ∈ questionNumber. ans (Abs_Question n) ∈ {E}})" unfolding As Es by simp
      show "(A = E) = (card {n ∈ questionNumber. ans (Abs_Question n) ∈ {A}} ∉ (λS. card {n ∈ questionNumber. ans (Abs_Question n) ∈ S}) ` { {B}, {C}, {D}, {E} })"
        unfolding image_insert As Bs by simp

### Question 19

The obligations for question 19 are all tautologies:

      show
        "(B = A) = (B = A)"
        "B = B"
        "(B = C) = (B = C)"
        "(B = D) = (B = D)"
        "(B = E) = (B = E)" "E = E" by simp_all
    qed

## Uniqueness

It remains to show that the answer we have found is unique. This follows since
we have reasoned our way to a single answer for each question, but this lemma
serves as a useful check that we have actually answered all of the questions.

    lemma (in Test) answer_unique: "f = ans"
    proof (intro ext)
      fix q
      define n where "n ≡ Rep_Question q"
      hence q_def: "q = Abs_Question n" by (simp add: n_def Rep_Question_inverse)

      have "n ∈ questionNumber" using Rep_Question unfolding n_def.
      from this q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
      have "answer n = ans (Abs_Question n)"
        by (cases rule: questionNumber_cases, simp_all add: ans_simps)
      thus "f q = ans q" by (simp add: q_def answer_def)
    qed

## Conclusion

I enjoyed this puzzle. [Self reference is kinda
fun](https://en.wikipedia.org/wiki/Metamagical_Themas). Also, as always,
Isabelle keeps you honest.
