---
layout: post
title:  "Partial functions in Isabelle/HOL"
date:   2018-04-09 09:09:09 +0000
---

A short note about [Joachim Breitner's post on the totality of Isabelle functions](http://www.joachim-breitner.de/blog/732-Isabelle_functions__Always_total%2C_sometimes_undefined) which says:

> For example, no Isabelle command allows you define a function `bogus :: () ⇒ nat` with the equation `bogus () = Suc (bogus ())`, because this equation does not have a solution.

In fact, the following is completely legitimate:

    function bogus :: "unit ⇒ nat" where "bogus () = Suc (bogus ())"
      by pat_completeness auto

`function` lets you define a function and defer the termination proof until later. Until termination is proved, all the generated facts
about the function have an extra precondition involving a predicate `bogus_dom` that restricts the fact to elements of the domain of the function:

    Scratch.bogus.psimps: bogus_dom () ⟹ bogus () = Suc (bogus ())
    Scratch.bogus.pinduct: bogus_dom ?a0.0 ⟹ (bogus_dom () ⟹ ?P () ⟹ ?P ()) ⟹ ?P ?a0.0
    Scratch.bogus.pelims: bogus ?x = ?y ⟹ bogus_dom ?x ⟹ (?x = () ⟹ ?y = Suc (bogus ()) ⟹ bogus_dom () ⟹ ?P) ⟹ ?P

This allows you to work with the partial definition of the function in a somewhat natural way. It's a bit of a pain, but it is less painful
than completely forbidding the partial definition. At some point you can try and turn these facts into the following total facts using a termination proof:

    Scratch.bogus.simps: bogus () = Suc (bogus ())
    Scratch.bogus.elims: bogus ?x = ?y ⟹ (?x = () ⟹ ?y = Suc (bogus ()) ⟹ ?P) ⟹ ?P

The termination proof of course is impossible here:

    termination bogus proof (intro allI)

    > proof (prove)
    > goal (1 subgoal):
    >  1. ⋀x. bogus_dom x

In other words we must show that every element is in the domain of the function, which is false. Perhaps interestingly it's false more because `bogus ()` is defined in terms of itself, rather than because there is no value `n :: nat` satisfying `n = Suc n`: the termination proof provides a local introduction lemma:

    local.termination: wf ?R ⟹ ((), ()) ∈ ?R ⟹ All bogus_dom

This tells us that in order to show termination we need to find a wellfounded relation that relates each equation in the function's definition to the values on which it depends, and any relation that includes `((), ())` is clearly not wellfounded.

Technically, `bogus` is indeed a total function of type `unit ⇒ nat`, but until we know anything about its domain its values are completely arbitrary. This means that theorems like

    lemma "bogus () ≥ 0" by auto

are true, simply because that's true of any natural number, and `bogus ()` is _some_ natural number, even if we don't know which one. In some contexts, the difference is important, but as a working user of Isabelle the difference doesn't matter too much.