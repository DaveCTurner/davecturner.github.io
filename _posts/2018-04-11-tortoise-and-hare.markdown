---
layout: post
title:  "Floyd's loop-finding algorithm"
date:   2018-04-11 09:09:09 +0000
---

This is the fifth post in an open-ended series on proving the correctness of
TLA specifications using Isabelle/HOL:

- [TLA+ in Isabelle/HOL]({% post_url 2018-02-12-tla-in-isabelle %})

- [Refining specifications in TLA+ and Isabelle/HOL]({% post_url
  2018-02-18-tla-clock-specification %})

- [Using TLA's induction rule]({% post_url 2018-03-23-tla-resource-allocator
  %})

- [Fairness properties in refinement proofs]({% post_url
  2018-03-24-tla-resource-scheduler %})

- **Floyd's loop-finding algorithm**

- [Uncrossing lines]({% post_url
  2018-07-24-uncrossing-lines %})

## Floyd's loop-finding algorithm

This post is about [Floyd's tortoise-and-hare
algorithm](https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare)
for detecting a loop in a linked list using constant space. The basic idea is
you have two pointers (called `tortoise` and `hare`) and you walk them along
the list with the hare going two steps for every one step of the tortoise. If
the hare finds the end of the list then you know there's no loop, and if the
hare meets up with the tortoise again then you know there is a loop.

I came across this example in [Hillel Wayne's list of TLA+
examples](https://hillelwayne.com/post/list-of-tla-examples/) which linked to
[a post by Lorin
Hochstein](https://lorinhochstein.wordpress.com/2017/10/16/the-tortoise-and-the-hare-in-tla/)
in which the TLA+ toolbox was used to show this algorithm's [partial
correctness](https://en.wikipedia.org/wiki/Correctness_(computer_science)): it
never gives the wrong answer, although it may never give any answer at all,
which is a safety property. I thought it'd be a nice exercise to strengthen
this to a total correctness argument by showing that the algorithm does
eventually terminate, i.e. a liveness property, using Isabelle/HOL.

This post is a tour of
[`TortoiseHare.thy`](https://github.com/DaveCTurner/tla-examples/blob/8e93381e46ed279a9424a25e2b29e6d8863c1629/TortoiseHare.thy)
in [my TLA examples Github
repository](https://github.com/DaveCTurner/tla-examples).

## Preliminaries on linked lists

We fix a linked list up-front as follows:

    locale LinkedList =
      fixes headCell :: 'Cell
      fixes nextCell :: "'Cell ⇒ 'Cell option"
      assumes finiteNext: "finite { c. nextCell c ≠ None }"

`headCell` is the start of the list, and the `nextCell` function either has
`nextCell c = Some c'` if `c'` follows `c` in the list, or else `nextCell c =
None` if `c` has no successor. We need to make some kind of assumption that
rules out infinite lists, and I elected to assume that only finitely many
`nextCell`s have been assigned. It'd also be fine to make the stronger
assumption that there are only finitely many cells, and the weaker assumption
that there are only finitely many cells reachable from `headCell`, but I liked
this one the best.

In order to state the algorithm it's useful to have a helper function for
moving the `hare` two steps forward, called `nextNextCell`:

    definition nextNextCell :: "'Cell ⇒ 'Cell option"
      where "nextNextCell c ≡ case nextCell c of None ⇒ None | Some c' ⇒ nextCell c'"

## Definitions

The specification extends the `LinkedList` locale:

    locale TortoiseHare = LinkedList
      where headCell = headCell
      for headCell :: 'Cell
        +

There are three variables. We already met `tortoise` and `hare` which point to
cells, and `hasLoop` is a `bool option` that indicates whether the algorithm is
still running (`hasLoop = None`) or if it has detected a loop (`hasLoop = Some
True`) or found that there is no loop (`hasLoop = Some False`):

      fixes tortoise :: "'Cell stfun"
      fixes hare     :: "'Cell stfun"
      fixes hasLoop  :: "bool option stfun"
      assumes bv: "basevars (tortoise, hare, hasLoop)"

Initially the tortoise and the hare are at the start of the list and the
algorithm has not terminated:

      fixes Initial :: stpred
      defines "Initial ≡ PRED
        tortoise = #headCell ∧ hare = #headCell ∧ hasLoop = #None"

A step of the algorithm involves moving `tortoise` to its `nextCell` and `hare`
to its `nextNextCell`, and then checking if the hare has met the tortoise again
or not:

      fixes Step :: action
      defines "Step ≡ ACT $hasLoop = #None
                            ∧ Some<hare$>     = nextNextCell<$hare>
                            ∧ Some<tortoise$> = nextCell<$tortoise>
                            ∧ hasLoop$ = (if hare$ = tortoise$ then #(Some True)
                                                               else #None)"

It's only possible to take this step if the `hare` has a `nextNextCell` - if
not then it has found the end of the loop and the algorithm terminates with
`hasLoop = Some False`.

      fixes Finish :: action
      defines "Finish ≡ ACT $hasLoop = #None
                                ∧ nextNextCell<$hare> = #None
                                ∧ hasLoop$ = #(Some False)"

Notice that in this case we do not need to define the values for `tortoise$`
and `hare$`: the algorithm has terminated so it does not matter what values
they hold. The `Step` and `Finish` actions are the only possible:

      fixes Next :: action
      defines "Next ≡ ACT (Step ∨ Finish)"

The full spec combines the definitions above with fairness conditions that
indicate that the algorithm always eventually takes a step or else terminates:

      fixes Spec :: temporal
      defines "Spec ≡ TEMP (Init Initial ∧ □[Next]_(tortoise, hare, hasLoop)
          ∧ WF(Step)_(tortoise, hare, hasLoop)
          ∧ WF(Finish)_(tortoise, hare, hasLoop))"

## Linked lists and transitive closures

Isabelle has some useful machinery for working with transitive closures, which
are important here, so here are some definitions that help to bridge the gap
from the presentation of a linked list above.

    definition r :: "('Cell × 'Cell) set"
      where "r ≡ {(c1, c2). nextCell c1 = Some c2}"

The relation `r` is the successor relation: the set of pairs of adjacent cells.

    definition loopExists :: bool
      where "loopExists ≡ ∃ c. (headCell, c) ∈ rtrancl r ∧ (c, c) ∈ trancl r"

The functions `trancl` and `rtrancl` return the transitive closure and the
reflexive-transitive closure of their input. Isabelle likes to write these as
superscript `+` and `*` respectively but they're too hard to type and the
difference is too subtle for me at the font size I prefer, so I like to spell
the names in full. In more detail, `trancl r` is all pairs of cells that are
reachable in one or more steps, and `rtrancl r` is all pairs reachable in zero
or more steps. The `+` and `*` notation is known as the [Kleene plus and Kleene
star](https://en.wikipedia.org/wiki/Kleene_star).  This means that `loopExists`
records the existence of a loop that is reachable from `headCell.`

It is clear that each cell has at most one successor:

    lemma unique_successor: "(c, c1) ∈ r ⟹ (c, c2) ∈ r ⟹ c1 = c2" by (auto simp add: r_def)

It is also important that the set of reachable cells from anywhere is finite,
which follows from assumption `finiteNext` above:

    lemma finiteList: "finite {c'. (c, c') ∈ rtrancl r}"

In the case where `c2` directly follows `c1` and `c3` transitively follows
`c1`, `c3` must be reachable from `c2`:

    lemma next_step:
      assumes c12: "(c1, c2) ∈ r" and c13: "(c1, c3) ∈ trancl r"
      shows "(c2, c3) ∈ rtrancl r"

It seems that the case where the loop is "tight", i.e. comprises one cell, is a
bit of a special case, and the following lemma is useful for handling this. It
says the (obvious) fact that the only cell that is reacahable from a tight loop
is the cell in the loop.

    lemma tight_loop_eq:
      assumes cc': "(c, c') ∈ rtrancl r" and loop: "(c, c) ∈ r"
      shows "c' = c"

It's useful to have a slightly stronger property when a loop exists: it means
that there is a cell which is ahead of all cells in the list:

    lemma loopExists_always_ahead:
      assumes "loopExists"
      shows "∃ c.  (headCell, c)  ∈ rtrancl r 
          ∧ (∀ c'. (headCell, c') ∈ rtrancl r ⟶ (c', c) ∈ trancl r)"

This allows us to show that `loopExists` is equivalent to knowing that every
cell that is reachable from `headCell` has a successor:

    lemma loopExists_no_end:
      "loopExists = (∀ c. (headCell, c) ∈ rtrancl r ⟶ nextCell c ≠ None)"
    proof (cases loopExists)

## Safety

The basic safety property is

    ⊢ Spec ⟶ □(hasLoop ≠ #(Some (¬ loopExists)))

In more detail, recall that `hasLoop = Some b` when the algorithm has
terminated, where the boolean `b` indicates whether a loop was found or not.
This safety property says that `hasLoop` can never be `Some (¬ loopExists)` -
it is always either `None` (if the algorithm has not terminated) or else `Some
loopExists` if it correctly determined the existence of a loop, which is the
partial correctness property we wanted.

In fact we show a slightly stronger property:

    definition Invariant :: stpred where "Invariant ≡ PRED
      hasLoop = #None ⟶ ((#headCell, tortoise) ∈ #(rtrancl r)
                          ∧ (tortoise, hare) ∈ #(rtrancl r))"

    definition Safety :: stpred where
      "Safety ≡ PRED Invariant ∧ hasLoop ≠ #(Some (¬ loopExists))"

The extra invariant says that (while the algorithm hasn't terminated) the
`tortoise` is always reachable from `headCell` and the `hare` is always
reachable from the `tortoise`.

It turns out that many of the proofs that follow break down into four cases: 

- a step is taken as normal (and no loop is found)
- a step is taken as normal and the hare catches the tortoise, so a loop is
  found
- the hare is at a cell with no successor, so no loop is possible, or
- the hare is at a cell with a successor but _this_ cell has no successor, so
  again no loop is possible.

It's useful to capture this observation in a cases lemma (as was done [last
time]({% post_url 2018-03-24-tla-resource-scheduler %}#safety)). The statement
of this lemma here is ludicrously long, mainly because there are so many cells
involved in the "step" cases:

- the `headCell`
- the tortoise (old and new positions)
- the hare (old and new positions, and the intervening cell)

There's quite a big set of reachability relationships between these cells, most
of which are important at some point in one of the proofs, so the cases lemma
states and proves them all at once to avoid duplication later. Here goes...

    lemma square_Next_cases [consumes 2, case_names unchanged Step FoundLoop LastHare PenultimateHare]:
      assumes s_Safety: "s ⊨ Safety" and sq_Next: "(s,t) ⊨ [Next]_(tortoise, hare, hasLoop)"
      assumes unchanged: "
          ⟦ tortoise t = tortoise s
          ; hare t = hare s
          ; hasLoop t = hasLoop s
          ; (s,t) ⊨ ¬Step
          ; (s,t) ⊨ ¬Finish
          ⟧ ⟹ P"
      assumes Step: "⋀h'.
          ⟦ hare t ≠ tortoise t
          ; hasLoop s = None
          ; hasLoop t = None
          ; (headCell, tortoise s) ∈ rtrancl r
          ; (headCell, hare s) ∈ rtrancl r
          ; (headCell, tortoise t) ∈ trancl r
          ; (headCell, h') ∈ trancl r
          ; (headCell, hare t) ∈ trancl r
          ; (tortoise s, hare s) ∈ rtrancl r
          ; (tortoise s, tortoise t) ∈ r
          ; (tortoise s, h') ∈ trancl r
          ; (tortoise s, hare t) ∈ trancl r
          ; (hare s, h') ∈ r
          ; (hare s, hare t) ∈ trancl r
          ; (tortoise t, h') ∈ rtrancl r
          ; (tortoise t, hare t) ∈ trancl r
          ; (h', hare t) ∈ r
          ; (s,t) ⊨ Step
          ; (s,t) ⊨ ¬Finish
          ; (s,t) ⊨ ¬unchanged(tortoise, hare, hasLoop)
          ⟧ ⟹ P"
      assumes FoundLoop: "⋀h'.
          ⟦ hare t = tortoise t
          ; hasLoop s = None
          ; hasLoop t = Some True
          ; loopExists
          ; (headCell, tortoise s) ∈ rtrancl r
          ; (headCell, hare s) ∈ rtrancl r
          ; (headCell, tortoise t) ∈ trancl r
          ; (headCell, h') ∈ trancl r
          ; (headCell, hare t) ∈ trancl r
          ; (tortoise s, hare s) ∈ rtrancl r
          ; (tortoise s, tortoise t) ∈ r
          ; (tortoise s, h') ∈ trancl r
          ; (tortoise s, hare t) ∈ trancl r
          ; (hare s, h') ∈ r
          ; (hare s, hare t) ∈ trancl r
          ; (tortoise t, h') ∈ rtrancl r
          ; (tortoise t, hare t) ∈ trancl r
          ; (h', hare t) ∈ r
          ; (s,t) ⊨ Step
          ; (s,t) ⊨ ¬Finish
          ; (s,t) ⊨ ¬unchanged(tortoise, hare, hasLoop)
          ⟧ ⟹ P"
      assumes LastHare: "
          ⟦ hasLoop s = None
          ; hasLoop t = Some False
          ; ¬ loopExists
          ; nextCell (hare s) = None
          ; (headCell, tortoise s) ∈ rtrancl r
          ; (headCell, hare s) ∈ rtrancl r
          ; (tortoise s, hare s) ∈ rtrancl r
          ; (s,t) ⊨ ¬Step
          ; (s,t) ⊨ Finish
          ; (s,t) ⊨ ¬unchanged(tortoise, hare, hasLoop)
          ⟧ ⟹ P"
      assumes PenultimateHare: "⋀h'.
          ⟦ hasLoop s = None
          ; hasLoop t = Some False
          ; ¬ loopExists
          ; (hare s, h') ∈ r
          ; nextCell h' = None
          ; (headCell, tortoise s) ∈ rtrancl r
          ; (headCell, hare s) ∈ rtrancl r
          ; (headCell, h') ∈ trancl r
          ; (tortoise s, hare s) ∈ rtrancl r
          ; (tortoise s, h') ∈ trancl r
          ; (hare s, h') ∈ r
          ; (s,t) ⊨ ¬Step
          ; (s,t) ⊨ Finish
          ; (s,t) ⊨ ¬unchanged(tortoise, hare, hasLoop)
          ⟧ ⟹ P"
      shows P

The proof of this is a little laborious, but it pays off: the safety lemma
follows almost automatically. Here is the proof in full:

    lemma safety: "⊢ Spec ⟶ □Safety"
    proof invariant
      fix sigma
      assume sigma: "sigma ⊨ Spec"
      thus "sigma ⊨ Init Safety"
        unfolding Invariant_def Safety_def Spec_def Initial_def r_def
        by (auto simp add: Init_def)

      show "sigma ⊨ stable Safety"
      proof (intro Stable)
        from sigma show "sigma ⊨ □[Next]_(tortoise, hare, hasLoop)"
          by (auto simp add: Spec_def)

        show "⊢ $Safety ∧ [Next]_(tortoise, hare, hasLoop) ⟶ Safety$"
        proof (intro actionI temp_impI, elim temp_conjE, unfold unl_before)
          fix s t
          assume "s ⊨ Safety" "(s,t) ⊨ [Next]_(tortoise, hare, hasLoop)"
          thus "(s,t) ⊨ Safety$"
            by (cases rule: square_Next_cases, auto simp add: Safety_def Invariant_def loopExists_no_end)
        qed
      qed
    qed

## Liveness & termination

The liveness proof for the case where there is a loop is really quite different
from the case where there isn't.  If there isn't a loop then the argument is
roughly that there is a cell with no successor (by lemma `loopExists_no_end`
above) and each transition takes the hare one step closer to finding it. If
there is a loop then there are two phases: firstly, each transition takes the
tortoise closer to being in the loop, and once the tortoise is in the loop then
each transition takes the hare one step closer to catching up with the
tortoise.

It is useful to formalise this idea of "closer" as follows:

    fun iterateNextCell :: "nat ⇒ 'Cell ⇒ 'Cell option"
      where "iterateNextCell 0       c = Some c"
      |     "iterateNextCell (Suc n) c
                      = (case iterateNextCell n c of None ⇒ None
                                                   | Some c' ⇒ nextCell c')"

The function `iterateNextCell n` returns the `n`<sup>th</sup> successor of its
input, satisfying properties like this:

    lemma iterateNextCell_sum: "iterateNextCell (a + b) c
      = (case iterateNextCell a c of None ⇒ None | Some c' ⇒ iterateNextCell b c')"

This allows us to define a function which measures the distance between two
cells:

    definition distanceBetween :: "'Cell ⇒ 'Cell ⇒ nat"
      where "distanceBetween c1 c2 ≡ LEAST n. iterateNextCell n c1 = Some c2"

An interesting feature of Isabelle is that functions do not need to be
well-defined on all their inputs: `distanceBetween c1 c2` only makes sense when
`c2` is reachable from `c1`, but there is no mention of this condition in its
definition. If given bad input, `distanceBetween` doesn't throw an exception or
fail to terminate or anything like that, it simply returns an arbitrary result.
This works because if we know nothing about `distanceBetween c1 c2` when `c2`
is unreachable from `c1` then we cannot use its value in any meaningful way,
which means that any statements about it will have to have ensure that the
right precondition holds. It might seem more obvious to put in a guard
condition as follows:

    definition distanceBetweenOrZero :: "'Cell ⇒ 'Cell ⇒ nat"
      where "distanceBetweenOrZero c1 c2
              ≡ if (c1, c2) ∈ rtrancl r
                then (LEAST n. iterateNextCell n c1 = Some c2)
                else 0"

This function is actually harder to use because it clearly defines its value
for all arguments, and yet its value is meaningless for unreachable inputs (and
would remain meaningless if `0` were replaced by any other number) so the
reachability precondition will still be necessary when using it. Moreover there
is a risk that we actually use its value on unreachable inputs, which can be
avoided if the return value is arbitrary. We can avoid that risk using an
`option` type to model the partiality of the function with something like this:

    definition maybeDistanceBetween :: "'Cell ⇒ 'Cell ⇒ nat option"
      where "maybeDistanceBetween c1 c2
              ≡ if (c1, c2) ∈ rtrancl r
                then Some (LEAST n. iterateNextCell n c1 = Some c2)
                else None"

Again, this is harder to use, and is no safer than the unguarded definition.

The preferred `distanceBetween` function satisfies all sorts of useful
properties, all of which have preconditions that guarantee reachability of its
arguments in one way or another:

    lemma iterateNextCell_distanceBetween:
      assumes "(c1, c2) ∈ rtrancl r"
      shows "iterateNextCell (distanceBetween c1 c2) c1 = Some c2"

    lemma distanceBetween_atMost:
      assumes "iterateNextCell n c1 = Some c2" shows "distanceBetween c1 c2 ≤ n"

    lemma distanceBetween_0 [simp]: "distanceBetween c c = 0"

    lemma distanceBetween_0_eq:
      assumes "(c1, c2) ∈ rtrancl r"
      shows "(distanceBetween c1 c2 = 0) = (c1 = c2)"

    lemma distanceBetween_le_1:
      assumes "(c1, c2) ∈ r" shows "distanceBetween c1 c2 ≤ 1"

    lemma distanceBetween_triangle:
      assumes c12: "(c1, c2) ∈ rtrancl r" and c23: "(c2, c3) ∈ rtrancl r"
      shows "distanceBetween c1 c3 ≤ distanceBetween c1 c2 + distanceBetween c2 c3"

    lemma distanceBetween_eq_Suc:
      assumes c13: "(c1, c3) ∈ rtrancl r" and c13_ne: "c1 ≠ c3"
          and c12: "(c1, c2) ∈ r"
      shows "distanceBetween c1 c3 = Suc (distanceBetween c2 c3)"

There is one other property that turns out to be useful: any cell has at most
one predecessor _in a loop_:

    lemma loop_unique_previous:
      assumes c1c: "(c1, c) ∈ r" and c1_loop: "(c1, c1) ∈ trancl r"
      assumes c2c: "(c2, c) ∈ r" and c2_loop: "(c2, c2) ∈ trancl r"
      shows "c1 = c2"

The proof of this works by computing the length of the loop that `c1` is in,
i.e. `1 + distanceBetween c c1`, and then showing that this is the same as the
length of the loop that `c2` is in.

It's also useful to specialise rule `WF1` for this specification, to cut out
some duplication:

    lemma WF1_Spec:
      fixes A :: action
      fixes P Q :: stpred
      assumes 0: "⊢ Spec ⟶ WF(A)_(tortoise, hare, hasLoop)"
      assumes 1: "⋀s t.
        ⟦ s ⊨ P; s ⊨ Safety; (s,t) ⊨ [Next]_(tortoise, hare, hasLoop) ⟧
          ⟹ t ⊨ P ∨ Q"
      assumes 2: "⋀s t.
        ⟦ s ⊨ P; s ⊨ Safety; (s,t) ⊨ [Next]_(tortoise, hare, hasLoop) ⟧
          ⟹ s ⊨ Enabled(<A>_(tortoise, hare, hasLoop))"
      assumes 3: "⋀s t.
        ⟦ s ⊨ P; s ⊨ Safety; (s,t) ⊨ [Next]_(tortoise, hare, hasLoop);
            (s,t) ⊨ A; (s,t) ⊨ ¬unchanged (tortoise, hare, hasLoop) ⟧
          ⟹ t ⊨ Q"
      shows "⊢ Spec ⟶ (P ↝ Q)"

The final "utility" lemma is to characterise the conditions under which the
`Step` action is enabled, which is when the `hare` has a second successor (and
the algorithm has not already terminated):

    lemma
      assumes s_Safety: "s ⊨ Safety"
      assumes nextNext: "nextNextCell (hare s) ≠ None"
      assumes notFinished: "hasLoop s = None"
      shows Enabled_StepI: "s ⊨ Enabled (<Step>_(tortoise, hare, hasLoop))"

Now the liveness proof can properly begin. The first step is to capture the
last transition in the no-loop case:

    lemma hare_endgame: "⊢ Spec ⟶ (nextNextCell<hare> = #None ↝ hasLoop ≠ #None)"

This follows from the fairness of the `Finish` action by a relatively
straightforward application of the `WF1_Spec` rule above. One minor wrinkle is
that `nextNextCell<hare> = #None` might be true after the algorithm has already
terminated, in which case the `Finish` action is not enabled, so we need to use
the diamond rule to consider the two cases `hasLoop = #None` and `hasLoop ≠
#None` separately.

The next step is to show that if the algorithm does not terminate then the
tortoise visits every reachable cell:

    lemma tortoise_visits_everywhere:
      assumes hd_c: "(headCell, c) ∈ rtrancl r"
      shows "⊢ Spec ⟶ ◇(hasLoop ≠ #None ∨ tortoise = #c)"

The key to proving this is to introduce a variable `n`, that tracks the
distance between the `tortoise` and the target cell, `c`, and then to observe
that `n` always decreases (or the algorithm terminates), so that eventually the
`tortoise` visits the target cell:

    ⊢ Spec
      ⟶ ((∃n. (tortoise, #c) ∈ #(rtrancl r)
               ∧ hasLoop = #None ∧ tortoise ≠ #c
               ∧ distanceBetween<tortoise, #c> = #n)
          ↝ hasLoop ≠ #None ∨ tortoise = #c)

Since here the structure that underpins the induction does not change, it's
possible that this could have been done with an external induction, but I
elected to use the [internal wellfounded induction rule]({% post_url
2018-03-23-tla-resource-allocator %}#conclusion) instead. It's a bit of a pain
to have to account for all of the things that _might_ happen in a step: the
full statement about a single `Step` transition is as follows:

    ⊢ Spec
        ⟶ ((tortoise, #c) ∈ #(rtrancl r)
                    ∧ hasLoop = #None
                    ∧ tortoise ≠ #c
                    ∧ distanceBetween<tortoise, #c> = #n
                    ∧ nextNextCell<hare> ≠ #None
              ↝   hasLoop ≠ #None
                ∨ tortoise = #c
                ∨ (∃n'. #((n', n) ∈ {(n, n'). n < n'})
                    ∧ (tortoise, #c) ∈ #(rtrancl r)
                    ∧ hasLoop = #None
                    ∧ tortoise ≠ #c
                    ∧ distanceBetween<tortoise, #c> = #n'))"

The preconditions are necessary:

- `(tortoise, #c) ∈ #(rtrancl r)` means we haven't overshot and passed the
  target cell already.
- `hasLoop = #None` means the algorithm hasn't already terminated.
- `tortoise ≠ #c` means we haven't found the target cell yet, or else `n` would
  be `0` and wouldn't be able to decrease, and
- `nextNextCell<hare> ≠ #None` means that the `Step` transition is actually
  enabled.

The diamond rule is used repeatedly to introduce these preconditions, by
handling the cases where they aren't true separately.

Onto the main theorem:

    theorem liveness: "⊢ Spec ⟶ ◇(hasLoop ≠ #None)"
    proof (cases loopExists)

The two cases (`loopExists` vs `¬ loopExists`) are very different. The latter
is much simpler: using `loopExists_no_end` yields a reachable cell `cLast` with
no successor, and then `tortoise_visits_everywhere` shows that either the
algorithm terminates or else the tortoise visits `cLast`. This is enough: the
`hare` is always reachable from the `tortoise` because of the safety invariant,
and at `cLast` the `tortoise` has no successor so the `hare` must also have no
successor, so `hare_endgame` applies and the algorithm terminates.

The case where `loopExists` is true is a little trickier. The first step is to
note that, because there is a loop, there is a reachable cell `cLoop` in the
loop, which the `tortoise` eventually reaches. Since the `hare` is always
reachable from the `tortoise`, this means the `hare` is also in the loop, which
means that the `tortoise` is now reachable from the `hare`.

From here we want to be able to say that every step now decrements
`distanceBetween<tortoise,hare>` so that eventually they meet and the algorithm
terminates, but it is sadly not quite so simple, because there is one corner
case in which this is not true: if `cLoop = headCell` then the `tortoise` is in
the loop at the system's initial state, but in the initial state
`distanceBetween<tortoise,hare> = 0` and yet the algorithm hasn't terminated:
the hare must go 1½ times around the loop until it meets the tortoise again,
and the first step therefore _increases_ `distanceBetween<tortoise,hare>`.

To get around this case, rather than doing induction on
`distanceBetween<tortoise,hare>` directly we can introduce an _inductor_, a
tuple of values, ordered lexicographically, which does decrease on each step.
Here the inductor is a pair:

    #inductor = (tortoise = hare, distanceBetween<hare, tortoise>)

The first component decreases from `True` to `False` in the corner case
mentioned above, and in all other cases the first component remains `False` and
the second component decreases. Using this inductor leaves us with the
following statement to prove:

    ⊢ Spec ⟶
      (hasLoop = #None
        ∧ (#cLoop, tortoise) ∈ #(trancl r)
        ∧ #inductor = (tortoise = hare, distanceBetween<hare, tortoise>)

        ↝ hasLoop ≠ #None
          ∨ (∃inductor'. #((inductor', inductor)
                              ∈ {(False, True)} <*lex*> {(i, j). i < j})
                ∧ hasLoop = #None
                ∧ (#cLoop, tortoise) ∈ #(trancl r)
                ∧ #inductor' = (tortoise = hare, distanceBetween<hare, tortoise>)))

This is not so complicated:

- `hasLoop = #None` means the algorithm hasn't already terminated.
- `(#cLoop, tortoise) ∈ #(trancl r)` is a useful invariant that indicates that
  the tortoise is still in the loop.
- `#inductor = (tortoise = hare, distanceBetween<hare, tortoise>)` defines the
  inductor.

It's also true for a single step, so rule `WF1_Spec` applies. There are two
cases to show, depending on whether `tortoise = hare` or not. If `tortoise =
hare` then after one step either `tortoise ≠ hare` or else the algorithm has
terminated, so this is simple. If `tortoise ≠ hare` then either the algorithm
terminates or else `distanceBetween<hare, tortoise>` decreases. This last part
follows from these three statements:

- `distanceBetween (hare s) (tortoise s) = Suc (distanceBetween h' (tortoise s))`
- `distanceBetween h' (tortoise t) ≤ Suc (distanceBetween h' (tortoise s))`
- `distanceBetween h' (tortoise t) = Suc (distanceBetween (hare t) (tortoise t))`

For context, the states `s` and `t` are the states before and after the
transition, and `h'` is the cell in between `hare s` and `hare t`. The first
and third statements say that moving the `hare` one cell forwards reduces the
distance to the tortoise by 1, which requres that the `hare` does not overtake
the `tortoise` in either of these steps, but fortunately we've already
accounted for this. The second statement says that moving the `tortoise` one
step forward does not increase the distance from the hare by more than one, so
that overall the distance _does_ decrease. The sequence of operations is
important here:

1. Move the `hare` one step forward, decreasing the distance by 1.

1. Move the `tortoise` one step forward, increasing the distance by at most 1.

1. Move the `hare` one step forward, decreasing the distance by 1.

Any other sequence does not behave so nicely. For example, if the `tortoise`
moves forwards first then it may meet the `hare`, reducing the distance to `0`,
and then moving the hare forward increases the distance again by some arbitrary
amount that turns out to be equal to the previous decrease, but it's a bit of a
pain to show this.

From here, the proof goes through without any further difficulty.

## Conclusion

It was hopefully interesting to see how it works to model the partial function
`distanceBetween` as a total function which returns an arbitrary value when its
arguments are not reachable, rather than using a specific value or explicit
partiality via the `option` type.

I was a little surprised by how branchy this proof was. I thought it was going
to be quite straightforward, but it needed slightly special handling for the
cases where the loop was tight (i.e. `nextCell cLoop = Some cLoop`) and for
when the loop included the head of the list. These do seem to be special cases
that aren't quite covered by the informal proof I was following, and although
they're not hard to cover I find it satisfying when Isabelle finds these kinds
of corner cases that informal proofs skip.

As always, I tried a number of approaches before settling on the final one
discussed here.  In retrospect, because I was expecting a less branchy proof I
was mostly trying to find a way to avoid the branches I kept encountering,
which needed to deal with the cases where the tortoise and hare were at the
same cell without the algorithm having terminated (e.g. at the start, or if the
tortoise moved "first" in each transition). Once I'd realised that these case
splits really were unavoidable then the proof went through and it didn't take
much tidying up to get to where it is here.

This was a nice exercise, and I'd like to thank
[Hillel](https://hillelwayne.com/post/list-of-tla-examples/) and
[Lorin](https://lorinhochstein.wordpress.com/2017/10/16/the-tortoise-and-the-hare-in-tla/)
for giving me the idea.
