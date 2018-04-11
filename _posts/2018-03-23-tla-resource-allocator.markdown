---
layout: post
title:  "Using TLA's induction rule"
date:   2018-03-23 23:09:09 +0000
---

This is the third post in an open-ended series on proving the correctness of
TLA specifications using Isabelle/HOL:

- [TLA+ in Isabelle/HOL]({% post_url 2018-02-12-tla-in-isabelle %})

- [Refining specifications in TLA+ and Isabelle/HOL]({% post_url
  2018-02-18-tla-clock-specification %})

- **Using TLA's induction rule**

- [Fairness properties in refinement proofs]({% post_url
  2018-03-24-tla-resource-scheduler %})

- [Floyd's loop-finding algorithm]({% post_url
  2018-04-11-tortoise-and-hare %})

Stephan Merz's article [_The Specification Language
TLA+_](https://members.loria.fr/SMerz/papers/tla+logic2008.pdf) has a running
example of a resource allocator, which manages a set of clients each requesting
exclusive access to a set of resources:

> 1. A client that currently does not hold any resources and that has no
> pending requests may issue a request for a set of resources.
>
> 2. The allocator may grant access to a set of available (i.e., not currently
> allocated) resources to a client.
>
> 3. A client may release some resources that it holds.
>
> 4. Clients are required to eventually free the resources they hold once their
> entire request has been satisfied.
>
> The system should be designed such that it ensures the following two
> properties.
>
> - Safety: no resource is simultaneously allocated to two different clients.
>
> - Liveness: every request issued by some client is eventually satisfied.

His article introduces a simple allocator, called `SimpleAllocator`, satisfying
(most of) the spec, and uses it to give a pretty comprehensive tour of the
features of TLA+ and the TLC model checker.

I thought it'd be interesting to explore this spec using the TLA implementation
in Isabelle/HOL.  The full theory documents can be found in the
[`Allocator/`](https://github.com/DaveCTurner/tla-examples/tree/master/Allocator)
folder of [my TLA examples Github
repository](https://github.com/DaveCTurner/tla-examples). This article is
mostly a tour of
[`SimpleAllocator.thy`](https://github.com/DaveCTurner/tla-examples/blob/master/Allocator/SimpleAllocator.thy).

## Definitions

In Isabelle/HOL, the spec for the simple allocator is fairly similar to the
TLA+ specification. As in [the previous article]({% post_url
2018-02-18-tla-clock-specification %}) I use a _locale_ to limit the scope of
these definitions, which will be useful later on.

    locale SimpleAllocator =

Firstly, the base variables: respectively, mappings from clients to the sets of
resources on which they are waiting and which they currently hold:

      fixes unsat :: "(Client ⇒ Resource set) stfun"
      fixes alloc :: "(Client ⇒ Resource set) stfun"
      assumes bv: "basevars (unsat, alloc)"

It's useful to give a name to the set of available resources like this:

      fixes available :: "Resource set stfun"
      defines "available s ≡ - (⋃c. alloc s c)"

Initially, no resources have been allocated or requested:

      fixes InitState :: stpred
      defines "InitState ≡ PRED (∀c. id<alloc,#c> = #{} ∧ id<unsat,#c> = #{})"

There are three actions in this specification. The first models a client
requesting a set of resources, which is only allowed to happen if the client
holds no resources and has not yet requested any, as per the first point in the
informal specification above. Generalising Merz's presentation slightly, the
universe of resources is allowed to be arbitrarily large as long as each client
only requests finitely many at once.

      fixes Request :: "Client ⇒ Resource set ⇒ action"
      defines "Request c S ≡ ACT #S ≠ #{} ∧ id<$unsat,#c> = #{} ∧ id<$alloc,#c> = #{}
                        ∧ #(finite S)
                        ∧ updated unsat c (add S)
                        ∧ unchanged alloc"

The second action models the allocation of some resources to a client,
satisfying some or all of its request.

      fixes Allocate :: "Client ⇒ Resource set ⇒ action"
      defines "Allocate c S ≡ ACT (#S ≠ #{} ∧ (#S ⊆ ($available ∩ id<$unsat,#c>))
                        ∧ (updated alloc c (add S))
                        ∧ (updated unsat c (del S)))"

The third action models the client returning some or all of the resources it
currently holds:

      fixes Return :: "Client ⇒ Resource set ⇒ action"
      defines "Return c S ≡ ACT (#S ≠ #{} ∧ #S ⊆ id<$alloc,#c>
                        ∧ updated alloc c (del S)
                        ∧ unchanged unsat)"

The next-state relation is simply the disjunction of all such actions:

      fixes Next :: action
      defines "Next ≡ ACT (∃ c S. Request c S ∨ Allocate c S ∨ Return c S)"

In order to satisfy any liveness properties, we require that `Return` and
`Allocate` are executed fairly. More precisely, `ReturnFair c` indicates that
the client `c` may not hold onto its allocated resources forever, and
`AllocateFair c` indicates that the scheduler must eventually allocate
requested resources to the client `c`.

      fixes ReturnFair :: "Client ⇒ temporal"
      defines "ReturnFair c ≡ TEMP WF(∃S. id<$alloc,#c> = #S ∧ Return c S)_(unsat,alloc)"

      fixes AllocateFair :: "Client ⇒ temporal"
      defines "AllocateFair c ≡ TEMP SF(∃S. Allocate c S)_(unsat,alloc)"

Notice that `AllocateFair` is a _strong_ fairness property: it requires the
scheduler to eventually allocate resources to `c` as long as those resources
are infinitely often available. Weak fairness would not be enough to give the
desired liveness property, because if there were two clients repeatedly
requesting a resource then weak fairness would allow for a situation where one
of the clients repeatedly received the resource and the other never did.
Informally, at least, this seems like an unfair situation in which to be.

The full specification is the conjunction of the parts introduced above, in the
standard form of a TLA specification:

      fixes SimpleAllocator :: temporal
      defines "SimpleAllocator ≡ TEMP (Init InitState ∧ □[Next]_(unsat,alloc)
                                     ∧ (∀c. ReturnFair c) ∧ (∀c. AllocateFair c))"

The target safety property is that no resource is ever allocated to more than
one client at once:

      fixes MutualExclusion :: stpred
      defines "MutualExclusion ≡ PRED
              ∀ c1 c2. #c1 ≠ #c2 ⟶ id<alloc,#c1> ∩ id<alloc,#c2> = #{}"

Because this model may contain infinitely many resources, we also need an
invariant that says that no client is ever waiting on infinitely many of them
at once. If this were not true then the system could allocate resources
one-at-a-time to a client without ever fully satisfying it: `AllocateFair c`
simply says that _some_ set of resources is eventually allocated to `c`, not
that all such sets are.

      fixes FiniteRequests :: stpred
      defines "FiniteRequests ≡ PRED ∀ c. finite<id<unsat,#c>>"

The overall safety property is simply the conjunction of these two invariants:

      fixes Safety :: stpred
      defines "Safety ≡ PRED (MutualExclusion ∧ FiniteRequests)"

The desired liveness property is that every requested resource is eventually
allocated:

      fixes Liveness :: temporal
      defines "Liveness ≡ TEMP (∀ c r. #r ∈ id<unsat,#c> ↝ #r ∈ id<alloc,#c>)"

## Safety

The first thing to prove is that the allocator satisfies its safety property,
which effectively works by induction over all the states: show that it is
satisfied by the initial state and then that it is stable (i.e. preserved by
all transitions):

    theorem safety: "⊢ SimpleAllocator ⟶ □Safety"
    proof invariant
      fix sigma
      assume sigma: "sigma ⊨ SimpleAllocator"

      from sigma show "sigma ⊨ Init Safety"
        by (auto simp add: Safety_def FiniteRequests_def MutualExclusion_def
                           SimpleAllocator_def InitState_def Init_def)

      show "sigma ⊨ stable Safety"
      proof (intro Stable)
        ... (* simple proof by cases on the different possible actions *)
      qed
    qed

Many safety proofs follow this pattern, and after splitting the proof into one
case for each possible action the automation found the proof easily.

## Liveness

Next up is liveness which, as before, turns out to be more complicated. We seek
that each resource request is eventually satisfied. Informally, if a request is
for a resource that is currently allocated to a different client then it must
first be released and then allocated to satisfy the request. At a high level,
the liveness proof follows these two steps, but must account for all of the
other possibilities: the resource may be allocated to and released by many
other clients before the request is eventually satisfied.

More formally, to use the strong fairness condition within `AllocateFair` we
first need to establish that `Allocate c S` is infinitely often enabled.

### Resources are infinitely often available

`Allocate c S` is enabled if `S` is a set of resources that are both available
and requested by `c`. It follows that there is such an `S` as long as `c`'s
requests are not all satisfied, so `Allocate c S` is enabled as long as each
resource is infinitely often available:

    lemma infinitely_often_available: "⊢ SimpleAllocator ⟶ □◇(#r ∈ available)"

The first step in the proof of this lemma is to turn this into a statement
involving the `↝` operator, using this general result:

    lemma unstable_implies_infinitely_often:
      fixes P :: stpred
      assumes "⊢ S ⟶ (¬P ↝ P)"
      shows "⊢ S ⟶ □◇P"
    proof -
      define T :: stpred where "T ≡ PRED #True"
      have "⊢ S ⟶ (T ↝ P)"
      proof (rule imp_leadsto_triangle_excl)
        show "⊢ S ⟶ (T ↝ T)" by (intro imp_imp_leadsto, simp)
        from assms show "⊢ S ⟶ (T ∧ ¬ P ↝ P)" by (simp add: T_def)
      qed
      thus ?thesis by (simp add: leadsto_def T_def)
    qed

This says that one way of showing that `P` holds infinitely often is to show
that any state in which `P` does not hold leads to one in which it does, so
that the system can never get stuck in a state where `¬P` holds forever: either
`P` eventually holds forever (which certainly implies that `P` holds infinitely
often) or else `P` and `¬P` alternate infinitely often.

The top-level structure of this proof then breaks down into these two steps:

    have "⊢ SimpleAllocator ⟶ (#r ∉ available ↝ (∃c. #r ∈ id<alloc,#c>))"
      ...
    also have "⊢ SimpleAllocator ⟶ ((∃c. #r ∈ id<alloc,#c>) ↝ #r ∈ available)"
      ...

The first step follows immediately by definition of `available` and the
existential quantification in the second is in negative position so can be
lifted out to a universal, reducing it to showing

      ⋀c. ⊢ SimpleAllocator ⟶ (#r ∈ id<alloc, #c> ↝ #r ∈ available)

This occurs in a single transition, in which the client `c` releases a set of
resources containing `r`. This transition eventually occurs because `⊢
SimpleAllocator ⟶ ReturnFair c`, which says that every client eventually gives
up all of its resources. More formally, this fairness condition is combined
with [lemma `WF1`]({% post_url 2018-02-12-tla-in-isabelle %}#liveness) to
reduce this fully temporal statement to three simpler statements about single
transitions:

1. If `#r ∈ id<alloc, #c>` then `Return c (alloc c)` is enabled.

2. If `#r ∈ id<alloc, #c>` and any action takes place then either `#r ∈
id<alloc, #c>` still, or else `#r ∈ available`

3. If `#r ∈ id<alloc, #c>` and the `Return c (alloc c)` action takes place then
`#r ∈ available` in the resulting state.

Proving enabledness of an action always seems harder than I expect. To show `s
⊨ Enabled A` involves proving the existence of a _next state_ `u` such that
`(s,u) ⊨ A`, i.e. a state in which the action took place. Automatically proving
existential statements seems tricky, meaning that you sometimes have to
construct the state `u` somewhat manually and then prove that it is a valid
next-state. The automation doesn't always fail, and `sledgehammer` is always
worth a shot, but it's not 100% reliable. In this case, I couldn't come up with
a slick way to get the automation to choose the right `u`, so I had to spell it
out:

            from basevars [OF bv]
            obtain u where
              "alloc u = (λa'. (if c = a' then del (alloc s c) else id) (alloc s a'))"
              and u: "unsat u = unsat s" by auto

From here the first statement, that the action is enabled, follows fairly
quickly.

The second statement follows by considering all the different possible
transitions that can occur, including stuttering ones, and the third is quite
straightforward. Both require the mutual exclusion safety property: without it,
if `r` were held by two clients `c` and `c'` and were then released by `c` then
it would be neither allocated to `c` nor available because `c'` would still
hold it.  Fortunately we already showed that this cannot occur in the safety
proof.

### Requests are eventually satisfied

Having shown `□◇(#r ∈ available)` we're now in a good position to show the
desired liveness property:

    ⊢ SimpleAllocator ⟶ #r ∈ id<unsat, #c> ↝ #r ∈ id<alloc, #c>

It's reasonable to expect that this should follow from the strong fairness
property:

    ⊢ SimpleAllocator ⟶ SF(∃S. Allocate c S)_(unsat,alloc)

In more detail, we have shown that the action is infinitely often enabled, so
strong fairness tells us that it eventually executes. Unfortunately it's not so
simple: that `∃S.` says that _something_ is allocated to `c` but it doesn't
guarantee that `r` is allocated to `c` the first time the action occurs.
Instead we must combine the following facts:

- Each time an `Allocate c S` action occurs at least one resource is allocated
  to `c`.

- Client `c` cannot request more resources until all its present requests
  (including `r`) have been satisfied.

- Client `c` is only waiting on finitely many resources.

Together, these mean that there's no infinite sequence of `Allocate c S`
actions in which `r` is not eventually allocated. This kind of loop, repeatedly
using a particular property, smells of induction, and indeed there is an
induction principle to use:

    lemma wf_imp_leadsto:
      assumes 1: "wf r"
          and 2: "⋀x. ⊢ S ⟶ (F x ↝ (G ∨ (∃y. #((y,x)∈r) ∧ F y)))"
      shows "⊢ S ⟶ (F x ↝ G)"

This is wellfounded (`wf`) induction, the most primitive and flexible form. We
require a wellfounded relation `r` (assumption `1`) and that a state in which
`F` holds for some value `x` leads either to a state in which `G` holds, or
else one in which `F` still holds for an `r`-smaller value of `x` (assumption
`2`).  Because `r` is wellfounded, it contains no infinite descending paths, so
`x` cannot be made smaller infinitely often, meaning that eventually `G` holds.

This induction principle, although powerful, is internal to TLA. Isabelle/HOL
has some very useful machinery that helps with doing proofs by simpler
induction over more structured sets (e.g. recursively defined datatypes) in
which more specialised induction principles are automatically derived, but
those don't seem to play well with doing induction internally within TLA
because in TLA the disjunction is deep within the assumption formula rather
than at the top level. In this case, it doesn't matter, because the wellfounded
relation `r` is the proper-subset relation on finite sets of resources which is
simple enough to work with:

    less_finite_Resource_set ≡ {(S1 :: Resource set, S2). finite S2 ∧ S1 ⊂ S2}

A further complication is that the fairness property is strong fairness, so
instead of rule `WF1` we use `SF1`:

    lemma WF1:
      assumes "⊢ $P ∧ N ⟶ $(Enabled(<A>_v))"
      assumes "⊢ $P ∧ N  ⟶ P$ ∨ Q$"
      assumes "⊢ ($P ∧ N) ∧ <A>_v ⟶ Q$"
      shows   "⊢ □N ∧ WF(A)_v ⟶ (P ↝ Q)"
        (* vs *)
    lemma SF1:
      assumes "⊢ □P ∧ □N ∧ □F ⟶ ◇Enabled(<A>_v)"
      assumes "⊢ $P ∧ N  ⟶ P$ ∨ Q$"
      assumes "⊢ ($P ∧ N) ∧ <A>_v ⟶ Q$"
      shows   "⊢ □N ∧ SF(A)_v ∧ □F ⟶ (P ↝ Q)"

The main difference is that instead of showing `$(Enabled(<A>_v))` we show the
weaker `◇Enabled(<A>_v)`, and we have an extra invariant `□F` to play with
which can be used to carry extra assumptions into the proof: `F == ◇(#r ∈
available) ∧ □Safety` is what is needed here, and this always holds because of
the lemmas that have already been proven.

That covers all the ingredients we're going to need, so now it just remains to
mix them together.

The proof starts by defining short names for the things that will appear a lot:

      define N   where "N  ≡ ACT [Next]_(unsat,alloc)"
      define A   where "A  ≡ ACT (∃S. Allocate c S)"
      define F   where "F  ≡ TEMP (◇(#r ∈ available) ∧ □Safety)"
      define Sp  where "Sp ≡ TEMP □N ∧ SF(A)_(unsat,alloc) ∧ □F"

The abbreviated spec, `Sp`, follows from the full spec and its safety property,
and is in the right form to use rule `SF1`.  The rest of the proof breaks into
two steps:

      have "⊢ Sp ⟶ (#r ∈ id<unsat, #c> ↝ (∃S. isWaitingFor c r S))"
        ...
      have "⊢ Sp ⟶ ((∃S. isWaitingFor c r S) ↝ hasResource c r)"
        ...

The first of these follows immediately, and the second proceeds by induction on
`S`, leaving the goal

    ⋀S. ⊢ Sp ⟶ (isWaitingFor c r S
                    ↝ hasResource c r
                        ∨ (∃S'. #(S' ⊂ S ∧ finite S) ∧ isWaitingFor c r S'))

This can be shown using rule `SF1` and the strong fairness of allocation: we
allocate _something_ to `c`. Either this includes `r` and we are done, or else
it doesn't include `r` and we are in a similar state to where we started,
except that the set of `c`'s unsatisfied requests is now strictly smaller.  The
only tricky bit, compared with previous liveness proofs, is now to show that
the allocation action is eventually enabled. The crux is to show the following:

    ⊢ ◇(isWaitingFor c r S ∧ #(finite S) ∧ #r ∈ available)
              ⟶ ◇(Enabled (<A>_(unsat, alloc)))

This follows because `⊢ P ⟶ Q` implies `⊢ ◇P ⟶ ◇Q` according to rule `DmdImpl`,
which reduces the temporal formula to a formula about a single state that can
be proven using non-temporal reasoning.

## Conclusion

In the [first]({% post_url 2018-02-12-tla-in-isabelle %}) [two]({% post_url
2018-02-18-tla-clock-specification %}) posts we saw deterministic systems:
those whose actions occurred in a fixed sequence, ignoring stuttering, and
whose liveness could be proved using (external) induction over that sequence.

Here we saw was a system with more nondeterminism whose liveness property
didn't follow directly from a fixed sequence of actions, instead depending on
repeatedly performing one action (possibly interleaved with other independent
actions) until the desired state was eventually reached. Because the sequence
of actions was not fixed, the induction had to be performed within the logic
rather than outside.

In the [next post]({% post_url 2018-03-24-tla-resource-scheduler %}) we look at
a refinement of this resource allocator which satisfies a stronger
specification at the cost of a much more complicated induction proof of its
correctness.
