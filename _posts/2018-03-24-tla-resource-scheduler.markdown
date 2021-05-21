---
layout: post
title:  "Fairness properties in refinement proofs"
date:   2018-03-24 09:09:09 +0000
---

This is the fourth post in an open-ended series on proving the correctness of
TLA specifications using Isabelle/HOL:

- [TLA+ in Isabelle/HOL]({% post_url 2018-02-12-tla-in-isabelle %})

- [Refining specifications in TLA+ and Isabelle/HOL]({% post_url
  2018-02-18-tla-clock-specification %})

- [Using TLA's induction rule]({% post_url 2018-03-23-tla-resource-allocator
  %})

- **Fairness properties in refinement proofs**

- [Floyd's loop-finding algorithm]({% post_url
  2018-04-11-tortoise-and-hare %})

- [Uncrossing lines]({% post_url
  2018-07-24-uncrossing-lines %})

As discussed [last time]({% post_url 2018-03-23-tla-resource-allocator %}),
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

The `SimpleAllocator` satisfies _most of_ this spec. After a thorough tour of
TLA+ and TLC, Merz returns to the specification in section 6 and observes that
it misses a small but crucial part:

> Clients are required to eventually free the resources they hold **once their
> entire request has been satisfied**.

Formally, the original spec said

    ∀ c ∈ Clients : WF (Return(c, alloc[c]))

but in fact this should have read

    ∀ c ∈ Clients : WF (unsat[c] = {} ∧ Return(c, alloc[c]))

The first of these two statements says that every client eventually returns
whatever resources it is currently allocated, and the second says that this is
only true once the client is not waiting for more resources. The second
statement is more realistic: typically the client requires all of its requested
resources simultaneously in order to undertake its task, so it is of no use if
we require clients to return their allocated resources while they are waiting
for others.

This seems to be a generalisation of the [dining philosophers
problem](https://en.wikipedia.org/wiki/Dining_philosophers_problem): with the
correction to the fairness condition, the system fails its liveness property
due to deadlock, which TLC finds reasonably quickly.

The article goes on to introduce a more refined allocator which tries to avoid
deadlock by ordering the requests from clients as they arrive according to a
schedule, and only allocating each resource _r_ to the highest-priority client
that is waiting for _r_. This new allocator is known as the
`SchedulingAllocator`.

Having explored the model of the `SimpleAllocator` in Isabelle/HOL, I thought
it'd be interesting to continue by looking at the `SchedulingAllocator` with a
goal of showing the refinement relation:

    ⊢ SchedulingAllocator ⟶ SimpleAllocator

> We chose to do this, and the other things, not because they are easy, but
> because we thought they would be easy.
>
> _-- [John F. Kennedy, 1962, in a less-well-known speech he gave on the use of
> formal
> methods](https://en.wikipedia.org/wiki/We_choose_to_go_to_the_Moon#Speech)_

The full theory documents can be found in the
[`Allocator/`](https://github.com/DaveCTurner/tla-examples/tree/master/Allocator)
folder of [my TLA examples Github
repository](https://github.com/DaveCTurner/tla-examples). This article is
mostly a tour of
[`SchedulingAllocator.thy`](https://github.com/DaveCTurner/tla-examples/blob/master/Allocator/SchedulingAllocator.thy)
and
[`Refinement.thy`](https://github.com/DaveCTurner/tla-examples/blob/master/Allocator/Refinement.thy).

## Design

The `SchedulingAllocator` is built around a _schedule_: an ordered list of
clients such that each resource can only be allocated to the highest-priority
client that is waiting for it.  The system partitions the clients into a number
of different states. Some clients are not waiting on any resources, although
they may still hold some. These clients are called _satisfied_.  When a
satisfied client that holds no resources wishes to request some, it is first
added to an (unordered) _pool_ of unsatisfied clients.  These clients are
called _pooled_. From time to time, the allocator _schedules_ the pool, sorting
them into some (unspecified) order and appending this list to the current
schedule. Once clients are _scheduled_ they can receive resource allocations,
and they remain scheduled until all their requests are satisfied.

It is hopefully plausible that this seems to be a more refined version of the
`SimpleAllocator`: it does the same sorts of actions, but imposes tighter
restrictions on when they can occur. It is less clear, at least to me, that
this system really does avoid deadlock if clients are not required to release
their resources until their requests are fully satisfied.  Finally, since
refinement is just TLA's logical implication, we will need to investigate how
the (weak) fairness properties of the scheduling allocator imply the (both weak
and strong) fairness properties of the simple allocator.

## Definitions

    locale SchedulingAllocator =
      (* variables *)
      fixes unsat :: "(Client ⇒ Resource set) stfun"
      fixes alloc :: "(Client ⇒ Resource set) stfun"
      fixes pool  :: "Client set stfun"
      fixes sched :: "Client list stfun"
      fixes vars defines "vars ≡ LIFT (unsat,alloc,pool,sched)"
      assumes bv: "basevars (unsat, alloc, pool, sched)"

The variables `unsat` and `alloc`, as before, record the pending and current
allocations of each client. This specification introduces the `pool` (a `Client
set`) and `sched` (a `Client list`) as described above.

It is useful to be able to talk about the set of available resources and the
set of higher-priority clients like this:

      fixes available :: "Resource set stfun"
      defines "available s ≡ - (⋃c. alloc s c)"
      fixes higherPriorityClients :: "Client ⇒ Client set stfun"
      defines "higherPriorityClients c s ≡ set (takeWhile (op ≠ c) (sched s))"

Initially, no resources are allocated or requested, and the pool and schedule
are empty:

      fixes InitState :: stpred
      defines "InitState ≡ PRED ((∀c. id<alloc,#c> = #{} ∧ id<unsat,#c> = #{}) 
                                      ∧ pool = #{} ∧ sched = #[])"

There are four actions that can take place in this system. Firstly a satisfied
client that holds no resources may request finitely many resources, at which
point it becomes pooled:

      fixes Request :: "Client ⇒ Resource set ⇒ action"
      defines "Request c S ≡ ACT #S ≠ #{} ∧ id<$unsat,#c> = #{}
                        ∧ id<$alloc,#c> = #{}
                        ∧ #(finite S)
                        ∧ updated unsat c (add S)
                        ∧ pool$ = (insert c)<$pool>
                        ∧ unchanged (alloc, sched)"

Secondly, the allocator may schedule the pooled clients, picking an order of
its contents and appending this list to the end of the current schedule. When
using TLC it's necessary to do this in a slightly roundabout way to avoid
dealing with infinite objects like `Client list` but here there is no such
restriction so we can take the direct route:

      fixes Schedule :: action
      defines "Schedule ≡ ACT ($pool ≠ #{} ∧ pool$ = #{}
          ∧ (∃ poolOrder. #(set poolOrder) = $pool ∧ #(distinct poolOrder)
          ∧ sched$ = $sched @ #poolOrder) ∧ unchanged (unsat, alloc))"

Thirdly, the allocator may allocate a set of available resources to a scheduled
client in order to (possibly partly) satisfy a request, as long as no
higher-priority client is waiting on any of the resources so allocated.  If
this allocation completely satisfies the client's request then it must be
removed from the schedule. This side condition gives us the useful invariant
that each scheduled client is unsatisfied, but does mean that proofs involving
`Allocate` actions tend to have to branch on whether `#S = id<$unsat,#c>` or
not.

      fixes Allocate :: "Client ⇒ Resource set ⇒ action"
      defines "Allocate c S ≡ ACT (#S ≠ #{} ∧ (#S ⊆ ($available ∩ id<$unsat,#c>))
                        ∧ #c ∈ set<$sched>
                        ∧ (∀c'. #c' ∈ $higherPriorityClients c 
                                          ⟶ id<$unsat,#c'> ∩ #S = #{})
                        ∧ sched$ = (if #S = id<$unsat,#c> 
                                      then (filter (op ≠ c))<$sched> 
                                      else $sched)
                        ∧ (updated alloc c (add S))
                        ∧ (updated unsat c (del S))
                        ∧ unchanged pool)"

Finally, a client may return some of the resources that it holds at any time.

      fixes Return :: "Client ⇒ Resource set ⇒ action"
      defines "Return c S ≡ ACT (#S ≠ #{} ∧ #S ⊆ id<$alloc,#c>
                        ∧ updated alloc c (del S)
                        ∧ unchanged (unsat, pool, sched))"

The next-state relation is simply the disjunction of all of these actions.

      fixes Next :: action
      defines "Next ≡ ACT ((∃ c S. Request c S ∨ Allocate c S ∨ Return c S)
                                 ∨ Schedule)"

There are three fairness properties to consider. Firstly, as discussed above,
now `Return` is only subject to a fairness constraint when the client is
completely satisfied, due to the extra `id<$unsat,#c> = #{}` condition:

      fixes ReturnFair :: "Client ⇒ temporal"
      defines "ReturnFair c ≡ TEMP WF(∃S. id<$unsat,#c> = #{}
                                        ∧ id<$alloc,#c> = #S 
                                        ∧ Return c S)_vars"

In this specification, `Allocate` actions need only be weakly fair, in contrast
to the strong fairness used in the `SimpleAllocator`. In fact, it is enough to
require weak fairness of allocations only to the highest-priority client at the
head of the schedule:

      fixes AllocateHeadFair :: temporal
      defines "AllocateHeadFair ≡ TEMP WF(∃S c. #c = hd<$sched> 
                                              ∧ Allocate c S)_vars"

The final fairness condition requires that the pool is always eventually
scheduled:

      fixes ScheduleFair :: temporal
      defines "ScheduleFair ≡ TEMP WF(Schedule)_vars"

The full specification is the conjunction of the definitions above, in the
standard form for a TLA formula:

      fixes SchedulingAllocator :: temporal
      defines "SchedulingAllocator ≡ TEMP (Init InitState ∧ □[Next]_vars
            ∧ (∀c. ReturnFair c) ∧ AllocateHeadFair ∧ ScheduleFair)"

We require the same basic safety property as with the `SimpleAllocator`:

      fixes MutualExclusion :: stpred
      defines "MutualExclusion ≡ PRED
              ∀ c1 c2. #c1 ≠ #c2 ⟶ id<alloc,#c1> ∩ id<alloc,#c2> = #{}"

In addition, the following invariants will prove useful (and true) when working
with this specification. This list was grown organically while working through
the proofs, rather than invented up-front: the workflow was generally to reach
a point where an extra invariant was needed and then to add it to this list,
rework the safety proof to include the extra invariant, and the continue with
the main proof.

      fixes AllocatorInvariant :: stpred
      defines "AllocatorInvariant ≡ PRED
        ( (∀c. #c ∈ pool ⟶ id<unsat,#c> ≠ #{})
        ∧ (∀c. #c ∈ pool ⟶ id<alloc,#c> = #{})
        ∧ (∀c. #c ∈ set<sched> ⟶ id<unsat,#c> ≠ #{})
        ∧ (∀c. #c ∈ set<sched>
              ⟶ (∀c'. #c' ∈ higherPriorityClients c
              ⟶ id<alloc,#c> ∩ id<unsat,#c'> = #{}))
        ∧ (∀c. #c ∉ pool ⟶ #c ∉ set<sched> ⟶ id<unsat,#c> = #{})
        ∧ (∀c. id<alloc,#c> ∩ id<unsat,#c> = #{})
        ∧ (pool ∩ set<sched> = #{})
        ∧ finite<pool>
        ∧ (∀c. finite<id<unsat,#c>>)
        ∧ (∀c. finite<id<alloc,#c>>)
        ∧ distinct<sched>)"

The overall safety property is the conjunction of these.

      fixes Safety :: stpred
      defines "Safety ≡ PRED (MutualExclusion ∧ AllocatorInvariant)"

The system specifies no liveness properties up-front. Recall that the goal is
to show that this is a refinement of `SimpleAllocator`, which means it will
inherit the `SimpleAllocator`'s liveness properties.

## Safety

Recall that safety proofs normally work by showing that the initial state
satisfies the invariants and then showing that each step preserves the
invariants.  The initial state satisfies the safety property trivially:

      assume sigma: "sigma ⊨ SchedulingAllocator"
      thus "sigma ⊨ Init Safety"
        by (auto simp add: Init_def Safety_def SchedulingAllocator_def
              InitState_def MutualExclusion_def AllocatorInvariant_def)

It remains to show that each action preserves the invariants, which works out
by splitting the proof by cases and unwinding definitions without needing any
great insights. Indeed, this is how my first version of the safety proof ran.
However, the safety property is a conjunction of 12 separate properties, not
all of which can always be automatically proved, and you have to prove that all
these properties are preserved by all four kinds of action (as well as
stuttering steps). It's tempting to write proofs like this ...

      have "something"
        unfolding something_def something_else_def ...
      proof auto
        ...
      qed

... in which the initial `auto` tactic cleans up all the easy stuff and you
just work through anything that remains. Although this may work, it's poor
style and gets you into trouble: the remaining goals sometimes bear little
obvious relationship to the original goal, making them much harder to prove,
and subsequent changes to definitions and other refactorings can drastically
alter the result of `auto`, meaning you have to rework the whole proof.  An
alternative is to write everything out longhand and only use `auto` at the end,
which also works but is pretty tedious. Instead, I showed an explicit
_introduction_ lemma for the safety property:

    lemma SafetyI:
      assumes "⋀c1 c2. c1 ≠ c2 ⟹ alloc s c1 ∩ alloc s c2 = {}"
      assumes "⋀c. c ∈ pool s ⟹ unsat s c ≠ {}"
      assumes "⋀c. c ∈ pool s ⟹ alloc s c = {}"
      assumes "⋀c. c ∈ set (sched s) ⟹ unsat s c ≠ {}"
      assumes "⋀c1 c2. c1 ∈ set (sched s)
                      ⟹ c2 ∈ higherPriorityClients c1 s
                      ⟹ alloc s c1 ∩ unsat s c2 = {}"
      assumes "⋀c. alloc s c ∩ unsat s c = {}"
      assumes "⋀c. c ∉ pool s ⟹ c ∉ set (sched s) ⟹ unsat s c = {}"
      assumes "pool s ∩ set (sched s) = {}"
      assumes "finite (pool s)"
      assumes "distinct (sched s)"
      assumes "⋀c. finite (unsat s c)"
      assumes "⋀c. finite (alloc s c)"
      shows "s ⊨ Safety"
      unfolding Safety_def AllocatorInvariant_def MutualExclusion_def
      using assms by simp

The proof is trivial, but the resulting lemma makes it possible to write proofs
like this:

      have "t ⊨ Safety"
      proof (intro SafetyI) (* the resulting goals are exactly
                               the assumptions of lemma SafetyI *)
        ... (* prove just the cases that `auto` can't manage *)
      qed auto (* cleans up the rest of the cases *)

This helped to cut down on duplication a lot without resorting to poor style. I
guess that reducing duplication by extracting this kind of lemma is pretty
similar to extracting functions to reduce duplication when writing code.
Another big source of duplication in this model was proving something about
actions by splitting the proof into all the different actions that there could
be. This only happens once in the safety proof, but it comes up quite a few
times later too, so it was worth extracting this:

    lemma square_Next_cases [consumes 1, case_names unchanged Request Schedule Allocate Return]:
      assumes Next: "(s,t) ⊨ [Next]_vars"
      assumes unchanged: "
        ⟦ unsat t = unsat s;
          alloc t = alloc s;
          pool t = pool s;
          sched t = sched s;
          available t = available s;
          ⋀c'. higherPriorityClients c' t = higherPriorityClients c' s
        ⟧ ⟹ P"
      assumes Request: "⋀c S.
        ⟦ S ≠ {};
          finite S;
          unsat s c = {};
          alloc s c = {};
          unsat t = modifyAt (unsat s) c (add S);
          unsat t c = S;
          pool t = insert c (pool s);
          alloc t = alloc s;
          sched t = sched s;
          available t = available s;
          ⋀c'. higherPriorityClients c' t = higherPriorityClients c' s
        ⟧ ⟹ P"
      assumes Schedule: "⋀poolOrder.
        ⟦ pool s ≠ {};
          pool t = {};
          set poolOrder = pool s;
          distinct poolOrder;
          sched t = sched s @ poolOrder;
          unsat t = unsat s;
          alloc t = alloc s;
          available t = available s;
          ⋀c'. c' ∈ set (sched s)
                ⟹ higherPriorityClients c' t = higherPriorityClients c' s
        ⟧ ⟹ P"
      assumes Allocate: "⋀c S.
        ⟦ S ≠ {};
          S ⊆ available s;
          S ⊆ unsat s c;
          c ∈ set (sched s);
          ⋀c' r'. c' ∈ higherPriorityClients c s
                ⟹ r' ∈ unsat s c' ⟹ r' ∈ S ⟹ False;
          sched t = (if S = unsat s c then filter (op ≠ c) (sched s) else sched s);
          alloc t = modifyAt (alloc s) c (add S);
          alloc t c = alloc s c ∪ S;
          unsat t = modifyAt (unsat s) c (del S);
          unsat t c = unsat s c - S;
          pool t = pool s;
          available t = available s - S;
          ⋀c'. higherPriorityClients c' t
              = (if S = unsat s c
                  then if c' = c
                    then set (sched t)
                    else higherPriorityClients c' s - {c}
                  else higherPriorityClients c' s)
        ⟧ ⟹ P"
      assumes Return: "⋀c S.
        ⟦ S ≠ {};
          S ⊆ alloc s c;
          alloc t = modifyAt (alloc s) c (del S);
          unsat t = unsat s;
          pool t = pool s;
          sched t = sched s;
          available s ⊆ available t;
          ⋀c'. higherPriorityClients c' t = higherPriorityClients c' s
        ⟧ ⟹ P"
      shows P

Although this looks quite large in fact it's fairly simple in structure:

    lemma MyCases:
      assumes "A ∨ B ∨ ..."
      assumes CaseA: "⟦ A1; A2 ⟧ ⟹ P"
      assumes CaseB: "⟦ B1; B2; B3; ... ⟧ ⟹ P"
      ...
      shows P

The advantage of writing it like this is that you can then use it with
Isabelle's `cases` tactic:

      have "A ∨ B ∨ ..." by (magic)
      then show ImportantResult
      proof (cases rule: MyCases)
        case CaseA: (* brings assumptions A1 and A2 into scope *)
          ...
      next
        case CaseB: (* brings assumptions B1, B2, B3, ... into scope *)
          ...
      next
        ...
      qed

In this proof, saying `case CaseA` brings the assumptions `A1` and `A2` into
scope which is dead handy if they're a bit of a pain to prove and they turn out
to be needed each time you do this case split.  The full safety result now
follows without much further fuss.

## Liveness

Although there are no particular liveness properties given in the
specification, we still care about liveness. Our goal is to show that
`SchedulingAllocator` refines `SimpleAllocator`, i.e.

    ⊢ SchedulingAllocator ⟶ SimpleAllocator

This means we need to be able to derive `SimpleAllocator`'s fairness
properties, which are really just special kinds of liveness as they say that
certain transitions must eventually occur under certain conditions.

In the [last refinement proof]({% post_url 2018-02-18-tla-clock-specification
%}#refinement) we used rule `WF2` to derive one weak fairness property from
another. There is also rule `SF2` which allows you to derive strong fairness
properties from each other:

    lemma SF2:
      assumes 1: "⊢ N ∧ <B>_f ⟶ <M>_g"
        and 2: "⊢ $P ∧ P$ ∧ <N ∧ A>_f ⟶ B"
        and 3: "⊢ P ∧ Enabled(<M>_g) ⟶ Enabled(<A>_f)"
        and 4: "⊢ □(N ∧ [¬B]_f) ∧ SF(A)_f ∧ □F ∧ □◇Enabled(<M>_g) ⟶ ◇□P"
      shows "⊢ □N ∧ SF(A)_f ∧ □F ⟶ SF(M)_g"

That's all well and good, but the `SchedulingAllocator` has only weak fairness
properties whereas in `SimpleAllocator` the `Allocate` action is strongly fair.
This needs more thought.  Fortunately, weak and strong fairness are defined in
terms of more primitive things:

      WF_def: "⋀v. TEMP WF(A)_v  ==  TEMP ◇□ Enabled(<A>_v) ⟶ □◇<A>_v" and
      SF_def: "⋀v. TEMP SF(A)_v  ==  TEMP □◇ Enabled(<A>_v) ⟶ □◇<A>_v" and

In each case, the conclusion is that some action occurs infinitely often: a
liveness property. The two actions in question are the allocation and release
of resources (there's no guarantee that any client ever actually requests any
resources) so it seems that we can prove these in their "raw" form as basic
liveness properties rather than using anything special about the structure of
fairness properties.

As a first step, it felt worthwhile to prove specialised versions of rule `WF1`
for use with the `SchedulingAllocator`:

    lemma WF1_SchedulingAllocator_Schedule:
      assumes 1: "⋀s t. s ⊨ P ⟹ s ⊨ Safety ⟹ (s,t) ⊨ [Next]_vars ⟹ s ⊨ pool ≠ #{}"
      assumes 2: "⋀s t. s ⊨ P ⟹ s ⊨ Safety ⟹ (s,t) ⊨ [Next]_vars ⟹ s ⊨ finite<pool>"
      assumes 3: "⋀s t. s ⊨ P ⟹ s ⊨ Safety ⟹ (s,t) ⊨ [Next]_vars ⟹ t ⊨ P ∨ Q"
      assumes 4: "⋀s t. s ⊨ P ⟹ s ⊨ Safety ⟹ (s,t) ⊨ [Next]_vars ⟹ (s,t) ⊨ <Schedule>_vars ⟹ t ⊨ Q"
      shows      "⊢ SchedulingAllocator ⟶ (P ↝ Q)"

    lemma WF1_SchedulingAllocator_Allocate:
      assumes 1: "⋀s t. s ⊨ P ⟹ s ⊨ Safety ⟹ (s,t) ⊨ [Next]_vars ⟹ s ⊨ available ∩ id<unsat,hd<sched>> ≠ #{}"
      assumes 2: "⋀s t. s ⊨ P ⟹ s ⊨ Safety ⟹ (s,t) ⊨ [Next]_vars ⟹ s ⊨ sched ≠ #[]"
      assumes 3: "⋀s t. s ⊨ P ⟹ s ⊨ Safety ⟹ (s,t) ⊨ [Next]_vars ⟹ t ⊨ P ∨ Q"
      assumes 4: "⋀s t. s ⊨ P ⟹ s ⊨ Safety ⟹ (s,t) ⊨ [Next]_vars ⟹ (s,t) ⊨ <∃S c. #c = hd<$sched> ∧ Allocate c S>_vars ⟹ t ⊨ Q"
      shows      "⊢ SchedulingAllocator ⟶ (P ↝ Q)"

    lemma WF1_SchedulingAllocator_Return:
      assumes 1: "⋀s t. s ⊨ P ⟹ s ⊨ Safety ⟹ (s,t) ⊨ [Next]_vars ⟹ s ⊨ id<alloc,#c> ≠ #{}"
      assumes 2: "⋀s t. s ⊨ P ⟹ s ⊨ Safety ⟹ (s,t) ⊨ [Next]_vars ⟹ s ⊨ id<unsat,#c> = #{}"
      assumes 3: "⋀s t. s ⊨ P ⟹ s ⊨ Safety ⟹ (s,t) ⊨ [Next]_vars ⟹ t ⊨ P ∨ Q"
      assumes 4: "⋀s t. s ⊨ P ⟹ s ⊨ Safety ⟹ (s,t) ⊨ [Next]_vars ⟹ (s,t) ⊨ <∃S. id<$unsat,#c> = #{} ∧ id<$alloc,#c> = #S ∧ Return c S>_vars ⟹ t ⊨ Q"
      shows      "⊢ SchedulingAllocator ⟶ (P ↝ Q)"

In particular, these encapsulate the conditions needed to be sure that each
action is enabled: as mentioned last time, enabledness proofs do not play very
nicely with automation, so it's useful to get this out of the way at the top
level.

### Liveness of scheduling

Using `WF1_SchedulingAllocator_Schedule` it's pretty straightforward to show
that unsatisfied clients are eventually scheduled:

    lemma unsatisfied_leadsto_scheduled:
      "⊢ SchedulingAllocator ⟶ (id<unsat, #c> ≠ #{} ↝ #c ∈ set<sched>)"

That's where the straightforwardness ended.

### Liveness of allocation

For quite some time I followed this idea of trying to showing the liveness of
allocation directly, using wellfounded induction, like [last time]({% post_url
2018-03-23-tla-resource-allocator %}#requests-are-eventually-satisfied).  It
was working, in a sense: after quite some effort I had managed to reach
half-way.  But it felt _painful_, and showing the other half looked like it was
going to be similarly hard work. The proof script was on track to exceed 5000
lines.  I was doing something wrong.

The trouble was, at least partly, that the induction is much more tangled than
it was last time. With `SimpleAllocator`, each allocation obviously takes you
closer to your goal: either you allocated everything or else you can find a
client holding a resource you need, wait for it to release everything, and then
do more allocation. Here this is less obviously true, because you're not
allowed to allocate anything for which a higher-priority client is waiting, and
you have to completely satisfy a client before you can be sure it will
eventually return its resources so they can be allocated to the
next-highest-priority client, and so on until you get to the target client.
More precisely, in order to show that a request is eventually satisfied, the
requesting client needs to be at the head of the schedule, and the requested
resource must not already be allocated.  If the client in question is not at
the head of the schedule then the client that _is_ at the head of the schedule
will eventually be satisfied and removed from the schedule. But _this_ client
can only be allocated more resources if there are some that are not held by
some other client (which is necessarily unscheduled and satisfied), which must
eventually happen but not necessarily immediately. And during all those
"eventually"s the original resource might already have been allocated and
returned by the original client. The formulae in the proof end up being
unmanageably large disjunctions to deal with this.

Unfortunately there's no way around this tangle of inductions, because it's a
fundamental part of the way the specification works. After some reflection, I
concluded that the painful thing was that the tangle was wrapped around the
actual content of the proof, with substantial duplication, and it'd be a good
idea to refactor it out, separating the tangle from the main proof.

The goal of this refactoring was to have the proof structured as a _single_
induction, perhaps over a quite complicated structure, rather than a nest of
related inductions. This raises the question of what kind of structure are we
looking for?  The tricky bit of the specification's behaviour is showing that a
scheduled (and hence unsatisfied) client `c` is eventually completely satisfied
(and hence removed from the schedule). This means that the structure we're
looking for is something that never increases while `c` is scheduled, and which
we can use the fairness properties to show that it eventually strictly
decreases.

The main fair step that brings `c` closer to satisfaction is allocating
resources to the head of the schedule: it either reduces the set of resources
on which the head is waiting, or else completely satisfies the head which
increases `c`'s priority by 1. Unfortunately this step isn't always enabled,
because all of the resources for which the head is waiting are already
allocated to other clients, so we also need to count unblocking the head as a
step towards satisfaction. It seems pretty obvious when you write it like that,
but this was far from obvious up-front, and there are lots of ways of capturing
this observation, but after _many_ iterations it boiled down to:

    record Inductor =
      higherSched :: "Client set"
      hd_unsats   :: "Resource set"
      hd_blocked  :: bool

    definition inductor :: "Client ⇒ Inductor stfun"
      where "inductor c s ≡ ⦇ higherSched = higherPriorityClients c s
                            , hd_unsats  = unsat s (hd (sched s))
                            , hd_blocked = unsat s (hd (sched s)) ∩ available s = {}
                            ⦈"

The `Inductor` is the type over which we do induction, and comprises three
components: the set of clients that have a higher priority than `c`, the set of
resources on which the head of the schedule is waiting, and a flag indicating
whether the head is blocked or not. The order on this is the lexicographic
product of the obvious orders:

    lemma inductor_prec_eq:
      assumes "s ⊨ Safety"
      shows "(inductor c t ≺ inductor c s)
        = (   higherPriorityClients c t ⊂ higherPriorityClients c s
           ∨ (higherPriorityClients c t = higherPriorityClients c s
              ∧ unsat t (hd (sched t)) ⊂ unsat s (hd (sched s)))
           ∨ (higherPriorityClients c t = higherPriorityClients c s
              ∧ unsat t (hd (sched t)) = unsat s (hd (sched s))
              ∧ (unsat s (hd (sched s)) ∩ available s = {})
              ∧ (unsat t (hd (sched t)) ∩ available t ≠ {})))"

Since `higherSched` and `hd_unsats` are both finite sets, this order is
wellfounded as needed for the induction to work. Hopefully this looks like this
should fit nicely with the fairness properties: when the head is blocked, the
fairness of `Return` means it will eventually become unblocked, reducing
`hd_blocked`, and when the head is not blocked then the fairness of `Allocate`
either reduces `hd_unsats` or else completely satisfies it, reducing
`higherSched`. By taking the lexicographic product in this order, it's fine if
allocating some resources to the head makes it become blocked, and fine if
completely satisfying the head replaces it with a new head that's waiting for
more resources.

It is also important to know that it never increases while `c` is scheduled, or
else the induction collapses:

    lemma
      assumes Safety_s: "s ⊨ Safety"
        and Next: "(s,t) ⊨ [Next]_vars"
        and scheduled: "c ∈ set (sched s)"
      shows scheduled_progress:
          "(s,t) ⊨ (op ≼)<(inductor c)$,$(inductor c)> ∨ #c ∉ set<sched$>"

The slightly ugly conclusion of this lemma is just because there's no syntactic
trickery defined for lifting `≼` to become a temporal operator, so although we
want to write `(inductor c)$ ≼ $(inductor c)` we have to say `(op ≼)<(inductor
c)$,$(inductor c)>` instead. In words, this says that as long as `c` is
scheduled, when we take a step either `c` becomes unscheduled or else `inductor
c` does not increase.

This puts us in a good position to show that clients are always eventually
removed from the schedule:

    lemma infinitely_often_unscheduled:
        "⊢ SchedulingAllocator ⟶ □◇(#c ∉ set<sched>)"

Lemma `unstable_implies_infinitely_often` allows us to only consider scheduled
clients (as clearly an always-unscheduled client satisfies this property)
reducing the goal to `#c ∈ set<sched> ↝ #c ∉ set<sched>` which is a good
starting point for the induction:

        have "⊢ SchedulingAllocator
            ⟶ (#c ∈ set<sched>
                    ↝ (∃i. #i = inductor c ∧ #c ∈ set<sched>))"
          by (intro imp_imp_leadsto, auto)
        also have "⊢ SchedulingAllocator
            ⟶ ((∃i. #i = inductor c ∧ #c ∈ set<sched>)
                    ↝ #c ∉ set<sched>)"

Using the induction rule here yields the goal of showing that eventually either
`c` is unscheduled or else the inductor `i` can be reduced:

    proof (state)
    goal (1 subgoal):
     1. ⋀i. ⊢ SchedulingAllocator
                ⟶ (#i = inductor c ∧ #c ∈ set<sched>
                        ↝ #c ∉ set<sched>
                          ∨ (∃y. #(y ≺ i) ∧ #y = inductor c ∧ #c ∈ set<sched>))

There's two situation to consider at each step: either the head is blocked or
it is not. The rule `imp_leadsto_diamond` is what's needed to do the split:

    lemma imp_leadsto_diamond:
      assumes "⊢ S ⟶ (A ↝ (B ∨ C))"
      assumes "⊢ S ⟶ (B ↝ D)"
      assumes "⊢ S ⟶ (C ↝ D)"
      shows   "⊢ S ⟶ (A ↝ D)"

In the situation where the head is blocked, we expect to use
`WF1_SchedulingAllocator_Return` to show that it's eventually unblocked; this
needs us to first find a specific client that's blocking the head, which is
done by introducing an existential:

    have "⊢ SchedulingAllocator
          ⟶ (#i = inductor c ∧ #c ∈ set<sched>
                               ∧ id<unsat, hd<sched>> ∩ available = #{}
            ↝ (∃ blocker. #i = inductor c ∧ #c ∈ set<sched>
                       ∧ id<unsat, hd<sched>> ∩ available = #{}
                       ∧ id<unsat, hd<sched>> ∩ id<alloc,#blocker> ≠ #{}))"
    ...
    also have "⊢ SchedulingAllocator
          ⟶ ((∃ blocker. #i = inductor c ∧ #c ∈ set<sched>
                       ∧ id<unsat, hd<sched>> ∩ available = #{}
                       ∧ id<unsat, hd<sched>> ∩ id<alloc,#blocker> ≠ #{})
            ↝ #c ∉ set<sched>
                ∨ (∃i'. #(i' ≺ i) ∧ #i' = inductor c ∧ #c ∈ set<sched>))"
    proof (intro imp_exists_leadstoI WF1_SchedulingAllocator_Return)
      ...

From here the proof is really just checking all the cases. One useful
intermediate result comes from the fact that the inductor never increases while
`c` is scheduled:

    have "(s, t) ⊨ (op ≼)<inductor c$,$inductor c> ∨ #c ∉ set<sched$>" by ...
    with s_Safety consider
        (alloc)    "c ∉ set (sched t)"
      | (progress) "c ∈ set (sched t)" "inductor c t ≺ inductor c s"
      | (same)     "c ∈ set (sched t)" "inductor c t = inductor c s"
                   "(unsat t (hd (sched t)) ∩ available t = {})
                  = (unsat s (hd (sched s)) ∩ available s = {})"

This gives us a local proof-by-cases rule that makes things quite neat: the
`alloc` and `progress` cases give desired conclusion trivially, and the bulk of
the rest of the work is to show that the `same` case:

1. leaves us in the same state as before, with the head blocked by `blocker`,
and

2. is impossible if `Return blocker (unsat blocker)` occurs, which eventually
happens by fairness.

In the situation where the head is not blocked, we expect to use
`WF1_SchedulingAllocator_Allocate` to show that it eventually makes progress;
this needs us to find the head before the rule can be applied, which is done
again by introducing an existential:

    have "⊢ SchedulingAllocator
          ⟶ (#i = inductor c ∧ #c ∈ set<sched>
                      ∧ id<unsat, hd<sched>> ∩ available ≠ #{}
            ↝ (∃ topPriority. #i = inductor c ∧ #topPriority = hd<sched>
                          ∧ #c ∈ set<sched>
                          ∧ id<unsat, hd<sched>> ∩ available ≠ #{}))"
    ...
    also have "⊢ SchedulingAllocator
          ⟶ ((∃ topPriority. #i = inductor c ∧ #topPriority = hd<sched>
                          ∧ #c ∈ set<sched>
                          ∧ id<unsat, hd<sched>> ∩ available ≠ #{}) 
            ↝ #c ∉ set<sched>
                  ∨ (∃y. #(y ≺ i) ∧ #y = inductor c ∧ #c ∈ set<sched>))"
    proof (intro imp_exists_leadstoI WF1_SchedulingAllocator_Allocate)
      ...

As before, the rule about the inductor never increasing gives us a nice local
proof-by-cases rule:

    have "(s, t) ⊨ (op ≼)<inductor c$,$inductor c> ∨ #c ∉ set<sched$>" by ...
    with s_Safety consider
        (alloc)    "c ∉ set (sched t)"
      | (progress) "c ∈ set (sched t)" "inductor c t ≺ inductor c s"
      | (same)     "c ∈ set (sched t)" "inductor c t = inductor c s"
                   "higherPriorityClients c t = higherPriorityClients c s"
                   "(unsat t (hd (sched t)) ∩ available t = {})
                  = (unsat s (hd (sched s)) ∩ available s = {})"
                   "unsat t (hd (sched t)) = unsat s (hd (sched s))"

Again the `alloc` and `progress` cases give the desired conclusion trivially,
and the bulk of the rest of the work is to show that nothing important changes
in the `same` case again, and that an `Allocate` action on the head of the
schedule implies that the `same` case did not occur.

### Liveness of the returning of resources

Having shown that clients are always eventually removed from the schedule it's
fairly straightforward to show that each client always eventually releases all
its resources:

    lemma infinitely_often_freed: "⊢ SchedulingAllocator ⟶ □◇(id<alloc,#c> = #{})"

A client that's holding resources is eventually not in the schedule. It may or
may not still hold resources by this point, but using the `imp_leadsto_diamond`
rule is a good way to consider those two situations separately. Since one of
those situations trivially shows the desired conclusion, a special case of the
diamond rule is more useful:

    imp_leadsto_triangle_excl [OF imp_leadsto_reflexive]:
      ⊢ S ⟶ (A ∧ ¬ C ↝ C) ⟹ ⊢ S ⟶ (A ↝ C)

The result follows without further fuss.

## Refinement

After all this, we can now pop the stack back to our original goal, showing
that the `SchedulingAllocator` is a refinement of the `SimpleAllocator`

    lemma refinement: "⊢ SchedulingAllocator ⟶ SimpleAllocator"

The two specifications were defined independently, in separate locales, which
allows us to bring them together by defining another locale, renaming the
clashing symbols:

    locale Refinement
      = Simple: SimpleAllocator
      where InitState    = InitState_Simple
        and Request      = Request_Simple
        and Allocate     = Allocate_Simple
        and Return       = Return_Simple
        and Next         = Next_Simple
        and ReturnFair   = ReturnFair_Simple
        and AllocateFair = AllocateFair_Simple
        and Safety       = Safety_Simple
        + SchedulingAllocator
      for InitState_Simple Request_Simple Allocate_Simple Return_Simple
        Next_Simple ReturnFair_Simple AllocateFair_Simple Safety_Simple

    context Refinement
    begin

All the definitions and theorems of the `SchedulingAllocator` locale are
available in the `Refinement` locale normally. The theorems of
`SimpleAllocator` are also available, but their names are prefixed with
`Simple.` to avoid collisions. The clashing symbols are redefined explicitly as
above. It's a little ugly that the symbols can't be renamed with a `Simple.`
prefix, so for instance the definition of `InitState_Simple` is called
`Simple.InitState_def`, but this is not insurmountable.

The `SimpleAllocator` spec had four parts: the initial state, the next-step
relation, and two fairness properties.  The initial state and next-step
relation follow quickly from the `SchedulingAllocator` spec. The
`SchedulingAllocator` turns out to satisfy a very strong fairness property for
the `Return` and `Allocate` actions: if they are ever enabled, even once, then
they eventually execute. This implies strong fairness as follows:

    lemma imp_SFI:
      assumes "⊢ S ⟶ (Enabled (<A>_v) ↝ <A>_v)" 
      shows "⊢ S ⟶ SF(A)_v"

Of course strong fairness implies weak fairness as the names suggest:

    lemma SFImplWF: "⊢ SF(A)_v ⟶ WF(A)_v"

It remains to show the claimed very strong fairness properties.

### Fairness of the returning of resources

Firstly we look at `A ≡ ∃S. id<$alloc, #c> = #S ∧ Return_Simple c S`. If this
action is enabled then certainly `c` holds some resources:

    have "⊢ SchedulingAllocator
        ⟶ (Enabled (<∃S. id<$alloc, #c> = #S ∧ Return_Simple c S>_(unsat,alloc))
            ↝ id<alloc,#c> ≠ #{})"

We also know that all resources are eventually freed but there's a couple of
small obstacles to using this fact straight away. Firstly, there are
specifications in which `□◇(id<alloc,#c> = #{})` is true but which no action
satisfying the specification of `Return_Simple` ever occurs: for instance a
specification in which two clients repeatedly pass their resources back and
forth. Secondly, the fact that `□◇(id<alloc,#c> = #{})` holds suffers from a
kind of "overshoot", yielding a state in which `Return_Simple` has already
occurred (possibly many steps previously).  The following lemma rescues this
situation, finding the transition at which `c` released the last of its
resources:

    lemma imp_unstable_leadsto_change:
      assumes "⊢ S ⟶ (P ↝ ¬P)"
      shows "⊢ S ⟶ (P ↝ ($P ∧ ¬P$))"

By enumerating the possible actions in `SchedulingAllocator`, the only way that
an action satisfying `id<$alloc,#c> ≠ #{} ∧ id<alloc$,#c> = #{}` can occur is
if it was `Return c (alloc c)` which satisfies the specification of
`Return_Simple` as needed.

### Fairness of allocation

Essentially the same reasoning works for `A ≡ ∃S. Allocate_Simple c S`: if
allocation to a client `c` is enabled then `c` must be unsatisfied, and we
showed that every client is eventually completely satisfied, so there's an
action which satisfies `id<$unsat,#c> ≠ #{} ∧ id<unsat$,#c> = #{}`, which by
looking at the possible actions in `SchedulingAllocator` must be an `Allocate`
action which satisfies the specification of `Allocate_Simple` as required.

It follows that

    ⊢ SchedulingAllocator ⟶ SimpleAllocator

as desired.

## Conclusion

The `SchedulingAllocator` feels like a more realistic example of a
specification, containing nontrivial nondeterminism and more intricate
interactions between the various actors. As specifications get more complex,
the direct approach to proofs starts to break down, since it involves some
duplication of effort which the proof automation finds increasingly difficult
to cut through.

Factoring out this duplicated work into separate lemmas worked well here. In
particular, the `square_Next_cases` lemma was invaluable in all the places
where we needed to consider all the different actions that could take place.
Similarly, giving a name to the "inductor" allowed us to prove useful
properties to support the various cases within the induction.

Showing a refinement relationship involves proving various fairness properties,
which are really just special kinds of liveness property since they say that
under certain conditions certain things eventually occur. In this case the
specification satisfied some very strong fairness properties: if the actions in
question were eventually enabled, even once, then they eventually occurred.
Comparing to weak and strong fairness, very strong fairness looks a little like
this:

      WF_def:  "⋀v. TEMP  WF(A)_v  ==  TEMP ◇□ Enabled(<A>_v) ⟶ □◇<A>_v" 
      SF_def:  "⋀v. TEMP  SF(A)_v  ==  TEMP □◇ Enabled(<A>_v) ⟶ □◇<A>_v"
      VSF_def: "⋀v. TEMP VSF(A)_v  ==  TEMP  ◇ Enabled(<A>_v) ⟶  ◇<A>_v"

It seemed simpler that we could show very strong fairness, rather than needing
to show the weaker properties directly.  It'll be interesting to think about
situations where very strong fairness doesn't hold, as it seems like quite a
common property to have.

It was interesting to discover `imp_unstable_leadsto_change`, a kind of
discrete analogue of the [intermediate value
theorem](https://en.wikipedia.org/wiki/Intermediate_value_theorem) which
allowed us to get hold of the pair of adjacent states at which a particular
transition occurred, simply from evidence that the transition had occurred at
some point.

Locales were useful for limiting the scope of each specification, and
Isabelle's flexible mechanism for importing locales meant it was possible to
combine the two specifications together in order to compare them, even though
there were name collisions and conflicting definitions.  Unfortunately I'm not
sure that you can do advanced things like variable hiding (modelled in TLA via
temporal existential quantification) using this mechanism, but it worked well
here.

