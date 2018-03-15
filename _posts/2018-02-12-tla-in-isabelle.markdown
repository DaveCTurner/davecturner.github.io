---
layout: post
title:  "TLA+ in Isabelle/HOL"
date:   2018-02-12 19:09:09 +0000
---

I'm a fan and long-term user of the [Isabelle/HOL proof
assistant](https://isabelle.in.tum.de). More recently I have been studying
Lamport's [TLA+ system](https://lamport.azurewebsites.net/tla/tla.html) which
is a popular choice for writing specifications of systems. This post is a
slightly tidied-up version of some notes about my early experiences of playing
with the implementation of TLA within Isabelle/HOL, to record a handful of
obstacles I hit and some techniques I found useful.

_Addendum:_ this post has grown into a series of posts, which continues to
expand:

- **TLA+ in Isabelle/HOL**

- [Refining specifications in TLA+ and Isabelle/HOL]({% post_url
  2018-02-18-tla-clock-specification %})

- [Using TLA's induction rule]({% post_url 2018-03-23-tla-resource-allocator
  %})

- [Fairness properties in refinement proofs]({% post_url
  2018-03-24-tla-resource-scheduler %})

## Introduction

TLA is a simple linear-temporal logic that is expressive enough to describe the
evolution of a system over time. Linear-temporal logics typically allow
formulae to be written that express relationships between the state of the
system at arbitrary times, whereas in TLA one can only really talk about
_actions_: relationships between pairs of successive states. This makes things
a whole load simpler without much practical effect on the expressiveness of the
logic. Additionally there are some constraints on the kinds of formulae that
can be written that force specifications to be invariant under _stuttering_,
which makes it much more straightforward to compose specifications out of
other, smaller, specifications, reflecting the decomposition of a system into
its subsystems.

There are two main tools (that I'm aware of) that help to investigate the
validity of a TLA+ specification: the [TLC model
checker](https://lamport.azurewebsites.net/tla/tlc.html), and the [TLAPS proof
system](https://tla.msr-inria.inria.fr/tlaps/content/Home.html). TLC is capable
of completely verifying properties of finite models, and does a pretty good job
of exploring infinite models too. TLAPS is a proof system that promises the
ability to formally prove properties of TLA+ models, allowing for a more
rigorous verification than a model-checker such as TLC can offer.

### TLAPS

I've never used TLAPS but I have read about it a bit. Since I'm currently
interested in TLA (the logic) and much more familiar with Isabelle, I thought
it'd be more useful to play around with TLA in Isabelle rather than try and
learn about it whilst also learning TLAPS. That said, I noted down some
questions about TLAPS that I'd like to answer in due course.

Firstly, at the time of writing, the TLAPS website says:

> The current release of TLAPS does not perform temporal reasoning, and it does
> not handle some features of TLA+. [...] TLAPS is now suitable for verifying
> safety properties of non-trivial algorithms.

I'm interested in proofs of both safety and liveness properties, and [Ron
Pressler says](https://twitter.com/pressron/status/962715285823393794) that the
website is out of date and gives some simple examples of temporal reasoning.
What are TLAPS's limits these days? Can it, for instance, use custom induction
principles in liveness proofs?

Next, the [Practical
Hints](https://tla.msr-inria.inria.fr/tlaps/content/Documentation/Tutorial/Practical_hints.html)
section of the TLAPS manual says the following, on the use of `ASSUME` and
`AXIOM`:

> Asserting facts is dangerous, because it's easy to make a mistake and assert
> something false, making your entire proof unsound. Fortunately, you can use
> the TLC model checker to avoid such mistakes.

It goes on to suggest the following assumption:

```
ASSUME GCDProperty3 ==
       \A p, q \in Nat \ {0}: (p < q) => GCD(p, q) = GCD(p, q-p)
```

Is this written as an assumption to keep the example short or can TLAPS not
prove properties like this?  Relying on TLC to verify that this kind of
property holds for many instances is often fine, and it's very valuable to be
able to quickly check such statements while you're developing a specification,
but I find it unsatisfactory that it's not eventually proved. I once spent
nearly a year developing some theory that turned out to be worthless due to a
plausible, yet false, assumption on the first page, so perhaps I am just
unreasonably averse to making the same sort of mistake again.

Furthermore, TLAPS is really just a front-end to a variety of provers,
including Isabelle, and this property is a specialisation of lemma `gcd_diff1`
in Isabelle's [GCD theory](https://isabelle.in.tum.de/library/HOL/HOL/GCD.html)
which is part of its extensive library of formalised mathematics, so it feels
as if TLAPS should be able to use this lemma directly instead of relying on a
user-specified assumption. It'd be interesting to find out whether this is
possible or not.

This also raises the question of how the integration between TLAPS and Isabelle
works, and particularly whether it's possible to automatically carry
definitions across from TLA+ in a way that lets me continue to use Isabelle's
rich proof system directly.

### Isabelle

The purpose of this article wasn't really to talk about TLAPS, but this sets
the context for my excitement at discovering that Isabelle includes [a
formalisation of (typed)
TLA](https://members.loria.fr/SMerz/projects/isabelle-tla/index.html) without
any obvious restrictions on the supported features of TLA or its integration
with the rest of Isabelle's other mathematical libraries. In fact, this
formalisation supports so-called "raw" TLA, which is a superset of TLA that is
not stuttering-invariant. Stuttering-invariance is a useful property of
specifications as it makes them easier to compose, but it seems likely that
it's sound and useful to be able to work in the "raw", stuttering-sensitive,
superset when doing proofs.

## Example: Termination Detection

The TLAPS distribution includes some examples, and one which caught my eye was
a formalisation of [Dijkstra's distributed termination detection
algorithm](https://www.cs.utexas.edu/users/EWD/ewd08xx/EWD840.PDF). The setup
is a fixed network of nodes each of which, if active, can activate other nodes
by passing messages. The purpose of the algorithm is to detect if all nodes
have become inactive. It works by passing a token from node to node (i.e. in a
ring) which collects information about the existence of active nodes. It is a
little subtle because an inactive node that's already passed the token on may
be activated by a node that's not yet received the token and which becomes
inactive before it does so. The [full description in
EWD840](https://www.cs.utexas.edu/users/EWD/ewd08xx/EWD840.PDF) is worth
reading for more details.

The example in the TLAPS distribution includes a proof of its safety property,
which says that the algorithm only detects termination if all nodes are indeed
inactive:

```
TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

...

THEOREM Spec => []TerminationDetection
```

It also includes a statement, but no proof, of a liveness property which
says that if all nodes are inactive then the algorithm eventually detects
termination:

```
Liveness ==
  (\A i \in Nodes : ~ active[i]) ~> terminationDetected
```

I thought it'd be a cute exercise to see what this algorithm looked like
formalised in Isabelle, and to see what a proof of that liveness property
looked like. I posted [a Gist of the resulting
theory](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21)
and will walk through some of its highlights below.

### Initial experiences

I initially found it quite hard work to use the TLA theory, at least partly
because of all the clever syntactic tricks it pulls. In Isabelle, TLA formulae
look like this:

```
"⊢ S ⟶ ((B ∧ ¬C) ↝ C)"
```

The turnstile (`⊢`) denotes that the following formula is _valid_, i.e., true
in all possible worlds. But there is overloading going on here: sometimes a
"world" is a single state; others are pairs of consecutive states; and yet
others are _behaviours_ which are, morally, infinite sequences of states. The
formula above is about a behaviour because it involves the leads-to (`↝`)
operator, but the operands of the leads-to operator may be single-state or
state-pair formulae.

This led to a certain amount of frustration, because some theorems about
formulae like the one above might only be applicable at certain types, and the
type constraints aren't clear from the usual output. While I was exploring it
helped a lot to make Isabelle be much more verbose with these declarations:

```
declare [[show_types]]
declare [[show_consts]]
```

A further source of confusion was that many of the things that look like
functions are in fact just more syntactic tricks: the names of
previously-declared functions are written in black text, but things like `Init`
and `Enabled` are a kind of turquoise colour because they're not really
functions. This means you can't (easily) search for theorems that mention them
in the _Query_ tab, since `Init` on its own is not a well-formed term so
searching for that yields a syntax error.

### Definitions

The Isabelle version of TLA is typed, unlike Lamport's TLA, so after a few
utility lemmas the theory [defines some
types](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L84-L86):

```
axiomatization NodeCount :: nat where NodeCount_positive: "NodeCount > 0"
typedef Node = "{0..<NodeCount}" using NodeCount_positive by auto
```

This defines a finite type `Node` as a subtype of the natural numbers. I think
it would all still have worked to just use `nat` throughout, although by using
a separate type you can keep from proliferating the assertion that node numbers
are `<NodeCount`.  Because `Node` is a separate type from `nat`, we need to
explicitly define things like an
[ordering](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L92-L105)
and an [induction principle](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L126-L129) to be used later.

```
datatype TerminationState = MaybeTerminated | NotTerminated
```

[This
type](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L154)
is used instead of colours (respectively white and black) for the state of the
token and of the nodes.

```
axiomatization
  isNodeActive  :: "(Node ⇒ bool) stfun" and
  nodeState     :: "(Node ⇒ TerminationState) stfun" and
  tokenPosition :: "Node stfun" and
  tokenState    :: "TerminationState stfun"
  where
  ewd_basevars: "basevars (isNodeActive, nodeState, tokenPosition, tokenState)"
```

[This](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L156-L162)
declares the variables along with their types. The `stfun` type constructor is
short for _state function_ and indicates that each of these depends on the
state of the system. The `basevars` axiom effectively says that these variables
are all independent of each other, and so their values can be freely changed by
actions.

```
definition StartState :: stpred where
  "StartState == PRED tokenPosition = #FirstNode ∧ tokenState = #NotTerminated"
```

The [definition of the initial
state](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L164-L165)
looks like this. Its type, `stpred`, means _state predicate_, and is short for
`bool stfun`. Recall that `tokenPosition` and `tokenState` are the base
variables; the `#` prefix on `FirstNode` and `NotTerminated` "lifts" these
constant values to become (constant) state functions. The `PRED` thing is more
syntactic trickery to let Isabelle know that the following syntax should be
parsed as a state predicate and not as an ordinary expression; this is
necessary for the `#` prefixes to work, and also note that the conjunction
(`∧`) is an overloaded version of the usual one that applies at each state
separately.

```
definition InitiateProbe :: action where
  "InitiateProbe == ACT
    (($tokenPosition = #FirstNode)
    ∧ ($tokenState = #NotTerminated ∨ id<$nodeState,#FirstNode> = #NotTerminated)
    ∧ tokenPosition$ = #LastNode
    ∧ tokenState$ = #MaybeTerminated
    ∧ (unchanged isNodeActive)
    ∧ (updatedFun nodeState FirstNode (const MaybeTerminated)))"

definition PassToken :: "Node ⇒ action" where
  "PassToken i == ACT
    (($tokenPosition = #i)
    ∧ ($tokenPosition ≠ #FirstNode)
    ∧ (¬ id<$isNodeActive,#i> ∨ id<$nodeState,#i> = #NotTerminated ∨ $tokenState = #NotTerminated)
    ∧ (tokenPosition$ = PreviousNode<$tokenPosition>)
    ∧ (tokenState$ = (if id<$nodeState,#i> = #NotTerminated then #NotTerminated else $tokenState))
    ∧ (unchanged isNodeActive)
    ∧ (updatedFun nodeState i (const MaybeTerminated)))"
```

The [definitions of the actions that perform a termination probe look like
this](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L167-L184).
The type `action` is a synonym for `bool trfun`, i.e. a boolean _transition
function_, a predicate on pairs of states. The `ACT` thing is the analogue of
`PRED` above, and `#` symbols lift constants as before.

In TLA+, transition functions are defined in terms of primed and unprimed
variables, but in the Isabelle translation the same concepts use a suffix and
prefix `$` symbol respectively. For instance, `$tokenPosition = #FirstNode` is
an enabling condition, indicating that the token must be at the first node
before this transition, and `tokenPosition$ = #LastNode` indicates that the
transition moves the token to the last node. As in TLA+, `unchanged X` is
shorthand for `$X = X$`.

The `updatedFun nodeState FirstNode (const MaybeTerminated)` expression is my
own (poor) reflection of `[nodeState EXCEPT ![FirstNode] = MaybeTerminated]`
[defined
locally](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L76-L77)
because it doesn't look like this is in the library and I'm not good enough at
Isabelle's syntactic trickery try and get closer to the TLA+ syntax at this
point.

Fixed functions can be applied to (up to 3) variable arguments using the
angle-bracket syntax `f<x,y>`. In this specification the variables `nodeState`
and `isNodeActive` are themselves functions, but `nodeState<#FirstNode>` does
not work since the function outside the angle brackets is a variable and not a
fixed function: it is part of the system's changing state. Using `id`, the
identity function, works around this: `id f x = f x`, so `id<f,x>` applies the
(variable) function `f` to the (variable) argument `x`.

```
definition SendMsg :: "Node ⇒ action" where
  "SendMsg i == ACT
    id<$isNodeActive,#i>
    ∧ (∃ j. #j ≠ #i ∧ (updatedFun isNodeActive j (const True))
                     ∧ (updatedFun nodeState i (ACT if #i < #j then #NotTerminated else id<$nodeState,#i>)))
    ∧ unchanged (tokenPosition, tokenState)"

definition Deactivate :: "Node ⇒ action" where
  "Deactivate i == ACT
    id<$isNodeActive,#i>
    ∧ (updatedFun isNodeActive i (const False))
    ∧ unchanged (tokenPosition, tokenState, nodeState)"
```

The definitions of the [actions that may occur outside of the control of the
termination detection
algorithm](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L186-L197)
are similar. In `SendMsg` the guard `#i < #j` can, according to the paper, be
replaced by `#True` without affecting its correctness.

```
definition Controlled :: action where
  "Controlled ≡ ACT (InitiateProbe ∨ (∃ n. PassToken n))"

definition Environment :: action where
  "Environment ≡ ACT (∃ n. SendMsg n ∨ Deactivate n)"

definition Next :: action where
  "Next ≡ ACT (Controlled ∨ Environment)"

definition Fairness :: temporal where
  "Fairness ≡ TEMP WF(Controlled)_(isNodeActive,nodeState,tokenPosition,tokenState)"

definition Spec :: temporal where
  "Spec ≡ TEMP (Init StartState ∧ □[Next]_(isNodeActive,nodeState,tokenPosition,tokenState) ∧ Fairness)"
```

The [remainder of the
specification](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L199-L212)
is also similar. Note that `Fairness` and `Spec` have type `temporal`
indicating that they are predicates on _behaviours_ (infinite sequences of
actions). The `WF` operator indicates weak fairness: if `Controlled` is
eventually always enabled then it eventually executes, changing the value of at
least one of the subscripted variables.

Notice that `Spec` is in the standard form for a TLA+ formula, describing its
initial state, a stuttering-invariant transition relation, and some fairness
rules.

```
definition TerminationDetected :: stpred where
  "TerminationDetected ≡ PRED
    (tokenPosition = #FirstNode
    ∧ tokenState = #MaybeTerminated
    ∧ id<nodeState,#FirstNode> = #MaybeTerminated
    ∧ ¬ id<isNodeActive,#FirstNode>)"
```

Finally, here is the [definition of how the algorithm detects
termination](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L214-L219).
It should be straightforward to see that this condition can be checked locally
on `FirstNode`.

### Safety

```
definition AllNodesInactive :: stpred where
  "AllNodesInactive ≡ PRED (∀ n. ¬ id<isNodeActive,#n>)"

definition SafetyInvariant where
  "SafetyInvariant ≡ PRED
    (∀ n. (tokenPosition < #n) ⟶ ¬ id<isNodeActive,#n>)
    ∨ (∃ n. #n ≤ tokenPosition ∧ id<nodeState,#n> = #NotTerminated)
    ∨ tokenState = #NotTerminated"

lemma safety:
  shows "⊢ Spec ⟶ □(TerminationDetected ⟶ AllNodesInactive)"
proof -
  ...
```

The [algorithm's safety
condition](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L278-L289)
is that it detects termination only if all nodes really are inactive. As in the
paper and the TLAPS presentation, it proceeds by [showing a safety
invariant](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L290-L291)
and then showing that this invariant implies the appropriate condition:

```
  have "⊢ Spec ⟶ □SafetyInvariant"
  proof invariant
    ...
```

The `invariant` proof method is appropriate for goals of this form, where
`SafetyInvariant` must be of type `stpred`. This was one case where the
overloading was confusing: other goals of the same syntactic form, but with an
`action` or `temporal` expression instead, cannot be reduced by this method.

The resulting subgoals are:

```
goal (2 subgoals):
 1. ⋀sigma. Spec sigma ⟹ sigma ⊨ Init SafetyInvariant
 2. ⋀sigma. Spec sigma ⟹ sigma ⊨ stable SafetyInvariant
```

This looks a lot like an induction proof: show that the initial state satisfies
the invariant, and then show that it is `stable` (i.e. once it becomes true it
remains true forever). The proofs of these goals are just definition-unwinding;
the second requires a case analysis on which transition within `Next` is
actually taken, which takes up some space.

After this step is complete, it remains to show that the invariant [implies the
safety
property](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L411-L413):

```
  moreover have "⊢ □SafetyInvariant ⟶ □(TerminationDetected ⟶ AllNodesInactive)"
    unfolding SafetyInvariant_def
  proof (intro STL4, clarsimp, intro conjI impI)
    ...
```

The TLA axiom `STL4` is `⊢ ?F ⟶ ?G ⟹ ⊢ □?F ⟶ □?G`, in which the types of `F`
and `G` are again important. After this step [the result follows
quickly](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L445):

```
  ultimately show ?thesis by (simp add: Valid_def)
```

### Liveness

The liveness property we're looking for is that if `AllNodesInactive` then
eventually `TerminationDetected`. I roughly expected to show this by showing
that the token always ends up back at the first node, and then accounting for
the fact that the first time it arrives there after it might be in the
`NotTerminated` state, so it has to go round once more to check that everything
really is terminated.

After a bit of mucking around trying to prove this I discovered that this isn't
how the algorithm works. This is one of the things that I like about proof (as
opposed to model checking): it forces you to understand the system you're
working on, and you can't just get away with writing down plausible statements
without thinking about _why_ they're true. Conversely it does mean you don't
need a deep understanding before you can start work on a system: you can just
wade in with a rough idea of how the proof is going to go, and when you get to
the bit that doesn't work then you can learn and iterate.

This algorithm may actually sometimes need to send the token round _twice_ more
after all the nodes have become inactive, not once. The first pass sets all the
nodes to `MaybeTerminated` but the token could still be contaminated by their
previous states, and the second pass results in a clean token too.

These three phases of the algorithm's endgame can be [characterised like
this](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L459-L470):

```
definition AllNodesInactiveAndTokenAt where "AllNodesInactiveAndTokenAt n ≡ PRED
  (AllNodesInactive ∧ tokenPosition = #n)"

definition NodeCleaningRunAt where "NodeCleaningRunAt n ≡ PRED
  (AllNodesInactiveAndTokenAt n
  ∧ id<nodeState,#FirstNode> = #MaybeTerminated
  ∧ (∀ m. #n < #m ⟶ id<nodeState,#m> = #MaybeTerminated))"

definition TokenCleaningRunAt where "TokenCleaningRunAt n ≡ PRED
  (AllNodesInactiveAndTokenAt n
  ∧ tokenState = #MaybeTerminated
  ∧ (∀ m. id<nodeState,#m> = #MaybeTerminated))"
```

The liveness proof can then go through by showing that each phase results in
the token back at the first node, which leads onto the next phase, and at the
end of the final phase termination is detected.  Actually even this is not
quite how it works, because if termination is detected at the end of a phase
then it just stops and doesn't carry on to the next phase. [This little
lemma](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L58-L61)
captures this behaviour nicely:

```
lemma imp_leadsto_triangle_excl:
  assumes AB: "⊢ S ⟶ (A ↝ B)"
  assumes BC: "⊢ S ⟶ ((B ∧ ¬C) ↝ C)"
  shows "⊢ S ⟶ (A ↝ C)"
```

The proof rule `WF1` was an important ingredient in the liveness proof. Its
statement is a little intimidating:

```
lemma WF1:
  "⟦ ⊢ $P ∧ N  ⟶ P` ∨ Q`;
      ⊢ ($P ∧ N) ∧ <A>_v ⟶ Q`;
      ⊢ $P ∧ N ⟶ $(Enabled(<A>_v)) ⟧
  ⟹ ⊢ □N ∧ WF(A)_v ⟶ (P ↝ Q)"
```

To unpack this, first notice that the conclusion is in approximately the form
we want.  The `□N ∧ WF(A)_v` expression looks like part of the specification,
where `N` is the transition predicate and `WF(A)_v` is a fairness condition.
The first precondition says that if `P` holds and any transition occurs then
either `P` still holds or else `Q` holds. The second says that if `P` holds and
an `A` transition occurs then this results in `Q`. The third says that while
`P` holds, `A` transitions can always occur. The fairness of `A` transitions
ensures that an `A` transition eventually occurs. In short, `WF1` is useful for
showing that a single step of the algorithm eventually occurs.  It's useful to
[specialise `WF1` as
follows](https://gist.github.com/DaveCTurner/4dbf5c4b43cd0500ff223ef1ed412b21#file-ewd840-thy-L475-L480):

```
lemma step:
  assumes "⊢ P ⟶ AllNodesInactive"
  assumes "⊢ P ⟶ ¬ TerminationDetected"
  assumes "⊢ $P ∧ unchanged (isNodeActive, nodeState, tokenPosition, tokenState) ⟶ P$"
  assumes "⊢ $P ∧ Controlled ⟶ Q$"
  shows   "⊢ Spec ⟶ (P ↝ Q)"
```

It remains to repeatedly apply this lemma in order to show that the algorithm
eventually detects termination. The high-level structure of the liveness proof
is as follows:

```
lemma liveness: "⊢ Spec ⟶ (AllNodesInactive ↝ TerminationDetected)"
proof -
  have "⊢ Spec ⟶ (AllNodesInactive ↝ AllNodesInactiveAndTokenAt FirstNode)"
    ...
  moreover have "⊢ Spec ⟶ ((AllNodesInactiveAndTokenAt FirstNode ∧ ¬ TerminationDetected) ↝ NodeCleaningRunAt LastNode)"
    ...
  moreover have "⋀n. ⊢ Spec ⟶ (NodeCleaningRunAt n ↝ NodeCleaningRunAt FirstNode)"
    ...
  moreover have "⊢ Spec ⟶ (NodeCleaningRunAt FirstNode ∧ ¬ TerminationDetected ↝ TokenCleaningRunAt LastNode)"
    ...
  moreover have "⋀n. ⊢ Spec ⟶ (TokenCleaningRunAt n ↝ TerminationDetected)"
    ...
  ultimately show ?thesis
    by (metis imp_leadsto_transitive imp_leadsto_triangle_excl)
qed
```

The second and fourth statement show that each phase leads onto the next, and
work by applying the `step` lemma and unfolding definitions.  The first, third
and fifth statements show that each phase terminates with the token at the
first node again. They're quantified over the token position, `n`, even though
it'd be sufficient to prove them where `n = LastNode`, because they have to be
done by induction on the token position and the extra generality doesn't hurt.
Apart from the complication introduced by needing to use induction, they also
simply involve applying the `step` lemma and unfolding definitions.

## Closing thoughts

After some initial struggles with the different types of validity statements,
and general confusion about the meanings of the available proof rules and
tactics, I quite enjoyed this exercise. It's pleasing to be able to prove
results like this from the ground up, with all the power of Isabelle (e.g.
induction over the set of nodes, and its full library of existing results) to
help along the way.

It's only fair to note that my initial attempts at proving this liveness result
were nothing like as neat as the finished result. There were many false starts,
and I proved a number of results that I thought would be useful but which
turned out not to be, before I stumbled across rule `WF1` and worked out how to
use it. I first got to the liveness result via a rather messy route and only
then was it possible to step back and see the higher-level structure. The
`step` lemma, specialising `WF1`, only came about after noticing the
duplication in each usage of `WF1`, and even then it went through a number of
iterations before ending up in its final form.

There are a few warts here, compared to how things are written in TLA+,
particularly the need to lift constants using `#`, and to say things like
`PRED` and `ACT` when writing state predicates and actions. This is not
entirely unexpected, given the mismatch between Isabelle/HOL's strong typing
and the untyped nature of TLA+. I also miss the ability to write long
conjunctions and disjunctions as a list bulleted with `∧` or `∨`, using
whitespace sensitivity instead of parentheses.

TLAPS proofs are much shorter than the proofs I've written here. My Isabelle
style is perhaps quite verbose, as I've found this to be useful when porting
proofs from one version to the next; denser proofs and ones that heavily rely
on a particular sequence of tactics tend to need more rework. The verbosity
seems to help to find common pieces of reasoning that can be factored out
later. I also prefer to spell out a proof instead of using an automatic tactic
when the automation would take a long time (more than a few hundred
milliseconds) to succeed, because this gets in the way of refactoring proofs
later. It'll be interesting to see how my style changes when working in TLAPS.

If there are any TLAPS fans reading this then I'd love to see how this liveness
proof looks in TLAPS.
