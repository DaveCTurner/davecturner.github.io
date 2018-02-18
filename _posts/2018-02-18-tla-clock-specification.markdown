---
layout: post
title:  "Refining specifications in TLA+ and Isabelle/HOL"
date:   2018-02-18 19:09:09 +0000
---

One of the great features of TLA+ is it's ability to formally express that one
specification refines another. Here is an [example of a pair of specifications,
one of which refines the other, along with a proof of this fact in
Isabelle/HOL](https://gist.github.com/DaveCTurner/96c0857869d9768920d7999f91f5bb3d).

## An hours-only clock

A number of TLA+ texts start out with an introductory example of a
specification for a clock. The clock is not a realtime clock, and it starts out
by just showing the hours: the `hr` variable increments until it gets to 12 and
then steps back down to 1 and carries on. I'm following the example from
[Stephan Merz's _Modeling and Developing Systems Using
TLA+_](https://members.loria.fr/SMerz/talks/argentina2005/handout.pdf) except
modelling a 12-hour clock instead of a 24-hour one.

After some initial lemmas (which I'll probably collect into a library at some point)
we introduce the specification of an `HourClock`:

    definition next_hour :: "nat ⇒ nat" where "⋀n. next_hour n ≡ if n = 12 then 1 else n+1"

    ...

    locale HourClock =
      fixes hr :: "nat stfun"
      assumes hr_basevar: "basevars hr"
      fixes HCini HCnxt HC
      defines "HCini ≡ PRED hr ∈ #{1..12}"
      defines "HCnxt ≡ ACT hr$ = next_hour<$hr>"
      defines "HC    ≡ TEMP Init HCini ∧ □[HCnxt]_hr ∧ WF(HCnxt)_hr"

    context HourClock
    begin

In contrast to the previous article, here I'm using an Isabelle _locale_ to limit
the scope of these definitions. The clock starts out displaying an arbitrary hour
(from 1 to 12) and at each step the hour is updated using the `next_hour` function, setting
it back to 1 if it hits 12 and incrementing it otherwise.

The safety property for the `HourClock` is a relatively simple type-correctness
property which just says that it only ever displays numbers from 1 to 12, which
is what the initial-state property `HCini` says too. The proof is a one-liner:

    lemma HC_safety: "⊢ HC ⟶ □ HCini"
      unfolding HC_def HCini_def HCnxt_def next_hour_def by (auto_invariant, auto)

Liveness is a little more interesting. We start by showing that the clock
always eventually updates the hour:

    lemma HC_liveness_step:
      assumes n: "n ∈ {1..12}"
      shows "⊢ HC ⟶ (hr = #n ↝ hr = #(next_hour n))"

The proof of this uses lemma `WF1`, mentioned last time. From this lemma it's
possible to show that the hour always eventually increases from any number to
any greater number (up to 12).

    lemma HC_liveness_progress_forwards:
      assumes m: "m ∈ {1..12}"
      assumes n: "n ∈ {1..12}"
      assumes mn: "m ≤ n"
      shows "⊢ HC ⟶ (hr = #m ↝ hr = #n)"

The proof of this goes through by induction; it probably could have just used
induction directly on the natural numbers, but I find it's often neater to use
an induction property that reflects the structure of the execution more
closely:

    lemma next_hour_induct [case_names base step, consumes 1]:
      fixes m :: nat
      assumes type: "m ∈ {1..12}"
      assumes base: "P 1"
      assumes step: "⋀n. 1 ≤ n ⟹ n < 12 ⟹ P n ⟹ P (next_hour n)"
      shows "P m"

From here it's a short hop to showing that the clock always eventually gets
from any number `m` to any other `n`, by taking it all the way up to 12, then
back to 1, and then up to `n`, using `HC_liveness_progress_forwards` twice.

    lemma HC_liveness_progress:
      assumes m: "m ∈ {1..12}"
      assumes n: "n ∈ {1..12}"
      shows "⊢ HC ⟶ (hr = #m ↝ hr = #n)"

Since the starting point of the clock is arbitrary, it follows that the clock
displays every number infinitely often, which is the desired liveness property:

    lemma HC_liveness:
      assumes n: "n ∈ {1..12}"
      shows "⊢ HC ⟶ □◇ hr = #n"

## An hours-and-minutes clock

In order to make this clock slightly more useful, it can be extended to one
which displays both the hours and the minutes. We introduce a new locale,
extending the `HourClock` locale, and defining a new specification:

    locale HourMinuteClock = HourClock +
      fixes mn :: "nat stfun"
      assumes hr_mn_basevars: "basevars (hr,mn)"
      fixes HMCini Mn Hr HMCnxt HMC
      defines "HMCini ≡ PRED HCini ∧ mn ∈ #{0..59}"
      defines "Mn     ≡ ACT mn$ = (if $mn = #59 then #0 else $mn + #1)"
      defines "Hr     ≡ ACT ($mn = #59 ∧ HCnxt) ∨ ($mn < #59 ∧ unchanged hr)"
      defines "HMCnxt ≡ ACT (Mn ∧ Hr)"
      defines "HMC    ≡ TEMP Init HMCini ∧ □[HMCnxt]_(hr, mn) ∧ WF(HMCnxt)_(hr, mn)"

    context HourMinuteClock
    begin

Each transition of this clock advances the minutes field, and if it gets to
`59` then it advances the hour too as per the `HourClock` specification.  One
thing to note is that the next-state relation for the hours-only clock,
`HCnxt`, was always enabled, even if `hr > 12`, whereas the next-state relation
for this clock is only enabled if `mn ≤ 59`. This is how Stephan Merz does it;
it'd be possible to make this consistent, but the inconsistency doesn't present
any real problem.

The safety property for this clock is also a simple type-correctness property
showing that the displayed hour is between 1 and 12, and the minutes are
between 0 and 59. The proof is short and mostly automatic:

    lemma HMC_safety: "⊢ HMC ⟶ □ (hr ∈ #{1..12} ∧ mn ∈ #{0..59})"
      unfolding HMC_def HMCini_def HCini_def HMCnxt_eq next_hour_def
      by (invariant, auto simp add: square_def Init_def)

Again, liveness is a little more interesting. We start by showing that
the clock always makes a step:

    definition timeIs :: "nat × nat ⇒ stpred" where "timeIs t ≡ PRED (hr, mn) = #t"

    lemma HMC_liveness_step:
      assumes "m ≤ 59"
      shows "⊢ HMC ⟶ (timeIs (h, m) ↝ (timeIs (if m = 59 then (if h = 12 then (1, 0) else (h+1, 0)) else (h, m+1))))"

It's useful to specialise this into two cases: one where the hour does not
change and the other where it does:

    lemma HMC_liveness_step_minute:
      assumes "m < 59"
      shows "⊢ HMC ⟶ (timeIs (h,m) ↝ timeIs (h, Suc m))"
      using HMC_liveness_step [of m h] assms by auto

    lemma HMC_liveness_step_hour:
      shows "⊢ HMC ⟶ (timeIs (h,59) ↝ timeIs (next_hour h, 0))"
      using HMC_liveness_step [of 59 h] unfolding next_hour_def by auto

The next step in the proof is to show that the minute can advance multiple steps, within a single hour:

    lemma HMC_liveness_progress_forwards_minute:
      assumes m12: "m1 ≤ m2" and m2: "m2 ≤ 59"
      shows "⊢ HMC ⟶ (timeIs (h,m1) ↝ timeIs (h,m2))"

This is shown by induction on `m2`, without using a custom induction principle.
The next step I chose is a little strange: it shows that the clock always
eventually goes from `h1:59` to `h2:59`. I tried a handful of alternatives and
this seemed to be the most useful next step:

    lemma HMC_liveness_progress_forwards_hour:
      assumes h1: "h1 ∈ {1..12}"
      assumes h2: "h2 ∈ {1..12}"
      assumes h1h2: "h1 ≤ h2"
      shows "⊢ HMC ⟶ (timeIs (h1,59) ↝ timeIs (h2,59))"

This is very similar to the proof of `HC_liveness_progress_forwards` above,
using the `next_hour_induct` induction principle. From this it follows that the
clock always eventually moves from any time to any other time, by going via
`12:59` and `1:00`:

    lemma HMC_liveness_progress:
      assumes h1: "h1 ∈ {1..12}"
      assumes h2: "h2 ∈ {1..12}"
      assumes m1: "m1 ≤ 59"
      assumes m2: "m2 ≤ 59"
      shows "⊢ HMC ⟶ (timeIs (h1,m1) ↝ timeIs (h2,m2))"

From here it follows quickly that the clock shows every time infinitely often:

    lemma HMC_liveness:
      assumes h: "h ∈ {1..12}"
      assumes m: "m ≤ 59"
      shows "⊢ HMC ⟶ □◇ timeIs (h,m)"

## Refinement

TLA+ lets you to express that one specification _refines_ another, simply using
logical implication between the specifications. This is really useful because
it means you can write a high-level specification which implies a number of
useful properties but which leaves any unimportant implementation decisions
undefined, and then a lower-level specification which clarifies some of those
decisions, and by showing that the lower-level specification refines the
higher-level one you can be sure that the useful properties are shared by both
specifications.

In this case it should be the case that the hours-and-minutes clock refines the hours-only clock:

    lemma HMC_refines_HC: "⊢ HMC ⟶ HC"
      unfolding HC_def
    proof (intro temp_imp_conjI)

This leaves three subgoals, corresponding to the usual three parts of a TLA+ formula:

    goal (3 subgoals):
     1. ⊢ HMC ⟶ Init HCini
     2. ⊢ HMC ⟶ □[HCnxt]_hr
     3. ⊢ HMC ⟶ WF(HCnxt)_hr

The first goal is fairly trivial and the second is also straightforward, since
they are safety properties. The third goal, showing that the fairness property
carries across, took me a while longer. The key step is the use of rule `WF2`:

    lemma WF2:
      assumes 1: "⊢ N ∧ <B>_f ⟶ <M>_g"
        and 2: "⊢ $P ∧ P$ ∧ <N ∧ A>_f ⟶ B"
        and 3: "⊢ P ∧ Enabled(<M>_g) ⟶ Enabled(<A>_f)"
        and 4: "⊢ □(N ∧ [¬B]_f) ∧ WF(A)_f ∧ □F ∧ ◇□Enabled(<M>_g) ⟶ ◇□P"
      shows "⊢ □N ∧ WF(A)_f ∧ □F ⟶ WF(M)_g"

Woah. The conclusion looks like it's in about the right form, if `M` is `HCnxt`
and `g` is `hr`, and a first guess would be that `□N ∧ WF(A)_f` could be the
next-step relation and fairness condition from the `HMC` spec. But what are
`F`, `B` and `P`? We get to choose! They all appear in positive and negative
positions, so this looks a bit like the job of picking an induction hypothesis:
they need to be strong enough that you can use them to derive the conclusion,
without being so strong that you can't derive them in turn.

The first premise is the first thing to look at. Substituting for `M` and `g`,
and guessing that `N` could be `[HMCnxt]_(hr,mn)` and `f` might be `(hr,mn)`,
it is:

     ⊢ [HMCnxt]_(hr,mn) ∧ <B>_(hr,mn) ⟶ <HCnxt>_hr

This gives a hint about `B`: it needs to be something that's true for a
`HMCnxt` transition to be a `HCnxt` transition, i.e. a transition which changes
the hour. Letting it be, say, `$mn = #59` would work for that.

The second premise is a bit weird. It says that if `P` doesn't change, but an
`N ∧ A` transition occurs, then `B` holds. It'd work to define `P` to be `mn =
59`, so that `⊢ $P ⟶ B`, but in that case `$P ∧ P$` is false so this is kinda
vacuous.

The third premise is about the compatibility between the `Enabled` predicates.
Following the guess that `<A>_f` is `<HMCnxt>_(hr,mn)` means that `P` must
imply that `mn ≤ 59`, because `Enabled(<M>_g)` is always true and
`Enabled(<HMCnxt>_(hr,mn))` is only true if `mn ≤ 59`.

The fourth premise says that a bunch of junk implies that `P` is eventually
always true. The first thing I tried was having `P` be `mn ≤ 59`, which _is_
always true as it's in the safety property, which works for the third premise
but is unhelpful in the second as we need it to imply that `mn = 59`. It needs
to be stronger.  How about setting `P` to be `mn = 59`? Unfortunately this
isn't eventually always true, but does the "bunch of junk" help with this?

Yes.

The first conjunct, `□(N ∧ [¬B]_f)`, says that we always make `N` transitions
which are not `B` transitions. `B` transitions seem to be the ones where the
hours change, so this says that if `mn = #59` then we can only make stuttering
transitions. The second conjunct, `WF(A)_f`, says we make infinitely many
non-stuttering transitions.  If we can show that we eventually hit a state
where `mn = #59` then this yields a contradiction. This is what the `F` is for:
if we let `F` be `◇ (mn = #59)` then we can derive `□F` from the liveness
property, and in turn this implies that we get stuck.

In fact, it's a little simpler to aim to hit the end of a _specific_ hour, say
`01:59`, rather than generalising to any time satisfying `mn = #59`, because
this fits the liveness property a little better. Therefore it works to say the
following:

      define P :: stpred   where "P ≡ timeIs (1,59)"
      define B :: action   where "B ≡ ACT $P"
      define F :: temporal where "F ≡ TEMP ◇P"
      define N :: action   where "N ≡ ACT [HMCnxt]_(hr,mn)"
      define A :: action   where "A ≡ HMCnxt"

The refinement result follows without much further fuss.

It seemed strange that the second premise involves the contradiction `$P ∧ P$ ∧
<N ∧ A>_f`: I tried quite hard to come up with a definition for `P` for which
this wasn't a contradiction before settling on `timeIs (1,59)`.  It'll be
interesting to work through some examples where it is less trivial.

There's a bit of a flavour of a contradiction in the fourth premise too,
because `P` is not eventually always true at all. This seems to be related to a
confusion I have had with the definition of weak fairness:

      WF(A)_v ≡ ◇□Enabled (<A>_v) ⟶ □◇<A>_v

Weak fairness says that if an action is eventually always enabled then it
occurs infinitely often. In the specs above the `Enabled` predicates are pretty
simple, and always true, so this is fine. However, in more complicated specs it
can be the case that when an action executes it disables itself, e.g. by
consuming the last message waiting in a queue. This puts us in a situation of
apparently circular reasoning: the action would eventually be enabled forever
if it didn't execute, so fairness implies that it does execute, but this
implies that it isn't enabled forever. There's no paradox here because it is
perfectly consistent for the action to execute repeatedly until it disables
itself, and there is no other consistent behaviour, but it took me a while to
convince myself of this.
