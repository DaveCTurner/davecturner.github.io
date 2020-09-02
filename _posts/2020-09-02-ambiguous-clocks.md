---
layout: post
title:  "Ambiguous clocks"
date:   2020-09-02
---

I recently came across a [video from Zach Star](https://youtu.be/LT_33XzEX2Q)
which posed the question of telling the time on a clock whose two hands are
identical lengths. This seems like a fairly well-known puzzle and it's kinda
entertaining to work out when you can and cannot tell the time on such a clock.
Then I wondered what would happen if you added a second (i.e. third) hand which
is also indistinguishable from the other two hands.

**Spoilers follow**. Stop reading if you'd like to try this puzzle yourself
first.

Zach gives a geometric argument for the two-handed case which you can extend to
the three-handed case by adding a dimension, so that you're looking for
intersections between lines in three-dimensional space which may reasonably
simply not exist.  However actually proving whether they do exist or not was
really rather fiddly given all the different ways that the hands could line up
with each other.

## Two-handed case

For the two-handed case, the time `t₁` is ambiguous if there is a different
time `t₂` such that `{h(t₁), m(t₁)} = {h(t₂), m(t₂)}`, i.e. `h(t₁) = m(t₂)` and
`h(t₂) = m(t₁)`, where `h` and `m` give the respective positions of the hour
and minute hand.  For simplicity's sake we measure times as a fraction of 12
hours (so `0` is midnight and `1` is noon) and only consider times in `[0,1)`,
and measure the hand position as a fraction of the circle, so that `h(t) = t`
and `m(t) = 12t - ⌊12t⌋`. Thus we want to solve 

    t₁ = 12t₂ - ⌊12t₂⌋
    t₂ = 12t₁ - ⌊12t₁⌋

Substituting gives ...

    t₁ = 144t₁ - ⌊144t₁⌋ - ⌊144t₁ - ⌊144t₁⌋⌋

... which tells us that the only solutions are where `143t₁` must be an
integer, say, `n₁`. If `n₁ < 143` then `h(t₁) = m(t₂) = n₁/143` and `h(t₂) =
m(t₁) = 12n₁ mod 143 / 143` is a solution to the equations, but this includes
the cases where the hands coincide and `t₁ = t₂` which are not ambiguous.
Excluding those cases gives the answer.

## Three-handed case

For the three-handed case, the time `t₁` is ambiguous if there is a different
time `t₂` such that `{h(t₁), m(t₁), s(t₁)} = {h(t₂), m(t₂), s(t₂)}` where `h`
and `m` are as before and `s` gives the position of the second hand, i.e. `s(t)
= 720t - ⌊720t⌋`. There are a lot of different ways to satisfy the equality
between those sets of hand positions, although at least we know for certain
that `h(t₁) ≠ h(t₂)`. Focussing just on the hour hands gives the following four
cases:

    h(t₁) = m(t₂) ∧ h(t₂) = m(t₁)
    h(t₁) = s(t₂) ∧ h(t₂) = s(t₁)
    h(t₁) = m(t₂) ∧ h(t₂) = s(t₁)
    h(t₁) = s(t₂) ∧ h(t₂) = m(t₁)

### Case 1

If `h(t₁) = m(t₂)` and `h(t₂) = m(t₁)` then this is the same as the two-handed
case, so the solution is of the form `t₁ = n/143` and `t₂ = 12n mod 143 / 143`.
However,

    s(t₁) = 720n mod 143 / 143 ∈ {h(t₂), m(t₂), s(t₂)}
                               = {h(t₁), m(t₁), s(t₂)}
                               = {n/143, 12n mod 143 / 143, 8640n mod 143 / 143}

Therefore `719n mod 143 = 0`, `708n mod 143 = 0` or `7920n mod 143 = 0`. But
719, 708 and 7920 are all coprime to 143 so in any case `n = 0` is the only
possible solution. This implies that `t₁ = t₂` (= midnight) which isn't ambiguous
so this case leads to no ambiguities.
	
### Case 2

This case is similar to the previous. If `h(t₁) = s(t₂)` and `h(t₂) = s(t₁)`
then a similar argument to the two-handed case tells us that the solution is of
the form `t₁ = n/(720×720-1) = n/518399` and `t₂ = 720n mod 518399 / 518399`.
However,

    m(t₁) = 12n mod 518399 / 518399 ∈ {h(t₂), m(t₂), s(t₂)}
                                    = {h(t₁), m(t₂), s(t₁)}
                                    = {n/518399, 8640n mod 518399 / 518399, 720n mod 518399 / 518399}

Therefore `11n mod 518399 = 0`, `8628n mod 518399 = 0` or `708n mod 518399 =
0`. But 11, 8628 and 708 are all coprime to 518399 so in any case `n = 0` is
the only possible solution. Therefore this case also leads to no ambiguities.

### Case 3

If `h(t₁) = m(t₂)` and `h(t₂) = s(t₁)` then

    t₁ =  12t₂ -  ⌊12t₂⌋
    t₂ = 720t₁ - ⌊720t₁⌋
    
Substituting gives

    t₁ = 8640t₁ - ⌊8640t₁⌋ - ⌊8640t₁ - ⌊8640t₁⌋⌋

Therefore the solution is of the form `t₁ = n/8639` and `t₂ = 720n mod 8639 / 8639`. However,

    m(t₁) = 12n mod 8639 / 8639 ∈ {h(t₂), m(t₂), s(t₂)}
                                = {h(t₁), s(t₁), s(t₂)}
                                = {n/8639, 720n mod 8639 / 8639, 518400n mod 8639 / 8639}

Therefore `11n mod 8639 = 0`, `708n mod 8639 = 0` or `518388n mod 8639 = 0`.
But 11, 708 and 518388 are all coprime to 8639 so in any case `n = 0` is the
only possible solution. Therefore this case also leads to no ambiguities.

### Case 4

This case is the same the previous case, swapping the roles of `t₁` and `t₂`,
so also leads to no ambiguities.

### Conclusion

Since an ambiguity is impossible in all cases, this shows that all positions of
the three hands on the clock uniquely determine the time even if the hands are
indistinguishable.

This was pretty fiddly. There are lots of other ways to split the equality
`{h(t₁), m(t₁), s(t₁)} = {h(t₂), m(t₂), s(t₂)}` into cases, many of which look
promising but lead to a lot of duplicated work.  Getting just the right amount
of case splitting took a few goes, and I reckon there's a more elegant argument
out there somewhere as even this solution really copy-pastes the same argument
four times.
