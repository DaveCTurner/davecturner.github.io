---
layout: post
title:  "The Doomsday rule: mental day-of-week calculations"
date:   2021-12-27
---

The [Doomsday rule](https://en.wikipedia.org/wiki/Doomsday_rule) is an
algorithm for working out the day of the week of a given date. It's based on
John Conway's observation that certain memorable dates called _doomsdays_ (4/4,
6/6, 8/8, 10/10, 12/12, 9/5, 5/9, 7/11, 11/7, ...) always occur on the same day
of the week in any given year. This day is known as the year's _anchor day_. To
compute an arbitary day of week you work out the anchor day for the given year
and the offset between the target date and an appropriate doomsday. It's
intended to be simple enough that you can do the computation in your head with
a bit of practice.

A couple of recent Youtube videos have raised its profile, first one by [James
Grimes on Numberphile](https://www.youtube.com/watch?v=z2x3SSBVGJU) and then a
second by [Mike Boyd](https://www.youtube.com/watch?v=eSpW4I5moiA). In both
videos they show that it's possible to do the mental calculations quite
quickly. I tried learning it some time ago and struggled to achieve that kind
of speed on the algorithm as described in the literature. The first part of the
computation involves counting leap years (i.e. dividing by 4) and the second
part involves subtracting numbers mod 7 which means you have to get the sign
right and sometimes have to deal with negative numbers. All definitely
possible, but tricky to do quickly in your head.

I found that the effects of practice was basically to inline various bits of
the strategy and commit the inlined version to memory, but the inlining wasn't
consistently applicable which meant that some dates ended up harder to compute
than others. Since the point of practice seemed to be to commit various things
to memory, I figured it'd be simpler to rework the algorithm to make use of
memorisation directly.

There's not actually that many things to remember, it only took me a couple of
hours, and once I'd done the memorisation work I found I can run the algorithm
pretty quickly even if distracted by other things such as continuing a
conversation. I wonder if when other folks say they're doing Conway's method
they're really doing something more like this, or whether it's just me that
finds recalling memorised facts much easier than doing actual computations.

One handy feature of the method presented here is that you combine all the
sub-computations together wih addition (mod 7) which is commutative and
associative so you can process the components of the date in any order and
reduce them to a single value at each step which saves on working memory slots.
Here in the UK most folks say the date in day-month-year order; in the US
month-day-year seems preferred, but really any order is reasonable.

### Overview

Process the day-of-month, the month, the century and the year-of-century in any
order you choose. Each component yields a value which you add to a running
total, computed mod 7. The final running total after all four values are added
(occasionally with a simple leap-year correction) indicates the day of the week
of the target date, with 0 meaning Sunday, 1 meaning Monday and so on.

### Day-of-month

When you hear the day of the month, add it to the running total, working mod 7.

### Month

When you hear the month, convert it to a value according to the following table
and add the value to your running total, working mod 7.

| Month     | Value | Month     | Value | Month     | Value |
|-----------|-------|-----------|-------|-----------|-------|
| January   | 4     | May       | 5     | September | 2     |
| February  | 0     | June      | 1     | October   | 4     |
| March     | 0     | July      | 3     | November  | 0     |
| April     | 3     | August    | 6     | December  | 2     |

Just learn this mapping. There's kind of a pattern but learning the values
doesn't take long and means you can process the month very quickly while
listening for the rest of the date.

### Century

When you hear the century—the first two digits of the year—convert it to a
value according to the following table and add that value to your running
total, working mod 7.

| Century | Value | Century | Value |
|---------|-------|---------|-------|
| 17xx    | 0     | 21xx    | 0     |
| 18xx    | 5     | 22xx    | 5     |
| 19xx    | 3     | 23xx    | 3     |
| 20xx    | 2     | 24xx    | 2     |

Again, just learn this mapping. There is a repeating pattern because the
Gregorian calendar repeats every 400 years, but in practice you'll mostly get
one of these centuries so it's simpler to remember them. You can reasonably
reject years before 1700 because the UK and US didn't start using the Gregorian
calendar until 1752, and if you get a year after 2499 then it's usually ok to
take a bit longer to work out to which of 20xx, 21xx, 22xx or 23xx it's
equivalent.

### Year-of-century

The year of the century—the last two digits of the year—is the trickiest bit to
deal with. If it's a multiple of 4 then it maps to a remainder mod 7 as follows
which should be added to the running total:

| Year | Value | Year | Value | Year | Value | Year | Value | Year | Value |
|------|-------|------|-------|------|-------|------|-------|------|-------|
| xx00 | 0     | xx20 | 4     | xx40 | 1     | xx60 | 5     | xx80 | 2     |
| xx04 | 5     | xx24 | 2     | xx44 | 6     | xx64 | 3     | xx84 | 0     |
| xx08 | 3     | xx28 | 0     | xx48 | 4     | xx68 | 1     | xx88 | 5     |
| xx12 | 1     | xx32 | 5     | xx52 | 2     | xx72 | 6     | xx92 | 3     |
| xx16 | 6     | xx36 | 3     | xx56 | 0     | xx76 | 4     | xx96 | 1     |

The values for the nine multiples of 12 are just the result of dividing by 12.
The other 16 are all ±4 away from a multiple of twelve so you can in principle
compute the nearest multiple of 12 and then add or subtract 2 according to the
pattern, but it's only 16 values so still not that hard to just memorise the
mapping.

If the year isn't a multiple of 4 then add its remainder mod 4 to your running
total, then round the year down to the nearest multiple of 4, grab the value
from the table above, and add that to the running total as well. There's
various other ways you could achieve this, for instance you could memorise all
100 values, but representing the year as `4k+r` and then processing `4k` and
`r` separately works best for me.

### Leap year correction

If the target is in January or February of a leap year then decrement the
running total by one. This is kind of irritating to remember. However note that
leap years are slightly simpler to compute since they're always a multiple of 4
so there's no remainder mod 4 to deal with at the year-of-century step.

### Finishing up

The final total represents the day of the week of the chosen date, with 0
meaning Sunday, 1 meaning Monday, and so on.

## Worked examples

### 19 July 1989

The day-of-month 19 becomes 5 which is the initial running total. July has
value 3, and adding this to the running total gives 1. The century 19xx is also
3, which adds to the running total to give 4. The year-of-century xx89 is 1
greater than a multiple of 4, namely xx88, so we add the 1 to the running total
to give 5. Finally xx88 has value 5 which is added to the running total to give
3, which means that 19 July 1989 was a Wednesday.

### February 27, 2204

February has value 0 so the running total starts out as zero. The day-of-month
27 becomes 6 which replaces the running total of zero.  The century 22xx has
value 5 which adds to the running total to give 4 (recalling that adding 6 is
the same as subtracting 1). The year-of-century xx04 is a multiple of 4 with
value 5 which adds to the running total to give 2. But 2204 is a leap year and
the date is in February so we must subtract 1, giving a final total of 1 which
means that 2 February 2204 will be a Monday.

### 1900-01-15

The century 19xx has value 3 so that's the initial running total.  The
year-of-century xx00 is a multiple of 4 with value 0 so the running total is
unchanged.  January has value 4 which is added to the running total to give 0.
The day-of-month 15 becomes 1 mod 7 so this is the new running total.  The
month is January and the year is a multiple of 4 but note that 1900 was _not_ a
leap year so no further correction is needed. 1900-01-15 was therefore a
Monday.

## How it works

The day and month values added together (minus one for January and February in
leap years) tells you the offset in days from the year's anchor day to the
target date. You can check that the memorable doomsdays all add up to a
multiple of seven: 4 April = 4 + 3 = 7; 9 May = 9 + 5 = 14; ...

The century and year-of-century values added together tells you the anchor day
for the year. The year-of-century table adds the number of years to the number
of earlier leap years in the century, i.e. it computes `5n/4 mod 7` for
multiples of 4.

## Speed tips

Recalling a value from memory is enormously faster than working it out. I'd
rather remember a table of 25 things instead of adding another computation
step.

I spent some time actively memorising the remainders mod 7 of the numbers from
1 to 31, even though I can compute them fairly well, because you need to do
this step quickly whilst distracted by listening for the rest of the date.

I also found it worth practicing doing sums of remainders mod 7. One of my very
early maths teachers made us do speed exercises for adding small numbers, much
like multiplication tables, which everyone hated at the time but I've since
realised how powerful it is to be able to do these sums _instantly_ rather than
merely quickly. There's not actually that many to learn in this case: the sums
that don't exceed 7 are just the regular ones; the sums that equal 7 are easy
to map to zero. Sums involving zero are also easy, and adding 6 is easier to
treat as subtracting 1. That just leaves 3+5, 4+4, 4+5 and 5+5 to learn.

I learned the year-of-century values in three batches: first the multiples of
12, then 04, 08, 16, 28, 32, 40, 76, 80, and finally 20, 44, 52, 56, 64, 68,
88, 92. Learning all 16 values at once didn't work well for me, but working 8
at a time was very effective. The batches were pretty much randomly chosen
except I made sure the split of values was as even as possible. There's not
much science behind that but it seemed to work.

I recommend learning the values for any years that you will use a lot, such as
the current year and a couple of nearby ones. 2021's is 0 and 2022's will be 1.

If you're coming at this cold then the only things you don't already know are
the values for the 12 months, 8 centuries, and the 16 years-of-century that
aren't multiples of 12, which is 36 individual items. To get faster you
probably also need to practice the 31 remainders for days-of-the-month, 9
remainders for the multiple-of-12 years, and the 21 sums mod 7. That is 97
things in total, plus maybe the value for the current year ±1 to make it up to
an even hundred. There's loads of spaced-repetition flashcard apps out there
that should help with this kind of thing. With a couple hours of up-front
investment you can save literally seconds per month of looking up dates in a
calendar.

[![Obligatory XKCD](https://imgs.xkcd.com/comics/is_it_worth_the_time.png)](https://xkcd.com/1205/)

