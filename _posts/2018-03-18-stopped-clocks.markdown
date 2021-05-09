---
layout: post
title:  "Stopped clocks"
date:   2018-03-18 09:09:09 +0000
---

One of my colleagues recently quipped that _"a stopped clock is right at least
once per day"_. This is a more pedantic version of the more common [_"a stopped
clock is right twice a
day"_](https://en.wiktionary.org/wiki/a_stopped_clock_is_right_twice_a_day).
The common statement is clearly not wholly true, for instance in time zones
that change offset due to DST. But what about the weaker statement?

There are some obvious counterexamples: if the clock has a [24-hour
dial](https://en.wikipedia.org/wiki/24-hour_analog_dial) rather than the more
usual 12-hour one then it's false on days where DST brings the clocks forwards.
Let's stick with a 12-hour display, ignoring any AM/PM indication.

Digital clocks rarely _stop_ (they tend to just die) but it's concievable that
one could have a fault that stops its display from updating. Arguably if the
fault resulted in the display showing something that's not a time then it's
never right, so let's define a stopped clock as something that actually shows a
time. (**Addendum 2021-05-09**: an analogue clock with randomly positioned
hands also almost certainly does not show a valid time, and is similarly
excluded, thanks
[@happydisciple](https://twitter.com/happydisciple/status/1391373804253896710?s=20)
for the additional pedantry).

If you're allowed to move timezone then it's easy to find a counterexample:
simply go one timezone east at 0600 (local time) and then another at 1800
(local time) and you will never have experienced a local time represented with
the hour hand between 6 and 7. On land you have to try quite hard to cross two
timezone boundaries in 11 hours (e.g. Las Vegas to Amarillo is 860 miles which
is [feasible if you ignore the speed
limits](https://jalopnik.com/meet-the-guy-who-drove-across-the-u-s-in-a-record-28-h-1454092837).)
It's definitely possible by plane, or you could do one of the hops using a DST
shift instead. Let's only think about cases where the clock stays in one place.
There may be a trick you can play [in
Jerusalem](https://www.haaretz.com/israel-news/.premium-israel-moves-clock-but-palestinians-dont-1.5453010)
where the time zone sometimes depends on more than just _where_ you are, but
let's just rule that kind of shenanigans out as well, and stay in a single time
zone as defined by the [IANA time zone
database](https://www.iana.org/time-zones).

How could a stopped clock fail to ever show the correct time within a day in a
single time zone? One possibility is setting the clocks forward twice in a day,
emulating the action of crossing two timzeone boundaries at a carefully timed
interval. This is theoretically possible but has never yet happened: the
closest two transitions in the database took place in `Europe/Warsaw` on
`1944-09-30` and `1944-10-04` which are well over a day apart.

The other possibility is a single transition in which the clocks were set
forward by more than 12 hours (but less than 24), but it seems implausible that
such an enormous shift would make any sense at all. In fact it's not that
implausible close to the poles where population is sparse and solar time is
vague:
[`Antarctica/DumontDUrville`](https://en.wikipedia.org/wiki/Dumont_d'Urville_Station)
apparently set the clocks forward by 10 hours on 1 November 1956 which isn't
far off the 12 hours that we need to exceed. However that's the largest shift
in the database so far,
meaning that there's (currently) no way of mucking around with timezones that
provides a counterexample.

Does this mean that _"a stopped clock is right at least once per day"_ is a
rare example of a plausible statement about time that's actually true? No, of
course not. All plausible statements about time
[are](http://infiniteundo.com/post/25326999628/falsehoods-programmers-believe-about-time)
[wrong](http://infiniteundo.com/post/25509354022/more-falsehoods-programmers-believe-about-time).
This one is wrong because during a [leap
second](https://en.wikipedia.org/wiki/Leap_second) a digital clock (UTC
timezone, 12-hour mode) should display `11:59:60`. If it got stuck with this on
its display then it's a stopped clock (it's displaying a valid time) which is
right much less frequently than once per day.
