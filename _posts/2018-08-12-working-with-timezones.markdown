---
layout: post
title:  "Working with timezones"
date:   2018-08-12 09:09:09 +0000
---

I do enjoy thinking about some of the strange things that can happen with
[time]({% post_url 2018-03-18-stopped-clocks %}) and [timezones]({% post_url
2017-12-27-timezone-curiosities %}) and it can be amusing, and occasionally
useful, to read some
[lists](http://infiniteundo.com/post/25326999628/falsehoods-programmers-believe-about-time)
of
[counterexamples](http://infiniteundo.com/post/25509354022/more-falsehoods-programmers-believe-about-time)
to reasonable-sounding statements about time, but it's hard to actually get
stuff done with this information alone. All those counterexamples might leave
you thinking that dealing with timezones is basically impossible to get right,
whereas in fact it's not that difficult once you draw the right pictures.  I
thought it'd be useful to share the pictures I find helpful when approaching
timezone-related problems.

## Local-universal time graphs

The basic tool for visualising a timezone is something I'm going to call a
_local-universal time graph_ (LUTG) which sounds awfully fancy but is really
just a line graph that relates universal time (on the horizontal axis) to local
time (on the vertical axis). The LUTG for the standard
[UTC](https://en.wikipedia.org/wiki/UTC±00:00) timezone looks like this:

![LUTG of UTC]({{ "/assets/2018-08-timezone-diagrams/01-utc.png" | relative_url }})

If you think this looks fairly boring then you'd be right. UTC is a fairly
boring timezone, and its LUTG reflects this perfectly. A marginally more
interesting timezone is something like
[`Etc/GMT-4`](https://en.wikipedia.org/wiki/UTC%2B04:00) whose LUTG looks like
this:

![LUTG of UTC]({{ "/assets/2018-08-timezone-diagrams/02-utc-4.png" | relative_url }})

This is still quite boring, admittedly, but it does at least show you
unambiguously whether to add or subtract the 4 hours necessary to convert from
local time to UTC or vice versa. The correct interpretation of the sign of a
timezone offset is just not a thing that seems to stay in my head, and the fact
that what the IANA call `Etc/GMT-4` is called `+04:00` by the ISO suggests that
there are other people who also struggle with this. So I draw this LUTG and I
find it helps.

## Changing offsets

The fun and games _really_ begin when you start to look at timezones that
sometimes change their offsets from UTC. This happens in two different ways.
Either they set their clocks forwards ...

![LUTG of clocks going forwards]({{ "/assets/2018-08-timezone-diagrams/03-clocks-go-forwards.png" | relative_url }})

... or they set them back ...

![LUTG of clocks going backwards]({{ "/assets/2018-08-timezone-diagrams/04-clocks-go-backwards.png" | relative_url }})

## Properties of LUTGs

There's a few things to notice about these graphs. Firstly, every UTC instant
has a _well-defined_ local time to which it corresponds:

![LUTG of clocks going backwards showing UTC-to-local conversion]({{ "/assets/2018-08-timezone-diagrams/05-utc-to-local-well-defined.png" | relative_url }})

_Some_ local times also have a single well-defined universal time to which they
correspond:

![LUTG of clocks going backwards showing unambiguous local-to-UTC conversion]({{ "/assets/2018-08-timezone-diagrams/06-local-to-utc-well-defined.png" | relative_url }})

However when the clocks go back, some local times have two corresponding UTC
times:

![LUTG of clocks going backwards showing ambiguous local-to-UTC conversion]({{ "/assets/2018-08-timezone-diagrams/07-local-to-utc-ambiguous.png" | relative_url }})

Similarly when the clocks go forwards, some local times never occur at all:

![LUTG of clocks going forwards showing missing local-to-UTC conversion]({{ "/assets/2018-08-timezone-diagrams/08-local-to-utc-missing.png" | relative_url }})

Away from the offset transition, time proceeds at the same rate on both axes:
all the lines are at 45°.

![LUTG of clocks going backwards showing gradients]({{ "/assets/2018-08-timezone-diagrams/09-lines-45-degrees.png" | relative_url }})

One thing that's perhaps not obvious from the graph, but which can be
important, is that the transition time belongs only to the _later_ line
segment.  Times strictly before the transition time have the earlier offset,
and times that are equal to or later than the transition time have the later
offset. I draw this with an open ○ at the exclusive endpoint and a filled ● at
the inclusive endpoint.

![LUTG of clocks going backwards showing inclusive/exclusive endpoints]({{ "/assets/2018-08-timezone-diagrams/10-inclusive-exclusive.png" | relative_url }})

## Offsets are _vertical_

An important point is that offsets from UTC are drawn as the _vertical_
distance between the line and the LUTG of UTC:

![LUTG of clocks going backwards showing offset is a vertical distance]({{ "/assets/2018-08-timezone-diagrams/11-offset-is-vertical.png" | relative_url }})

I think this point is absolutely crucial to fully understanding timezone
calculations. It's tricky because most of the time the vertical distance is the
same as the horizontal distance:

![LUTG of clocks going backwards showing offset is the same horizontally]({{ "/assets/2018-08-timezone-diagrams/12-vertical-equals-horizontal-offset.png" | relative_url }})

But near to a transition this isn't true, even where the horizontal distance is
unambiguous and well-defined:

![LUTG of clocks going backwards showing offset is the same horizontally]({{ "/assets/2018-08-timezone-diagrams/13-vertical-not-equals-horizontal-offset.png" | relative_url }})

It's very easy to write [plausible-looking code that confuses horizontal and
vertical
offsets](https://github.com/JodaOrg/joda-time/blob/5f98d636174cc0c6b76c9f434ee17e2b36577414/src/main/java/org/joda/time/chrono/ZonedChronology.java#L552-L554)
which [gives undesirable results near to
transitions](https://github.com/elastic/elasticsearch/blob/8114646e12661a860bcc388124eebb74aa8b7ea3/server/src/main/java/org/elasticsearch/common/rounding/Rounding.java#L210-L228).

## When do transitions occur?

In many timezones there's two transitions a year, approximately 6 months apart,
that respectively set the clocks forwards and back by an hour.  These
transitions are a long way apart, and do not shift the clocks by very much, so
they don't really interact in most calculations. But what if the transitions
were closer together, and larger, so that a local time might occur three times?

![LUTG of clocks going backwards twice in quick succession]({{ "/assets/2018-08-timezone-diagrams/14-interacting-transitions.png" | relative_url }})

In theory it's possible for this to happen, but it hasn't yet, and would be a
slightly strange thing for a government to decide on. Still, who knows if it'll
happen in the future? APIs like
[`java.time.zone.ZoneRules#getValidOffsets`](https://docs.oracle.com/javase/8/docs/api/java/time/zone/ZoneRules.html#getValidOffsets-java.time.LocalDateTime-)
do allow for this to occur. The closest two transitions in the current database
occurred three days apart in `Europe/Warsaw` on `1944-10-01` and `1944-10-04`.

There are other things to remember when thinking about when transitions happen:

- the southern hemisphere starts each year in summertime, so the
  forwards/backwards shifts of their clocks is the other way round from
timezones in the northern hemisphere

- timezones near to the equator may not shift their clocks at all

- timezones such as Morocco's sometimes change their clocks 4 times a year,
  returning to standard time for the duration of Ramadan.

- timezones also occasionally perform an ad-hoc transition to change the
  alignment of their clocks with their neighbours. This might even divide a
single timezone in two, if only part of the original timezone changes its
rules. [Indiana](https://en.wikipedia.org/wiki/Time_in_Indiana) seems
particularly prone to this sort of thing, and has its own subdirectory in the
IANA timezone database because of it.

In short, it's fairly hopeless trying to calculate when transitions might occur
in any given timezone, or to expect there to be exactly two every year. You
have to check the database provided by your operating system or libraries. Note
also that the transition rules are set by a political process, so can change
(sometimes at [very short
notice](https://codeofmatt.com/2016/04/23/on-the-timing-of-time-zone-changes/)),
which means you have to update your timezone database as new decisions are
made.

### Future transitions

Future entries in the timezone transition database are predictions &mdash;
educated guesses based on a pattern of past behaviour &mdash; and subject to
revision. This means it's [wrong to blindly convert all date-time values in
your system into UTC for
storage](http://www.creativedeletion.com/2015/03/19/persisting_future_datetimes.html):
human events like meetings (and legal events like deadlines) are normally given
in local time, and you cannot know for certain the UTC offset that will be in
force at the time of a future event, so [prematurely converting future local
times to UTC does not
work](https://codeblog.jonskeet.uk/2019/03/27/storing-utc-is-not-a-silver-bullet/).

## Transitions in linked timezones

If you are working with multiple, linked, timezones then be aware of how their
transitions are linked. In the EU, the clocks change at the same universal time
(0100 UTC) which preserves the difference in offsets between neighbouring
timezones:

![LUTG of multiple clock changes in the EU]({{ "/assets/2018-08-timezone-diagrams/15-eu-simultaneous-transitions.png" | relative_url }})

However, in North America, the clocks change at the same _local_ time (0200)
which temporarily changes the relative offsets between neighbouring zones:

![LUTG of multiple clock changes in the US]({{ "/assets/2018-08-timezone-diagrams/16-us-local-time-transitions.png" | relative_url }})

Given that timezone offsets are agreed politically and subject to change, this
kind of linkage is not very reliable. It's much better to ignore it and to
perform the calculations properly using the timezone database instead.

## Sizes of offsets

![How large can offsets be?]({{ "/assets/2018-08-timezone-diagrams/17-offset-size.png" | relative_url }})

The majority of offsets from UTC are a whole number of hours, but there are
many that aren't. Historically, many timezones were set using solar time,
giving quite odd offsets indeed, but since 1980 all offsets in the IANA
database are a multiple of 15 minutes. The last one that wasn't was
`Pacific/Kiritimati` which changed offset from `-10:40` to `-10:00` at midnight
on `1979-10-01`. That's not to say that a future change might introduce a
non-15-minute offset again, just that at the moment there aren't any known
ones.

In a perfect world, all offsets would be between `-12:00` and `+12:00` from
UTC. However, the international date line is not straight, and islands near to
it seem to prefer to be on the Australasian side than the American side, so the
actual range of offsets found in practice is `-12:00` to `+14:00`. Again,
that's not to say that a future change might introduce an offset outside that
range, just that there aren't any at the moment.

## Sizes of transitions

![How large can transitions be?]({{ "/assets/2018-08-timezone-diagrams/18-transition-size.png" | relative_url }})

Most regular transitions shift the clocks by a whole hour - in fact, the only
one I know not to is `Australia/Lord_Howe` which shifts the clocks by 30
minutes. Ad-hoc transitions can shift the clocks by any amount. The largest
clock changes I know of were in `Antarctica/DumontDUrville` which has sometimes
been in UTC and sometimes in `UTC+10:00`, with a ten-hour clock change at the
transitions. There have also been numerous transitions by ±24 hours as
timezones shift across the international date line in one direction or the
other, which aren't strictly a _clock_ change (they don't affect the time of
day, just the day itself) but which still cause issues for software.

## Effects on midnight and other special times

Since a transition can cause local times to be skipped or duplicated, beware of
issues caused by this affecting a "special" time like midnight. Most
transitions try and avoid affecting midnight like this, but there are timezones
like `Atlantic/Azores` which set the clocks back an hour at `01:00` local time
giving two midnights:

![Duplicating midnight]({{ "/assets/2018-08-timezone-diagrams/19-duplicated-midnight.png" | relative_url }})

There's also the mess caused by setting the clocks back [just after
midnight]({% post_url 2017-12-27-timezone-curiosities %}) which makes the two
days overlap in terms of their local times:

![Overlapping days]({{ "/assets/2018-08-timezone-diagrams/20-overlapping-days.png" | relative_url }})

The opposite can occur if the clocks are set forwards just before midnight too:

![Missing midnights]({{ "/assets/2018-08-timezone-diagrams/21-no-midnight.png" | relative_url }})

In applications where there are other special local times, e.g. when trying to
round a time to the nearest hour, beware of similar effects. Where offsets
change by an amount that isn't a whole multiple of an hour, you need to decide
whether to keep rounding to the top of an hour, or to keep the intervals all an
hour long, since you can't do both.

## Leap seconds

These diagrams treat universal time (UTC) as if it advances at a constant rate.
In fact this isn't true, it's
[TAI](https://en.wikipedia.org/wiki/International_Atomic_Time) that advances at
a fixed rate, and UTC differs from TAI by a whole number of seconds that
changes from time to time via the insertion of a leap second.  In practice most
data that you come across tends to have already dealt with leap seconds in one
way or another, so a UTC-to-local diagram is appropriate. If the difference was
important then it'd be fine to draw this kind of diagram with TAI on the
horizontal axis instead of UTC.

## Choosing a timezone

(addendum 2018-08-13) Redditor
[/u/dbxp](https://www.reddit.com/r/programming/comments/96qhjo/working_with_timezones/e43xt4u)
points out that I omitted to talk about how to choose the appropriate timezone
for any given calculation, and gives the example of Jerusalem in which the
choice of timezone depends on more than just geography. A similar example to
this is that of the [Mount Washington
Observatory](https://github.com/eggert/tz/blob/5c005615f3f8beaa3eaf4a67ab9c87dc702e1781/northamerica#L296-L300)
which apparently keeps to
[`Etc/GMT+5`](https://en.wikipedia.org/wiki/UTC-05:00) even though
geographically it should be in `America/New_York`.

The choice of timezone is a human activity, so the only reliable way to choose
a timezone is to expose the choice directly to a human being. Guessing it based
on other factors is likely to fail for some of your users.

Additionally, using a proper timezone name in the UI for this is much better
than trying to abbreviate it cleverly. It's hard to trust a UI that describes
the UK timezone as `GMT`, which suggests that it doesn't correct for daylight
saving. [It'd be nice if Microsoft didn't do
this](https://support.microsoft.com/en-gb/help/973627/microsoft-time-zone-index-values):

> (GMT) Greenwich Mean Time: Dublin, Edinburgh, Lisbon, London

😭

## Conclusion

A graph showing local time against universal time is a useful thing to draw if
you have to work on some timezone-sensitive system and need help visualising
all the things that might occur. With the right pictures, it's much easier to
get things right.
