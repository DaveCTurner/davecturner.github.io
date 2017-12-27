---
layout: post
title:  "Timezone curiosities"
date:   2017-12-27 16:14:00 +0000
---

A few days ago an [interesting test
failure](https://github.com/elastic/elasticsearch/issues/27966) occurred in the
Elasticsearch test suite, highlighting a rare and obscure assumption-violation
that's lain dormant for a number of years. I hesitate to call it a _bug_,
because it's not really clear what the correct behaviour is here, but there's
definitely a discrepancy between the assumptions recorded in the test suite and
the behaviour of the production code.

The discrepancy only manifests in Newfoundland (specifically, the
`America/St_Johns` IANA timezone) and only for 59 minutes of each of the years
from 1987 to 2010 inclusive.

The assumption that we were incorrectly making was, roughly, that the act of
extracting the date from a local time is a nondecreasing function. This is
pretty much the case in pretty much all other timezones, but in Newfoundland
for a while they set the clocks back each autumn at `00:01` local time, meaning
that the first minute of the Sunday on which the clocks changed was followed by
a reprise of the last 59 minutes _of the previous Saturday,_ then the first
minute of the Sunday again, before normal service was resumed.

A consequence of this situation is that there are _two local midnights_ on each
of the days when the clocks go back. This is not the only way this can happen,
and Elasticsearch's test suite already checks for [this case in the
`Atlantic/Azores`
timezone](https://github.com/elastic/elasticsearch/blob/31d4a4bf7c6d74f7c4e2e94f2b64bdb0c18db87b/core/src/test/java/org/elasticsearch/common/rounding/TimeZoneRoundingTests.java#L521-L534)
which sets its clocks back by an hour at `01:00` so the first hour of the day
of the change is repeated, including midnight, without any overlap between that
day and the previous.

Now it's fairly well-known that essentially all reasonable assumptions about
time
[are](http://infiniteundo.com/post/25326999628/falsehoods-programmers-believe-about-time)
[wrong](http://infiniteundo.com/post/25509354022/more-falsehoods-programmers-believe-about-time)
so this particular case isn't _that_ surprising. I [tweeted about
it](https://twitter.com/DaveCTurner/status/944266008302444545) seeing as how it
wasn't on either of Noah's lists.

## Alaska

One of the responses was [this one from James
Davenport](https://twitter.com/JamesHDavenport/status/945084089186570240)
pointing me to the temporal effects of the purchase of Alaska from Russia by
the United States of America, which is another interesting curiosity. Since
this occurred in 1867 it pre-dated the adoption of time zones, so time was
typically defined by local solar time everywhere. The transfer of sovereignty
didn't change the movement of the sun across the sky, so the effect of the
purchase on local _clocks_ was nonexistent. The effect on _calendars_ was more
complicated.  Firstly, Russia sits on the opposite side of the [International
Date Line](https://en.wikipedia.org/wiki/International_Date_Line) from the USA,
so the transfer shifted calendars back a day. Secondly, at that time Russia was
using the Julian calendar and the USA was using the Gregorian calendar, which
was 12 calendar days ahead at the time.

According to the [Sacramento Daily
Union](https://cdnc.ucr.edu/cgi-bin/cdnc?a=d&d=SDU18671114.2.12.1) at 1530 on
Friday 18 October 1867 there was a ceremony in Sitka marking the transfer. The
preceding sentence is itself a little confusing as the date, appearing as it
does in an American newspaper, is presumably given in the Gregorian calendar,
and also presumably given according to the American side of the International
Date Line. It's not wholly clear, but this is how the [IANA Timezone
database](https://www.iana.org/time-zones) interprets it at least: taking the
time of the transition to have occurred at the time of the ceremony then then
in the surrounding seconds the local time at Sitka would have looked like this:

    Saturday 1867-10-07 15:29:58
    Saturday 1867-10-07 15:29:59
    Friday   1867-10-18 15:30:00
    Friday   1867-10-18 15:30:01
    Friday   1867-10-18 15:30:02

This is wrong for a couple of reasons. Firstly, I'm using [ISO
8601](https://en.wikipedia.org/wiki/ISO_8601) date formatting, but ISO 8601
prescribes the Gregorian calendar, so those first few days should really be
written `1867-10-19`, or else something like `7 октября 1867 г.` that isn't in
an ISO 8601 format. Written like that, this is another counterexample to the
assumption that date truncation is nondecreasing.

It's also wrong because this description of the transition is very precise but
very inaccurate. Time and date weren't terribly well-documented or communicated
back in 1867, and governments took even less interest in defining them
precisely than they do now. I don't know that there's any evidence that the
locals of Sitka set their calendars back to Friday at the transition ceremony,
and it seems unlikely to me that anyone did. There's [an
account](http://alaskahistoricalsociety.org/wp-content/uploads/2016/12/Ahllund-2006-Memoirs-of-a-Finnish-Workman.pdf)
of someone who kept on the Russian calendar for another couple of days, and
then celebrated two Sundays in a row, so perhaps it'd be more accurate to have
the transition at midnight on `1867-10-21`, although the account describes the
second Sunday as "our Monday" so perhaps they didn't change their calendar even
then. Changing everywhere at local midnight would give a nondecreasing date
truncation function again, but would mean that different locations in Alaska
would change at different times since local time was solar time back then.

Communication in Alaska at that time was pretty poor, so it seems likely that
anyone outside of Sikta was unaware of the transition for quite a while yet.
Frankly, if you're trying to interpret temporal data from Alaska in 1867,
you're going to have to work out what time zone and calendar were in use
yourself. It's almost certainly not in any time zone described by the IANA
database.

## Samoa and Tokelau

There are various other examples of countries moving across the International
Date Line that pre-date the adoption of timezones. In many cases (e.g.
`Pacific/Pago_Pago`, `Pacific/Apia`) the IANA database records these shifts as
occurring at local midnight, giving a simple 48-hour day with no overlaps with
the neighbouring days.

A more recent example of a shift across the International Date Line is the case
of [Samoa and Tokelau](http://www.bbc.co.uk/news/world-asia-16351377) who
changed sides _because of_ the effect on their calendar. The change, in the
opposite direction from Alaska in 1867, took place at local midnight, skipping
over Friday `2011-12-30` entirely. The date truncation function _is_
nondecreasing here, but this is a nice source of other counterexamples.
