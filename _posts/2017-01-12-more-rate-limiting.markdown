---
layout: post
title:  "More rate limiting"
date:   2017-01-12 19:09:09 +0000
---

Following on from [the previous post on rate limiting]({% post_url
2016-12-01-rate-limiting %}), recall the graph of the level _L_ of water in the
bucket as a function of time:

![Level vs time]({{ "/assets/2016-12-01/04-level-vs-time.png" | relative_url }})

## Bursts

The bucket capacity represents the system's ability for handling bursts of
traffic. It should not be set so high that a burst of requests could overwhelm
the system before the bucket fills up.

## Varying the parameters

As drawn, the bucket capacity _L<sub>C</sub>_ and the leak rate _r_ are
constant, but for more advanced rate-limiting situations one may want them to
vary. Their ratio, _L<sub>C/r_ is the _reset time_: the time it takes for a
full bucket to completely empty by leaking.

### Slow-start

Sometimes the first few requests to a service are more expensive or are handled
more slowly, e.g. due to cold caches. In this case it may be useful to start
with a tight rate limit and then slacken it over time. A simple approach is to
progressively increase _r_ (and probably to increase _L<sub>C</sub>_ too to
keep the reset time constant).

A more adaptive approach would be to make _r_ and/or the size of each request a
function of the current level _L_ in the bucket. Given a reasonably steady rate
of requests, the bucket is normally either mostly-empty (if the rate is lower
than the limit) or mostly-full (if the rate is higher than the limit). If the
request rate is significantly lower than the limit then any caches in the
system may "cool down" and it may be desirable to reduce the leak rate and
capacity to protect against a sudden burst of traffic.

## Scaling-out

A single-bucket rate limiter could be a bottleneck in a distributed system, but
the analogy (and algorithm) can be extended across multiple buckets. If the
buckets are all independent then they impose independent rate limits,
obviously, which may be appropriate. Alternatively the buckets could be linked
together by occasionally moving some water from one bucket to another, freeing
up some extra capacity in one otherwise-overfull bucket.

This may not need any terribly strong consistency, depending on the target SLA:
it is probably fine to occasionally lose a bit of water in transit, which has
the effect of allowing more requests through than are technically permitted.


