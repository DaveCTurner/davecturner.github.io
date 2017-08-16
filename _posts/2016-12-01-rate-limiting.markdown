---
layout: post
title:  "Rate limiting"
date:   2016-12-01 19:09:09 +0000
---

The idea of a leaky-bucket rate limiter is as follows. There is a bucket with a
limited capacity for water, and each request adds some water to the bucket.

![Add water]({{ "/assets/2016-12-01/01-fill-up-bucket.png" | relative_url }})

If a request would have overflowed the bucket then it is rejected instead. The
capacity of the bucket is written _L<sub>C</sub>_.

![Reject on overflow]({{ "/assets/2016-12-01/02-no-overflow.png" | relative_url }})

The bucket leaks its contents at a particular rate, _r_, freeing up capacity
for further requests.

![Leak at fixed rate]({{ "/assets/2016-12-01/03-leak-at-fixed-rate.png" | relative_url }})

As a function of time the level _L_ of water in the bucket follows a path like
this as requests arrive.

![Level vs time]({{ "/assets/2016-12-01/04-level-vs-time.png" | relative_url }})

It is possible to simulate the leak of water from the bucket with a simple loop
that subtracts water from the bucket on each iteration, or else on each
request, the new level _L'_ of water in the bucket can be calculated as
follows.

![On each request]({{ "/assets/2016-12-01/05-on-each-request.png" | relative_url }})

It follows that the amount of water that can be added to the bucket in a time
interval _&Delta;t_ is at most _r&Delta;t + L<sub>C</sub>_.

[This whole post is available in one image.]({{ "/assets/2016-12-01/rate-limiting.png" | relative_url }})

