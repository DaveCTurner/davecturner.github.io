---
layout: post
title:  "Safety of the Synod algorithm"
date:   2016-09-18 19:09:09 +0000
---

The Synod algorithm is the one-decree foundation of the Paxos distributed
consensus algorithm.

I'm of the school of thought that you can't really understand an algorithm
without understanding the proof of why it works correctly. The clearest proof
that I know of for why the Synod algorithm works is in [Paxos made
simple](https://www.microsoft.com/en-us/research/publication/paxos-made-simple/),
but even that is not all that clear. Here's an illustrated presentation of that
proof that helped me to understand it better. It's a fairly informal outline of
the proof, but there is a more formal version in Appendix B of the [Unbounded
pipelining in Paxos]({% post_url 2016-06-09-unbounded-pipelining-paxos %})
paper that shows there are no gaps in this argument.

#### Proof

Suppose values have been learned for terms _P_ and _Q_:

![01-learned-two-values]({{ "/assets/2016-09-18/01-learned-two-values.png" |
relative_url }})

It is simplest to [argue by
contradiction](https://en.wikipedia.org/wiki/Proof_by_contradiction) so suppose
that the values for these terms are distinct and denote them respectively **X**
and **Y**:

![02-learned-two-different-values]({{
"/assets/2016-09-18/02-learned-two-different-values.png" | relative_url }})

Learned values must have been proposed, so this means that value **X** was
proposed in term _P_ and value **Y** was proposed in term _Q_ by sending
`proposed` (a.k.a. phase 2a) messages:

![03-proposed-learned-values]({{
"/assets/2016-09-18/03-proposed-learned-values.png" | relative_url }})

It may be that values were proposed in terms between _P_ and _Q_ too:

![04-proposed-other-values]({{
"/assets/2016-09-18/04-proposed-other-values.png" | relative_url }})

Find the earliest term _R_ later than _P_ but no later than _Q_ in which a
proposal was made whose value is not **X**:

![05-first-different-term]({{ "/assets/2016-09-18/05-first-different-term.png"
| relative_url }})

_R_ must exist since the proposals made in terms _P_ and _Q_ had different
values. Put differently, all the proposals made in terms earlier than _R_ but
no earlier than _P_ have value **X**:

![06-previous-values-equal]({{ "/assets/2016-09-18/06-previous-values-equal.png" | relative_url }})

The value in term _P_ must have been learned because a majority _S_ of acceptors
sent acceptance (a.k.a. phase 2b) messages:

![07-value-accepted-by-quorum]({{ "/assets/2016-09-18/07-value-accepted-by-quorum.png" | relative_url }})

Also, the value in term _R_ was proposed because of
promises from another majority of acceptors:

![08-promises-by-quorum]({{ "/assets/2016-09-18/08-promises-by-quorum.png" | relative_url }})

Since these majorities overlap, there is at least one node `a` which belongs to
both sets: it accepted a value in term _P_ and then sent a promise for term
_R_.  It must have happened in that order as, having sent a promise for term
_R_, `a` would then not have been able to accept a value in term _P_ since _P_
&lt; _R_:

![09-intersection-accepted]({{ "/assets/2016-09-18/09-intersection-accepted.png" | relative_url }})

Of course `a` may also have accepted some proposals in terms later than _P_
before sending a promise for term _R_, but in any case, the highest-numbered
term accepted by `a` before it sent its promise for term _R_ is no earlier than
_P_ and is strictly earlier than _R_, and therefore has value **X**:

![10-intersection-last-accepted]({{ "/assets/2016-09-18/10-intersection-last-accepted.png" | relative_url }})

Therefore when `a` sent its promise for term _R_, the promise must have
included the last-accepted term which is no earlier than _P_ and is strictly
earlier than _R_, and whose value is therefore **X**.

Other nodes also sent promises for term _R_ and some of these may have included
a previously-accepted term, all of which are strictly less than _R_:

![11-other-last-accepted]({{ "/assets/2016-09-18/11-other-last-accepted.png" | relative_url }})

In any case, the value proposed in term _R_ must be the value of the promise
with greatest last-accepted term, which must be **X** as the greatest
last-accepted term is no earlier than _P_ and is strictly earlier than _R_.
This means that _R_ didn't have a different value from _P_, which is a
contradiction, so the original assumption that _P_ and _Q_ had different values
was wrong, as required.
