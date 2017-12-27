---
layout: post
title:  "Strong leadership in Paxos clusters"
date:   2017-12-27 10:01:00 +0000
---

Implementations of
[Paxos](http://lamport.azurewebsites.net/pubs/lamport-paxos.pdf)-based
[RSMs](https://www.microsoft.com/en-us/research/publication/how-to-build-a-highly-available-system-using-consensus/)
usually include some kind of leader election in order to ensure that the
implementation has the right kind of [liveness properties]({% post_url
2017-08-17-paxos-pre-voting %}). In the implementations that I've worked on in
the past ([e.g. this]({% post_url 2017-09-15-zero-copy-paxos %})) any node
could theoretically become the leader at any point, so the votes in the
election [include the values last accepted by the voting node in any
uncommitted
slots](https://github.com/DaveCTurner/zero-copy-paxos/blob/1951f653c774fbc6ab765d3af0aabe6f31613d0b/src/h/Paxos/Promise.h#L47).

It's a little wasteful to include the last-accepted value in _each_ voting
message, since the node that's collecting votes discards all but one of the
values it receives, and in the most common failure modes it can discard all of
them since it already has the appropriate value stored locally.

It's not unreasonably wasteful if the values are small enough that they don't
cost much extra to transfer during the election. Indeed, in order to show the
algorithm's liveness properties we need to assume that [there is an upper bound
on the time it takes to send messages between nodes]({% post_url
2017-08-17-paxos-pre-voting
%}#unboundedly-large-messages). The work I've been doing recently has involved
values with much larger on-the-wire representations than before, which means
that it has been worthwhile putting more effort into avoiding this kind of
waste.

One possible optimisation here is to break the election into two phases, with
each node announcing just the term of its last-accepted value in the first
phase and deferring the costlier transfer of the value itself until the second
phase, which gives the opportunity to skip this transfer if it is not needed.
This makes for a more complex protocol, with more messages to lose in flight
and more states to track, so doesn't seem like the right thing to do.

My colleagues in the distributed systems team at [Elastic](http://elastic.co)
pointed me to an alternative idea recently, taken from
[Raft's](https://ramcloud.stanford.edu/~ongaro/thesis.pdf) so-called _strong
leadership_ property, which I hadn't really pondered in sufficient depth
before: don't send any values during an election, and simply abort the election
if you receive an indication that your local state isn't the freshest.

It's hopefully obvious that this has no impact on the safety property, but the
effect on the system's liveness is less clear. With a little thought you should
be able to see that there is _some_ node that has a local last-accepted state
that's no more stale than that of its peers, and it is a node like this that
must end up as master.

One nice property of my favourite [liveness mechanism]({% post_url
2017-08-17-paxos-pre-voting %}) is that in the absence of progress all nodes
eventually become candidates, at which point if _any_ of them wakes up and
starts a pre-voting phase then this results in a successful election and at
least one value being chosen, and hence progress. This is no longer true if
some nodes abort their election upon the realisation that they have stale
state, but this property can be recovered by adding a mechanism for
_transferring_ the election instead of simply aborting it: the transfer message
effectively wakes up the less-stale recipient and puts the more-stale sender to
sleep. There is no need for the sender to attempt to find its freshest
(least-stale) peer by waiting for multiple votes: transferring the election to
any strictly-fresher peer is enough. This can only happen finitely often and
ensures that if any node wakes up then, in bounded time, a sufficiently
fresh node wakes up, wins an election, and makes progress.

This recovers the liveness argument, including the nice property that
eventually _any_ wake-up results in progress.
