---
layout: post
title:  "Catch-up-free elections"
date:   2017-12-27 11:38:00 +0000
---

Implementations of
[Paxos](http://lamport.azurewebsites.net/pubs/lamport-paxos.pdf)-based
[RSMs](https://www.microsoft.com/en-us/research/publication/how-to-build-a-highly-available-system-using-consensus/)
usually include some kind of mechanism to allow nodes that have fallen behind
the rest of the cluster to catch up again by copying the freshest committed
state directly from a peer, avoiding the need to compute each
intervening state transition.

This catch-up mechanism means that nodes can discard information about
committed transitions and need only track the latest known committed state (as
well as the data associated with any uncommitted slots) in order to guarantee
the [system's liveness]({% post_url 2017-08-17-paxos-pre-voting %}). This is
closely related to [Raft's](https://ramcloud.stanford.edu/~ongaro/thesis.pdf)
log compaction mechanism, albeit with a clearer distinction between the natures
of the committed and uncommitted portions of the log, which I think more
closely matches the implementation of systems that do not have any need for an
explicit log of committed values.

In the implementations that I've worked on in the past ([e.g. this]({% post_url
2017-09-15-zero-copy-paxos %})) I've built the catch-up mechanism into the
[pre-voting phase]({% post_url 2017-08-17-paxos-pre-voting %}): if, during
pre-voting, a node discovers that it does not have the freshest committed
state, then it aborts the pre-voting and performs a catch-up. This means that,
in the absence of progress, eventually all nodes are candidates with the same
states (i.e. sets of committed values) which means that progress can be made.

A possible problem with this greedy catch-up mechanism is that the number of
catch-ups before convergence is at-most-quadratic in the number of nodes in the
cluster. A committed state may have a large representation on-the-wire, meaning
that catch-up is quite a costly mechanism, so a quadratic bound is something to
try and avoid if possible.

My colleagues in the distributed systems team at [Elastic](http://elastic.co)
pushed for an alternative approach in which catch-up was deferred until the
`proposed`/`accepted` phase of the algorithm, which occurs after an election is
won. Because the election is won by a maximally-fresh node, and this node
serves all the catch-up requests, the number of catch-ups is optimal: at most
linear in the size of the cluster.

This complicates the liveness argument quite a bit, particularly since we also
rely on [strong leadership]({% post_url 2017-12-27-strong-leadership-in-paxos
%}) to avoid the need to transfer any accepted-but-not-yet-committed state
during an election. Nodes abort their election if they discover the existence
of a peer with
* a fresher committed state, or
* an equally-fresh committed state and a fresher last-accepted value for the
first uncommitted slot.

As described so far, this scheme can get into a state where no node can win an
election: there is no guarantee that some node with the freshest committed
state also has the freshest last-accepted value for the next slot, which means
that the desired liveness property does not hold.

Fortunately, the only way to get into this state is to allow nodes to accept
values proposed for slots that are strictly later than the first uncommitted
slot. We do not support this kind of pipelining in the implementation on which
we are currently working: the only way a node can accept a value for a slot is
if it knows that the previous slot was committed, which repairs the hole in the
liveness argument.

There may be other ways to repair this hole _and_ support pipelining. This post
is a note-to-self to avoid using the same catch-up-free election mechanism in
an implementation that supports pipelining without thinking about the liveness
implications again.
