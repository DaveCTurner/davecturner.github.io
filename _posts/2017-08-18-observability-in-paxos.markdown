---
layout: post
title:  "Observability in Paxos clusters"
date:   2017-08-18 20:03:17 +0000
---

The trouble with fault-tolerant systems is that they tolerate faults: by design
they can appear to be working normally despite some underlying problem, but
there is a limit to how many such problems can be tolerated before the system
entirely fails so it is important to be aware of them.

### Monitoring health

A _healthy_ Paxos cluster is capable of accepting instructions from clients and
makes regular progress. A cluster can be healthy despite underlying faults, but
it's worth having a basic health check for this to help rule out possibilities
when you are investigating a broader issue.

At the other end of the scale, a cluster is _unhealthy_ if it is unable to
accept any instructions from clients, which may be due to a network partition
or the failure of at least half of the nodes.  If using the [pre-voting
mechanism]({% post_url 2017-08-17-paxos-pre-voting %}) then (after a timeout or
two) all nodes in an unhealthy cluster are candidates which is fairly easy to
observe. This is sufficient because non-candidates, by definition, made
progress recently, and progress requires communication between a majority of
nodes, so if there are any non-candidates then the system was recently
available. Contrapositively, if the system wasn't recently available then all
nodes are candidates.

A _completely-healthy_ Paxos cluster is healthy and has no underlying faults.
It has a leader, and all other nodes are followers of that leader. The leader
does not change, and proposes new values at some minimum frequency to continue
to assert its leadership. It receives timely responses from all its followers
when it proposes new values, and all nodes learn the new values reasonably soon
after they are proposed.

The more interesting cases are those which are healthy but not completely
healthy: the system is still making progress, but at an elevated risk of
becoming unavailable. If the system is in such a state then an operator needs
to be warned about it, but it is not urgent to resolve the failure. The two
main symptoms of such a state are

* _any_ node is (or was recently) a candidate or uncontactable, and

* any pair of nodes is (or was recently) unable to communicate with each other.

The first state can be detected by querying all nodes, and/or by raising a
warning on recent receipt of a `seek-votes` message which indicates the sender
was a candidate.

The second state requires all nodes to periodically contact all other nodes.
It is important to verify this as it is possible for a partial network
partition to allow all followers to communicate with the leader but not with
each other. In this kind of partition if the leader were to fail then none of
the followers may be able to form a majority and take over as a new leader,
so the cluster would immediately be _unhealthy_.

It's turned out to be useful for nodes to continue to report unhealthiness for
some period of time (say 10s) after technically becoming healthy again, to
mitigate the risk that a persistent yet intermittent fault is missed by the
monitoring system. _Any_ unhealthiness indicates some kind of genuine fault and
if the fault isn't transient then the operators need to know about it.

It's also turned out to be useful to enter a warning state if any peer was
recently in a warning state (for reasons other than this one) as this
propagates warnings across the whole cluster.

### Logging unusual activity

In normal running each node of the cluster executes quite a small subset of its
code, avoiding all of the branches that are only active during some kind of
failure. More specifically, this is something like:

* a follower expects to receive only `proposed` and `committed` messages from
  the current leader for its current term, and never to become a candidate.

* a leader expects to receive only `accepted` messages from its followers for
  its current term, and to send `proposed` messages due to timeouts or client
requests.  It occasionally becomes an incumbent, but never a candidate.

It has turned out to be worthwhile and simple to log all activity that is not
on these paths. The resulting logs are empty when the system is operating
normally, but contain very detailed information whenever something unexpected
happens.
