---
layout: post
title:  "Observability in Paxos clusters"
date:   2017-08-18 20:03:17 +0000
---

The trouble with fault-tolerant systems is that they tolerate faults: by design
they can appear to be working normally despite some underlying problem.

Majority-based consensus algorithms such as Paxos are designed to keep working
as long as more than half of the nodes in the cluster are healthy and
communicating with each other, but in practice you want to know about unhealthy
nodes or connectivity issues so they can be fixed before they lead to a total
failure.

Fortunately there are some fairly simple symptoms that can be used to detect
and act on all sorts of hidden problems.

### Health

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
so the cluster would immediately become unhealthy.

It's turned out to be useful for nodes to continue to report unhealthiness for
some period of time (say 10s) after technically becoming healthy again, to
mitigate the risk that a persistent yet intermittent fault is missed. _Any_
unhealthiness indicates some kind of genuine fault and if the fault isn't
transient then the operators need to know about it.

It's also turned out to be useful to enter a warning state if any peer was
recently in a warning state (for reasons other than this one) as this
propagates warnings across the whole cluster.

### Latency

Another latent fault to watch out for is to do with (hoho) latency. High
latency at an otherwise healthy-looking node can be a strong leading indicator
of impending doom, such as the system getting too close to at some kind of
throughout limit.

In a majority-based system, the latency presented to clients is related to the
_median_ latency of the individual nodes, which can hide the fact that a
minority of nodes are struggling. The trouble is that if just one of the
healthy nodes goes offline then the median latency can shift dramatically,
possibly triggering a cascading failure.

This means it's a good idea to keep track of the response latencies of all the
nodes as well as the client-facing (i.e. median) latency, to catch any problems
before they start to have consequences.

### Bandwidth

Most of the network bandwidth required to run a Paxos implementation is used
sending data from the leader to its followers. When the leader fails and
another node takes over there can be a dramatic change in the flow pattern of
data in the system, which risks overwhelming some network links. I don't have a
comprehensive answer for how to detect this in advance, but be aware that it
can happen.

Leadership changes should be needed relatively rarely (I count four occurrences
in the last two months in one of our production clusters) but can be disruptive
when they occur, so it could be a good idea to add a Revolutionary Monkey to
your [Simian
Army](https://medium.com/netflix-techblog/the-netflix-simian-army-16e57fbab116)
to depose the current leader more frequently than would happen naturally.

### Unusual activity

In normal running each node of the cluster executes quite a small subset of its
code, avoiding all of the branches that are only active during some kind of
failure. More specifically, this is something like:

* a follower expects to receive only `proposed` and `committed` messages from
  the current leader for its current term, and never to become a candidate.

* a leader expects to receive only `accepted` messages from its followers for
  its current term, and to send `proposed` messages due to timeouts or client
requests.  It occasionally becomes an incumbent, but never a candidate.

It has turned out to be worthwhile and simple to record, in detail, all
activity that is not on these paths. The resulting logs are empty when the
cluster is completely healthy, but contain very detailed information whenever
something unexpected happens.

### Observability

_Observability_ is about measuring the state of your system and using these
measurements to take further action.

If the cluster is completely healthy and all the latency measurements seem
reasonable then all is well in the world. If the cluster is
healthy-but-not-completely then it's still working from the clients'
perspectives but there's an elevated risk of failure. Nodes that become
candidates, even temporarily, warrant further investigation. The logs of
activity off the usual paths will show if it's a problem with the node itself
or its connectivity.

If the cluster is critically unhealthy then immediate action may be required to
restore service. Unusual-activity logs and other monitoring can determine
whether the cluster is down because of lost connectivity or because of the
failure of too many nodes. If the former, fix the connectivity to restore
service. If the latter, there is a risk that some recently-acknowledged data
has been lost, but (accepting this risk) it is sometimes possible to restore a
cluster from any remaining nodes. The last resort is for the cluster to be
completely terminated and then started from backups on a set of healthy nodes.
