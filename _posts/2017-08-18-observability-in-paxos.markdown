---
layout: post
title:  "Observability in Paxos clusters"
date:   2017-08-18 20:03:17 +0000
---

It is important to expose information about the health of systems to operators,
in case there is some kind of fault that needs action to resolve. The trouble
with fault-tolerant systems is that they tolerate faults: by design they can
appear to be working normally despite some underlying problem, but there is a
limit to how many such problems can be tolerated before the system entirely
fails so it is important to be aware of them.

### Monitoring health

A _healthy_ Paxos cluster has a leader, and all other nodes are followers of
that leader. The leader does not change, and proposes new values at some
minimum frequency to continue to assert its leadership. It receives timely
responses from all its followers when it proposes new values, and all nodes
learn the new values reasonably soon after they are proposed.

If using the [pre-voting mechanism]({% post_url 2017-08-17-paxos-pre-voting %})
then a _critically-unhealthy_ cluster is one in which all nodes are candidates
(or uncontactable) which is fairly easy to observe. This is sufficient because
non-candidates, by definition, made progress recently, and progress requires
communication between a majority of nodes, so if there are any non-candidates
then the system was recently available. Contrapositively, if the system wasn't
recently available then all nodes are candidates.

The more interesting cases are those which are neither healthy nor critically
unhealthy: the system is still making progress, but at an elevated risk of
becoming unavailable. If the system is in such a state then an operator needs
to be warned about it, but it is not urgent to resolve the failure. The two
main symptoms of such a state are

* any node is (or was recently) a candidate or uncontactable, and

* any pair of nodes were unable to communicate with each other.

The first state can be detected by querying all nodes, and also by raising
a warning on recent receipt of a `seek-votes` message which indicates the sender
was a candidate.

The second state requires all nodes to periodically contact all other nodes,
and is important to verify as it is possible for a partial network partition to
allow all followers to communicate with the leader but not with each other. In
this kind of partition if the leader were to fail then none of the followers
may be able to form a majority and take over as a new leader.

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
