---
layout: post
title:  "Weighted majorities"
date:   2017-08-15 17:45:09 +0000
---

Most distributed systems are exposed to some failure modes that can
simultaneously take out multiple nodes, such as the failure of a shared power
feed or networking hardware. In the cloud, this possibility for correlated
failures is presented abstractly as zones (AWS and GCE) or fault domains
(Azure), and you may have a similar abstraction in your own data centres too.
The implication is that correlated failures may occur within each zone, and you
should design for this, but failures across zones should be independent.
Indeed, the [AWS EC2 SLA](http://aws.amazon.com/ec2/sla) considers a
single-zone failure not even to be a service-level outage.

Zones are also a limited resource. There are few regions in AWS and GCE that
have more than three zones. Three zones is the absolute minimum for running a
distributed consensus algorithm such as Paxos or Raft: any fewer and a one-zone
failure can take down your system.

A Raft cluster is defined in terms of the current set of nodes, and the allowed
reconfigurations are those that add or remove a single node from the set. The
reason for this is that every majority subset of a set _N_ of nodes intersects
every majority subset of _N_ &#x222A; {_n_}, so a one-node reconfiguration
can't introduce inconsistency. Suppose you have three zones, _A_, _B_ and _C_,
containing three nodes _a_, _b_ and _c<sub>1</sub>_, and suppose you want to
replace _c<sub>1</sub>_ with a new node _c<sub>2</sub>_, also in zone _C_. The
reconfiguration sequence you need is one of the following:

| _a_ | _b_ | _c<sub>1</sub>_ | _c<sub>2</sub>_
|-----|-----|-----------------|----------------
|  Y  |  Y  |        Y        |
|  Y  |  Y  |        Y        |        Y
|  Y  |  Y  |                 |        Y
{: .weights-table }

<div class="table-spacer">or</div>

| _a_ | _b_ | _c<sub>1</sub>_ | _c<sub>2</sub>_
|-----|-----|-----------------|----------------
|  Y  |  Y  |        Y        |
|  Y  |  Y  |                 |
|  Y  |  Y  |                 |        Y
{: .weights-table }

<div style="clear: both">&nbsp;</div>

In either case, in the interim configuration the system is exposed to the risk
that a single-zone failure takes the system down.  If using simple
sets-of-nodes configurations then the only solution to this is to use a fourth
zone, which will be expensive if it's even possible. However if you use a
slightly more general type of configuration based on assigning each node an
integer _weight_ then the need for an extra zone can be avoided. In this setup
the allowed reconfigurations are those that increment or decrement the weight
of a single node by one, which also has the property that the majorities
before a reconfiguration intersect the majorities after the reconfiguration, and
this allows the following sequence:

| _a_ | _b_ | _c<sub>1</sub>_ | _c<sub>2</sub>_
|-----|-----|-----------------|----------------
|  2  |  2  |        2        |
|  2  |  2  |        2        |        1
|  2  |  2  |        1        |        1
|  2  |  2  |        1        |        2
|  2  |  2  |                 |        2
{: .weights-table }

<div style="clear: both">&nbsp;</div>

At every step of this sequence, every zone holds less than half of the total
weight which means the system is resilient to any single-zone failure.

For proofs of the statements about the intersections of majorities, see
Appendix A of the [Unbounded pipelining in Paxos]({% post_url
2016-06-09-unbounded-pipelining-paxos %}) paper.
