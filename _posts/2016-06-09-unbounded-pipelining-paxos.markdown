---
layout: post
title:  "Unbounded pipelining in dynamically reconfigurable Paxos clusters"
date:   2016-06-09 19:09:09 +0000
---

### Abstract

Consensus is an essential ingredient of a fault-tolerant distributed system
systems. When equipped with a consensus algorithm a distributed system can act
as a replicated state machine (RSM), duplicating its state across a cluster of
redundant components to avoid the failure of any single component leading to a
system-wide failure.

Paxos and Raft are examples of algorithms for achieving distributed consensus.
Practical implementations of this kind of system must support dynamic
reconfiguration in order to be able to replace failed components and perform
other administrative tasks without downtime.

Paxos can achieve high performance by pipelining (starting work on new requests
before existing requests have completed) but typically bounds the length of the
pipeline to ensure consistency during reconfiguration. Raft also supports
pipelining and imposes no such bound on concurrent requests, preserving
consistency instead by restricting which reconfigurations may be performed.

This article shows how to extend Paxos to support a more general form of
reconfiguration which subsumes the original bounded-pipeline approach as well
as Raft-like fully-concurrent reconfigurations and more besides.

[PDF](http://tessanddave.com/paxos-reconf-latest.pdf)

### Further Reading

Some followup articles by simbo1905:

* [Paxos reconfiguration stalls](https://simbo1905.blog/2016/12/15/paxos-reconfiguration-stalls)

* [UPaxos: unbounded Paxos reconfigurations](https://simbo1905.blog/2016/12/16/upaxos-unbounded-paxos-reconfigurations/)

* [Paxos voting weights](https://simbo1905.blog/2017/03/16/paxos-voting-weights/)
