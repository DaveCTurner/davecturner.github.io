---
layout: post
title:  "Faster commitment in small Paxos clusters"
date:   2017-08-28 19:09:09 +0000
---

An alternative message flow for a Paxos cluster that

* can perform cluster-wide commitment in one or two network delays (rather than
the usual two or three) for small clusters,
* requires no more message delays than the usual scheme in larger clusters,
* has time-to-cluster-wide-commitment no worse (possibly better) than the
usual scheme, and
* may be simpler to implement.

### Usual flow

The usual flow of messages in a Paxos protocol is as follows:

![Usual flow of messages in Paxos]({{ "/assets/2017-08-28/01.png" | relative_url }})

Firstly one of the nodes (node 2 in the diagram) broadcasts a `prepare` (a.k.a.
phase 1a) message and the other nodes respond with `promised` (a.k.a. phase 1b)
messages. When a quorum of these has been received, indicated by a Q on the
diagram, the algorithm is said to have completed phase 1 and enters phase 2. In
phase 2 a `proposed` (a.k.a. phase 2a) message is broadcast and a set of
`accepted` (a.k.a. phase 2b) messages sent in response. On receipt of a quorum
of acceptances by node 2 the proposed value is chosen and acknowledgements of
this fact can be sent. The other nodes are informed that this value is chosen
by sending a `committed` message.

| Phase | Message     | Alternative name | Sender    | Recipient
| ------| ---------   | -----------------| --------- | ----------
| 1     | `prepare`   | phase 1a         | Leader    | All nodes
| 1     | `promised`  | phase 1b         | All nodes | Leader
| 2     | `proposed`  | phase 2a         | Leader    | All nodes
| 2     | `accepted`  | phase 2b         | All nodes | Leader
|       | `committed` |                  | Leader    | All nodes
{: .message-types-table }

The system then remains in phase 2, sending further proposals and acceptances,
for an extended period, typically many hours or days until a failure or
transmission delay occurs, at which point it returns to phase 1 again:

![Subsequent proposals do not need to re-enter phase 1]({{ "/assets/2017-08-28/02.png" | relative_url }})

At higher load, writes may be overlapped which allows `committed` messages to
be combined with subsequent `proposed` messages:

![Combining `committed` and `proposed` messages]({{ "/assets/2017-08-28/03.png" | relative_url }})

If the writes are more heavily overlapped, it might be that the leader proposes
quite a few values `A`, `B`, `C`, ... `W`, `X` before achieving quorum on
having written `A`, so `committed(A)` ends up getting combined with
`proposed(Y)`.

### Avoiding commitment

An alternative scheme is for each acceptor (including the leader) to broadcast
`accepted` messages to all other nodes on receipt of a `proposed` message, and
to have each node check for a quorum itself rather than to wait for a
`committed` message from the leader.

![Broadcasting `accepted` messages]({{ "/assets/2017-08-28/04.png" | relative_url }})

| Phase | Message    | Alternative name  | Sender    | Recipient
| ------| ---------  | ----------------- | --------- | ----------
| 1     | `prepare`  | phase 1a          | Leader    | All nodes
| 1     | `promised` | phase 1b          | All nodes | Leader
| 2     | `proposed` | phase 2a          | Leader    | All nodes
| 2     | `accepted` | phase 2b          | All nodes | _**All nodes**_
{: .message-types-table }

Notice that each node independently achieves quorum (shown as 'Q') on the
chosen value on receipt of `accepted` messages from a majority of its peers.
Since this is a three-node cluster, it only needs a single `accepted` message,
together with the one it sends itself, to reach quorum. This means there is
no need for the non-proposing nodes to broadcast their `accepted` messages:

![Avoiding broadcasting]({{ "/assets/2017-08-28/05.png" | relative_url }})

In this scheme the `proposed` and `accepted` messages from the leader can
always be combined into a single message, since there is little point in the
leader broadcasting a proposal that it does not itself accept:

![Combining `proposed` and `accepted` messages]({{ "/assets/2017-08-28/06.png" | relative_url }})

| Phase | Message             | Sender    | Recipient
| ------| ---------           | --------- | ----------
| 1     | `prepare`           | Leader    | All nodes
| 1     | `promised`          | All nodes | Leader
| 2     | `proposed+accepted` | Leader    | All nodes
| 2     | `accepted`          | All nodes | _**Selected nodes**_
{: .message-types-table }

Subsequent proposals follow the same pattern and therefore do not need to
re-enter phase 1. The overall flow of messages is reduced simply to the leader
broadcasting `proposed+accepted` messages and its followers responding with
`accepted` messages:

![Subsequent proposals do not need to re-enter phase 1]({{ "/assets/2017-08-28/07.png" | relative_url }})

These messages can be overlapped, allowing proposals to be made without waiting
for earlier ones to be accepted:

![Pipelining]({{ "/assets/2017-08-28/08.png" | relative_url }})

### Commentary

From implementation experience, I quite like this scheme.

It seems a bit simpler to combine the `proposed` and `accepted` messages than
to combine a `proposed` message with any pending `committed` messages. The
`proposed` and `accepted` messages are for the same slot, generated on the same
code path, whereas in the usual scheme an implementation must check for
`committed` messages for earlier slots when sending a `proposed` message. This
means that an implementation of the usual scheme must hold off on sending
`committed` messages until a `proposed` message is also ready to send which
adds a delay the the commitment of values across the whole cluster;
implementations must also have a separate mechanism for sending pending
`committed` messages if there are no `proposed` messages to send for a period
of time, in order to bound the delay before cluster-wide commitment.

It's particularly nice for three-node clusters where `accepted` messages from
the follower nodes don't need to be broadcast, and the followers learn that
values have been committed after a single message delay. For three-node
clusters this reduces the number of messages required compared with the
standard scheme, but in larger clusters, or during reconfiguration, this
advantage is lost.

Note also that both `proposed` and `committed` messages generally carry the
value of the proposal in question, whereas `accepted` messages do not. If
values are large and the cluster is small then broadcasting `accepted` messages
could be significantly cheaper than sending each value twice over the wire.
