---
layout: post
title:  "TCP backpressure"
date:   2025-12-21
---

Backpressure in a distributed system allows receiving nodes to notify sending nodes that they temporarily lack the capacity to handle further requests. Without backpressure the receiving node must attempt to handle every request and, if overloaded, must shed load by returning error responses, often causing more work as the sender retries the failed requests.

A very useful (if somewhat misunderstood) feature of TCP is its built-in support for backpressure. Every TCP packet includes a 16-bit _window_ field in its header which indicates how many more bytes the sender can accept. Typically this value is shifted by some number of bits known as the _window scale_ set with a TCP option during the initial handshake (and potentially modified later) as defined in [RFC 7323](https://datatracker.ietf.org/doc/html/rfc7323#section-2). A node, receiving a stream of data faster than it can handle it, applies backpressure by reducing the window size in its TCP acknowledgements. Crucially, the node may reduce this window size all the way down to zero, indicating that it can handle no more data. This backpressure mechanism is built into the operating system's TCP implementation and the only thing that an application needs to do to access it is to stop reading data from the socket in question while it is overloaded. Once the overload has passed, the application reads from the socket again which causes the kernel to transmit a packet advertising that the window is open again, inviting the sender to continue sending data.

One of the misunderstandings about this mechanism is the belief that there must be some kind of timeout after which a connection in the zero-window backpressure state indicates some kind of error condition and should be closed. [RFC 1122](https://datatracker.ietf.org/doc/html/rfc1122#page-92) says that this is not the case:

            A TCP MAY keep its offered receive window closed
            indefinitely.  As long as the receiving TCP continues to
            send acknowledgments in response to the probe segments, the
            sending TCP MUST allow the connection to stay open.

There is no need for any timeout here because the zero-window state is actively maintained by the two endpoints: the prospective sender repeatedly sends so-called zero-window probes to which the receiver responds, indicating that both ends remain alive but that the backpressure situation persists. This is essential because when the backpressure is released the receiver sends a single window-open advertisement but this packet may be lost. As long as the sender eventually sends another probe it will eventually discover that the backpressure has been released.

These repeated zero-window probes also ensure that the sender eventually detects a network partition by watching for a sufficiently long sequence of consecutive probes to which it has not received a response, as if it were sending TCP keepalives.

[RFC 1122](https://datatracker.ietf.org/doc/html/rfc1122#page-92) has some recommendations about the exact timings of the zero-window probes:

            The transmitting host SHOULD send the first zero-window
            probe when a zero window has existed for the retransmission
            timeout period (see Section 4.2.2.15), and SHOULD increase
            exponentially the interval between successive probes.

            [...]                   Exponential backoff is
            recommended, possibly with some maximum interval not
            specified here.

In practice a maximum is essential, or else the sender may wait for unreasonably long before discovering that the window has reopened. For example, if it backed off by a factor of 2 on every probe with no maximum and the window-opening packet went undelivered then the sender would effectively wait for twice the length of the backpressure period before discovering that the window has reopened.

But how exactly are these timings calculated?

## Linux

In Linux by default the zero-window probes are scheduled similarly to regular [retransmissions]({% post_url 2025-12-02-tcp-retries2 %}), starting at `RTO_MIN` (200ms) and backing off repeatedly by a factor of 2 up to a maximum of `RTO_MAX` (2 minutes), which it reaches after the backpressure has lasted for a little under 3½ minutes:

| Probe   | Start/mm:ss | Timeout         | Timeout/s | End/mm:ss.s
|--------:|------------:|----------------:|----------:|-----------------:
| 0       | 0:00.0      |       `RTO_MIN` | 0.2       | 0:00.2
| 1       | 0:00.2      |   `2 × RTO_MIN` | 0.4       | 0:00.6
| 2       | 0:00.6      |   `4 × RTO_MIN` | 0.8       | 0:01.4
| 3       | 0:01.4      |   `8 × RTO_MIN` | 1.6       | 0:03.0
| 4       | 0:03.0      |  `16 × RTO_MIN` | 3.2       | 0:06.2
| 5       | 0:06.2      |  `32 × RTO_MIN` | 6.4       | 0:12.6
| 6       | 0:12.6      |  `64 × RTO_MIN` | 12.8      | 0:25.4
| 7       | 0:25.4      | `128 × RTO_MIN` | 25.6      | 0:51.0
| 8       | 0:51.0      | `258 × RTO_MIN` | 51.2      | 1:42.2
| 9       | 1:42.2      | `512 × RTO_MIN` | 102.4     | 3:24.6
| 10      | 3:24.6      | `RTO_MAX`       | 120.0     | 5:24.6
| 11      | 5:24.6      | `RTO_MAX`       | 120.0     | 7:24.6
| 12      | 7:24.6      | `RTO_MAX`       | 120.0     | 9:24.6
| 13      | 9:24.6      | `RTO_MAX`       | 120.0     | 11:24.6
| 14      | 11:24.6     | `RTO_MAX`       | 120.0     | 13:24.6
| ⋮        | ⋮     | ⋮       | ⋮     | ⋮

The `tcp_retries2` sysctl also works similarly on zero-window probes to how it works with regular retransmissions: if more than `tcp_retries2` consecutive zero-window probes go unacknowledged then the connection fails. With the default value of `15`, this means that a connection across a network partition may not be considered faulty for 30 whole minutes (15 times `RTO_MAX`) if it had been experiencing backpressure for more than 3½ minutes prior to the partition. Yikes!

The `tcp_retries2` sysctl has an additional effect on connections experiencing backpressure: it also limits the time between zero-window probes. I couldn't find this mentioned in any documentation but [this is where it's implemented](https://github.com/torvalds/linux/blob/9094662f6707d1d4b53d18baba459604e8bb0783/net/ipv4/tcp_output.c#L4583-L4584):

        if (icsk->icsk_backoff < READ_ONCE(net->ipv4.sysctl_tcp_retries2))
            icsk->icsk_backoff++;

Here `icsk->icsk_backoff` is the backoff counter, visible using tools such as `ss -tonie`, and from which the re-probe interval is computed. The effect of this code is to stop increasing the backoff counter, and thus the re-probe interval, once it reaches `tcp_retries2`. Thus with `tcp_retries` set to a [more reasonable value]({% post_url 2025-12-02-tcp-retries2 %}) of `5` the interval between zero-window probes will not increase beyond `32 × RTO_MIN` which is a little over 6 seconds:

| Probe   | Start/mm:ss | Timeout         | Timeout/s | End/mm:ss.s
|--------:|------------:|----------------:|----------:|-----------------:
| 0       | 0:00.0      |       `RTO_MIN` | 0.2       | 0:00.2
| 1       | 0:00.2      |   `2 × RTO_MIN` | 0.4       | 0:00.6
| 2       | 0:00.6      |   `4 × RTO_MIN` | 0.8       | 0:01.4
| 3       | 0:01.4      |   `8 × RTO_MIN` | 1.6       | 0:03.0
| 4       | 0:03.0      |  `16 × RTO_MIN` | 3.2       | 0:06.2
| 5       | 0:06.2      |  `32 × RTO_MIN` | 6.4       | 0:12.6
| 6       | 0:12.6      |  `32 × RTO_MIN` | 6.4       | 0:19.0
| 7       | 0:19.0      |  `32 × RTO_MIN` | 6.4       | 0:25.4
| 8       | 0:25.4      |  `32 × RTO_MIN` | 6.4       | 0:31.8
| 9       | 0:31.8      |  `32 × RTO_MIN` | 6.4       | 0:38.2
| 10      | 0:38.2      |  `32 × RTO_MIN` | 6.4       | 0:44.6
| ⋮        | ⋮     | ⋮       | ⋮     | ⋮

 This means that a prospective sender will be able to pick up the open window within a few seconds even if the window-opening packet goes undelivered, and a network partition will be detected in `5 × 32 × RTO_MIN` which is a little over 30 seconds, a much more reasonable behaviour than the 30-minute default.
