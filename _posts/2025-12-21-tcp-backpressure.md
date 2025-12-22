---
layout: post
title:  "TCP backpressure"
date:   2025-12-21
---

Backpressure in a distributed system allows receiving nodes to notify sending
nodes that they temporarily lack the capacity to handle further requests.
Without backpressure the receiving node must attempt to handle every request
and, if overloaded, must shed load by returning error responses, often causing
more work as the sender retries the failed requests.

A very useful (if somewhat misunderstood) feature of TCP is its built-in
support for backpressure. Every TCP packet includes a 16-bit _window_ field in
its header which indicates how many more bytes the sender can accept. Typically
this value is shifted by some number of bits known as the _window scale_ set
with a TCP option during the initial handshake (and potentially modified later)
as defined in [RFC
7323](https://datatracker.ietf.org/doc/html/rfc7323#section-2). A node,
receiving a stream of data faster than it can handle it, applies backpressure
by reducing the window size in its TCP acknowledgements. Crucially, the node
may reduce this window size all the way down to zero, indicating that it can
handle no more data. This backpressure mechanism is built into the operating
system's TCP implementation and the only thing that an application needs to do
to access it is to stop reading data from the socket in question while it is
overloaded. Once the overload has passed, the application reads from the socket
again which causes the kernel to transmit a packet advertising that the window
is open again, inviting the sender to continue sending data.

## Infinite patience

One of the misunderstandings about this mechanism is the belief that there must
be some kind of timeout after which a connection in the zero-window
backpressure state indicates some kind of error condition and should be closed.
[RFC 1122](https://datatracker.ietf.org/doc/html/rfc1122#page-92) says that
this is not the case:

            A TCP MAY keep its offered receive window closed
            indefinitely.  As long as the receiving TCP continues to
            send acknowledgments in response to the probe segments, the
            sending TCP MUST allow the connection to stay open.

There is no need for any timeout here because the zero-window state is actively
maintained by the two endpoints: the prospective sender repeatedly sends
so-called zero-window probes to which the receiver responds, indicating that
both ends remain alive but that the backpressure situation persists. This is
essential because when the backpressure is released the receiver sends a single
window-open advertisement but this packet may be lost. As long as the sender
eventually sends another probe it will eventually discover that the
backpressure has been released.

These repeated zero-window probes also ensure that the sender eventually
detects a network partition by watching for a sufficiently long sequence of
consecutive probes to which it has not received a response, as if it were
sending TCP keepalives.

## Probe timings

[RFC 1122](https://datatracker.ietf.org/doc/html/rfc1122#page-92) has some
recommendations about the exact timings of the zero-window probes:

            The transmitting host SHOULD send the first zero-window
            probe when a zero window has existed for the retransmission
            timeout period (see Section 4.2.2.15), and SHOULD increase
            exponentially the interval between successive probes.

            [...]                   Exponential backoff is
            recommended, possibly with some maximum interval not
            specified here.

In practice a maximum is essential, or else the sender may wait for
unreasonably long before discovering that the window has reopened. For example,
if it backed off by a factor of 2 on every probe with no maximum and the
window-opening packet went undelivered then the sender would effectively wait
for twice the length of the backpressure period before discovering that the
window has reopened.

But how exactly are these timings calculated?

In Linux by default the zero-window probes are scheduled similarly to regular
[retransmissions]({% post_url 2025-12-02-tcp-retries2 %}), starting at
`RTO_MIN` (200ms) and backing off repeatedly by a factor of 2 up to a maximum
of `RTO_MAX` (2 minutes), which it reaches after the backpressure has lasted
for a little under 3½ minutes:

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

Thus the default behaviour is that the resolution of a backpressure situation
which lasted for just a few minutes might not be noticed for a further two
minutes (`RTO_MAX`) in the unfortunate, but not uncommon, event that the single
window-opening packet goes undelivered. Occasionally the first probes after the
window opens may also go unacknowledged, each time adding another two minutes
to any backpressure-related delays. That seems awfully long to me.

This also raises the question of how the system deals with unacknowledged
probes, such as would happen if the network were partitioned or the receiving
process were no longer running.

The answer is that the `tcp_retries2` sysctl works similarly on zero-window
probes to how it works with regular retransmissions: if more than
`tcp_retries2` consecutive zero-window probes go unacknowledged then the
connection fails. With the default value of `15`, this means that a connection
across a network partition might not be considered faulty for a whopping 30
minutes (`15 × RTO_MAX`) after the start of the partition. Yikes!

## Less is more

The best way to reduce the time it takes to detect a network partition in a
backpressure situation is to reduce `tcp_retries2` to a [more reasonable
value]({% post_url 2025-12-02-tcp-retries2 %}), just as in the non-backpressure
case. By setting `tcp_retries2` to `5` the system will close the connection and
report the failure to the application after just 5 unacknowledged probes in a
row.

If the interval between the zero-window probes were allowed to grow up to
`RTO_MAX` then waiting for 5 of them to go unacknowledged would still take a
pretty dreadful 10 minutes. However, the `tcp_retries2` sysctl also limits the
time between the probes. I couldn't find this mentioned in any documentation
but [this is where it's implemented in
`tcp_send_probe0()`](https://github.com/torvalds/linux/blob/9094662f6707d1d4b53d18baba459604e8bb0783/net/ipv4/tcp_output.c#L4583-L4584):

        if (icsk->icsk_backoff < READ_ONCE(net->ipv4.sysctl_tcp_retries2))
            icsk->icsk_backoff++;

Here `icsk->icsk_backoff` is the backoff counter, visible using tools such as
`ss -tonie`, and from which the re-probe interval is computed. The effect of
this code is to stop increasing the backoff counter, and thus the re-probe
interval, once it reaches `tcp_retries2`. By default this allows the re-probe
interval to increase all the way to `RTO_MAX`, but if `tcp_retries2` is `5`
then the interval between zero-window probes will not increase beyond `32 ×
RTO_MIN` which is a little over 6 seconds:

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

This means that a prospective sender will be able to pick up the open window
within a few seconds even if the window-opening packet goes undelivered, losing
only a few more seconds on each undelivered probe, and a network partition will
be detected in `5 × 32 × RTO_MIN` which is a little over 30 seconds, surely
vastly preferable to the 30-minute default.

## User timeouts

Cloudflare has a [blog post about detecting dead TCP
connections](https://blog.cloudflare.com/when-tcp-sockets-refuse-to-die/) which
concludes that typical applications sending data to the internet should set
Linux's `TCP_USER_TIMEOUT` socket option to be equal to the overall TCP
keepalive timeout (i.e. `TCP_KEEPIDLE + TCP_KEEPINTVL * TCP_KEEPCNT`) so that
sockets with nonempty send buffers can still detect network partitions in as
timely a fashion as ones with empty send buffers.

Linux's `TCP_USER_TIMEOUT` socket option has the following meaning according to
[`man tcp`](https://man7.org/linux/man-pages/man7/tcp.7.html):

       TCP_USER_TIMEOUT (since Linux 2.6.37)
              This option takes an unsigned int as an argument.  When the
              value is greater than 0, it specifies the maximum amount of
              time in milliseconds that transmitted data may remain
              unacknowledged, or buffered data may remain untransmitted
              (due to zero window size) before TCP will forcibly close
              the corresponding connection and return ETIMEDOUT to the
              application.  If the option value is specified as 0, TCP
              will use the system default.

              [...]

              Further details on the user timeout feature can be found in
              RFC 793 and RFC 5482 ("TCP User Timeout Option").

However, [RFC 5482](https://datatracker.ietf.org/doc/html/rfc5482) describes
a subtly different timeout:

        The Transmission Control Protocol (TCP) specification [RFC0793]
        defines a local, per-connection "user timeout" parameter that
        specifies the maximum amount of time that transmitted data may remain
        unacknowledged before TCP will forcefully close the corresponding
        connection.

This RFC specifies a TCP option allowing endpoints to communicate such a
timeout to each other, but as far as I can tell Linux doesn't make use of this
facility even if `TCP_USER_TIMEOUT` is set.

Confusingly [RFC 793](https://datatracker.ietf.org/doc/html/rfc0793) describes
such a "user timeout" with different semantics again:

        The timeout, if present, permits the caller to set up a timeout
        for all data submitted to TCP.  If data is not successfully
        delivered to the destination within the timeout period, the TCP
        will abort the connection.  The present global default is five
        minutes.

This is the timeout specified in Linux by the `SO_SNDTIMEO` socket option, not
`TCP_USER_TIMEOUT`.

The difference between the timeout described in RFC 5482 and the implementation
of the `TCP_USER_TIMEOUT` option in Linux is subtle but vitally important when
considering TCP backpressure. The RFC 5482 timeout only considers
_unacknowledged_ data, but a TCP connection in a zero-window state has no
unacknowledged data and thus this timeout will not take effect. In contrast,
the `TCP_USER_TIMEOUT` socket option also considers _untransmitted_ data and
thus imposes a time limit on any backpressure situation after which the
connection is closed, violating [RFC
1122](https://datatracker.ietf.org/doc/html/rfc1122#page-92):

            A TCP MAY keep its offered receive window closed
            indefinitely.  As long as the receiving TCP continues to
            send acknowledgments in response to the probe segments, the
            sending TCP MUST allow the connection to stay open.

Unfortunately this makes this option useless, if not positively harmful, in a
system that makes proper use of TCP backpressure. I can imagine ways that it
might be appropriate to use in Cloudflare's particular situation, but it does
not apply more generally.

Although the `tcp_retries2` option does get a brief mention in Cloudflare's
post, the author fails to explore the consequences of reducing this from its
unreasonably large default of `15` down to something more sensible. Had they
done so, I suspect they might have concluded that this is a more effective
solution to the problems they were describing than the
backpressure-incompatible `TCP_USER_TIMEOUT` option.
