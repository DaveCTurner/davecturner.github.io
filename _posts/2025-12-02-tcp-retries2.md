---
layout: post
title:  "TCP retransmissions"
date:   2025-12-02
---

Distributed systems must always be able to _correctly_ deal with the non-delivery (or [non-acknowledgement](https://en.wikipedia.org/wiki/Two_Generals%27_Problem)) of a message, but in any reasonable network environment one can assume that message non-delivery is fairly rare. This means we need not behave _optimally_ in the case of a message non-delivery. In principle the system should still work correctly even if retransmissions were totally disabled, but in practice TCP uses packet loss to signal network congestion and apply backpressure so some small number of retransmissions are to be expected and need to be handled gracefully.

The question is therefore how tenaciously to retry a delivery before eventually giving up and performing some corrective action. Of course this depends on the exact use-case but typically a few seconds of retries is going to be more than enough. Assuming for instance that network-congestion-signalling packet loss affects even a whopping 1% of packets, and that those packets are chosen at random, the probability of losing a few retransmissions in a row from the same connection quickly becomes _vanishingly_ small.

The latest standard on the subject of retransmissions is [RFC 1122](https://datatracker.ietf.org/doc/html/rfc1122#page-101), which uses `R2` to denote the overall timeout on message deliveries and specifies the following:

    The value of R2 SHOULD correspond to at least 100 seconds.

Note however that the scope of this RFC is rather narrow:

    The requirements spelled out in this document are designed
    for a full-function Internet host, capable of full
    interoperation over an arbitrary Internet path.

Most nodes in a modern distributed system are not a `full-function Internet host` in this sense. Aside from nodes at the edge, very little traffic in such a system is sent over an `arbitrary Internet path`, and none goes over paths that behave like the internet did in October 1989 when this RFC was written. Instead, the nodes in the interior of the system will be communicating over a much more reliable and performant network and different configuration choices are appropriate for this kind of network environment.

See also this less-opinionated [blog post by Marco Pracucci](https://pracucci.com/linux-tcp-rto-min-max-and-tcp-retries2.html) on the same subject.

## Linux

In Linux, the retransmission behaviour is controlled by [the `net.ipv4.tcp_retries2` sysctl](https://github.com/torvalds/linux/blob/4a26e7032d7d57c998598c08a034872d6f0d3945/Documentation/networking/ip-sysctl.rst#L799-L814):

    tcp_retries2 - INTEGER
        This value influences the timeout of an alive TCP connection,
        when RTO retransmissions remain unacknowledged.
        Given a value of N, a hypothetical TCP connection following
        exponential backoff with an initial RTO of TCP_RTO_MIN would
        retransmit N times before killing the connection at the (N+1)th RTO.

        The default value of 15 yields a hypothetical timeout of 924.6
        seconds and is a lower bound for the effective timeout.
        TCP will effectively time out at the first RTO which exceeds the
        hypothetical timeout.

The mentioned "exponential backoff" uses a factor of two, and is also bounded above by `TCP_RTO_MAX`, where the constants are [defined as the following numbers of jiffies](https://github.com/torvalds/linux/blob/4a26e7032d7d57c998598c08a034872d6f0d3945/include/net/tcp.h#L161-L163):

        #define TCP_RTO_MAX_SEC 120
        #define TCP_RTO_MAX ((unsigned)(TCP_RTO_MAX_SEC * HZ))
        #define TCP_RTO_MIN ((unsigned)(HZ / 5))

`HZ` is a compile-time-configurable constant representing the number of jiffies per second, so these values work out to 200ms and 120s respectively. This is where the documented "hypothetical timeout of 924.6 seconds" comes from:

| Attempt | Start/mm:ss | Timeout         | Timeout/s | End/mm:ss.s
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
| 15      | 13:24.6     | `RTO_MAX`       | 120.0     | 15:24.6

I don't think I've ever encountered a situation where waiting for ≥15 minutes in case a message is finally delivered and acknowledged is the right thing to do, and even waiting the RFC-1122-specified ≥100 seconds for 8 retransmissions is almost always excessive.

If you instead set `tcp_retries2=5` then the system will report failure to deliver a message after a little under 13s, allowing for much more prompt corrective action. This will only happen if the connection in question failed to deliver 6 packets in a row which is incredibly unlikely to happen naturally. Assuming random and independent packet loss due to congestion etc. of 1%, the loss of 6 packets in a row would have probability 0.0000000001%. Put differently, if you find you are getting connection timeouts with `tcp_retries2=5` then the packet loss is almost certainly non-random, and therefore something deserving of investigation and a remedy.

### Linux ≥6.15

Starting in Linux 6.15 the `TCP_RTO_MAX` value can be adjusted at runtime via the `net.ipv4.tcp_rto_max_ms` sysctl, affecting all connections on the system, and applications can also override the system-wide maximum on each socket via the `TCP_RTO_MAX_MS` socket option. For instance, setting the shortest permitted `TCP_RTO_MAX_MS=1000` yields the following retransmission schedule:

| Attempt | Start/mm:ss | Timeout         | Timeout/s | End/mm:ss.s
|--------:|------------:|----------------:|----------:|-----------------:
| 0       | 0:00.0      |       `RTO_MIN` | 0.2       | 0:00.2
| 1       | 0:00.2      |   `2 × RTO_MIN` | 0.4       | 0:00.6
| 2       | 0:00.6      |   `4 × RTO_MIN` | 0.8       | 0:01.4
| 3       | 0:01.4      | `RTO_MAX`       | 1.0       | 0:02.4
| 4       | 0:02.4      | `RTO_MAX`       | 1.0       | 0:03.4
| 5       | 0:03.4      | `RTO_MAX`       | 1.0       | 0:04.4
| 6       | 0:04.4      | `RTO_MAX`       | 1.0       | 0:05.4
| 7       | 0:05.4      | `RTO_MAX`       | 1.0       | 0:06.4
| 8       | 0:06.4      | `RTO_MAX`       | 1.0       | 0:07.4
| 9       | 0:07.4      | `RTO_MAX`       | 1.0       | 0:08.4
| 10      | 0:08.4      | `RTO_MAX`       | 1.0       | 0:09.4
| 11      | 0:09.4      | `RTO_MAX`       | 1.0       | 0:10.4
| 12      | 0:10.4      | `RTO_MAX`       | 1.0       | 0:11.4
| 13      | 0:11.4      | `RTO_MAX`       | 1.0       | 0:12.4
| 14      | 0:12.4      | `RTO_MAX`       | 1.0       | 0:13.4
| 15      | 0:13.4      | `RTO_MAX`       | 1.0       | 0:14.4

A timeout in under 15 seconds is vastly preferable to waiting over 15 minutes. It remains to be seen whether such frequent retransmissions can have negative consequences, perhaps even causing additional network congestion and further packet loss, but I expect this will behave better in very many situations.
