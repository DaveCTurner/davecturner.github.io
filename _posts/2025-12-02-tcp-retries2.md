---
layout: post
title:  "TCP retransmissions"
date:   2025-09-03
---

Distributed systems must always be able to _correctly_ deal with the non-delivery (or [non-acknowledgement](https://en.wikipedia.org/wiki/Two_Generals%27_Problem)) of a message, but in any reasonable network environment one can assume that message non-delivery is fairly rare. This means we need not behave _optimally_ in the case of a message non-delivery. In principle the system should still work correctly even if retransmissions were totally disabled, but in practice TCP uses packet loss to signal network congestion and apply backpressure so some small number of retransmissions are to be expected and need to be handled gracefully.

The question is therefore how tenaciously to retry a delivery before eventually giving up and performing some corrective action. Of course this depends on the exact use-case but typically a few seconds of retries is going to be more than enough. Assuming for instance that network-congestion-signalling packet loss affects even a whopping 1% of packets, and that those packets are chosen at random, the probability of losing a few retransmissions in a row from the same connection quickly becomes _vanishingly_ small.

The latest standard on the subject of retransmissions is [RFC 1122](https://datatracker.ietf.org/doc/html/rfc1122#page-101), which uses `R2` to denote the overall timeout on message deliveries and specifies the following:

    The value of R2 SHOULD correspond to at least 100 seconds.

I could believe that might have made sense in October 1989 when this RFC was published, but it is frankly nonsensical in most modern distributed systems.

In Linux, the retransmission behaviour is controlled by [the `tcp_retries2` sysctl](https://github.com/torvalds/linux/blob/4a26e7032d7d57c998598c08a034872d6f0d3945/Documentation/networking/ip-sysctl.rst#L799-L814):

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

The mentioned "exponential backoff" uses a factor of two, and is also bounded above by `TCP_RTO_MAX`[^1], where the constants are [defined as the following numbers of jiffies](https://github.com/torvalds/linux/blob/4a26e7032d7d57c998598c08a034872d6f0d3945/include/net/tcp.h#L161-L163):

        #define TCP_RTO_MAX_SEC 120
        #define TCP_RTO_MAX ((unsigned)(TCP_RTO_MAX_SEC * HZ))
        #define TCP_RTO_MIN ((unsigned)(HZ / 5))

[^1]: In Linux ≥6.15 the `TCP_RTO_MAX` value can be adjusted at runtime via the `tcp_rto_max_ms` sysctl, affecting all connections on the system, and can also be configured differently on each socket via the `TCP_RTO_MAX_MS` socket option.


`HZ` is a compile-time-configurable constant representing the number of jiffies per second, so these values work out to 200ms and 120s respectively. This is where the documented "hypothetical timeout of 924.6 seconds" comes from:

| Attempt | Start/mm:ss | Timeout       | Timeout/s | End/mm:ss.s
|--------:|----------:|----------------:|----------:|-----------------:
| 0       | 0:00.0    |       `RTO_MIN` | 0.2       | 0:00.2
| 1       | 0:00.2    |   `2 × RTO_MIN` | 0.4       | 0:00.6
| 2       | 0:00.6    |   `4 × RTO_MIN` | 0.8       | 0:01.4
| 3       | 0:01.4    |   `8 × RTO_MIN` | 1.6       | 0:03.0
| 4       | 0:03.0    |  `16 × RTO_MIN` | 3.2       | 0:06.2
| 5       | 0:06.2    |  `32 × RTO_MIN` | 6.4       | 0:12.6
| 6       | 0:12.6    |  `64 × RTO_MIN` | 12.8      | 0:25.4
| 7       | 0:25.4    | `128 × RTO_MIN` | 25.6      | 0:51.0
| 8       | 0:51.0    | `258 × RTO_MIN` | 51.2      | 1:42.2
| 9       | 1:42.2    | `512 × RTO_MIN` | 102.4     | 3:24.6
| 10      | 3:24.6    | `RTO_MAX`       | 120.0     | 5:24.6
| 11      | 5:24.6    | `RTO_MAX`       | 120.0     | 7:24.6
| 12      | 7:24.6    | `RTO_MAX`       | 120.0     | 9:24.6
| 13      | 9:24.6    | `RTO_MAX`       | 120.0     | 11:24.6
| 14      | 11:24.6   | `RTO_MAX`       | 120.0     | 13:24.6
| 15      | 13:24.6   | `RTO_MAX`       | 120.0     | 15:24.6

I don't think I've ever encountered a situation where waiting for ≥15 minutes in case a message is finally delivered and acknowledged is the right thing to do.

If you instead set `tcp_retries2=5` then the system will report failure to deliver a message after a little under 13s, allowing for much more prompt corrective action. This will only happen if the connection in question failed to deliver 6 packets in a row which is incredibly unlikely to happen naturally. Assuming random and independent packet loss due to congestion etc. of 1%, the loss of 6 packets in a row would have probability 0.0000000001%. Put differently, if you find you are getting connection timeouts with `tcp_retries2=5` then the packet loss is almost certainly non-random, and therefore something you can investigate and fix.

See also [this blog post by Marco Pracucci](https://pracucci.com/linux-tcp-rto-min-max-and-tcp-retries2.html) on the same subject.