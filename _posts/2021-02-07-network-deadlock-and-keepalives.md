---
layout: post
title:  "Network-induced deadlocks and TCP keepalives"
date:   2021-02-07
---

TCP keepalives are a powerful feature of the networking stack, offloading vital
liveness checks out of your application and into the operating system. However
they are often misunderstood or misconfigured and this confusion sometimes
leads developers and operators towards alternative liveness mechanisms, such as
timeout-and-retry, with undesirable side-effects. This article explains TCP
keepalives, their relationship to liveness, and why you should embrace them in
your distributed system.

## Introduction

Many distributed systems have a communication model based on request/response
pairs of messages.
[HTTP](https://en.wikipedia.org/wiki/Hypertext_Transfer_Protocol) is a very
common example of this, but other examples include client/server database
protocols like the ones used by
[Postgres](https://www.postgresql.org/docs/13/protocol.html),
[Redis](https://redis.io/topics/protocol),
[Mongodb](https://docs.mongodb.com/manual/reference/mongodb-wire-protocol/) and
many more, as well as all the various [remote procedure
call](https://en.wikipedia.org/wiki/Remote_procedure_call) implementations. The
endpoint that sends the request is called the _client_, which is received by
the other endpoint called the _server_, which processes the request and then
sends the response back to the client.

Most request/response systems rely at a high level on the simplifying
assumption that every request eventually receives a response. The response is
allowed to be an error, maybe even a timeout or a network error, but it's still
a response that means the requester can stop waiting and get on with its work.
This is a powerful and useful assumption because it rules out a lot of
potential liveness problems. Without this assumption, every time a developer
makes a remote request they would need to consider how to deal with the case
that they never receive a response. Experience has shown that this is easy to
forget and difficult — sometimes impossible — to get right.

It's certainly useful to assume that every request receives a response, but how
can we make this assumption valid? The answer falls into two main pieces:

1. make sure that the system satisfies some kind of useful liveness properties
   (e.g. it contains no deadlocks) assuming the network works perfectly, and
   then

1. make sure that network failures do not introduce any liveness bugs.

This article is about the second piece of the answer. The first piece is a huge
topic and is definitely out of scope here, so we assume it is solved elsewhere.

## A recap of TCP

The protocols of interest use
[TCP](https://en.wikipedia.org/wiki/Transmission_Control_Protocol) for the
underlying network transport. [Other options are available](https://notcp.io)
but the same basic concerns apply to any transport so we will focus on TCP.

A TCP connection is a linked pair of streams of data between two endpoints, one
in each direction. The data sent in each direction is divided up into packets
by the transmitter, and the receiver responds with acknowledgements as the data
arrives. The streams are linked by in the sense that they typically close, or
experience errors, together: an error on one of the streams typically causes
the closure of both of them.

TCP also has a bunch of control mechanisms for opening and closing connections
which are also implemented by sending packets of data between the two ends.
Opening a connection involves three packets going back-and-forth, and closing a
connection involves three or four.

Responses are usually sent using the same TCP connection as the corresponding
request. This is important for liveness since it makes use of the fact that the
streams in the two directions are linked. If responses were sent using a
different connection then the application would be responsible for establishing
the link between the request and response streams itself, which is of course
technically possible but introduces a good deal of extra complexity.

A TCP connection can legitimately remain dormant, without sending any packets
in either direction, for an arbitrarily long time. This has a few consequences:

1. there is no fundamental requirement for requests to complete and receive
   responses quickly. Even an HTTP request may take days to complete: it's up
   to you whether that represents a failure condition in your system or not.

1. the same TCP connection can be used for a whole sequence of requests and
   responses, even if they are separated by long pauses. Establishing a new TCP
   connection, and all the associated session state, may be expensive, so
   connection re-use is a powerful optimisation.

1. if a TCP endpoint is in a state where it is waiting to receive a response
   then it might wait forever.

Of course you might not get the response you want: for instance the connection
might be closed in the meantime, and handling such errors correctly may be
tricky. You need to correctly handle connection errors no matter how quickly
your requests return, the only question is how often such errors occur. In
practice, on a properly-configured and well-managed network you can expect TCP
connections to remain established until actively terminated many months later.
A connection being closed mid-request on a production network represents a rare
failure condition, a bug that should be investigated.

A popular technique for handling connection errors is to "go async": a request
triggers a long-running task but receives a response as soon as the task has
started. This initial response identifies the task so that subsequent requests
can monitor its status and ultimately retrieve any results once it completes.
Since the subsequent requests may use different TCP connections this technique
is very robust against connection failures while the task is running. It's also
quite complicated to implement correctly, taking into account the additional
server-side state management, the storage of results for later retrieval, and
other concerns such as cancellation. 

A complementary technique is [long
polling](https://en.wikipedia.org/wiki/Push_technology#Long_polling) which
converts a pull-based request/response protocol into one that effectively
pushes timely notifications to clients as soon as they are available. The
client polls for (i.e. repeatedly requests) notifications, but the server waits
until a notification is available before sending a response. This works well
for retrieving the results of tasks that have "gone async", since on a
connection failure the client can simply retry its notification request.
Ideally, the client has no timeout, it simply waits forever until it receives a
response.

# Proxies and other intermediaries

A modern network is rarely just two endpoints connected directly to each other.
There are usually all sorts of intermediary devices that manipulate and direct
the network traffic.
