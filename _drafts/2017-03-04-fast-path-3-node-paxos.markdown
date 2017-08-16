---
layout: post
title:  "A fast path in 3-node Paxos"
date:   2017-03-04 19:09:09 +0000
---

TODO:

* Follower: value immediately chosen (enough votes) so write and forget? If the
value is subsequently needed, it's done via catch up.

* Leader: streaming values to one follower, getting acks back. Must track
in-flight values. When acks received, write and forget.


