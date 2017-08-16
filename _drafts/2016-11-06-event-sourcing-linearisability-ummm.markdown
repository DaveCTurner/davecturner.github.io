---
layout: post
title:  "Event sourcing and linearisability"
date:   2016-11-06 19:09:09 +0000
---

> Linearisability is a bit odd as it relies on real-time order, but you can't
> observe real-time order in a distributed system.
>
> Centralising event sequence is, however, conservative: the req is logged
> _before_ the op starts, and the resp is logged _after_ the op finishes.
> Separation is relativistically "timelike"?
>
> Come up with an example that is not linearisable but not observably so.

Addendum 2017-08-16: no idea what I was on about in this note.

Also:

> Linearisability is too strong for event sourcing.
>
> Captured in the definition of the real-time order which must be respected in
> full linearisability.
>
> Need some constraints on the ordering of things - linearisable writes? But
> stale reads are ok as the client can tell they're stale.


