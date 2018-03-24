---
layout: post
title:  "Nominal Domain Theory for Concurrency"
date:   2008-12-15 19:09:09 +0000
---

My [PhD thesis](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-751.pdf).

## Abstract

Domain theory provides a powerful mathematical framework for describing
sequential computation, but the traditional tools of domain theory are
inapplicable to concurrent computation. Without a general mathematical
framework it is hard to compare developments and approaches from different
areas of study, leading to time and effort wasted in rediscovering old ideas in
new situations.

A possible remedy to this situation is to build a denotational semantics based
directly on computation paths, where a process denotes the set of paths that it
may follow. This has been shown to be a remarkably powerful idea, but it lacks
certain computational features. Notably, it is not possible to express the idea
of names and name-generation within this simple path semantics.

Nominal set theory is a non-standard mathematical foundation that captures the
notion of names in a general way. Building a mathematical development on top of
nominal set theory has the effect of incorporating names into its fabric at a
low level. Importantly, nominal set theory is sufficiently close to
conventional foundations that it is often straightforward to transfer
intuitions into the nominal setting.

Here the original path-based domain theory for concurrency is developed within
nominal set theory, which has the effect of systematically adjoining
namegeneration to the model. This gives rise to an expressive metalanguage,
Nominal HOPLA, which supports a notion of name-generation. Its denotational
semantics is given entirely in terms of universal constructions on domains. An
operational semantics is also presented, and relationships between the
denotational and operational descriptions are explored.

The generality of this approach to including name generation into a simple
semantic model indicates that it will be possible to apply the same techniques
to more powerful domain theories for concurrency, such as those based on
presheaves.
