---
layout: post
title:  "Bisection in DCVSs"
date:   2016-01-31 19:09:09 +0000
---

[Bisection](https://git-scm.com/docs/git-bisect) is a mightily powerful tool
for debugging issues that were quietly introduced into a codebase and not
noticed for an extended period of time. With a fine-grained linear history I
have found it often to be possible to quickly bisect to the single-line change
that causes an issue, even amongst tens of thousands of commits spanning many
years from a shifting team of developers, armed only with a reproducible test
case.

## Fine-grained commits

Bisection is particularly powerful when it identifies a small commit as the
culprit. To increase the chances of this happening, keep all commits as small
as possible. Wide-reaching but low-risk changes like renaming classes or
auto-reformatting code should be kept separate from semantically important
changes. It's not a good feeling when you isolate the offending commit and it
comprises thousands of whitespace changes plus one or two non-whitespace bits
that are hidden in the noise.

It's also useful for bisection if most commits contain code that compiles and
passes (a reasonable proportion of) all of the tests. This obviously isn't
always possible.

## Rebase, don't merge

Merging is where two independent sequences of commits (green and blue) are
combined at a _merge commit_ (red):

![merged]({{ "/assets/2016-01-31/merged.png" | relative_url }})

Rebasing is where one of the sequences (blue) is moved on top of the other one
(green):

![rebased]({{ "/assets/2016-01-31/rebased.png" | relative_url }})

Both of these process can require manual intervention if the underlying changes
are in conflict with each other. There are two related advantages of rebasing
that come about particularly if there's an issue that isn't immediately
noticed:

* When merging, the issue may be present in neither the green nor the blue
  commits, but may be present at the merge commit. When using bisection to
isolate where a issue was introduced, it often ends up pointing at a merge
commit. The problem with this is that merge commits may be quite a bit larger
than non-merge commits, which makes bisection that bit less useful as a
debugging tool. When rebasing, the resulting commits are all non-merge commits
so can be made much more supportive of bisection.

* When rebasing, there is a clear division of responsibility between the two
  developers. The green developer pushed first, so the onus is on the blue
developer to rebase their changes correctly. When merging, the green and blue
commits may all be correct and yet the merged code is not. Again, bisection does
not work well as a tool to find a problem in the merge commit.

Additionally, bisection only really works if there is always a well-defined
commit half-way between the known-good and known-bad states. In the merging
diagram above there is no particularly sensible half-way point between the red
and black commits.

## Merge, don't fast-forward

The trouble with naively rebasing is that you end up with a sequence of
commits, some of which contain work-in-progress and others contain finished
features:

![fast-forwarded]({{ "/assets/2016-01-31/fast-forward.png" | relative_url }})

When looking back through history, it's useful to be able to distinguish the
finished ones from the WIP. The best way to do this is to perform a trivial
merge at the end of each feature, rather than simply to fast-forward to the tip
of the feature branch:

![not fast-forwarded]({{ "/assets/2016-01-31/not-fast-forward.png" | relative_url }})

Since each merge is trivial, the problems with merging discussed above do not
apply.

If a bisection hits an untestably bad WIP commit it's normally a good idea to
jump to a nearby merge and continue from there.

## Squashing considered harmful

Squashing a whole feature branch into a single commit (often done at rebase)
destroys the usefulness of bisection because the resulting commit is not
fine-grained, so not particularly helpful for later debugging. The argument in
favour of squashing seems to be that it yields a "tidier" history, which I
charitably interpret to mean "contains no WIP commits". Trivial merges are a
much better idea for distinguishing the WIP from finished features without
losing the valuable detail of the WIP commits either.
