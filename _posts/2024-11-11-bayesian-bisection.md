---
layout: post
title:  "Bayesian bisection"
date:   2024-11-11
---

[Bisection]({% post_url 2016-01-31-bisection-in-dcvss %}) is a mightily
effective technique for debugging those tricky issues that were quietly
introduced into a codebase and not noticed for an extended period of time. You
can find the first bad commit from a range of thousands (or more) in a
logarithmic number of steps via a binary search, halving the range of possible
bad commits on each step.

At least, you can do this as long as you have a way to say for each commit
whether it is definitely good or definitely bad. But sometimes you might have a
test case that started failing extremely rarely. If you can reproduce the
failure on a commit then it's definitely bad, but if the failure doesn't
reproduce then it could be that the commit is good or it could be that you just
didn't get lucky this time. So you run it again. And again. But how many good
runs in a row do you need before you can consider the commit to be good?

To give some figures from a recent example, I was recently chasing down a test
that started to fail roughly approximately once in ~2700 runs. Each run of the
test took around 6 seconds so you could expect a bad commit to fail in around
4-and-a-half hours. The offending commit was somewhere in a range of about a
thousand commits, so in principle should be findable with a binary search of 10
steps. The trouble was that each run of the test took around 6 seconds so you
could expect a bad commit to take around 4-and-a-half hours to fail.

One possible strategy would be to consider a commit that gets 2700 successful
runs in a row to be good, and carry on with the normal binary search process.
But consider what happens with this strategy if we were just unlucky and a bad
commit took a little longer than expected to fail. In this case, we discard the
half of the commit range that actually contains the first bad commit, and the
binary search process will terminate pointing to an earlier, and actually good,
commit.

We can improve on this by looking for longer sequences of successful runs
before considering a commit to be good. For instance, we could wait until we've
seen twice as many successes in a row. But this means that on a good commit
we'll have to wait nine hours before moving to the next step. With ten steps to
run that'd be 90 hours of work. And then we'd still have the concern that at
least one of those steps was unlucky and didn't capture the failure, leading to
low confidence that the binary search really found the first bad commit. We
could increase that confidence by running the tests for much longer on the
(claimed) last good commit, but if any of the preceding runs was unlucky then
we'd find the (claimed) last good commit actually to be bad, and from there we
have limited options apart from restarting the binary search on the smaller
range, because all those commits we thought to be good are now under suspicion
again.

It'd be awfully nice if we could use the output of the preceding 90 hours of
test runs somehow. This is a rough sketch of something I hacked together to do
just that, speeding up the process of finding the first flaky commit.

### Bayesian inference

Rather than treating the outcome of a test run as a binary pass-or-fail thing,
we can model the system in terms of probabilities. Specifically, consider a
sequence of commits C<sub>i</sub> for i ∈ {1..N}, the first of which is good
and the last of which is bad, and a discrete distribution of probabilities that
each respective commit is the first bad one: P<sub>i</sub> = P(C<sub>i</sub> is
the first bad commit).

Given the result of a test run at commit C<sub>j</sub> we can update this prior
distribution using [Bayes' theorem](https://en.wikipedia.org/wiki/Bayes%27_theorem):

P'<sub>i</sub> = P(C<sub>i</sub> is the first bad commit \| test result at C<sub>j</sub>)<br>
&nbsp;&nbsp;= P(test result at C<sub>j</sub> \| C<sub>i</sub> is the first bad commit) <br>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;× P(C<sub>i</sub> is the first bad commit) ÷ P(test result at commit C<sub>j</sub>)<br>
&nbsp;&nbsp;∝ P(test result at C<sub>j</sub> \| C<sub>i</sub> is the first bad commit) × P<sub>i</sub>

... noting that the denominator P(tests passed at commit C<sub>j</sub>) is
independent of i and is really more like a normalization factor that scales all
the numbers so that to sum to 1 again. Thus we can compute the posterior
distribution by multiplying each probability in the prior distribution by a
factor which depends on the probability _p_ of a test failing on a bad commit:

* P(test passes at C<sub>j</sub> \| C<sub>i</sub> is the first bad commit) = (1-_p_) if i ≤ j else 1
* P(test fails at C<sub>j</sub> \| C<sub>i</sub> is the first bad commit) = _p_ if i ≤ j else 0

Doing this repeatedly for a sequence of test results yields a posterior
probability distribution which reflects all the knowledge gathered from those
test runs. The initial prior distribution is not particularly important, but a
uniform distribution makes sense to me.

### Testing the median

Given such a probability distribution, it makes the most sense to do the next
test run on the _median_ commit: the last commit C<sub>k</sub> such that
∑<sub>i≤k</sub> P<sub>i</sub> ≤ ½. Information-theoretically, the outcome of
that test has the highest expected entropy.

Repeatedly recomputing and testing the median has an intuitively useful
behaviour: as tests pass the median will slowly creep upwards towards the first
known-bad commit, and then whenever a test fails it will jump downwards again.
In effect, it re-tests some commits that we were previously considering to be
probably good, gathering more information about their quality. If we've seen a
failure on the actual first-bad commit then the median will creep upwards until
it arrives at the last-good commit, where it will stay. So the results will
include be a sequence of successes as long as you'd like on one commit, and a
failure on the next commit, giving us as much confidence as we'd like that
we've found the first bad commit.

Note also that in the limit if the test is not flaky (so _p_ is 1) and we start
from a uniform prior distribution then testing the median will do a standard
binary search exactly like regular bisection does.

### Estimating _p_

The process described above assumes we know roughly how flaky the test is, i.e.
we have a good estimate for _p_. In fact whatever value we use for _p_ will
still yield the right quantitative behaviour and find the right commit in the
end, it just might move the median around at the wrong speed. But we can
compute a reasonable estimate for _p_ using [maximum likelihood
estimation](https://en.wikipedia.org/wiki/Maximum_likelihood_estimation): write
a function in terms of _p_ which calculates how likely it is to see the test
results we've seen, and then use the value of _p_ which maximises this
function:

f(p) = P(observed results \| p)<br>
&nbsp;&nbsp;= ∑<sub>k</sub> P(observed results ∧ C<sub>k</sub> is the first bad commit \| p)
&nbsp;&nbsp;= ∑<sub>k</sub> p<sup>successes<sub>≥k</sub></sup> (1-p)<sup>failures<sub>≥k</sub></sup>

where successes<sub>≥k</sub> and failures<sub>≥k</sub> are respectively the
number of successes and failures observed at commit C<sub>k</sub> or a later
commit.
