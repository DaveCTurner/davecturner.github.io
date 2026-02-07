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
test case that started failing extremely rarely, and this is where traditional
binary search struggles. If you can reproduce the failure on a commit then that
commit is definitely bad, but if the failure doesn't reproduce on some other
commit then it could be that that commit is good or it could be that you just
didn't get lucky this time. So you run it again. And again. But how many good
runs in a row do you need before you can consider the commit to be good?

To give some figures from a recent example, I was recently chasing down a test
that started to fail roughly approximately once in ~2700 runs. Each run of the
test took around 6 seconds so you could expect a bad commit to fail in around
4-and-a-half hours. The offending commit was somewhere in a range of about a
thousand commits, so in principle should be findable with a binary search of 10
steps.

One possible strategy would be to consider a commit that gets 2700 successful
runs in a row to be good, and carry on with the normal binary search process.
This would take a couple of days to narrow the search down to a single commit.
But consider what happens with this strategy if we were just unlucky and a bad
commit took a little longer than expected to fail. In this case, we discard the
half of the commit range that actually contains the first bad commit, and the
binary search process will terminate pointing to an earlier, and actually good,
commit.

We can improve on this by looking for longer sequences of successful runs
before considering a commit to be good. For instance, we could wait until we've
seen twice as many successes in a row. But this means that on a good commit
we'll have to wait nine hours before moving to the next step. With ten steps to
run that'd be around four days of work, and then we'd still have the concern
that at least one of those steps was unlucky and didn't capture the failure,
leading to low confidence that the binary search really found the first bad
commit. We could increase that confidence by running the tests for much longer
on the (claimed) last good commit, but if any of the preceding runs was unlucky
then we'd find the (claimed) last good commit actually to be bad, and from
there we have limited options apart from restarting the binary search on the
smaller range, because all those commits we thought to be good are now under
suspicion again.

It'd be awfully nice if we could use the output of the preceding hours of test
runs to influence the restarted search somehow. This is where Bayesian
inference steps in, allowing us to generalize traditional binary search into
one which takes account of the probabilistic nature of the test results and
continuously updates our belief about which commit introduced the flakiness.
This is a rough sketch of something I hacked together to do just that, speeding
up the process of finding the first flaky commit.

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
&nbsp;&nbsp;= P(test result at C<sub>j</sub> \| C<sub>i</sub> is the first bad commit)<br>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;× P(C<sub>i</sub> is the first bad commit)<br>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;÷ P(test result at commit C<sub>j</sub>)<br>
&nbsp;&nbsp;∝ P(test result at C<sub>j</sub> \| C<sub>i</sub> is the first bad commit) × P<sub>i</sub>

... noting that the denominator P(tests passed at commit C<sub>j</sub>) is
independent of i and is really more like a normalization factor that scales all
the numbers so that they sum to 1 again. Thus we can compute the posterior
distribution by multiplying each probability in the prior distribution by a
factor which depends on the probability _p_ of a test failing on a bad commit:

* P(test passes at C<sub>j</sub> \| C<sub>i</sub> is the first bad commit) = (1-_p_) if i ≤ j else 1
* P(test fails at C<sub>j</sub> \| C<sub>i</sub> is the first bad commit) = _p_ if i ≤ j else 0

In words: given a prior distribution of probabilities that each commit in a
sequence is the first bad commit, and another test result on a commit
C<sub>j</sub>, compute the posterior distribution of those probabilities as
follows. If the test passed at C<sub>j</sub>, multiply by (1-_p_) the
probabilities of all C<sub>i</sub> for i ≤ j, to reflect that it has now become
slightly less likely that any of these commits is the first bad one. In
contrast, if the test failed on a commit C<sub>j</sub> then it has now become
impossible for any earlier commit to be the first bad one, so sets to zero the
probabilities of all commits C<sub>i</sub> for j < i. In the latter case there
is in fact no need to multiply the remaining probabilities by _p_, as the above
formula suggests, because they will need to be renormalized anyway.

Doing this repeatedly for a sequence of test results yields a posterior
probability distribution which reflects all the knowledge gathered from those
test runs. The initial prior distribution is not particularly important, but a
uniform distribution makes sense to me.

### Testing the median

Given such a probability distribution, it makes the most sense to do the next
test run on the _median_ commit: the last commit C<sub>k</sub> such that
∑<sub>i≤k</sub> P<sub>i</sub> ≤ ½. Testing the median commit is optimal because
its outcome (pass or fail) most evenly divides the remaining probability space,
meaning it provides the expected maximum possible reduction in uncertainty
about the location of the first bad commit.

Repeatedly testing the median commit according to the posterior probability
distribution has an intuitively useful behaviour: as tests pass the median will
slowly creep upwards towards the first known-bad commit, and then whenever a
test fails it will jump downwards again. In effect, it re-tests some commits
that we were previously considering to be probably good, gathering more
information about their quality. If we've seen a failure on the actual
first-bad commit then the median will creep upwards until it arrives at the
first-bad commit, where it will stay.

However, as the algorithm enters the endgame and the distribution becomes more
and more concentrated at the first-bad commit, eventually the first-bad commit
will become the median commit. It's certainly useful to keep running further
tests on this commit in order to refine our estimates of the flakiness
probability _p_ (see below) but we must also run tests on the previous commit,
believed to be the last-good commit, in case it turns out that this commit is
also bad. My preference is to switch between these two commits so as to
equalise the number of iterations run on each of them, because this ultimately
yields a sequence of test runs on the bad commit, some of which failed, and a
similar length of sequence of test runs on the previous commit, all of which
passed, which forms a compelling argument that we've really found the first bad
commit even without having to resort to any probability calculations.

As a slight further refinement, in the endgame I prefer to run a sequence of
tests on each commit before switching to the other one, to avoid the overheads
associated with switching commits such as having to recompile the system under
test. I have typically chosen to run ten such commits on each one before
switching.

Note that the speed at which the median creeps towards the first known-bad
commit is determined by _p_. The rarer the test failures on bad commits, the
slower the median commit moves, so that the algorithm spends more time testing
potentially-bad commits. In contrast, if test failures are relatively likely
then the median commits moves more quickly. In the limit, if the test is not
flaky at all (so _p_ is 1) and we start from a uniform prior distribution then
testing the median will do a standard binary search exactly like regular
bisection does.

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
number of successes and failures observed so far for commits at or after commit
C<sub>k</sub>.

Note that if you re-estimate _p_ this way every iteration then the median
doesn't quite behave as described above and it's not clear that the process
eventually converges. It's also rather complicated.

Instead, I decided to estimate _p_ from the test results on commits which are
known to be bad, simply dividing the number of failures by the total number of
runs on these commits. At the very start of the process, when no test failures
have been observed, it seems best to run the test repeatedly on the last commit
in the sequence: the number of successful runs before this first failure gives
a useful initial estimate for the actual failure probability.

### High-level Algorithm

Here's a conceptual outline of the Bayesian bisection algorithm:

1.  **Initialize**:
    *   Define a range of suspected commits, where the first is believed to be
        good and the last is known to be bad.
    *   Assign an initial uniform probability distribution P<sub>i</sub> to
        each commit in the range, representing the belief that C<sub>i</sub> is
        the first bad commit.
    *   Repeatedly run the test on the last commit in the range until it fails,
        and use this for the initial estimate of the flakiness probability _p_
        for the test.
2.  **Iterate**:
    *   **Select Next Commit**: Identify the median commit C<sub>j</sub> based
        on the current probability distribution P<sub>i</sub>. If the median
        commit is known to be bad, choose between this commit and the next one so as to
        keep the number of runs on each commit reasonably equal.
    *   **Run Test**: Execute the flaky test on C<sub>j</sub>.
    *   **Re-estimate _p_**: Recompute the estimate of the flakiness
        probability _p_ as the number of failures of commits known to be bad
        divided by the total number of runs on those commits.
    *   **Recompute posterior distribution**: Given the new estimate for _p_,
        the latest test result, and the history of other test results, compute
        the new probability distribution P'<sub>i</sub>.
3.  **Conclude**: Once the probability mass is concentrated as desired on a
    single commit, and we have a sufficiently long run of successes on the
    previous commit, declare that commit as the most likely first bad commit.
