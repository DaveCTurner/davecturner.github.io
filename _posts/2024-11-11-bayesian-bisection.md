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
This would take a couple of days to complete the 10 steps needed to narrow the
search down to a single commit. But consider what happens with this strategy if
we were just unlucky and a bad commit took a little longer than expected to
fail. In this case, we discard the half of the commit range that actually
contains the first bad commit, and the binary search process will terminate
pointing to an earlier, and actually good, commit.

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
continuously updates our belief about which commit introduced the flakiness
based on the history of failures and successes.

### Bayesian inference

Rather than treating the outcome of a test run as a binary pass-or-fail thing,
we can model the system in terms of probabilities. Specifically, consider a
sequence of commits C<sub>i</sub> for i ∈ {1..N} together with some k ∈ {2..N}
such that the initial subsequence C<sub>i&lt;k</sub> are all _good_, reliably
passing some test, and the remainder C<sub>i≥k</sub> are all _bad_,
occasionally failing the test with flakiness probability _p_. Assume also that
the failures of distinct test runs are independent. Our goal is to identify the
first bad commit C<sub>k</sub>, which we will do by computing a discrete
probability distribution P<sub>i</sub> = P(C<sub>i</sub> is the first bad
commit) based on a history of successes and failures on the various commits in
the sequence.

This computation works iteratively: given any prior distribution P<sub>i</sub>
and another test result at commit C<sub>j</sub>, we can compute a posterior
distribution P'<sub>i</sub> which incorporate the evidence from the new test
result into the distribution using [Bayes'
theorem](https://en.wikipedia.org/wiki/Bayes%27_theorem):

P'<sub>i</sub> = P(C<sub>i</sub> is the first bad commit \| test result at C<sub>j</sub>)<br>
&nbsp;&nbsp;= P(test result at C<sub>j</sub> \| C<sub>i</sub> is the first bad commit)<br>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;× P(C<sub>i</sub> is the first bad commit)<br>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;÷ P(test result at commit C<sub>j</sub>)<br>
&nbsp;&nbsp;∝ P(test result at C<sub>j</sub> \| C<sub>i</sub> is the first bad commit) × P<sub>i</sub>

... noting that the denominator P(test result at commit C<sub>j</sub>) is
independent of i and is really more like a normalization factor that scales all
the numbers so that they sum to 1 again. Thus we can compute the posterior
distribution by multiplying each probability in the prior distribution by a
factor which depends on the probability _p_ of a test failing on a bad commit:

* P(test passes at C<sub>j</sub> \| C<sub>i</sub> is the first bad commit) = (1-_p_) if i ≤ j else 1
* P(test fails at C<sub>j</sub> \| C<sub>i</sub> is the first bad commit) = _p_ if i ≤ j else 0

In words: given a prior distribution of probabilities that each commit in a
sequence is the first bad commit, and another test result on a commit
C<sub>j</sub>, compute the posterior distribution of those probabilities as
follows. If the test passed at C<sub>j</sub> then multiply by (1-_p_) the
probabilities of all C<sub>i</sub> for i ≤ j to reflect that it has now become
slightly less likely that any of these commits is the first bad one. In
contrast, if the test failed on a commit C<sub>j</sub> then it has now become
impossible for any earlier commit to be the first bad one, so set to zero the
probabilities of all commits C<sub>i</sub> for j < i. In the latter case there
is in fact no need to multiply the remaining probabilities by _p_, as the above
formula suggests, because we are only working up to proportionality and we must
renormalize everything to sum to 1 to compute the true probabilities anyway.

Doing this repeatedly for a sequence of test results yields a posterior
probability distribution which reflects all the knowledge gathered from those
test runs. The initial prior distribution is not particularly important, but a
uniform distribution is easiest to implement so I suggest to use that.

### Testing the median

Given such a probability distribution, it makes the most sense to do the next
test run on the _median_ commit, because
the outcome of this run (pass or fail) most evenly divides the remaining probability space,
meaning it provides the maximum possible expected reduction in uncertainty
about the location of the first bad commit.

Repeatedly testing the median commit according to the posterior probability
distribution has an intuitively useful behaviour: as tests pass the median will
slowly creep upwards towards the first known-bad commit, and then whenever a
test fails it will jump downwards again. In effect, it re-tests some commits
that we were previously believed to be good, gathering more
information about their quality and possibly discovering a failure on an earlier commit than
the previous best. If we've seen a failure on the actual
first-bad commit then the median will creep upwards until it is between the
first-bad and last-good commits, where it will stay.

Note that the speed at which the median creeps towards the first known-bad
commit is determined by _p_. The rarer the test failures on bad commits, the
slower the median commit moves, so that the algorithm spends more time testing
commits further from the known-bad ones. In contrast, if test failures are
relatively likely then the median commits moves more quickly. In the limit, if
the test is not flaky at all (so _p_ is 1) and we start from a uniform prior
distribution then testing the median will do a standard binary search exactly
like regular bisection does.

Since this is a discrete probability distribution there typically is no
commit which is the exact median. Instead, one must choose between the _submedian_ commit,
i.e. the last commit C<sub>j</sub> such that ∑<sub>i≤j</sub> P<sub>i</sub> ≤ ½, 
and the _supermedian_ commit, i.e. the first commit C<sub>j</sub> such that
∑<sub>i≤j</sub> P<sub>i</sub> ≥ ½. When the algorithm is just starting out
the difference is fairly unimportant, but as things converge it
turns out that neither of these choices alone behaves quite as desired: we
must repeatedly test the believed-last-good commit in case it turns out to be bad,
but always choosing the submedian can end up focussing on the
commit just before the believed-last-good commit, whereas always choosing the
supermedian will end up focussing on the believed-first-bad commit instead.

My preferred solution is to choose whichever of the submedian or supermedian commits has
had fewer test runs so far. In the endgame, this scheme means the algorithm alternates
between the last-good and first-bad commits, which has some useful consequences.
Running further tests on the first-bad commit helps to refine our estimate of the flakiness
probability _p_ (see below), while repeatedly checking the believed-last-good commit
will eventually see a failure if this commit is in fact bad.
Additionally, this scheme produces a sequence of test runs on a bad commit, some of which failed, and a
similar length of sequence of test runs on the previous commit, all of which
passed, which forms an intuitively compelling argument that we've really found
the first bad commit even without having to resort to any probability
calculations.

As a slight further refinement, I instead choose the commit with the smaller value of ⌊runs÷10⌋,
preferring the submedian in case of a tie. Rather than alternating between the two commits each time, this
runs ten tests in a row on each commit before switching to the other one. Doing several runs on each commit
amortises the overheads associated with switching commits, such as having to
recompile the system under test. You may find a
different number works better in other cases according to your commit-switching overheads.

### Estimating _p_

The process described above assumes we know roughly how flaky the test is, i.e.
we have a good estimate for _p_. In fact whatever value we use for _p_ will
still yield the right quantitative behaviour and find the right commit in the
end, it just might move the median around at a suboptimal speed. We can compute
a reasonable estimate for _p_ using [maximum likelihood
estimation](https://en.wikipedia.org/wiki/Maximum_likelihood_estimation): write
a function in terms of _p_ which calculates how likely it is to see the test
results we've seen, and then use the value of _p_ which maximises this
function:

f(p) = P(observed results \| p)<br>
&nbsp;&nbsp;= ∑<sub>k</sub> P(observed results ∧ C<sub>k</sub> is the first bad commit \| p)<br>
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
in the sequence C<sub>N</sub>: the number of successful runs on this commit
before observing a failure gives a useful initial estimate for the actual
failure probability.

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
    *   **Select next commit**: Identify the submedian and supermedian commits
        according to the current probability distribution P<sub>i</sub>. Choose
        whichever has smaller value of ⌊runs÷10⌋, preferring the submedian in case
        of a tie, and call it C<sub>j</sub>.
    *   **Run test**: Execute the flaky test on C<sub>j</sub>.
    *   **Re-estimate _p_**: Recompute the estimate of the flakiness
        probability _p_ as the number of failures of commits known to be bad
        divided by the total number of runs on those commits.
    *   **Recompute posterior distribution**: Given the new estimate for _p_,
        the latest test result, and the history of other test results, compute
        the new probability distribution P'<sub>i</sub>.
3.  **Conclude**: Once the probability mass is concentrated as desired on a
    single commit, and we have a sufficiently long run of successes on the
    previous commit, declare that commit as the most likely first bad commit.
