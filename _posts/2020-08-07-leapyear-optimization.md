---
layout: post
title:  "Identifying leap years"
date:   2020-08-07
---

One of my colleagues was recently looking at some date-based calculations that
needed to know whether a year is a leap year or not, on the hot path, and he
found an [8% speed
improvement](https://github.com/elastic/elasticsearch/pull/60585) by reworking
the leap year predicate a bit. The JVM compiles this down to a few fast integer
operations, avoiding slow things like division entirely. I thought it'd be
interesting to dig into how to calculate the leap year predicate without
division.

Note that your compiler may already do these optimisation steps for you, so I
don't recommend obfuscating your leap-year predicate implementation like this
without some careful contemplation of its worth. This is really just an
exercise in understanding what a sufficiently clever compiler might do here.

I looked at what GCC does with the naive calculation when compiling to AVR
assembler (as used by Arduino microcontrollers) and it came up with something
much slower than this even with `-O2`. So if you need a high-performance leap
year calculation on an Arduino for some reason then maybe this'll be what you
need.

## Version 0

A year is a leap year (in the Gregorian calendar) if it is divisible by 4 and
is not divisible by 100 unless it is also divisible by 400. So 1996 is a leap
year (it's divisible by 4 and not by 100) as is 2000 (it's divisible by 4 and
400) but 1900 is not (it's divisible by 4 and 100 but not 400).

In symbols, where `a dvd b` means that `a` divides exactly into `b`:

    isLeapYear y == 4 dvd y ∧ (¬ 100 dvd y ∨ 400 dvd y)

## Version 1

It's pretty easy for a computer to tell whether an integer is divisible by a
power of two since this only needs bitwise operations. For instance `y` is
divisible by 4 iff its last two bits are zero, i.e. `y & 3 == 0`. Checking for
divisibility by 100 and 400 isn't so easy however.

It's hopefully clear that `y` is a multiple of 100 iff it is a multiple of 4
and of 25, since 4 and 25 are coprime and their product is 100. Similarly `y`
is a multiple of 400 iff it is a multiple of 16 and of 25. This helps because
rather than needing to calculate divisibility by 4, 100 and 400 it reduces the
problem to needing to calculate divisibility by 4, 16 and 25, only one of which
isn't a power of two.

Naively substituting into the definition above gives a rather complicated
formula which pleasingly simplifies to either of these:

    isLeapYear y == 16 dvd y ∨  (4 dvd y ∧ ¬ 25 dvd y)
                 ==  4 dvd y ∧ (16 dvd y ∨ ¬ 25 dvd y)

It's not clear which one of these is better. I think the first one can be
implemented with fewer instructions since `16 dvd y` is implemented with a
bitmask as `y & 15 == 0` and if that test fails then you can compute
divisibility by 4 using the intermediate value, i.e. `(y & 15) & 3 == 0` saving
a second load of `y`. On the other hand this involves more checks, on average,
since most numbers aren't divisible by 16.

## Version 2

Computers typically use fixed-width (i.e. bounded) integers for calculations.
If an operation exceeds the bound then the most-significant bits are discarded,
so integer calculations are effectively performed modulo `2ⁿ` where `n` is the
width of the integer type. We'll only use unsigned integers here, and in this
case the width `n` is often 64, 32 or 16 bits.

Since 25 is odd it is coprime with `2ⁿ`. This means it has a multiplicative
inverse, i.e. there is a number `a` such that `a * 25 = 1 (mod 2ⁿ)`. You can
find this using Euclid's algorithm. For instance, if you're working with 16-bit
integers:

    2^16 = 65536 = 2621 * 25 + 11
              25 =    2 * 11 +  3
              11 =    3 * 3  +  2
               3 =    1 * 2  +  1
               2 =    2 * 1  +  0   => gcd(65536,25) = 1
               1 = 3 - 1 * 2
                 = 3 - 1 * (11 - 3 * 3)
                 = -1 * 11 + 4 * 3
                 = -1 * 11 + 4 * (25 - 2 * 11)
                 = 4 * 25 - 9 * 11
                 = 4 * 25 - 9 * (65536 - 2621 * 25)
                 = -9 * 65536 + 23593 * 25

Therefore `23593 * 25 = 1 (mod 2^16)`.

Now consider the effects of multiplying by `a` mod `2ⁿ` on the multiples of 25:

    a * 0  = 0 (mod 2ⁿ)
    a * 25 = 1 (mod 2ⁿ)
    a * 50 = 2 (mod 2ⁿ)
    a * 75 = 3 (mod 2ⁿ)
    ...

Since our integers are bounded we can only have finitely many multiples of 25.
Define `b = 2ⁿ div 25`, then `25b` is the largest multiple of 25 less than `2ⁿ`
and therefore there are `b+1` multiples of 25 in total, and multiplying them by
`a` (mod `2ⁿ`) maps them onto the numbers `[0..b]`.

However `a` itself has a multiplicative inverse, namely 25, and therefore
multiplying by `a` is an injective operation, which means that no other numbers
can map onto `[0..b]`. This means we can use the result after multiplying by
`a` as a cute way to test for divisibility by 25:

    y dvd 25 ⟷ (y * a) mod 2ⁿ ≤ b

Note that `a` and `b` depend only on the width of our integers `n` and not on
the input `y` so you (or the compiler) can compute them in advance. This means
that for fixed-width integers:

    isLeapYear y == 16 dvd y ∨ (4 dvd y ∧ b < (y * a) mod 2ⁿ)

Note that now this calculation only uses bitwise operations and a single
multiplication so is pretty cheap.

## Prove it!

The divisibility check mentioned above is quite a general thing that really
only needs the divisor to be coprime to the modulus. However there's a few
corner cases that I didn't cover in the sketch above. Here's an Isabelle/HOL
formalisation of its full correctness proof:

    theorem dvd_mod_mult_equiv:
      fixes m d :: nat
      fixes a assumes a_prop: "(a * d) mod m = 1"
      fixes b assumes b_prop: "b = m div d"
      fixes n assumes n: "n < m"
      shows "(n * a) mod m ≤ b ⟷ d dvd n"
    proof -
      consider (m0) "m = 0"
        | (bdm)     "m ≠ 0" "b * d = m"
        | (general) "m ≠ 0" "b * d ≠ m"
        by linarith
      thus ?thesis
        using n a_prop
      proof cases
        case bdm
        from a_prop have "(a * d mod m * b mod m) mod m = b mod m" by simp
        with bdm have "b mod m = 0" by auto
        with bdm show ?thesis by auto
      next
        case general

        from a_prop have d_pos: "0 < d" using neq0_conv by fastforce

        have "{ n. n < m ∧ d dvd n } = { n. n < m ∧ (n * a) mod m ≤ b }"
        proof (intro card_seteq)
          show "{ n. n < m ∧ d dvd n } ⊆ { n. n < m ∧ (n * a) mod m ≤ b }"
          proof (intro subsetI CollectI conjI, simp, elim CollectE conjE)
            fix n assume n: "n < m" and "d dvd n"
            then obtain k where k: "n = d * k" unfolding dvd_def by blast

            from k have "k ≤ n" using d_pos by auto
            with n have km: "k < m" by simp

            have "(n * a) mod m = (a * d * k) mod m" by (metis k mult.assoc mult.commute)
            also have "… = ((a * d) mod m * k) mod m" by (simp add: mod_mult_left_eq)
            also have "… = k" using km a_prop by simp

            also from k n have "d * k ≤ m" by simp
            hence "(d * k) div d ≤ m div d" using div_le_mono by blast
            hence kb: "k ≤ b" using d_pos b_prop by simp

            finally show "(n * a) mod m ≤ b" .
          qed

          have "card {n. n < m ∧ n * a mod m ≤ b} ≤ card {0..b}"
          proof (intro card_inj_on_le inj_onI, elim CollectE conjE)
            fix n1 n2
            assume "(n1 * a) mod m = (n2 * a) mod m"
            hence "(d * (a * n1)) mod m = (d * (a * n2)) mod m" by (metis mod_mult_eq mult.commute)
            hence "((a * d) mod m * n1) mod m = ((a * d) mod m * n2) mod m"
              by (simp add: mod_mult_left_eq mult.assoc mult.left_commute)
            with a_prop have "n1 mod m = n2 mod m" by simp
            moreover assume "n1 < m" "n2 < m"
            ultimately show "n1 = n2" by auto
          qed auto

          also have "card {0..b} = card ((*) d ` {0..b})"
            apply (intro sym [OF card_image] inj_onI) using d_pos by auto

          also have "((*) d) ` {0..b} ⊆ {n. n < m ∧ d dvd n}"
          proof (intro subsetI CollectI conjI, elim imageE, simp)
            fix n assume "n ≤ b" hence "d * n ≤ b * d" by simp
            also have le: "b * d ≤ m" unfolding b_prop using div_times_less_eq_dividend by blast
            with general have "b * d < m" by simp
            finally show "d * n < m" using a_prop general by auto
          qed auto
          hence "card ((*) d ` {0..b}) ≤ card {n. n < m ∧ d dvd n}" by (intro card_mono, simp_all)

          finally show "card {n. n < m ∧ n * a mod m ≤ b} ≤ card {n. n < m ∧ d dvd n}" .
        qed simp

        with n show ?thesis by blast
      qed auto
    qed

## Examples

Here are the relevant constants for the common bit widths, in hexadecimal:

    Width (bits)                   a   b
    16               23593 or 0x5c29   0x0a3d
    32                    0xc28f5c29   0x0a3d70a3
    64            0x8f5c28f5c28f5c29   0x0a3d70a3d70a3d70

## Signed integers

The story is similar with signed integers, except that now half of the
multiples of 25 are negative, so the largest multiple of 25 is now `25b` where
`b = 2ⁿ⁻¹ div 25`. This means there are `2b+1` multiples of 25 in total, and
multiplication by `a` maps them injectively onto `[-b..b]`, so the divisibility
predicate becomes:

    y dvd 25 ⟷ |(y * a) mod 2ⁿ| ≤ b

That said, the Gregorian calendar has only existed for a few hundred years
anyway so leap years in BC don't really work this way. Maybe signed integers
aren't the right choice for this application.

