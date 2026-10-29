# 4. Prime density from the prime number theorem

[Mapping index](README.md) · derived field `primes` · one published premise

The retained statement is `NearCubicGates.Published.Apostol.primeNumberTheorem` in
[Statement.lean](../Statement.lean): as the **real** variable x tends to +∞, π(x) log(x)/x tends to 1.
`primeCountingReal x` counts natural primes p ≤ x, including an endpoint that is prime. `Real.log` is the natural
logarithm. Its total definition below 2 has no effect on the limit. No error rate or effective onset is assumed.

[`Base.primes_of_primeNumberTheorem`](../SourceAdapters/Base/Primes.lean) proves the intermediate statement
`ApostolPrimeNumberTheorem`: for each ε > 0 there is an onset at least 2 such that every natural n above it
satisfies |π(n) log(n)/n − 1| < ε. The adapter proves that the real count at a natural argument equals Mathlib's
`Nat.primeCounting`, restricts the limit to naturals, and raises the onset to 2. The dyadic-interval prime count
used by the lower bound is then derived; it is not a stronger short-interval premise.

Source: T. M. Apostol, *Introduction to Analytic Number Theory*, Springer (1976), Chapter 4 §4.1, printed p.74;
the analytic proof is in Chapter 13. The [publisher's Chapter 4 page](https://link.springer.com/chapter/10.1007/978-1-4757-5579-4_5)
supplies a preview of the actual printed statement, with PDF SHA-256
`812bf5275a7717f606be81ac5837f36382015be99ee7719e199c7b2ed9ac9c32`. Its text layer garbles some symbols, so the
displayed limit and prime-count convention were checked on the page image. This is stronger provenance than the
older abstract-only record. Chapter 13's proof was not read as part of that source comparison.

The current [paper](../paper/paper.tex) label is `lem:primes`. Check the real-argument limit, inclusive prime
endpoint and absence of an effective rate in the retained premise, then the separate natural-argument theorem.
