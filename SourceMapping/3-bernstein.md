# 3. Finite Bernstein inequality

[Mapping index](README.md) · derived field `bernstein` · no published premise

[`Probability.finiteBernstein`](../SourceAdapters/Probability/BernsteinFinite.lean) proves
`Vershynin18_Theorem2_8_4_FiniteBernstein.{0,0}`. Its finite, uniform probability space and finite index set are
nonempty. If the Y_i are mutually independent, centered and satisfy |Y_i| ≤ 1, then for every s > 0,

    Pr[|Σ_i Y_i| ≥ s] ≤ 2 exp(−s² / (2(Σ_i E[Y_i²] + s/3))).

Here expectation and probability are finite averages. Independence quantifies over finite subfamilies and events
in the real-valued coordinates. Since each variable has finite range, arbitrary real events can be intersected
with that finite range without changing their preimages; the adapter proves the connection to measure-theoretic
independence. The exponential-moment argument and tail estimate are checked in the probability modules.

Mathematical credit: R. Vershynin, *High-Dimensional Probability*, first edition (2018), Theorem 2.8.4,
[author's first-edition text](https://webapps.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf), printed p.38.
The finite statement is its K = 1 specialization, but this specialization is now proved rather than assumed.
The current [paper](../paper/paper.tex) uses label `lem:bernstein`.

Check mutual rather than pairwise independence, the mean-zero and absolute-bound hypotheses, the second-moment
sum in the denominator and the strict positive threshold. No Vershynin premise enters `PublishedInputs`.
