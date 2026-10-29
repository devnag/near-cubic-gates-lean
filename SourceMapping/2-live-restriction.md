# 2. Live gates under random restrictions

[Mapping index](README.md) · derived field `restriction` · no published premise

[`Restriction.centralBinomialRestriction`](../SourceAdapters/Restriction/CentralBinomial.lean) proves
`CTW26_AppendixA3_CentralBinomialRestriction`. For a real threshold gate on n inputs and 0 < k < n, it bounds
the probability that the gate remains nonconstant by

    k · choose(n−k, floor((n−k)/2)) / 2^(n−k).

The uniform restriction consists of a k-element set of live coordinates and one assignment on its complement.
Thus every element of the finite restriction space appears once. “Live” means there are two inputs agreeing with
that outer assignment on which the gate's outputs differ. Averaging the indicator of this event gives exactly
its probability; it is not a claim about an independently sampled set of coordinates.

The proof establishes the central-binomial estimate by finite counting and the threshold gate's unateness.
The paper's square-root estimate k/√(n−k+1) and weighted Markov consequence are further proved consequences.
Neither the exact counting estimate nor the asymptotic bound is retained as a published premise.

Mathematical credit: Chen–Tal–Wang, [ECCC TR26-039](https://eccc.weizmann.ac.il/report/2026/039/), Lemma 4.1 and
Appendix A.3, especially the threshold specialization of Lemma A.3.1 and equations (14)–(15). The current
[paper](../paper/paper.tex) labels are `lem:live` and `app:live`.

Check the 0 < k < n range, the uniform finite restriction law, the definition of nonconstancy and the exact
central-binomial coefficient. CTW26 supplies attribution, not an extra field of `PublishedInputs`.
