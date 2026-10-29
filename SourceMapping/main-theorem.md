# Main theorem: near-cubic constant-error hardness

[Mapping index](README.md) · the conclusion of the proof

The release theorem is `NearCubicGates.Close.main_from_published : FinalStatement`, where
`FinalStatement := PublishedInputs → NearCubicGates.Target.MainStatement`.
[Statement.lean](../Statement.lean) contains the conclusion and the seven retained published premises;
[MainTheorem.lean](../MainTheorem.lean) proves the implication. The nine intermediate interfaces in
[NineInputs.lean](../NineInputs.lean) are derived by [SourceAdapters/Assembly.lean](../SourceAdapters/Assembly.lean).
They are not nine additional published assumptions.

The current [paper](../paper/paper.tex) is version 3, October 28, 2026, SHA-256
`3bfede57ee87cb531f0623dcd29529c25d8be2c19251670f1cf7e5e5d849be88`. The relevant labels are `thm:main` and
`def:class`. This page refers to those labels, not the previous version's line numbers.

## Quantifiers and circuit class

There is a rational γ with 0 < γ < 1 such that for every real d with 0 < d < γ/5, there are a positive integer K,
a language F in E^NP and an onset n₀ ≥ 4. For every n ≥ n₀ and every circuit in the stated class satisfying its
budget, the fraction of inputs on which the circuit agrees with F is strictly less than 1−d. The language and
onset may depend on d; the conclusion holds at all sufficiently large lengths, not merely infinitely often.

`WeightedSymmetricCircuit` consists of arbitrary real threshold gates g_i, nonzero integer top coefficients w_i
and an arbitrary lookup f : ℤ → {0,1}. Its score is Σ_i w_i g_i(x), its output is f of that score, and its top
weight is W = Σ_i |w_i|. Real bottom weights and fan-in are unrestricted. The stored support of a threshold gate
is exactly its nonzero-weight set; it imposes no extra restriction. A gate outputs one exactly when its weighted
sum is at least the threshold, including ties.

`agreement` divides the number of agreeing Boolean inputs by 2^n. With unit top weights W is the bottom gate
count. [StatementChecks/CircuitClass.lean](../StatementChecks/CircuitClass.lean) supplies the ordinary SYM∘THR
embedding into this weighted class.

## Budget and complexity class

Let λ_n = ⌈log₂ n⌉ and μ_n = ⌈log₂ λ_n⌉. The Lean budget is

    (K · W · μ_n^7)^4 · λ_n^21 ≤ n^12.

For n ≥ 4 and K > 0 this is equivalent to the paper's integer budget
W ≤ floor(n³/(K λ_n^(21/4) μ_n^7)). The fourth power removes real division and fractional powers without
weakening the statement. [`mainBudget_iff_floor`](../StatementChecks/MainBudget.lean) proves the equivalence.

`InENP` gives an explicit deterministic multitape oracle program computing F within 2^O(n) counted steps,
together with an NP verifier for its oracle language. The NP verifier's witness length and running time are
polynomial in the query's binary length. Queries are adaptive; writing and asking one is charged its framed
length plus one step. The certificate is therefore an ordinary exponential-time computation with an NP oracle,
not a unit-cost oracle capable of obtaining an arbitrarily long query for free.

[`StatementChecks/ENPDeterminism.lean`](../StatementChecks/ENPDeterminism.lean) checks that such a certificate
determines its language. [Nontrivial.lean](../StatementChecks/Nontrivial.lean) supplies further checks on the
statement's meaning, including its existential constant-error formulation.

## What the verification establishes

The seven premises are listed in the [mapping index](README.md); the nine pages identify their proved consumers.
Normalization, restriction, finite Bernstein and the refuter need no published premise. The short-PCP consumer
uses an ordinary construction machine, and the three-query consumer requires only an efficient encoder.

`Check.lean` checks the compiled theorem type and permitted axioms. Comparator compares the solution with this
trusted challenge and replays its proof through Lean's kernel. These checks do not establish that the published
premises are true or that their definitions faithfully express the sources. Those are the separate mathematical
questions documented here. No claim about the paper's other theorems follows merely from checking this one.
