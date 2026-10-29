# 8. Hardness amplification from STV list decoding

[Mapping index](README.md) · derived field `amplification` · one published premise

[`Amplification.field8`](../SourceAdapters/Amplification/Field8.lean) proves
`NearCubicGates.Close.CLW20_Lemma3_9_Multitape` from
`NearCubicGates.Published.STV.Theorem29` alone. The intermediate statement is the full-range amplification
interface credited to CLW20 Lemma 3.9; that lemma is not itself a retained premise.

Source: M. Sudan, L. Trevisan and S. Vadhan, *Pseudorandom Generators without the XOR Lemma*, J. Comput. System
Sci. 62(2):236–266 (2001). Theorem 29 and Definition 20 were checked in the journal-version preprint (pp.17 and
13), PDF SHA-256 `6155baab46b3204122e9f2f801a70f891b9333f34cf396b1047809973ce53cf7`, and against
[ECCC TR98-074, revision 2](https://eccc.weizmann.ac.il/report/1998/074/), SHA-256
`87ccd011e2e0d55929decddd29caaf4b4c89659dee9c93760a8e29d950d59865`.

## The retained premise

The fields are binary polynomial-basis fields F₂[X]/(q), with q monic irreducible of degree t. The relevant
polynomials in m variables have **total** degree at most d. If ε > c√(d/|F|), the premise supplies a list of at
most L/ε randomized oracle machines. The absolute constants precede all parameters and the oracle; one list is
chosen before the polynomial to be recovered. Every degree-bounded polynomial agreeing with the oracle on at
least an ε fraction of points is computed by some member of that same list.

“Computes” means probability at least 3/4 **at each input point**, not agreement on 3/4 of the points. Every
machine halts on every random string within the stated polynomial budget. Its finite transition-table size and
coin count also have polynomial bounds, preventing an arbitrarily large polynomial from being hard-wired for
free. Queries and field elements use explicit bit representations.

The publication gives a randomized reconstruction procedure. The retained statement takes only the existence of
a successful output list, which follows from positive success probability; it does not assume a uniform
deterministic procedure for choosing that successful list. Binary-field representation and ordinary oracle-machine
conventions are documented in [Statement.lean](../Statement.lean).

## The proved consequence

For every time-constructible size bound S, the derived amplifier maps each n-bit function f to a function g of
O(n) bits. If f has no circuit of size S(n), then circuits of size S(n)^(1/c) agree with g on less than a
1/2 + S(n)^(−1/c) fraction of inputs. Its truth table is constructed in 2^O(n) time. Circuit size counts nodes,
including inputs and constants; the full range, including small and sublinear S, is part of the proved theorem.

The [reconstruction](../SourceAdapters/Amplification/Reconstruction.lean),
[truth-table construction](../SourceAdapters/Amplification/Construction.lean), finite exceptional cases and
[ordinary-to-TM2 time conversion](../SourceAdapters/Machine/OrdinaryToTM2.lean) are supplied proofs. The main
lower-bound proof's later polynomial-clock specialization does not replace the full-range theorem by an assumption.
The current [paper](../paper/paper.tex) labels are `imp:ae-amplification` and `app:sources`.
