# 7. The fixed-machine refuter

[Mapping index](README.md) · derived field `refuter` · no published premise

[`Assembly.field7`](../SourceAdapters/Assembly/Field7.lean) proves `CLW20_Theorem1_13` outright. The mathematical
reference is Chen–Lyu–Williams, *Almost-Everywhere Circuit Lower Bounds from Non-Trivial Derandomization*,
[ECCC TR20-150](https://eccc.weizmann.ac.il/report/2020/150/), Theorem 1.13 and its Section 4 proof. This citation
does not introduce a CLW premise into `PublishedInputs`. The current [paper](../paper/paper.tex) labels are
`imp:ae-refuter` and `lem:multitape-refuter`.

For every time-constructible T with n ≤ T(n) ≤ 2^poly(n), the theorem supplies a language L in NTIME[T],
an oracle refuter R and a fixed polynomial exponent. For every fixed weak machine M running in o(T(n)) time,
R(M,1^n) eventually finds an n-bit input on which M and L disagree, within C_M(T(n)+1)^d steps. The onset and
coefficient may depend on M; the exponent and refuter are fixed beforehand.

The definitions use actual multitape machines. A time constructor writes the binary clock from unary n in
O(T(n)+1) time. The weak machine's witness has floor(n/16) bits, and its worst-case clock is little-o of T.
The hierarchy language has an ordinary verifier with witness length and time O(T(n)+1). The refuter's SAT oracle
uses explicit three-literal CNF queries, with framed query/output words and charged oracle interaction.

The proof constructs the hierarchy and recurrence, the loader and refuter rounds in
[`Refuter/RLoadField.lean`](../SourceAdapters/Refuter/RLoadField.lean), and the paid bounded
[computation-to-3-CNF compiler](../SourceAdapters/Compile/CNFMainE.lean). It covers the stated full clock range,
including linear clocks. In particular it does not justify a framing change merely by saying that O(n) overhead
is harmless: at a linear clock such overhead need not preserve a little-o promise.

Check the quantifier order, the fixed-machine dependence of the onset, the worst-case time promise and the
charged oracle encoding. These are properties of the proved interface, not unchecked changes to a trusted
CLW theorem.
