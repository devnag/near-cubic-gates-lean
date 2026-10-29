# 5. Rectangular matrix product

[Mapping index](README.md) · derived field `rectangularProduct` · one published premise

The retained premise is `NearCubicGates.Published.Williams.RectangularProductLeaf` in
[Statement.lean](../Statement.lean). One deterministic multitape machine, its tapes, constants C,e and onset N₀
are chosen before the dimensions and matrices. For N ≥ N₀ and natural m = N^(1/10), it multiplies an N×m zero-one
matrix by an m×N zero-one matrix over the integers in O(N² poly(log N)) steps. Restricting to N = k^10 gives an
unbounded range of integral dimensions and avoids a rounding convention for N^(1/10).

Source: R. Williams, *Nonuniform ACC Circuit Lower Bounds*, J. ACM 61(1), Article 2 (2014),
[doi:10.1145/2559903](https://doi.org/10.1145/2559903), Corollary 4.4 (p.2:17), restated as Corollary C.2 (p.2:29).
Appendix C (p.2:26) explicitly discusses a multitape implementation. Pinned PDF SHA-256:
`78d7c472224906600e31369914d4210d875af894b92903c362c3c1cf680b021c`.

The source fixes no alphabet, tape layout or binary matrix codec. The retained model permits a general finite
alphabet, finite control and local unit head moves on one-sided tapes. Its **single combined input word** is A
row by row, a separator, then B row by row. Output entries are binary digits followed by separators. These are
explicit representation conventions, not a claim that Williams specifies two input tapes. Base-two logarithms
are also a convention: changing a fixed base changes the existential time constant.

[`Williams.Final.williams14_of_leaf`](../SourceAdapters/Williams/Final.lean) proves
`Williams14_Corollary4_4` in the target bit-multitape model. Its loader, finite-alphabet simulation and output
conversion are actual paid constructions. They supply the two input tapes, dimension header and fixed-width
output expected by the lower-bound proof. The natural-number sum of zero-one products is the integer matrix
product, and every entry is at most k ≤ N, so ⌊log₂ N⌋+1 bits suffice. The adapter raises the onset to at least 2;
no correctness claim below that onset is required.

The current [paper](../paper/paper.tex) label is `imp:batch`. Check uniformity of the single source machine,
the onset, perfect-tenth-power specialization, arithmetic over integers and the source/target encoding
distinction. The binary simulation is a proved adapter conclusion, not another hypothesis.
