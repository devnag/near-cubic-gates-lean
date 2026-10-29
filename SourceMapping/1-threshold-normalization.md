# 1. Integer threshold normalization

[Mapping index](README.md) · derived field `normalization` · no published premise

[`Normalization.threshold_normalization`](../SourceAdapters/Normalization/IntegerThreshold.lean) proves
`NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2` outright. The name records the mathematical citation; it does not
make the result a trusted assumption. The current paper uses it at `lem:integer`.

For every natural m and every threshold gate on m Boolean inputs, the theorem supplies an equivalent gate whose
weights **and threshold** are integers in [−m^m, m^m]. A threshold gate has real parameters and outputs one when
Σ_i w_i x_i ≥ t, including equality. Equivalence means agreement on every 0–1 input; it is not a claim about all
real inputs. The proof transfers between Boolean vectors and real vectors whose coordinates are zero or one.

The proof obtains a factorial bound from the finite-dimensional separation argument. For m ≥ 3 that bound is at
most m^m; dimensions one and two have separate constructions. At m = 0 the function is constant and Lean's
0^0 = 1 convention gives the required range. These cases, including the threshold parameter, are proved rather
than added as assumptions. Bit-length consequences are downstream results.

Mathematical credit: L. Chen, A. Tal and Y. Wang, *Super-quadratic Lower Bounds for Depth-2 Linear Threshold
Circuits*, [ECCC TR26-039](https://eccc.weizmann.ac.il/report/2026/039/), Lemma 3.2, which attributes the result to
Muroga, Toda and Takasu (1961). CTW26 is not one of the seven retained published statements.

Check the quantifiers, inclusive comparison, Boolean input domain, bound on the threshold as well as the weights,
and the zero-input case against the exported theorem. The main theorem receives this result through a proof,
not a source hypothesis.
