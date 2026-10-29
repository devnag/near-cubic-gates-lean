# Published statements and their proved consequences

The release proves `PublishedInputs → MainStatement`. **PublishedInputs has seven fields.** The nine pages below
follow the nine intermediate interfaces used by the lower-bound proof; each page says which published premises
it needs and names its actual Lean producer. Four of the interfaces need no published premise.

| Page | Derived interface | Published premises | Closing theorem under `NearCubicGates.Adapters` |
|---|---|---|---|
| [1](1-threshold-normalization.md) | Integer threshold normalization | None | `Normalization.threshold_normalization` |
| [2](2-live-restriction.md) | Central-binomial restriction bound | None | `Restriction.centralBinomialRestriction` |
| [3](3-bernstein.md) | Finite Bernstein inequality | None | `Probability.finiteBernstein` |
| [4](4-prime-number-theorem.md) | Natural-argument prime density | Apostol prime number theorem | `Base.primes_of_primeNumberTheorem` |
| [5](5-rectangular-product.md) | Binary multitape rectangular product | Williams Corollary 4.4 = C.2 | `Williams.Final.williams14_of_leaf` |
| [6](6-short-pcp.md) | Short PCP with an ordinary circuit-construction machine | BCGT Theorem 11.1 and Algorithm 17 | `Assembly.field6Ordinary` |
| [7](7-refuter.md) | Full-range framed refuter | None | `Assembly.field7` |
| [8](8-amplification.md) | Full-range hardness amplification | STV Theorem 29 | `Amplification.field8` |
| [9](9-three-query-pcpp.md) | Three-query proximity and an efficient linear encoder | CW19 Lemma 22 at half soundness and Lemma 26 | `Assembly.field9Encoder` |
| [Main](main-theorem.md) | Near-cubic constant-error hardness | The seven statements above, through all nine derived interfaces | `NearCubicGates.Close.main_from_published` |

The exact seven premise names, under `NearCubicGates.Published`, are `CW19Proximity.Lemma22Half`,
`CW19Code.Lemma26`, `BCGT13.BCGT13_Theorem11_1`, `Shoup.FindIrrPolyAlgorithm17`, `STV.Theorem29`,
`Apostol.primeNumberTheorem` and `Williams.RectangularProductLeaf`. In the release their definitions and source
models are in [Statement.lean](../Statement.lean). [NineInputs.lean](../NineInputs.lean) contains the intermediate
statements; it is not an additional trusted boundary.

## Reading the correspondence

The mathematical meanings and source conventions must be reviewed against the publications. A source's informal
phrase “polynomial time” does not specify a tape layout. The retained statements therefore state the chosen source
encodings and conventional machine semantics explicitly. Their budgets charge the entire encoded input. An
ordinary `WordFunction` uses one fixed program, input framing of length 2|w|+1, a fresh output tape and exact output
words, including trailing zero bits. These are representation conventions, not words quoted from the publications.

Conversions to the proof's target formats are proved in `SourceAdapters/`. This includes finite-alphabet
simulation for Williams, bounded simulation and ordinary-to-TM2 compilation, verifier/circuit serialization,
proof-address trimming and honest-proof restriction. Each theorem supplies its particular time bound; we do not
assume a universal constant-overhead equivalence of all machine models.

Some retained statements are faithful specializations, rather than literal copies of a universal printed claim.
In particular, the BCGT soundness theorem is restricted to positive exponents in its soundness constant, and the
STV premise retains existence of a successful list of machines rather than its randomized reconstruction
algorithm. The relevant pages spell out these choices. CTW26, Vershynin, Murray–Williams and CLW20 remain useful
mathematical credits for derived statements; they are not extra fields of `PublishedInputs`.

## Paper and verification scope

References use labels in the current [paper](../paper/paper.tex), version 3 (October 28, 2026), SHA-256
`3bfede57ee87cb531f0623dcd29529c25d8be2c19251670f1cf7e5e5d849be88`. The earlier version-2 excerpts and their line
numbers do not describe this file. The pages link to current producer modules and name declarations directly;
they do not claim to print the complete constant closure of the final statement.

Run `python3 SourceMapping/check.py` from the release root to check the documentation manifest. File identity,
the seven-premise/nine-interface inventory, local links, paper labels and source quotation checks are distinct
from mathematical review. The checker reports missing source files and formula transcriptions separately; a
local identity PASS does not mean every quotation was checked against a source PDF. The Lean build, `Check.lean`
and comparator have the separate roles described in the [repository README](../README.md).

Source provenance is explicit on each page. The Apostol statement was checked on the publisher's printed-page
preview; Chapter 13's proof was not reviewed there. BCGT Algorithm 17 was checked directly; the original FOCS 1988
Shoup corollary was not, and the corroborating journal preprint has a different theorem number. These limitations
are not replaced by an unsupported claim of complete primary-source verification.
