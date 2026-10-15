# Source mapping: near-cubic gates

This directory maps every published theorem that the Lean proof assumes, and the main theorem it proves, to the
exact Lean text. It belongs to the paper [`paper/paper.tex`](../paper/paper.tex)
(version 2).

**Status.** The theorem this repository proves is `NearCubicGates.Close.FinalStatement`: the nine published inputs
below imply `NearCubicGates.Target.MainStatement`, the paper's `thm:main`. The comparator (`make comparator` at the repository root) checks a proof of that
theorem against the statement file [`Statement.lean`](../Statement.lean), allowing only the standard logical
foundations `propext`, `Classical.choice` and `Quot.sound`. This mapping checks identities and records the
correspondence between the published statements and the Lean premises; it is not a proof.

## Pages

Each page has a header with the source's bibliographic data (URL and PDF SHA-256) and a table **Paper (verbatim) |
Lean (verbatim)**: one row for the statement and one row for each definition it uses. On the paper side are the
source PDF's text, pinned to PDF pages, and paper v2's statement, pinned to line numbers. On the Lean side is the
text of the statement file, with links to the exact lines.

Every declaration of the statement's custom closure is printed on its page exactly as it appears in
`Statement.lean`: every declaration of that file that the page's statement depends on, directly or through other
declarations. The closure stops at
Lean's core library and Mathlib. Their definitions (for example `Nat.clog`, `Real.log`, real powers, `Finset.card`,
`Nat.primeCounting` and `Turing.TM2ComputableInTime`) are not printed; they are those of the pinned Lean and
Mathlib versions (`lean-toolchain` and `lake-manifest.json` at the repository root). The custom closure of `FinalStatement`, the theorem this repository proves, has 321 constants: 316 named declarations with their constructors, recursors, structure projections and pattern-matching helpers, and 5 proofs that Lean generates while elaborating a declaration (named `…._proof_n`).

| Page | Paper v2 | Published source | Lean statement |
|---|---|---|---|
| [Main theorem](main-theorem.md) | `thm:main` | the paper itself | `NearCubicGates.Target.MainStatement` |
| [1. Threshold normalization](1-threshold-normalization.md) | `lem:integer` | CTW26 Lemma 3.2 | `NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2` |
| [2. Live gates under restrictions](2-live-restriction.md) | `lem:live` | CTW26 Lemma 4.1, Appendix A.3 | `NearCubicGates.PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction` |
| [3. Bernstein's inequality](3-bernstein.md) | `lem:bernstein` | Vershynin Theorem 2.8.4 | `NearCubicGates.PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein` |
| [4. Prime number theorem](4-prime-number-theorem.md) | `lem:primes` | Apostol, Chapters 4 and 13 | `NearCubicGates.PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem` |
| [5. Rectangular matrix product](5-rectangular-product.md) | `imp:batch` | Williams (J. ACM 2014) Corollary 4.4 = C.2 | `NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4` |
| [6. Short PCP](6-short-pcp.md) | `imp:short-pcp` | Murray–Williams (SIAM J. Comput. 2020) Section 5, from BV14 | `NearCubicWires.Bindings.MW20.MW20_OracleCircuitPCP_TM2` |
| [7. Fixed-machine refuter](7-refuter.md) | `imp:ae-refuter` | CLW20 Theorem 1.13 | `NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13` |
| [8. Hardness amplification](8-amplification.md) | `imp:ae-amplification` | CLW20 Lemma 3.9 | `NearCubicGates.Close.CLW20_Lemma3_9_Multitape` |
| [9. Three-query PCPP and code](9-three-query-pcpp.md) | `imp:three-pcpp` | CW19 Lemmas 24 and 27 | `NearCubicGates.PublishedSources.PCPP.ThreeQuerySourceGroup` |

The Lean names are those of this repository's statement file; namespaces such as `NearCubicWires` are part of the
names and nothing more. Paper v2's other cited results (for example the periodic theorem's two-query PCPP) are
not assumptions of the main theorem and have no page.

## What a reader checks

On each page, compare the paper column with the Lean column row by row, then read the page's numbered **What to
check** list; it states every reading (quantifier order, rounding, model) and the documented deviations. Lean
cannot check the readings. Each page states its own (for example the circuit size on page 8 and the verifier's
running time on page 9); two kinds recur across pages.

**Models.** The published algorithms of pages 5 and 7 are read as multitape Turing machines, which Williams
states for page 5 and which paper v2 derives for page 7 (`lem:multitape-refuter`); the verifier of page 6 is a
multitape machine, the case paper v2 proves (`thm:short-pcp-ours`); time-constructibility (pages 7 and 8, one
shared definition) is the multitape notion. Pages 6, 8 and 9 state some algorithms as machines of
Mathlib's `Turing.TM2` model, a finite program over finitely many stacks. Three standard simulations connect these
models: a multitape machine over a larger tape alphabet runs on bits with a constant-factor slowdown (each symbol
coded as a block of a fixed number of cells); a TM2 machine and a multitape machine simulate each other with
constant overhead per step (a tape as two stacks, a stack as a tape); and multitape machines simulate random-access
machines with polynomial overhead. So polynomial time, and 2<sup>O(n)</sup> time on a 2<sup>n</sup>-bit truth
table, are the same class in each of these models. These simulations are arguments, not checked by Lean.

**Encodings.** The sources fix no codes or tape layouts; each page prints the ones Lean uses. The usual codes of
the same objects (numbers in binary, matrices row by row or column by column, lists of clauses, gates or
transitions) convert into one another in time polynomial in their length, and for the matrices of page 5 in
quasi-linear time on a multitape machine (a transposition by sorting). Each bound in the inputs absorbs that:
N<sup>2</sup> · polylog N on page 5; polynomial, or 2<sup>O(n)</sup> on a truth table, on pages 6, 8 and 9; and on
page 7 a constant that may depend on the fixed machine M. This is an argument, not checked by Lean.

## Checking the identities

From the repository root:

```sh
python3 SourceMapping/check.py
```

It needs only Python 3. It checks that `Statement.lean` and `paper/paper.tex` are the pinned files (SHA-256); that
every Lean and paper excerpt on the pages equals the current file lines and is printed verbatim; that every
declaration of each page's closure is printed on it; that every quotation is printed on its page; and that every
link resolves as written, with line anchors inside the file and links to proof declarations on the declaring line.

The published sources are not distributed with this repository. To check the quotations against them too:

```sh
scripts/fetch_sources.sh
python3 SourceMapping/check.py
```

`fetch_sources.sh` downloads the 8 published sources that the pages cite from their official URLs into
`SourceMapping/pdfs/` (which git ignores), checks each file's SHA-256, and extracts the text of each PDF page with pypdf 6.19.0
(downloaded from PyPI, SHA-256 pinned). Two sources cannot be fetched by a script (Apostol's publisher page; the J. ACM PDF of Williams' paper); the script
prints where to save them from a browser. With the sources present, `check.py` also checks each source file's
SHA-256 and that every quoted line occurs on the pinned page of the source's text. The comparison ignores white space
and the characters `^ _ { }`, and reads the TeX command names that some PDFs' text layers use for symbols (for
example `\geq` and `\ell` in the Murray–Williams PDF) as those symbols. These are identity checks, not
mathematics, and their scope is limited in two ways:

- 9 quoted lines are displayed formulas that the extracted PDF text does not reproduce (fractions,
  sums, binomial coefficients). They are formula readings, reviewed by hand against the PDF page, not byte matches
  of the PDF text; the checker counts them separately and does not verify them. [manifest.json](manifest.json) lists
  them (the `transcribed` line indices of each quotation).
- The checker verifies that every declaration of a page's closure list in [manifest.json](manifest.json) is printed
  on the page. That the list is the complete closure is established by the Lean query that generated it (a walk of
  the declarations' types and definition bodies in the compiled statement), not by the checker.
