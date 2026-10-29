# Near-cubic gate lower bounds for SYM∘THR circuits: a Lean proof

This repository formalizes the main theorem of Dev Nag's *Almost-Everywhere Near-Cubic Gate Lower Bounds for
SYM∘THR Circuits*, [version 3, October 28, 2026](paper/paper.tex). The theorem is proved from **seven published
statements**. The nine intermediate statements used by the lower-bound proof are all derived in Lean; they are
not nine additional assumptions.

The paper's `thm:main` says that there is a rational constant 0 < γ < 1 such that, for every fixed 0 < d < γ/5,
there are a positive integer K_d and a language F_d ∈ E^NP such that, at every sufficiently large n,

> W(C) ≤ ⌊n³/(K_d λ_n^{21/4} μ_n^7)⌋ implies agr(C, F_d) < 1 − d for every C ∈ 𝒲.

Here C(x) = f(Σ_i w_i g_i(x)): the bottom gates g_i have arbitrary real threshold weights, the w_i are nonzero
integers, and f : ℤ → {0,1} is arbitrary. W(C) = Σ_i |w_i|; with unit top weights this is the number of bottom
gates. Also λ_n = ⌈log₂ n⌉, μ_n = ⌈log₂ λ_n⌉, and agreement is the fraction of Boolean inputs on which C and F_d
coincide. Thus every circuit within the near-cubic budget is wrong on more than a d fraction of inputs at every
large length. The constant γ is existential and is not optimized.

## The trusted statements and the proved interfaces

In the release, [Statement.lean](Statement.lean) defines `NearCubicGates.Close.PublishedInputs` and
`FinalStatement := PublishedInputs → NearCubicGates.Target.MainStatement`. Its seven fields are the following
statements; names in the second column are under `NearCubicGates.Published`.

| Published result | Lean statement | Used to derive |
|---|---|---|
| Chen–Williams, Lemma 22, at soundness 1/2 | `CW19Proximity.Lemma22Half` | [Three-query proximity](SourceMapping/9-three-query-pcpp.md) |
| Chen–Williams, Lemma 26 | `CW19Code.Lemma26` | [Efficient linear code and encoder](SourceMapping/9-three-query-pcpp.md) |
| Ben-Sasson–Chiesa–Genkin–Tromer, Theorem 11.1, on the positive-exponent domain | `BCGT13.BCGT13_Theorem11_1` | [Short PCP](SourceMapping/6-short-pcp.md) |
| Deterministic irreducible-polynomial algorithm, BCGT Algorithm 17, citing Shoup | `Shoup.FindIrrPolyAlgorithm17` | [Field construction for the short PCP](SourceMapping/6-short-pcp.md) |
| Sudan–Trevisan–Vadhan, Theorem 29 | `STV.Theorem29` | [Hardness amplification](SourceMapping/8-amplification.md) |
| Apostol, prime number theorem | `Apostol.primeNumberTheorem` | [Prime density](SourceMapping/4-prime-number-theorem.md) |
| Williams, Corollary 4.4 = C.2 | `Williams.RectangularProductLeaf` | [Rectangular matrix product](SourceMapping/5-rectangular-product.md) |

The distinction matters. [Threshold normalization](SourceMapping/1-threshold-normalization.md),
[random restrictions](SourceMapping/2-live-restriction.md), [finite Bernstein](SourceMapping/3-bernstein.md) and
the [fixed-machine refuter](SourceMapping/7-refuter.md) are proved without a published premise.
The other five interfaces follow from the seven statements above. [SourceMapping](SourceMapping/README.md)
records the precise dependencies, mathematical conventions and source locators.

The short-PCP endpoint is the **ordinary-machine** theorem
[`Assembly.field6Ordinary`](SourceAdapters/Assembly/Field6Ordinary.lean), from the BCGT verifier theorem and the
irreducible-polynomial algorithm alone. Its affine constraint reduction, compact generator, verifier running time,
amplification, mask construction and circuit printer are proved. The three-query endpoint is
[`Assembly.field9Encoder`](SourceAdapters/Assembly/Field9Encoder.lean), from the two CW19 premises. Its final
interface needs only the code's encoder; the stronger total-decoder theorem is also proved separately.

## Verify the release

Install [elan](https://github.com/leanprover/elan), then run `make` in the repository. The pinned toolchain is in
[lean-toolchain](lean-toolchain); the build obtains Mathlib's cache, builds the proof and runs
[Check.lean](Check.lean). A full build needs substantial disk space, memory and time.

For the sandboxed check, run `make comparator` on Linux in a **fresh clone**. The command installs the revisions
pinned by [scripts/comparator.sh](scripts/comparator.sh), builds inside the sandbox, compares
[Solution.lean](Solution.lean) with [Challenge.lean](Challenge.lean), checks the permitted axioms and replays the
proof through Lean's kernel. The script refuses a tree containing previously compiled proof files. Its launch
message records the sandbox mode available on the host. Run `make` on platforms where this wrapper is unavailable.

`Check.lean` prints the conclusion, `PublishedInputs`, the main theorem
`NearCubicGates.Close.main_from_published`, and its dependencies. Its successful result means the compiled theorem
has the requested type and uses only `propext`, `Classical.choice` and `Quot.sound`. It does not itself replay every
proof through the kernel. Comparator's successful result is `VERDICT: PASS … comparator: Your solution is okay!`
with exit status zero. These are instructions for obtaining a verification result, not a substitute for the
output of that run.

Optional checks are `make kernel-replay` (standalone `leanchecker`), `make names`, and
`python3 SourceMapping/check.py` (documentation identity, inventories, labels and links). The source-mapping
checker's report distinguishes checked source quotations from displayed-formula transcriptions and unavailable
source files. It does not establish a mathematical source correspondence or replace the kernel checks.

## What to read and what remains trusted

Start with [the main-theorem mapping](SourceMapping/main-theorem.md), then the seven premises in
[Statement.lean](Statement.lean). The trusted statement imports Mathlib; it contains the mathematical models and
the seven premises, not the proofs of their consequences. The correctness of those premises and the faithfulness
of their formal meanings to the publications require mathematical review.

[NineInputs.lean](NineInputs.lean) holds the intermediate interfaces.
[SourceAdapters/Assembly.lean](SourceAdapters/Assembly.lean) assembles their proofs from `PublishedInputs`;
[MainTheorem.lean](MainTheorem.lean) composes this with the lower-bound proof. `Bindings/`, `Proof/`,
`SourceAdapters/` and `StatementSupport.lean` are proof code, not additional trusted hypotheses.

[StatementChecks/](StatementChecks/) provides useful checks on the conclusion: the integer budget agrees with
the paper's floor bound, ordinary SYM∘THR circuits embed with W equal to their gate count, an E^NP certificate
determines its language, and the statement is neither vacuous nor universal over all languages. The mapping pages
explain the quantifiers and machine definitions needed to assess these claims.

Comparator checks the exact challenge statement, the permitted axioms and the kernel proof. It does not check
whether the seven published results are true, whether their formal meanings are faithful, or whether the
conclusion is the intended paper theorem. Its trusted infrastructure also includes the pinned Lean/Mathlib
definitions, build configuration and sandbox tools. `Challenge.lean` deliberately leaves its proof open for the
comparison; `Solution.lean` supplies the proof.

Machine conventions are explicit. Ordinary programs use finite-control, local multitape transitions and pay for
their input/output representations. The supplied ordinary-to-TM2 bridge proves the bounds needed by its consumers;
there is no blanket constant-overhead claim for arbitrary machine models. The seven source statements document
their own model conventions separately from the downstream encoding conversions proved in the adapters.

The formalized conclusion is the near-cubic constant-error theorem. The periodic-top results of version 2 and
other results in version 3 are outside this main-theorem certificate. Names such as `NearCubicWires` occur in included code shared with earlier
formalizations; they do not change the theorem stated in `Statement.lean`.

## Paper, provenance and license

The current [paper source](paper/paper.tex) is version 3 (October 28, 2026), SHA-256
`a9010ba2a94e6f27a767a30eaacdc96c5664bbc342f98e12716cf3012c0da8ca`.
[Version 1](https://doi.org/10.5281/zenodo.23224160) and
[version 2](https://doi.org/10.5281/zenodo.23405983) are archival releases. Citations to those versions should not
be read as references to the current source's line numbers.

Generative-AI models were used substantively in the paper and formalization; see the paper's AI methodology
statement. Verification relies on the proof checks and mathematical source review, not on trusting those models.

Code is [Apache-2.0](LICENSE), except the [paper, licensed CC BY 4.0](paper/README.md). Quoted passages remain their
authors' work. Cite Dev Nag, *Almost-Everywhere Near-Cubic Gate Lower Bounds for SYM∘THR Circuits*, version 3,
October 28, 2026.
