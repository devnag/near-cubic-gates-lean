# 6. Short PCP with an ordinary circuit-construction machine

[Mapping index](README.md) · derived field `shortPCP` · two published premises

[`Assembly.field6Ordinary`](../SourceAdapters/Assembly/Field6Ordinary.lean) proves
`OrdinaryOracleCircuitPCP` from exactly `NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1` and
`NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17`. Their source models are in
[Statement.lean](../Statement.lean). The target is described in
[`Assembly/OrdinaryField.lean`](../SourceAdapters/Assembly/OrdinaryField.lean); its construction algorithm is an
ordinary polynomial-time word function, not an assumed Mathlib TM2 constructor.

For each ordinary verifier V and time function T with n ≤ T(n), assuming V halts within T(n) on all inputs and
witnesses, the theorem supplies a uniform constructor. It reads x and the binary clock T(|x|), each framed, and
writes the exact oracle-circuit word. Its running time and circuit size are polynomial in |x|+log T(|x|).
The circuit has ℓ input bits and ℓ-bit oracle addresses, with 2^ℓ ≤ K T(n) logScale(T(n))^e.

If an accepting witness of length T(n) exists, some oracle makes the circuit false on every input. If no such
witness exists, every oracle makes it true on at least a 1−1/n fraction of inputs. These are the PCP's reject
circuits: their satisfying assignments are rejecting random strings. The assertions use n ≥ 1. The clock is
supplied as input; no unproved efficient algorithm for computing an arbitrary function T is assumed.

## Retained results and their domains

BCGT13 is E. Ben-Sasson, A. Chiesa, D. Genkin and E. Tromer, *On the Concrete Efficiency of
Probabilistically-Checkable Proofs*, [ECCC TR12-045, revision 3](https://eccc.weizmann.ac.il/report/2012/045/),
Theorem 11.1 (p.51), Definition 4.15, Equation (6) (p.53) and the specified RS/VRS verifiers. The pinned PDF has
SHA-256 `9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0`.

The retained theorem is a **faithful specialization to positive soundness exponents** e1 > 0 and e2 > 0,
in addition to Equation (6). Equation (6) alone permits (η,κ₀,γ,μ) = (3,5,2,2), for which e2 = log₂(5/5) = 0
and the printed exponent 1/min(e1,e2) is undefined. The consumer uses only (2,4,0,1), where the two exponents are
log₂(6/5) and log₂(5/3), both positive; this is proved by
`ShortPCP.Verifier.tuple0_positive_exponents` in
[`VerifierJoin.lean`](../SourceAdapters/ShortPCP/VerifierJoin.lean). The source formulas and Equation (6) are
preserved. This is not presented as an exact transcription over every tuple allowed by Equation (6).

The BCGT premise supplies completeness and soundness of the named mathematical verifiers, not a running-time
bound or a RAM reduction. Its documented semantic choices follow Algorithm 12's VRS equation, the vanishing and
interpolation output specifications, least-significant-bit-first subspace indexing, and zero answers for absent
queries. The source's inconsistent pseudocode passages are identified in the retained statement. In particular,
no general numerical bound from Lemma C.1 is assumed; the needed bounds for the chosen tuple are proved.

The second premise is deterministic polynomial-time construction of an irreducible degree-f polynomial over F₂
from unary f ≥ 1, with its f+1 coefficients written constant-first. This is **Algorithm 17, FindIrrPoly**, on
p.124 of the same pinned BCGT source. It cites Shoup's FOCS 1988 Corollary 3.2. Algorithm 17 was checked directly;
the original FOCS corollary was not read. Shoup's author-hosted journal preprint corroborates the algorithm in
Theorem 3.2 (p.8), with polynomial runtime at fixed characteristic; it is not the original corollary locator.
No claim about degree zero or primitive polynomials is imported.

## Proved construction

The [affine constraint model](../SourceAdapters/ACSP/Affine.lean) uses one assignment polynomial and genuine
field-affine neighbors aX+b; its [encoding](../SourceAdapters/ACSP/Encoding.lean) is defined separately. The [RAM-to-constraint assembly](../SourceAdapters/RAMACSP/Assembly.lean) proves its
completeness and soundness; the generator prints the compact instance with a paid ordinary program. It does not
enumerate an exponentially large computation graph for free. The exact model and codecs are part of this proof.

The remaining stages are the single-run verifier and its
[`Time.singleRunTime`](../SourceAdapters/ShortPCP/TimeCells.lean), amplification and masks, the bounded
[computation-to-circuit compiler](../SourceAdapters/Compile/OraclePrintMain.lean), and the final ordinary
constructor in [`ShortPCP.OracleCircuitPCP`](../SourceAdapters/ShortPCP/Assembly.lean). These suppliers discharge
the implementation requirements of `field6Ordinary`; they are not algorithm callbacks left as assumptions.

The current [paper](../paper/paper.tex) labels are `imp:short-pcp`, `app:short-pcp-proof`,
`thm:short-pcp-ours`, `def:acsp` and `thm:embedding`. Murray–Williams' SIAM J. Comput. 2020 Section 5 supplies the
oracle-circuit formulation as mathematical context; it is not a retained premise. The paper's
`rem:bv14-printed` explains the SAT-compression consequence of a stronger printed formulation. That consequence
alone is not a proof that P differs from NP, and that stronger formulation is not assumed here.
