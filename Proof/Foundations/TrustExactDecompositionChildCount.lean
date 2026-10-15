import Proof.Foundations.EncodedListLengthWidthBound
import Proof.Foundations.VerifiedLinker

/-!
# The decomposition child count is derived, not assumed

`ExecutableDisjointExactDecompositionContract` used to carry a second clause,

```
∀ request, (algorithm.run request.gate).children.length ≤ algorithm.runner.budget request
```

alongside the existence of the decomposition algorithm itself.  That clause is
not an independent fact about the imported source: it is forced by the runner
ABI already fixed in `ExecutableInterfaces`, because the child list is decoded
from the runner's single natural-number output.

The chain proved below is

* the decoded child list is a `List.map` over the canonical encoded spine, so
  its length is `CanonicalEncodedListLengthProgram.encodedListLength` of the
  output code;
* `EncodedListLengthWidthBound.encodedListLength_le_natBitLength` bounds that
  spine length by the binary width of the output code;
* `VerifiedLinker.run_output_bounded`, applied to
  `PolynomialNatProgram.run_eq_execute`, bounds that width by the runner's own
  polynomial budget.

Consequently the published contract only has to supply the algorithm.  This
module also re-homes `executableDisjointDecomposition_implies_semantic`, which
needs the derived bound and therefore cannot stay upstream in
`ExecutableInterfaces` (both `EncodedListLengthWidthBound` and `VerifiedLinker`
import that module).  The declaration keeps its fully qualified name, so no
consumer is renamed.

Manuscript correspondence: the quantitative half of the decomposition is
Appendix A.12's erratum-safe threshold-conversion lemma, `paper.tex:2576-2696`,
which the manuscript replays locally precisely because CW19's printed Lemma 48
proof contains three identified errors and the manuscript "imports no one of
those three literal claims" (`paper.tex:2698-2705`).  Nothing below imports
CW19; the bound is discharged from the interpreter ABI.
-/

namespace NearCubicWires.ExecutableInterfaces

open NearCubicWires
open NearCubicWires.CanonicalEncodedListLengthProgram
open NearCubicWires.EncodedListLengthWidthBound
open NearCubicWires.SourceInterfaces

/-- Spine-length identity at the exact-gate payload type.  Same induction as
`CanonicalEncodedListLengthProgram.encodedListLength_eq_decode`; only the
`Encodable` instance differs. -/
theorem encodedListLength_eq_decode_exactGates (code : ℕ) :
    encodedListLength code =
      ((Encodable.decode code : Option (List (List ℤ × ℤ))).getD []).length := by
  induction code using encodedListLength.induct with
  | case1 =>
      simp [encodedListLength]
  | case2 spine inductionHypothesis =>
      simp [encodedListLength, inductionHypothesis, Nat.add_comm]

/-- `decodeExactThresholdGates` maps over that spine, so it does not move the
length. -/
theorem decodeExactThresholdGates_length (n code : ℕ) :
    (decodeExactThresholdGates n code).length = encodedListLength code := by
  unfold decodeExactThresholdGates
  simp [encodedListLength_eq_decode_exactGates]

/-- **The child count is bounded by the runner's own budget, with no source
assumption.**  This is the clause the published contract used to carry. -/
theorem ExecutableExactDecompositionAlgorithm.children_length_le_budget
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : ExactDecompositionRequest) :
    (algorithm.run request.gate).children.length ≤
      algorithm.runner.budget request := by
  have hchildren :
      (algorithm.run request.gate).children =
        decodeExactThresholdGates request.arity
          (algorithm.runner.execute request) := rfl
  have houtput :
      natBitLength (algorithm.runner.execute request) ≤
        algorithm.runner.budget request :=
    NearCubicWires.VerifiedLinker.run_output_bounded
      (algorithm.runner.run_eq_execute request)
  rw [hchildren, decodeExactThresholdGates_length]
  exact le_trans
    (encodedListLength_le_natBitLength (algorithm.runner.execute request))
    houtput

/-- **The trust-base statement for this row, as a checked equivalence.**

The published field is now `Nonempty ExecutableExactDecompositionAlgorithm`.
This proves the weakening lost nothing: it is equivalent to the retired
two-clause form `LegacyDisjointExactDecompositionContract`, because the
child-count clause is a theorem about the fixed `NPOracleProgram` interpreter
rather than an assumption about the imported source.

Appendix A.12 (`paper.tex:2576-2696`) proves a *strictly sharper* statement — a
disjoint OR of at most `max{1, n·L̄}` exact integer equations with explicit
coefficient and target envelopes, constructible in time polynomial in its
explicit output description.  The interface never needed it. -/
theorem executableDisjointExactDecomposition_iff_legacy :
    ExecutableDisjointExactDecompositionContract ↔
      LegacyDisjointExactDecompositionContract := by
  constructor
  · rintro ⟨algorithm⟩
    exact ⟨algorithm,
      ExecutableExactDecompositionAlgorithm.children_length_le_budget algorithm⟩
  · rintro ⟨algorithm, _⟩
    exact ⟨algorithm⟩

/-- Semantic projection of the published decomposition row.  The child-count
and step bounds come from the derivation above rather than from the contract,
at coefficient `algorithm.runner.coefficient` and degree
`algorithm.runner.degree`. -/
theorem executableDisjointDecomposition_implies_semantic :
    ExecutableDisjointExactDecompositionContract →
      DisjointExactDecompositionContract := by
  rintro ⟨algorithm⟩
  refine ⟨algorithm.toSemantic, algorithm.runner.coefficient,
    algorithm.runner.degree, algorithm.runner.coefficientPositive, ?_⟩
  intro n gate
  let request : ExactDecompositionRequest := ⟨n, gate⟩
  refine ⟨le_rfl, ?_⟩
  simpa [ExecutableExactDecompositionAlgorithm.toSemantic,
    ExactDecompositionRequest.measure, PolynomialNatProgram.budget,
    polynomialBudget, request] using
      ExecutableExactDecompositionAlgorithm.children_length_le_budget
        algorithm request

end NearCubicWires.ExecutableInterfaces
