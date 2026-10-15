import Proof.CaseAnalysis.RawRowsModeDegree
import Proof.CaseAnalysis.RowsUniversalLoad
import Proof.CaseAnalysis.FinalThresholdRows

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open scoped BigOperators
open NearCubicWires
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.CloseoutRawRows
open NearCubicWires.RepairSource.CloseoutRowsUniversal

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdRowIdentity

noncomputable section

variable (a : DecompositionAlgorithm)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

/-! ## 1. The printed row IS the estimator's row (A.13.6/A.13.7) -/

/-- **The THR printed-form identity at the CORRECTED source.**  Evaluating the printed polynomial
`thresholdRow a r sel …` (A.13.7's `Q_{g,p,e,f}` at the actual offset `f = f_{g,p}(z)`) on A.2's
coded occurrence-residual variables returns the estimator's tuple row
`canonicalOccurrenceCoefficientRadixRow`, i.e.
`CloseoutFinalC10ThresholdRows.selectionRow`.  No `ExecutableExactDecompositionAlgorithm`. -/
theorem thresholdRow_eq_canonical (liveScale denominator : ℕ) (input : BitInput r.q)
    (sel : ThresholdRows.Selection a r) {cutoff : ℕ} (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable (thresholdFourfoldOccurrences r)
            (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) input index)
        (thresholdRow a r sel liveScale denominator prime.val
          (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
            (ThresholdRows.equation a r sel) prime.val) seed) =
      canonicalOccurrenceCoefficientRadixRow
        (digits := modulusDigitCount prime.val)
        (thresholdFourfoldOccurrences r) liveScale denominator input
        Finset.univ
        (modularCoefficientResidue (ThresholdRows.equation a r sel) prime.val)
        seed prime.val
        (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
          (ThresholdRows.equation a r sel) prime.val) := by
  rw [thresholdRow, evaluateStructuralCanonicalOccurrenceCoefficientRadixRow,
    executableCanonicalOccurrenceCoefficientRadixRow_refines]

/-- The same identity written at the estimator's own name for the tuple row. -/
theorem thresholdRow_eq_selectionRow (liveScale denominator : ℕ) (input : BitInput r.q)
    (sel : ThresholdRows.Selection a r) {cutoff : ℕ} (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable (thresholdFourfoldOccurrences r)
            (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) input index)
        (thresholdRow a r sel liveScale denominator prime.val
          (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
            (ThresholdRows.equation a r sel) prime.val) seed) =
      CloseoutFinalC10ThresholdRows.selectionRow a r liveScale denominator input sel prime seed :=
  thresholdRow_eq_canonical a r liveScale denominator input sel prime seed

/-! ## 2. A.13.8 — the per-row preprocessing budget, with NO `|G|` factor -/

/-- **A.13.8 (`paper.tex:3127–3140`) for the corrected source.**  The printed row for ONE external
label `(g,p,e,f)` has at most `rowCountBase ^ modulusDigitCount p` internal radix tuples and raw
monomial degree at most `modulusDigitCount p * coordinateDegree`.  Both exponents are the paper's
`\tau`; neither mentions `Fintype.card (ThresholdRows.Selection a r)`. -/
theorem thresholdRow_degree_le (sel : ThresholdRows.Selection a r)
    (liveScale denominator : ℕ) {cutoff : ℕ} (prime : PrimeIndex cutoff) (offset : ℕ)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) :
    (thresholdRow a r sel liveScale denominator prime.val offset seed).length ≤
        rowCountBase (thresholdFourfoldOccurrences r) liveScale denominator ^
          modulusDigitCount prime.val ∧
      RawMonomialDegreeAtMost
        (modulusDigitCount prime.val *
          coordinateDegree (thresholdFourfoldOccurrences r) liveScale denominator)
        (thresholdRow a r sel liveScale denominator prime.val offset seed) :=
  ⟨threshold_count a r sel liveScale denominator prime.val offset seed,
    threshold_degree a r sel liveScale denominator prime.val offset seed⟩

/-- **The printed THR row fits the printer's digit width.**  This is the literal `hmon` of
`C10SupplierRowInput.rowInput` (`Proof/CaseAnalysis/FinalSupplierRowInput.lean`) and hence the `w`
of `raw_cuts_gate` (`Proof/CaseAnalysis/RawRowsLoad.lean`), at the exponent
`modulusDigitCount prime.val` = A.13.8's `\tau`.  `Fintype.card (ThresholdRows.Selection a r)` does
not occur: the paper's `g` is an EXTERNAL label here, so it costs `T_prep`, not `s_gen`
(`paper.tex:3216–3219`). -/
theorem thresholdRow_printed_fit (sel : ThresholdRows.Selection a r)
    (live : Finset (Fin r.q)) (liveScale denominator ell childBits : ℕ)
    {cutoff : ℕ} (prime : PrimeIndex cutoff) (offset : ℕ)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator)
    (hell : natBitLength (2 * (thresholdFourfoldOccurrences r).length + 1) ≤ ell)
    (hchildren : ∀ i : Fin (pool live (thresholdFourfoldOccurrences r)).length,
      (ExtDecompositionBatch.children a
        ((pool live (thresholdFourfoldOccurrences r)).get i)).length ≤ 2 ^ childBits) :
    (lower a live (thresholdFourfoldOccurrences r)
        (thresholdRow a r sel liveScale denominator prime.val offset seed)).length <
      2 ^ actualWidth (thresholdFourfoldOccurrences r) liveScale denominator
        (modulusDigitCount prime.val) ell (childBits + 1) :=
  row_digit_fit a live (thresholdFourfoldOccurrences r) liveScale denominator
    (modulusDigitCount prime.val) ell childBits _
    (threshold_count a r sel liveScale denominator prime.val offset seed)
    (threshold_degree a r sel liveScale denominator prime.val offset seed) hell hchildren

/-! ## 3. Where the paper's label `g` lives: OUTSIDE the printed row -/

/-- One prime's row VALUE is the aggregation, over the paper's external label `g`, of the
EVALUATIONS of `Fintype.card (ThresholdRows.Selection a r)` separate printed rows.  A.13.10 does the
`g`-sum on the tables `T_{g,p,e,f}(z)`, not inside `Q_{g,p,e,f}`; this is that step. -/
theorem primeRow_eq_printedDisjunction (liveScale denominator : ℕ) (input : BitInput r.q)
    {cutoff : ℕ} (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) :
    CloseoutFinalC10ThresholdRows.primeRow a r liveScale denominator input prime seed =
      finiteBoolDisjunction (fun sel : ThresholdRows.Selection a r =>
        evaluateStructuralGF2
          (encodedFiniteBooleanAssignment fun index =>
            occurrenceResidualVariable (thresholdFourfoldOccurrences r)
              (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) input index)
          (thresholdRow a r sel liveScale denominator prime.val
            (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
              (ThresholdRows.equation a r sel) prime.val) seed)) := by
  unfold CloseoutFinalC10ThresholdRows.primeRow
  exact congrArg finiteBoolDisjunction
    (funext fun sel =>
      (thresholdRow_eq_selectionRow a r liveScale denominator input sel prime seed).symm)

/-- The complete THR row at one external label `(p,e)` is the `g`-aggregation of the EVALUATIONS of
`Fintype.card (ThresholdRows.Selection a r)` separate printed rows.  A.13.10 (`paper.tex:3178–3195`)
does the `g`-sum on the tables `T_{g,p,e,f_{g,p}(z)}(z)`, outside `Q_{g,p,e,f}`; this is that step. -/
theorem fourfoldRow_eq_printedDisjunction (liveScale target : ℕ) (input : BitInput r.q)
    (sample : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) ×
      NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
        (CloseoutFinalC10ThresholdRows.listDenominator a r target)) :
    CloseoutFinalC10ThresholdRows.fourfoldRow a r liveScale target input sample =
      finiteBoolDisjunction (fun sel : ThresholdRows.Selection a r =>
        evaluateStructuralGF2
          (encodedFiniteBooleanAssignment fun index =>
            occurrenceResidualVariable (thresholdFourfoldOccurrences r)
              (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) input index)
          (thresholdRow a r sel liveScale
            (CloseoutFinalC10ThresholdRows.listDenominator a r target) sample.1.val
            (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
              (ThresholdRows.equation a r sel) sample.1.val) sample.2)) :=
  primeRow_eq_printedDisjunction a r liveScale
    (CloseoutFinalC10ThresholdRows.listDenominator a r target) input sample.1 sample.2

/-- **THE TASK-ZERO RECEIPT.**  The external row count of `thresholdRows` enumerates the prime `p`
and the amplified-list seed `e` and NOTHING else: it carries no
`Fintype.card (ThresholdRows.Selection a r)` factor.  Together with
`fourfoldRow_eq_printedDisjunction` (the paper's `g` is aggregated OUTSIDE the printed polynomial)
and `thresholdRow_degree_le` (each printed polynomial's budget has exponent
`modulusDigitCount prime.val`, never `|G|`), this is the Lean statement of
`paper.tex:3216–3219`: the external labels `(g,p,e,f)` are paid by `T_prep`, not by `s_gen`.  The
normalisation matches A.13.10's `1/(|\mathcal P_q||\mathcal E|2^q)`, which likewise has no
`|\mathcal G|`. -/
theorem thresholdRows_rowCount (spectrum : SourceInterfaces.ExpanderSpectrumContract)
    (theta : SourceInterfaces.PrimeThetaBoundContract)
    (liveScale : ℕ) (targetDenominator : ℕ → ℕ) :
    (CloseoutFinalC10ThresholdRows.thresholdRows spectrum theta a liveScale
        targetDenominator).rowCount r =
      Fintype.card
        (PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r (targetDenominator r.q)) ×
          NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
            (CloseoutFinalC10ThresholdRows.listDenominator a r (targetDenominator r.q))) := by
  simp only [CloseoutFinalC10ThresholdRows.thresholdRows]

end

end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdRowIdentity
