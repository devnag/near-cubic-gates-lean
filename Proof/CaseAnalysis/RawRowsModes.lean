import Proof.CaseAnalysis.RawRowsWalk
import Proof.Supplier.RowThresholdSelections

/-! Actual symmetric rows and the corrected source's threshold-selection
row use the same occurrence-coordinate count. Multiplicity is retained. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator
open SupplierListPolynomial SupplierListSchedule SupplierWalkBridge SupplierPrime SupplierPrinter SupplierRadix
open RepairRepresentation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem structuralGF2OneHotLookup_length_le
    {populationBound coordinateBound : ℕ}
    (lookup : Fin (populationBound + 1) → Bool)
    (oneHot : Fin (populationBound + 1) → StructuralGF2Polynomial)
    (hbound : ∀ candidate, (oneHot candidate).length ≤ coordinateBound) :
    (structuralGF2OneHotLookup lookup oneHot).length ≤
      (populationBound + 1) * coordinateBound := by
  rw [structuralGF2OneHotLookup, parity_length]
  calc
    (∑ candidate : Fin (populationBound + 1),
        (if lookup candidate then oneHot candidate
          else structuralGF2Zero).length) ≤
        ∑ _candidate : Fin (populationBound + 1), coordinateBound := by
      refine Finset.sum_le_sum ?_
      intro candidate _
      by_cases hlookup : lookup candidate
      · simpa only [hlookup, if_true] using hbound candidate
      · simp [hlookup, structuralGF2Zero]
    _ = (populationBound + 1) * coordinateBound := by
      simp [Finset.sum_const, Finset.card_univ]

theorem structuralCanonicalSymmetricCircuitRow_length_le
    {coordinateBound : ℕ}
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : ℕ)
    (hcoordinate : ∀ candidate,
      (structuralCanonicalOccurrenceListCoordinate
        (symmetricFourfoldOccurrences request) liveScale denominator
        (symmetricCircuitMask request circuitIndex) sample candidate).length ≤
        coordinateBound) :
    (structuralCanonicalSymmetricCircuitRow request liveScale denominator
        circuitIndex sample constantOffset).length ≤
      ((symmetricFourfoldOccurrences request).length + 1) * coordinateBound := by
  unfold structuralCanonicalSymmetricCircuitRow
    structuralCanonicalOccurrenceLookupRow
  exact structuralGF2OneHotLookup_length_le _ _ hcoordinate

theorem structuralCanonicalSymmetricFourfoldRow_length_le
    {coordinateBound : ℕ}
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : Fin request.circuits.length → ℕ)
    (hcoordinate : ∀ (circuitIndex : Fin request.circuits.length) candidate,
      (structuralCanonicalOccurrenceListCoordinate
        (symmetricFourfoldOccurrences request) liveScale denominator
        (symmetricCircuitMask request circuitIndex) sample candidate).length ≤
        coordinateBound) :
    (structuralCanonicalSymmetricFourfoldRow request liveScale denominator
        sample constantOffset).length ≤
      (((symmetricFourfoldOccurrences request).length + 1) * coordinateBound) ^
        request.circuits.length := by
  unfold structuralCanonicalSymmetricFourfoldRow
  refine conjunction_bound _
    fun circuitIndex => ?_
  exact structuralCanonicalSymmetricCircuitRow_length_le request liveScale
    denominator circuitIndex sample (constantOffset circuitIndex)
    (hcoordinate circuitIndex)

theorem structuralGF2ModularRadixRow_length_le
    {digits populationBound coordinateBound : ℕ}
    (modulus offset base : ℕ)
    (oneHot : Fin digits → Fin (populationBound + 1) →
      StructuralGF2Polynomial)
    (hcoordinate : ∀ digit candidate,
      (oneHot digit candidate).length ≤ coordinateBound) :
    (structuralGF2ModularRadixRow modulus offset base oneHot).length ≤
      (populationBound + 1) ^ digits * coordinateBound ^ digits := by
  rw [structuralGF2ModularRadixRow, parity_length]
  calc
    (∑ code : Fin ((populationBound + 1) ^ digits),
      (let tuple :=
        (finFunctionFinEquiv :
          (Fin digits → Fin (populationBound + 1)) ≃
            Fin ((populationBound + 1) ^ digits)).symm code
       if modularTupleAccepts modulus offset base tuple then
         structuralGF2FiniteConjunction fun digit => oneHot digit (tuple digit)
       else structuralGF2Zero).length) ≤
        ∑ _code : Fin ((populationBound + 1) ^ digits),
          coordinateBound ^ digits := by
      apply Finset.sum_le_sum
      intro code _
      dsimp only
      split
      · exact conjunction_bound _
          (fun digit => hcoordinate digit _)
      · simp [structuralGF2Zero]
    _ = (populationBound + 1) ^ digits * coordinateBound ^ digits := by
      simp

def rowCountBase {q : ℕ} (gs : List (SupportedNormalizedGate q)) (L den : ℕ) : ℕ :=
  (gs.length+1)*canonicalOccurrenceCoordinateCompressedRawBound gs L den

theorem symmetric_count
    (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L den : ℕ)
    (seed : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences r) L den)
    (offset : Fin r.circuits.length → ℕ) :
    (structuralCanonicalSymmetricFourfoldRow r L den seed offset).length ≤
      rowCountBase (symmetricFourfoldOccurrences r) L den ^ r.circuits.length := by
  exact structuralCanonicalSymmetricFourfoldRow_length_le r L den seed offset
    (fun i j => structuralCanonicalOccurrenceListCoordinate_length_le_compressed _ L den _ seed j)

theorem coefficient_count {q digits : ℕ} (gs : List (SupportedNormalizedGate q))
    (L den : ℕ) (mask : Finset (Fin gs.length)) (coefficient : Fin gs.length → ℕ)
    (seed : NormalizedOccurrenceListSeed gs L den) (p offset : ℕ) :
    (structuralCanonicalOccurrenceCoefficientRadixRow (digits := digits)
      gs L den mask coefficient seed p offset).length ≤ rowCountBase gs L den ^ digits := by
  unfold structuralCanonicalOccurrenceCoefficientRadixRow
    structuralCanonicalOccurrenceModularRadixRow
  unfold rowCountBase
  rw [mul_pow]
  apply structuralGF2ModularRadixRow_length_le
  intro digit candidate
  exact structuralCanonicalOccurrenceListCoordinate_length_le_compressed
    gs L den _ seed candidate

/-- The repaired selection equation, with no obsolete executable decomposition. -/
def thresholdRow (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : RepairOrdinary.ThresholdRows.Selection a r) (L den p offset : ℕ)
    (seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) L den) :
    StructuralGF2Polynomial :=
  structuralCanonicalOccurrenceCoefficientRadixRow (digits := modulusDigitCount p)
    (thresholdFourfoldOccurrences r) L den Finset.univ
    (fun i => modularCoefficientResidue (RepairOrdinary.ThresholdRows.equation a r sel) p i)
    seed p offset

theorem threshold_count (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : RepairOrdinary.ThresholdRows.Selection a r) (L den p offset : ℕ)
    (seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) L den) :
    (thresholdRow a r sel L den p offset seed).length ≤
      rowCountBase (thresholdFourfoldOccurrences r) L den ^ modulusDigitCount p := by
  exact coefficient_count _ L den _ _ seed p offset

end
end NearCubicWires.RepairSource.CloseoutRawRows
