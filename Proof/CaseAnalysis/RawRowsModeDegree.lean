import Proof.CaseAnalysis.RawRowsMonomials
import Proof.CaseAnalysis.RowsRawLogShape

/-! The actual SYM/THR raw degrees and count budgets fit the checked paper
load expression. The population/child logarithm is kept explicit. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator
open SupplierListPolynomial SupplierListSchedule SupplierWalkBridge SupplierTouching
open RepairRepresentation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem symmetric_degree (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L den : ℕ)
    (seed : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences r) L den)
    (offset : Fin r.circuits.length → ℕ) :
    RawMonomialDegreeAtMost
      (r.circuits.length*coordinateDegree (symmetricFourfoldOccurrences r) L den)
      (structuralCanonicalSymmetricFourfoldRow r L den seed offset) := by
  unfold structuralCanonicalSymmetricFourfoldRow
  apply rawDegree_conjunction
  intro i
  unfold structuralCanonicalSymmetricCircuitRow structuralCanonicalOccurrenceLookupRow
    structuralGF2OneHotLookup
  apply rawDegree_parity
  intro candidate
  split
  · exact rawDegree_coordinate _ L den _ seed candidate
  · exact rawDegree_zero _

theorem coefficient_degree {q digits : ℕ} (gs : List (SupportedNormalizedGate q))
    (L den : ℕ) (mask : Finset (Fin gs.length)) (coefficient : Fin gs.length → ℕ)
    (seed : NormalizedOccurrenceListSeed gs L den) (p offset : ℕ) :
    RawMonomialDegreeAtMost (digits*coordinateDegree gs L den)
      (structuralCanonicalOccurrenceCoefficientRadixRow (digits := digits)
        gs L den mask coefficient seed p offset) := by
  unfold structuralCanonicalOccurrenceCoefficientRadixRow
    structuralCanonicalOccurrenceModularRadixRow structuralGF2ModularRadixRow
  apply rawDegree_parity
  intro code
  dsimp only
  split
  · apply rawDegree_conjunction
    intro digit
    exact rawDegree_coordinate gs L den _ seed _
  · exact rawDegree_zero _

theorem threshold_degree (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : RepairOrdinary.ThresholdRows.Selection a r) (L den p offset : ℕ)
    (seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) L den) :
    RawMonomialDegreeAtMost (modulusDigitCount p*
      coordinateDegree (thresholdFourfoldOccurrences r) L den)
      (thresholdRow a r sel L den p offset seed) :=
  coefficient_degree _ L den _ _ seed p offset

def rowDepth {q : ℕ} (gs : List (SupportedNormalizedGate q)) (L : ℕ) :=
  canonicalGradedDepth (touchingCost (occurrenceSupport gs) (normalizedLiveSet gs L))
def windowSum {q : ℕ} (gs : List (SupportedNormalizedGate q)) (L : ℕ) :=
  ∑ i : Fin (rowDepth gs L), executableGradedWindow
    (touchingCost (occurrenceSupport gs) (normalizedLiveSet gs L)) i

theorem rawDegree_window_sum {depth : ℕ} (window : Fin depth → ℕ) :
    structuralListCoordinateRawDegree depth window gradedTerminalWindow = 2*∑ i,window i := by
  rw [structuralListCoordinateRawDegree_eq_listDegree,listDegree_eq_terminal_add_sum]
  simp only [gradedTerminalWindow,Nat.zero_add,Finset.mul_sum]

theorem coordinateDegree_eq {q : ℕ} (gs : List (SupportedNormalizedGate q)) (L den : ℕ) :
    coordinateDegree gs L den = 2*canonicalWalkLength den*windowSum gs L := by
  unfold coordinateDegree windowSum rowDepth
  dsimp only
  rw [rawDegree_window_sum]
  ring

theorem compressedLog_window_sum (depth pop ell : ℕ) (window : Fin depth → ℕ)
    (hell : natBitLength (2*pop+1) ≤ ell) :
    compressedListCoordinateLogBudget depth pop window gradedTerminalWindow ≤
      RepairOrdinary.CloseoutRowsRawLogShape.baseLog (∑ i,window i) depth ell := by
  have hp : natBitLength (pop+1) ≤ ell :=
    (PolynomialClock.natBitLength_mono (by omega : pop+1 ≤ 2*pop+1)).trans hell
  have h := structuralListCoordinateLogLedger_le_windowSum depth pop window
  have hb : structuralListCoordinateLogLedger depth pop window 0 ≤
      4+depth*ell+6*((∑ i,window i)+depth)*(ell+2) := by
    calc
      _ ≤ _ := h
      _ ≤ _ := by gcongr
  unfold compressedListCoordinateLogBudget
  rw [rawDegree_window_sum]
  change structuralListCoordinateLogLedger depth pop window 0+2*(∑ i,window i)+1 ≤ _
  unfold RepairOrdinary.CloseoutRowsRawLogShape.baseLog
  omega

theorem coordinate_log {q : ℕ} (gs : List (SupportedNormalizedGate q)) (L den ell : ℕ)
    (hell : natBitLength (2*gs.length+1) ≤ ell) :
    canonicalOccurrenceCoordinateCompressedLogBudget gs L den ≤
      RepairOrdinary.CloseoutRowsRawLogShape.coordinateLog (canonicalWalkLength den)
        (windowSum gs L) (rowDepth gs L) ell := by
  have h := compressedLog_window_sum (rowDepth gs L) gs.length ell
    (executableGradedWindow (touchingCost (occurrenceSupport gs) (normalizedLiveSet gs L))) hell
  unfold canonicalOccurrenceCoordinateCompressedLogBudget
    RepairOrdinary.CloseoutRowsRawLogShape.coordinateLog
  change (canonicalWalkLength den+1)+
    (canonicalWalkLength den*(compressedListCoordinateLogBudget (rowDepth gs L) gs.length
      (executableGradedWindow (touchingCost (occurrenceSupport gs) (normalizedLiveSet gs L)))
      gradedTerminalWindow+1)+1) ≤ _
  gcongr
  exact h

theorem rowCount_log {q : ℕ} (gs : List (SupportedNormalizedGate q)) (L den ell : ℕ)
    (hell : natBitLength (2*gs.length+1) ≤ ell) :
    natBitLength (rowCountBase gs L den) ≤ ell+
      RepairOrdinary.CloseoutRowsRawLogShape.coordinateLog (canonicalWalkLength den)
        (windowSum gs L) (rowDepth gs L) ell := by
  have hp : natBitLength (gs.length+1) ≤ ell :=
    (PolynomialClock.natBitLength_mono (by omega : gs.length+1 ≤ 2*gs.length+1)).trans hell
  exact (ValidatorPolynomialDomination.natBitLength_mul_le _ _).trans
    (Nat.add_le_add hp ((canonicalOccurrenceCoordinateCompressedRawBound_bitLength_le gs L den).trans
      (coordinate_log gs L den ell hell)))

end
end NearCubicWires.RepairSource.CloseoutRawRows
