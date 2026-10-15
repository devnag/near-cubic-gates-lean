import Proof.CaseAnalysis.RawRowsLog

/-! The same masked list and powered-walk raw row, with its seed-uniform
logarithmic census. Only the existing constructor recurrence is used. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierListPolynomial SupplierListSchedule
open SupplierToeplitz SupplierToeplitzCore SupplierPipeline SupplierEstimator
open SupplierWalk SupplierWalkBridge SupplierTouching
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem structuralMaskedCoordinate_length_le_one
    {population : ℕ} (mask : Finset (Fin population))
    (coordinate : Fin population) :
    (structuralMaskedCoordinate mask coordinate).length ≤ 1 := by
  unfold structuralMaskedCoordinate
  split <;> simp [structuralGF2Variable, structuralGF2Zero]

theorem structuralListLiteralAtom_length_le_two
    {rank depth population : ℕ}
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (code : ℕ) :
    (structuralListLiteralAtom (depth := depth) mask label seed code).length ≤
      2 := by
  generalize hdecode : decodeListLiteralVariable depth population code = decoded
  cases decoded with
  | none => simp [structuralListLiteralAtom, hdecode, structuralGF2Zero]
  | some literal =>
    cases literal with
    | terminal coordinate =>
        simp only [structuralListLiteralAtom, hdecode]
        split
        · exact (structuralMaskedCoordinate_length_le_one mask coordinate).trans
            (by norm_num)
        · simp [structuralGF2Zero]
    | delta level slot =>
        simp only [structuralListLiteralAtom, hdecode]
        cases hslot : decodeListLiteralSlot slot with
        | inl coordinate =>
            simp only
            split
            · exact
                (structuralMaskedCoordinate_length_le_one mask coordinate).trans
                  (by norm_num)
            · simp [structuralGF2Zero]
        | inr coordinate =>
            simp only
            split
            · have hcoordinate :=
                structuralMaskedCoordinate_length_le_one mask coordinate
              unfold structuralGF2Not structuralGF2Add structuralGF2One
              simp only [List.length_append, List.length_cons,
                List.length_nil]
              omega
            · simp [structuralGF2Zero]

theorem structuralMaskedListCoordinate_length_le_compressed
    {rank depth population : ℕ}
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank) (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    (structuralMaskedListCoordinate mask label seed window terminalWindow candidate).length ≤
      structuralListCoordinateRawLedger depth population window terminalWindow *
        2 ^ structuralListCoordinateRawDegree depth window terminalWindow := by
  exact (RepairOrdinary.CloseoutRowsRawOccurrenceBound.substitute_bound
    (structuralListLiteralAtom (depth := depth) mask label seed) 2
    (structuralListCoordinateRawDegree depth window terminalWindow) (by omega)
    (structuralListLiteralAtom_length_le_two mask label seed) _
    (rawDegree_structuralListPolynomialVector label seed window terminalWindow candidate)).trans
    (Nat.mul_le_mul_right _
      (structuralListPolynomialVector_length_le label seed window terminalWindow candidate))

theorem structuralGF2BooleanSelector_length_le
    {arity atomBound : ℕ} (bits : Fin arity → StructuralGF2Polynomial)
    (target : BitInput arity) (hbits : ∀ i, (bits i).length ≤ atomBound) :
    (structuralGF2BooleanSelector bits target).length ≤ (atomBound + 1)^arity := by
  have h := RepairOrdinary.CloseoutRowsRawOccurrenceBound.product_bound (atomBound+1)
    (List.ofFn (fun i => if target i = true then bits i else structuralGF2Not (bits i))) (by
      intro p hp
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
      split
      · exact (hbits i).trans (Nat.le_succ _)
      · have hi := hbits i
        simp only [structuralGF2Not,structuralGF2Add,structuralGF2One,
          List.length_append,List.length_cons,List.length_nil]
        omega)
  simpa only [structuralGF2BooleanSelector,List.length_ofFn] using h

theorem structuralGF2TruthTable_length_le
    {arity atomBound : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial)
    (function : BitInput arity → Bool)
    (hbits : ∀ index, (bits index).length ≤ atomBound) :
    (structuralGF2TruthTable bits function).length ≤
      2 ^ arity * (atomBound + 1) ^ arity := by
  unfold structuralGF2TruthTable
  rw [parity_length]
  calc
    (∑ code : Fin (2 ^ arity),
      (if function (structuralTruthAssignment arity code) then
        structuralGF2BooleanSelector bits
          (structuralTruthAssignment arity code)
       else structuralGF2Zero).length) ≤
        ∑ _code : Fin (2 ^ arity), (atomBound + 1) ^ arity := by
      apply Finset.sum_le_sum
      intro code _
      split
      · exact structuralGF2BooleanSelector_length_le bits _ hbits
      · simp [structuralGF2Zero]
    _ = 2 ^ arity * (atomBound + 1) ^ arity := by simp

theorem structuralGF2BitMajority_length_le
    {arity atomBound : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial)
    (hbits : ∀ index, (bits index).length ≤ atomBound) :
    (structuralGF2BitMajority bits).length ≤
      2 ^ arity * (atomBound + 1) ^ arity := by
  unfold structuralGF2BitMajority
  exact structuralGF2TruthTable_length_le bits compiledBitMajority hbits

def compressedListCoordinateRawBound
    (depth population : ℕ) (window : Fin depth → ℕ)
    (terminalWindow : ℕ) : ℕ :=
  structuralListCoordinateRawLedger depth population window terminalWindow *
    2 ^ structuralListCoordinateRawDegree depth window terminalWindow

private theorem capBlind_natBitLength_two_pow (exponent : ℕ) :
    natBitLength (2 ^ exponent) = exponent + 1 := by
  unfold natBitLength
  rw [Nat.log_pow (by omega)]

private theorem capBlind_natBitLength_succ_le (value : ℕ) :
    natBitLength (value + 1) ≤ natBitLength value + 1 := by
  have hlt : value < 2 ^ natBitLength value := by
    simpa [natBitLength] using
      Nat.lt_pow_succ_log_self (b := 2) (by omega) value
  have hmono : Nat.log 2 (value + 1) ≤
      Nat.log 2 (2 ^ natBitLength value) := Nat.log_mono_right hlt
  unfold natBitLength at hmono ⊢
  rw [Nat.log_pow (by omega)] at hmono
  omega

def compressedListCoordinateLogBudget
    (depth population : ℕ) (window : Fin depth → ℕ)
    (terminalWindow : ℕ) : ℕ :=
  structuralListCoordinateLogLedger depth population window terminalWindow +
    structuralListCoordinateRawDegree depth window terminalWindow + 1

/-- This is the key compression step: the explicit raw substitution ledger
contributes its additive log ledger, while the `2^degree` substitution factor
contributes exactly `degree+1` bits. -/
theorem compressedListCoordinateRawBound_bitLength_le
    (depth population : ℕ) (window : Fin depth → ℕ)
    (terminalWindow : ℕ) :
    natBitLength
        (compressedListCoordinateRawBound depth population window
          terminalWindow) ≤
      compressedListCoordinateLogBudget depth population window
        terminalWindow := by
  unfold compressedListCoordinateRawBound compressedListCoordinateLogBudget
  have hmul := ValidatorPolynomialDomination.natBitLength_mul_le
    (structuralListCoordinateRawLedger depth population window terminalWindow)
    (2 ^ structuralListCoordinateRawDegree depth window terminalWindow)
  have hraw := structuralListCoordinateRawLedger_bitLength_le depth population
    window terminalWindow
  rw [capBlind_natBitLength_two_pow] at hmul
  omega

theorem structuralMaskedWalkListCoordinate_length_le_compressed
    {rank depth population t : ℕ}
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (sample : MargulisWalkSample
      (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population + 1)) :
    (structuralMaskedWalkListCoordinate mask label window terminalWindow
        sample candidate).length ≤
      2 ^ t *
        (compressedListCoordinateRawBound depth population window
          terminalWindow + 1) ^ t := by
  unfold structuralMaskedWalkListCoordinate
  apply structuralGF2BitMajority_length_le
  intro time
  unfold compressedListCoordinateRawBound
  exact structuralMaskedListCoordinate_length_le_compressed mask label
    (toeplitzWalkEncoding rank (sample.vertex time)).1 window terminalWindow
    candidate

def canonicalOccurrenceCoordinateCompressedRawBound
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) : ℕ :=
  let activeBound := touchingCost (occurrenceSupport occurrences)
    (normalizedLiveSet occurrences liveScale)
  let depth := canonicalGradedDepth activeBound
  let window := executableGradedWindow (depth := depth) activeBound
  2 ^ canonicalWalkLength denominator *
    (compressedListCoordinateRawBound depth occurrences.length window
      gradedTerminalWindow + 1) ^ canonicalWalkLength denominator

def canonicalOccurrenceCoordinateCompressedLogBudget
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) : ℕ :=
  let activeBound := touchingCost (occurrenceSupport occurrences)
    (normalizedLiveSet occurrences liveScale)
  let depth := canonicalGradedDepth activeBound
  let window := executableGradedWindow (depth := depth) activeBound
  let walk := canonicalWalkLength denominator
  (walk + 1) +
    (walk *
      (compressedListCoordinateLogBudget depth occurrences.length window
        gradedTerminalWindow + 1) + 1)

theorem canonicalOccurrenceCoordinateCompressedRawBound_bitLength_le
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) :
    natBitLength
        (canonicalOccurrenceCoordinateCompressedRawBound occurrences liveScale
          denominator) ≤
      canonicalOccurrenceCoordinateCompressedLogBudget occurrences liveScale
        denominator := by
  let activeBound := touchingCost (occurrenceSupport occurrences)
    (normalizedLiveSet occurrences liveScale)
  let depth := canonicalGradedDepth activeBound
  let window := executableGradedWindow (depth := depth) activeBound
  let walk := canonicalWalkLength denominator
  let coordinate := compressedListCoordinateRawBound depth occurrences.length
    window gradedTerminalWindow
  have hmul := ValidatorPolynomialDomination.natBitLength_mul_le
    (2 ^ walk) ((coordinate + 1) ^ walk)
  have hpow := ValidatorPolynomialDomination.natBitLength_pow_le
    (coordinate + 1) walk
  have hcoordinate := compressedListCoordinateRawBound_bitLength_le depth
    occurrences.length window gradedTerminalWindow
  have hsucc := capBlind_natBitLength_succ_le coordinate
  change natBitLength coordinate ≤
    compressedListCoordinateLogBudget depth occurrences.length window
      gradedTerminalWindow at hcoordinate
  have hsuccBound : natBitLength (coordinate + 1) ≤
      compressedListCoordinateLogBudget depth occurrences.length window
        gradedTerminalWindow + 1 :=
    hsucc.trans (Nat.add_le_add_right hcoordinate 1)
  have hpowBound : natBitLength ((coordinate + 1) ^ walk) ≤
      walk *
        (compressedListCoordinateLogBudget depth occurrences.length window
          gradedTerminalWindow + 1) + 1 :=
    hpow.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left walk hsuccBound) 1)
  change natBitLength (2 ^ walk * (coordinate + 1) ^ walk) ≤ _
  change _ ≤ (walk + 1) +
    (walk *
      (compressedListCoordinateLogBudget depth occurrences.length window
        gradedTerminalWindow + 1) + 1)
  calc
    natBitLength (2 ^ walk * (coordinate + 1) ^ walk) ≤
        natBitLength (2 ^ walk) +
          natBitLength ((coordinate + 1) ^ walk) := hmul
    _ = (walk + 1) + natBitLength ((coordinate + 1) ^ walk) := by
      rw [capBlind_natBitLength_two_pow]
    _ ≤ (walk + 1) +
        (walk *
          (compressedListCoordinateLogBudget depth occurrences.length window
            gradedTerminalWindow + 1) + 1) :=
      Nat.add_le_add_left hpowBound _

theorem structuralCanonicalOccurrenceListCoordinate_length_le_compressed
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (mask : Finset (Fin occurrences.length))
    (sample : NormalizedOccurrenceListSeed occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1)) :
    (structuralCanonicalOccurrenceListCoordinate occurrences liveScale
        denominator mask sample candidate).length ≤
      canonicalOccurrenceCoordinateCompressedRawBound occurrences liveScale
        denominator := by
  let activeBound := touchingCost (occurrenceSupport occurrences)
    (normalizedLiveSet occurrences liveScale)
  unfold structuralCanonicalOccurrenceListCoordinate
    canonicalOccurrenceCoordinateCompressedRawBound
  exact structuralMaskedWalkListCoordinate_length_le_compressed mask
    (canonicalGradedLabel occurrences.length activeBound)
    (executableGradedWindow
      (depth := canonicalGradedDepth activeBound) activeBound)
    gradedTerminalWindow sample candidate

end
end NearCubicWires.RepairSource.CloseoutRawRows
