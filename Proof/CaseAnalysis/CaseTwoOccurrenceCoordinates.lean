import Proof.MachineModel.CaseTwoOccurrenceProgram

/-!
# The scheduled Case-2 occurrence coordinates as one natural code

`CaseTwoOccurrenceSpecification.caseTwoSeed_apply_executable` evaluates the
published factory at `caseTwoOccurrenceCoordinates`, which drops the two
scheduled padding axes from the requested seed point.  Both drops —
`projectPaddedSystematicOccurrenceInput` on the input axis and
`projectPaddedOccurrenceInput` on the clause axis — are plain index gathers:
each coordinate of the result is one coordinate of the request.

This module reads that gather off a single natural code.  The three windows
involved are exactly the ones the executable stack already has:

* the low input window, `bitSlice 0 _`, also computed by
  `BitInputPrefixProgram.bitInputPrefixProgram`;
* the interior clause window, `bitSlice`, computed by
  `CanonicalBitSliceProgram.bitSliceProgram`;
* the single occurrence position digit, one `testBit`.

`nativeOccurrenceCode` repacks those three windows into the occurrence ABI of
`CaseTwoOccurrenceProgram`, and `caseTwoOccurrenceCoordinates_prefixView` is
the exact identification.  Combined with
`CaseTwoOccurrenceEvaluation.executableOccurrenceValue_prefixView` and the
contract `caseTwoSeed_apply_executable`, this yields the executable seed bit at
every scheduled Case-2 coordinate.
-/

namespace NearCubicWires.CaseTwoOccurrenceCoordinates

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-! ## 1. Digit composition of two adjacent blocks -/

private theorem testBit_add_mul_low {low high offset index : ℕ}
    (hlow : low < 2 ^ offset) (hindex : index < offset) :
    (low + 2 ^ offset * high).testBit index = low.testBit index := by
  have hmod : (low + 2 ^ offset * high) % 2 ^ offset = low := by
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hlow
  calc
    (low + 2 ^ offset * high).testBit index =
        (decide (index < offset) &&
          (low + 2 ^ offset * high).testBit index) := by
      simp [hindex]
    _ = ((low + 2 ^ offset * high) % 2 ^ offset).testBit index := by
      rw [Nat.testBit_mod_two_pow]
    _ = low.testBit index := by rw [hmod]

private theorem testBit_add_mul_high {low high offset index : ℕ}
    (hlow : low < 2 ^ offset) (hindex : offset ≤ index) :
    (low + 2 ^ offset * high).testBit index =
      high.testBit (index - offset) := by
  have hdiv : (low + 2 ^ offset * high) / 2 ^ offset = high := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos offset),
      Nat.div_eq_of_lt hlow]
    omega
  have hshift :
      ((low + 2 ^ offset * high) >>> offset).testBit (index - offset) =
        (low + 2 ^ offset * high).testBit (offset + (index - offset)) :=
    Nat.testBit_shiftRight (low + 2 ^ offset * high)
  rw [Nat.shiftRight_eq_div_pow, hdiv] at hshift
  rw [hshift, show offset + (index - offset) = index by omega]

/-! ## 2. The native occurrence code -/

theorem bitSlice_lt (offset width value : ℕ) :
    bitSlice offset width value < 2 ^ width :=
  Nat.mod_lt _ (Nat.two_pow_pos width)

/-- The requested occurrence point repacked into the native occurrence ABI:
the low input window, then the interior clause window scanned at the padded
input offset, then the single occurrence position digit. -/
def nativeOccurrenceCode
    (nativeInputBits paddedInputBits nativeClauseBits paddedClauseBits
      code : ℕ) : ℕ :=
  bitSlice 0 nativeInputBits code +
    2 ^ nativeInputBits * bitSlice paddedInputBits nativeClauseBits code +
      2 ^ (nativeInputBits + nativeClauseBits) *
        (code.testBit (paddedInputBits + paddedClauseBits)).toNat

private theorem nativeOccurrenceCode_nested
    (nativeInputBits paddedInputBits nativeClauseBits paddedClauseBits
      code : ℕ) :
    nativeOccurrenceCode nativeInputBits paddedInputBits nativeClauseBits
        paddedClauseBits code =
      bitSlice 0 nativeInputBits code +
        2 ^ nativeInputBits *
          (bitSlice paddedInputBits nativeClauseBits code +
            2 ^ nativeClauseBits *
              (code.testBit (paddedInputBits + paddedClauseBits)).toNat) := by
  unfold nativeOccurrenceCode
  rw [pow_add]
  ring

theorem testBit_nativeOccurrenceCode_input
    (nativeInputBits paddedInputBits nativeClauseBits paddedClauseBits
      code index : ℕ) (hindex : index < nativeInputBits) :
    (nativeOccurrenceCode nativeInputBits paddedInputBits nativeClauseBits
        paddedClauseBits code).testBit index =
      code.testBit index := by
  rw [nativeOccurrenceCode_nested]
  rw [testBit_add_mul_low (bitSlice_lt 0 nativeInputBits code) hindex]
  rw [bitSlice, Nat.testBit_mod_two_pow]
  simp [hindex]

theorem testBit_nativeOccurrenceCode_clause
    (nativeInputBits paddedInputBits nativeClauseBits paddedClauseBits
      code index : ℕ) (hlow : nativeInputBits ≤ index)
    (hhigh : index < nativeInputBits + nativeClauseBits) :
    (nativeOccurrenceCode nativeInputBits paddedInputBits nativeClauseBits
        paddedClauseBits code).testBit index =
      code.testBit (paddedInputBits + (index - nativeInputBits)) := by
  rw [nativeOccurrenceCode_nested]
  rw [testBit_add_mul_high (bitSlice_lt 0 nativeInputBits code) hlow]
  rw [testBit_add_mul_low
    (bitSlice_lt paddedInputBits nativeClauseBits code) (by omega)]
  have hwindow : index - nativeInputBits < nativeClauseBits := by omega
  rw [bitSlice, Nat.testBit_mod_two_pow]
  simp [hwindow, Nat.testBit_shiftRight]

theorem testBit_nativeOccurrenceCode_position
    (nativeInputBits paddedInputBits nativeClauseBits paddedClauseBits
      code : ℕ) :
    (nativeOccurrenceCode nativeInputBits paddedInputBits nativeClauseBits
          paddedClauseBits code).testBit
        (nativeInputBits + nativeClauseBits) =
      code.testBit (paddedInputBits + paddedClauseBits) := by
  rw [nativeOccurrenceCode_nested]
  rw [testBit_add_mul_high (bitSlice_lt 0 nativeInputBits code)
    (by omega)]
  rw [show nativeInputBits + nativeClauseBits - nativeInputBits =
    nativeClauseBits by omega]
  rw [testBit_add_mul_high
    (bitSlice_lt paddedInputBits nativeClauseBits code) (le_refl _)]
  rw [Nat.sub_self]
  cases code.testBit (paddedInputBits + paddedClauseBits) <;> rfl

/-! ## 3. Both padding drops are one digit window -/

theorem projectPaddedOccurrence_prefixView
    {nativeInputBits paddedInputBits nativeClauseBits paddedClauseBits : ℕ}
    (hinput : nativeInputBits ≤ paddedInputBits)
    (hclause : nativeClauseBits ≤ paddedClauseBits) (code : ℕ) :
    projectPaddedOccurrenceInput hclause
        (projectPaddedSystematicOccurrenceInput hinput
          (bitInputPrefixView (paddedInputBits + paddedClauseBits + 1)
            code)) =
      bitInputPrefixView (nativeInputBits + nativeClauseBits + 1)
        (nativeOccurrenceCode nativeInputBits paddedInputBits nativeClauseBits
          paddedClauseBits code) := by
  funext index
  unfold projectPaddedOccurrenceInput projectPaddedSystematicOccurrenceInput
    bitInputPrefixView
  by_cases hinterior : index.val < nativeInputBits + nativeClauseBits
  · rw [dif_pos hinterior]
    by_cases hlow : index.val < nativeInputBits
    · rw [dif_pos hlow]
      exact
        (testBit_nativeOccurrenceCode_input nativeInputBits paddedInputBits
          nativeClauseBits paddedClauseBits code index.val hlow).symm
    · rw [dif_neg hlow]
      exact
        (testBit_nativeOccurrenceCode_clause nativeInputBits paddedInputBits
          nativeClauseBits paddedClauseBits code index.val (by omega)
          hinterior).symm
  · rw [dif_neg hinterior]
    rw [dif_neg (by omega : ¬ nativeInputBits + paddedClauseBits <
      nativeInputBits)]
    have hposition : index.val = nativeInputBits + nativeClauseBits := by
      have hlt := index.isLt
      omega
    have hbit :=
      testBit_nativeOccurrenceCode_position nativeInputBits paddedInputBits
        nativeClauseBits paddedClauseBits code
    rw [← hposition] at hbit
    rw [hbit]
    simp

/-! ## 4. The scheduled Case-2 instance -/

/-- The scheduled seed point read as one natural code. -/
theorem scheduledPoint_prefixView
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (requiredDegree sourceIndex : ℕ)
    (point :
      BitInput (seedArity outer pcppSource requiredDegree sourceIndex)) :
    (fun index :
        Fin (widthEnvelope outer (sourceLength sourceIndex) +
          clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
            (sourceLength sourceIndex) + 1) =>
      point
        (Fin.cast
          (seedArity_eq_envelope outer pcppSource requiredDegree
            sourceIndex).symm index)) =
      bitInputPrefixView
        (widthEnvelope outer (sourceLength sourceIndex) +
          clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
            (sourceLength sourceIndex) + 1)
        (encodeBitInput point) := by
  rw [bitInputPrefixView_encodeBitInput point
    (le_of_eq
      (seedArity_eq_envelope outer pcppSource requiredDegree
        sourceIndex).symm)]
  rfl

/-- **The Case-2 coordinate lemma.**  The occurrence point the published
factory is asked about is exactly the low digit window of one natural code
built from three windows of the requested seed point: the low input window,
the interior clause window at the padded input offset, and the single
occurrence position digit. -/
theorem caseTwoOccurrenceCoordinates_prefixView
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (point :
      BitInput (seedArity outer pcppSource requiredDegree sourceIndex)) :
    caseTwoOccurrenceCoordinates pcppSource caseTwo point =
      bitInputPrefixView
        (outer.pcp.nativeWidth (sourceLength sourceIndex) +
          (caseTwoFactoryPCPP pcppSource caseTwo).clauseBits + 1)
        (nativeOccurrenceCode
          (outer.pcp.nativeWidth (sourceLength sourceIndex))
          (widthEnvelope outer (sourceLength sourceIndex))
          (caseTwoFactoryPCPP pcppSource caseTwo).clauseBits
          (clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
            (sourceLength sourceIndex))
          (encodeBitInput point)) := by
  unfold caseTwoOccurrenceCoordinates
  rw [scheduledPoint_prefixView pcppSource outer requiredDegree sourceIndex
    point]
  exact projectPaddedOccurrence_prefixView
    (nativeWidth_le_widthEnvelope outer (sourceLength sourceIndex))
    (caseTwoFactoryPCPP_clauseBits_le pcppSource caseTwo)
    (encodeBitInput point)

/-- **The executable Case-2 seed bit.**  One scheduled Case-2 seed bit is the
honest occurrence value of the published factory at the repacked natural
occurrence code, that is exactly the value computed by
`CaseTwoOccurrenceProgram.run_caseTwoOccurrenceProgram`. -/
theorem caseTwoSeed_apply_occurrenceCodeValue
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (point :
      BitInput (seedArity outer pcppSource requiredDegree sourceIndex)) :
    caseTwoSeed pcppSource caseTwo point =
      occurrenceCodeValue pcppSource.factory
        (caseTwoSubstitutedCircuit caseTwo)
        (nativeOccurrenceCode
          (outer.pcp.nativeWidth (sourceLength sourceIndex))
          (widthEnvelope outer (sourceLength sourceIndex))
          (caseTwoFactoryPCPP pcppSource caseTwo).clauseBits
          (clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
            (sourceLength sourceIndex))
          (encodeBitInput point)) := by
  rw [caseTwoSeed_apply_executable pcppSource caseTwo point,
    caseTwoOccurrenceCoordinates_prefixView pcppSource caseTwo point]
  exact
    executableOccurrenceValue_prefixView pcppSource.factory
      (caseTwoSubstitutedCircuit caseTwo)
      (nativeOccurrenceCode (outer.pcp.nativeWidth (sourceLength sourceIndex))
        (widthEnvelope outer (sourceLength sourceIndex))
        (caseTwoFactoryPCPP pcppSource caseTwo).clauseBits
        (clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
          (sourceLength sourceIndex))
        (encodeBitInput point))

end NearCubicWires.CaseTwoOccurrenceCoordinates
