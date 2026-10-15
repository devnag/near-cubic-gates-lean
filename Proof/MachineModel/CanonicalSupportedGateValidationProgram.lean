import Proof.MachineModel.CanonicalBoolListValidationProgram
import Proof.MachineModel.CanonicalIntListValidationProgram
import Proof.MachineModel.CanonicalTaggedTupleProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Canonical supported-gate validation

A normalized supported gate is encoded by the fixed tagged tuple
`[weights, threshold, membership]`.  This module validates those heterogeneous
fields by composing the repository's unique signed-integer, integer-list, and
Boolean-list validators.  The output retains exactly the canonical field codes
needed by the subsequent length and support-relation stage.
-/

namespace NearCubicWires.CanonicalSupportedGateValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBoolListValidationProgram
open NearCubicWires.CanonicalIntListValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Fixed gate tuple -/

def supportedGateTupleOutput (raw : ℕ) : ℕ :=
  taggedTupleOutput 3 raw

def supportedGateTupleFlag (raw : ℕ) : ℕ :=
  (Nat.unpair (supportedGateTupleOutput raw)).1

def supportedGateTupleFields (raw : ℕ) : ℕ :=
  (Nat.unpair (supportedGateTupleOutput raw)).2

def supportedGateMembershipCode (raw : ℕ) : ℕ :=
  (Nat.unpair (supportedGateTupleFields raw)).2

def supportedGateThresholdFrame (raw : ℕ) : ℕ :=
  (Nat.unpair (supportedGateTupleFields raw)).1

def supportedGateThresholdCode (raw : ℕ) : ℕ :=
  (Nat.unpair (supportedGateThresholdFrame raw)).2

def supportedGateWeightsFrame (raw : ℕ) : ℕ :=
  (Nat.unpair (supportedGateThresholdFrame raw)).1

def supportedGateWeightsCode (raw : ℕ) : ℕ :=
  (Nat.unpair (supportedGateWeightsFrame raw)).2

theorem supportedGateTupleFlag_ne_zero_iff
    (raw : ℕ) :
    supportedGateTupleFlag raw ≠ 0 ↔
      ∃ weightsCode thresholdCode membershipCode,
        decodeTaggedList raw =
          some [weightsCode, thresholdCode, membershipCode] := by
  constructor
  · intro hflag
    have htuple : taggedTupleOutput 3 raw ≠ 0 := by
      intro hzero
      exact hflag <| by
        simp [supportedGateTupleFlag, supportedGateTupleOutput, hzero]
    obtain ⟨values, hdecode, hlength⟩ :=
      (taggedTupleOutput_ne_zero_iff_decodeTaggedList 3 raw).1 htuple
    cases values with
    | nil => simp at hlength
    | cons weightsCode rest =>
        cases rest with
        | nil => simp at hlength
        | cons thresholdCode rest =>
            cases rest with
            | nil => simp at hlength
            | cons membershipCode rest =>
                cases rest with
                | nil =>
                    exact
                      ⟨weightsCode, thresholdCode, membershipCode, hdecode⟩
                | cons extra tail => simp at hlength
  · rintro ⟨weightsCode, thresholdCode, membershipCode, hdecode⟩
    have hraw :
        encodeTaggedList [weightsCode, thresholdCode, membershipCode] = raw :=
      encodeTaggedList_of_decode hdecode
    have htupleDecode :
        decodeTaggedTuple 3 raw =
          some (reversePairFields
            [weightsCode, thresholdCode, membershipCode]) := by
      rw [← hraw]
      exact
        decodeTaggedTuple_encode
          [weightsCode, thresholdCode, membershipCode]
    simp [supportedGateTupleFlag, supportedGateTupleOutput,
      taggedTupleOutput, htupleDecode]

theorem supportedGateCodes_of_decode
    {raw weightsCode thresholdCode membershipCode : ℕ}
    (hdecode :
      decodeTaggedList raw =
        some [weightsCode, thresholdCode, membershipCode]) :
    supportedGateWeightsCode raw = weightsCode ∧
      supportedGateThresholdCode raw = thresholdCode ∧
      supportedGateMembershipCode raw = membershipCode := by
  have hraw :
      encodeTaggedList [weightsCode, thresholdCode, membershipCode] = raw :=
    encodeTaggedList_of_decode hdecode
  have htupleDecode :
      decodeTaggedTuple 3 raw =
        some (reversePairFields
          [weightsCode, thresholdCode, membershipCode]) := by
    rw [← hraw]
    exact
      decodeTaggedTuple_encode
        [weightsCode, thresholdCode, membershipCode]
  have htupleOutput :
      supportedGateTupleOutput raw =
        Nat.pair 1
          (reversePairFields
            [weightsCode, thresholdCode, membershipCode]) := by
    simp [supportedGateTupleOutput, taggedTupleOutput, htupleDecode]
  simp [supportedGateWeightsCode, supportedGateWeightsFrame,
    supportedGateThresholdCode, supportedGateThresholdFrame,
    supportedGateMembershipCode, supportedGateTupleFields, htupleOutput,
    reversePairFields]

/-! ## Tuple-field projection -/

def supportedGateRemainingFields (raw : ℕ) : ℕ :=
  Nat.pair (supportedGateThresholdCode raw)
    (Nat.pair (supportedGateMembershipCode raw) 0)

def supportedGateInitialAccumulator (raw : ℕ) : ℕ :=
  Nat.pair (supportedGateTupleFlag raw)
    (supportedGateThresholdCode raw)

def supportedGateFieldProjectionContext (raw : ℕ) : ℕ :=
  Nat.pair (supportedGateRemainingFields raw)
    (supportedGateInitialAccumulator raw)

def supportedGateFieldProjectionOutput (raw : ℕ) : ℕ :=
  Nat.pair (supportedGateWeightsCode raw)
    (supportedGateFieldProjectionContext raw)

def supportedGateFieldProjectionProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 4 6 5
  , .unpairRight 4 7 6
  , .unpairRight 6 8 7
  , .set 9 0 8
  , .pair 5 9 10 9
  , .pair 7 10 11 10
  , .pair 2 7 12 11
  , .pair 11 12 13 12
  , .pair 8 13 0 13
  , .halt 0
  ]

@[simp] theorem supportedGateFieldProjectionProgram_oracleFree :
    OracleFree supportedGateFieldProjectionProgram := by
  rfl

def supportedGateFieldProjectionFuel : ℕ := 14

private def supportedGateFieldProjectionValues
    (inputLength raw : ℕ) : List ℕ :=
  [ inputLength
  , supportedGateTupleOutput raw
  , supportedGateTupleFlag raw
  , supportedGateTupleFields raw
  , supportedGateThresholdFrame raw
  , supportedGateMembershipCode raw
  , supportedGateWeightsFrame raw
  , supportedGateThresholdCode raw
  , supportedGateWeightsCode raw
  , 0
  , Nat.pair (supportedGateMembershipCode raw) 0
  , supportedGateRemainingFields raw
  , supportedGateInitialAccumulator raw
  , supportedGateFieldProjectionContext raw
  , supportedGateFieldProjectionOutput raw
  ]

private def supportedGateFieldProjectionBits
    (inputLength raw : ℕ) : ℕ :=
  (supportedGateFieldProjectionValues inputLength raw).map natBitLength
    |>.foldr max 1

private theorem bitLength_le_values_max
    {values : List ℕ} {value : ℕ} (hvalue : value ∈ values) :
    natBitLength value ≤
      (values.map natBitLength).foldr max 1 := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hvalue
      simp only [List.map_cons, List.foldr_cons]
      rcases hvalue with rfl | htail
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis htail).trans (Nat.le_max_right _ _)

private theorem projectionValue_bits
    {inputLength raw value : ℕ}
    (hvalue :
      value ∈ supportedGateFieldProjectionValues inputLength raw) :
    natBitLength value ≤
      supportedGateFieldProjectionBits inputLength raw := by
  unfold supportedGateFieldProjectionBits
  exact bitLength_le_values_max hvalue

theorem run_supportedGateFieldProjectionProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram supportedGateFieldProjectionProgram
        (supportedGateFieldProjectionBits inputLength raw)
        supportedGateFieldProjectionFuel
        (initialNPOracleState inputLength
          (supportedGateTupleOutput raw)) =
      some (supportedGateFieldProjectionOutput raw) := by
  let maximumBits := supportedGateFieldProjectionBits inputLength raw
  have hflag :
      natBitLength (supportedGateTupleFlag raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  have hfields :
      natBitLength (supportedGateTupleFields raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  have hthresholdFrame :
      natBitLength (supportedGateThresholdFrame raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  have hmembership :
      natBitLength (supportedGateMembershipCode raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  have hweightsFrame :
      natBitLength (supportedGateWeightsFrame raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  have hthreshold :
      natBitLength (supportedGateThresholdCode raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  have hweights :
      natBitLength (supportedGateWeightsCode raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  have hzero : natBitLength 0 ≤ maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  have hmembershipTail :
      natBitLength (Nat.pair (supportedGateMembershipCode raw) 0) ≤
        maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  have hremaining :
      natBitLength (supportedGateRemainingFields raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  have hinitialAccumulator :
      natBitLength (supportedGateInitialAccumulator raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  have hcontext :
      natBitLength (supportedGateFieldProjectionContext raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  have houtput :
      natBitLength (supportedGateFieldProjectionOutput raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [supportedGateFieldProjectionValues])
  rw [show supportedGateFieldProjectionFuel = 13 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 13)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := supportedGateTupleFlag raw)
    (by rfl) rfl
    (by simp [initialNPOracleState, supportedGateTupleFlag,
      supportedGateTupleOutput])
    hflag]
  rw [show (13 : ℕ) = 12 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 12)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := supportedGateTupleFields raw)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, supportedGateTupleFields,
      supportedGateTupleOutput])
    hfields]
  rw [show (12 : ℕ) = 11 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 11)
    (pc := 2) (source := 3) (destination := 4) (next := 3)
    (value := supportedGateThresholdFrame raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateThresholdFrame])
    hthresholdFrame]
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 10)
    (pc := 3) (source := 3) (destination := 5) (next := 4)
    (value := supportedGateMembershipCode raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateMembershipCode])
    hmembership]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 9)
    (pc := 4) (source := 4) (destination := 6) (next := 5)
    (value := supportedGateWeightsFrame raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateWeightsFrame])
    hweightsFrame]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 8)
    (pc := 5) (source := 4) (destination := 7) (next := 6)
    (value := supportedGateThresholdCode raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateThresholdCode])
    hthreshold]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 7)
    (pc := 6) (source := 6) (destination := 8) (next := 7)
    (value := supportedGateWeightsCode raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateWeightsCode])
    hweights]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_set_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 6)
    (pc := 7) (register := 9) (value := 0) (next := 8)
    (by rfl) rfl hzero]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_pair_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 5)
    (pc := 8) (left := 5) (right := 9) (destination := 10) (next := 9)
    (value := Nat.pair (supportedGateMembershipCode raw) 0)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hmembershipTail]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_pair_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 4)
    (pc := 9) (left := 7) (right := 10) (destination := 11) (next := 10)
    (value := supportedGateRemainingFields raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateRemainingFields])
    hremaining]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 3)
    (pc := 10) (left := 2) (right := 7) (destination := 12) (next := 11)
    (value := supportedGateInitialAccumulator raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateInitialAccumulator])
    hinitialAccumulator]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 2)
    (pc := 11) (left := 11) (right := 12)
    (destination := 13) (next := 12)
    (value := supportedGateFieldProjectionContext raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateFieldProjectionContext])
    hcontext]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 1)
    (pc := 12) (left := 8) (right := 13)
    (destination := 0) (next := 13)
    (value := supportedGateFieldProjectionOutput raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateFieldProjectionOutput])
    houtput]
  exact run_halt_instruction
    (program := supportedGateFieldProjectionProgram)
    (maximumBits := maximumBits) (fuel := 0)
    (pc := 13) (outputRegister := 0)
    (value := supportedGateFieldProjectionOutput raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## Heterogeneous field sequencing -/

/-- Advance from one validated field to the next while accumulating validation
results.  Both transitions in the three-field pipeline use this one adapter. -/
def supportedGateValidationAdvanceResult (input : ℕ) : ℕ :=
  (Nat.unpair input).1

def supportedGateValidationAdvanceContext (input : ℕ) : ℕ :=
  (Nat.unpair input).2

def supportedGateValidationAdvancePending (input : ℕ) : ℕ :=
  (Nat.unpair (supportedGateValidationAdvanceContext input)).1

def supportedGateValidationAdvanceAccumulator (input : ℕ) : ℕ :=
  (Nat.unpair (supportedGateValidationAdvanceContext input)).2

def supportedGateValidationAdvanceNext (input : ℕ) : ℕ :=
  (Nat.unpair (supportedGateValidationAdvancePending input)).1

def supportedGateValidationAdvanceRest (input : ℕ) : ℕ :=
  (Nat.unpair (supportedGateValidationAdvancePending input)).2

def supportedGateValidationAdvanceNextAccumulator (input : ℕ) : ℕ :=
  Nat.pair (supportedGateValidationAdvanceAccumulator input)
    (supportedGateValidationAdvanceResult input)

def supportedGateValidationAdvanceNextContext (input : ℕ) : ℕ :=
  Nat.pair (supportedGateValidationAdvanceRest input)
    (supportedGateValidationAdvanceNextAccumulator input)

def supportedGateValidationAdvanceOutput (input : ℕ) : ℕ :=
  Nat.pair (supportedGateValidationAdvanceNext input)
    (supportedGateValidationAdvanceNextContext input)

def supportedGateValidationAdvanceProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 4 6 5
  , .unpairRight 4 7 6
  , .pair 5 2 8 7
  , .pair 7 8 9 8
  , .pair 6 9 0 9
  , .halt 0
  ]

@[simp] theorem supportedGateValidationAdvanceProgram_oracleFree :
    OracleFree supportedGateValidationAdvanceProgram := by
  rfl

def supportedGateValidationAdvanceFuel : ℕ := 10

private def supportedGateValidationAdvanceValues
    (inputLength input : ℕ) : List ℕ :=
  [ inputLength
  , input
  , supportedGateValidationAdvanceResult input
  , supportedGateValidationAdvanceContext input
  , supportedGateValidationAdvancePending input
  , supportedGateValidationAdvanceAccumulator input
  , supportedGateValidationAdvanceNext input
  , supportedGateValidationAdvanceRest input
  , supportedGateValidationAdvanceNextAccumulator input
  , supportedGateValidationAdvanceNextContext input
  , supportedGateValidationAdvanceOutput input
  ]

private def supportedGateValidationAdvanceBits
    (inputLength input : ℕ) : ℕ :=
  (supportedGateValidationAdvanceValues inputLength input).map natBitLength
    |>.foldr max 1

private theorem advanceValue_bits
    {inputLength input value : ℕ}
    (hvalue :
      value ∈ supportedGateValidationAdvanceValues inputLength input) :
    natBitLength value ≤
      supportedGateValidationAdvanceBits inputLength input := by
  unfold supportedGateValidationAdvanceBits
  exact bitLength_le_values_max hvalue

theorem run_supportedGateValidationAdvanceProgram
    (inputLength input : ℕ) :
    runNPOracleProgram supportedGateValidationAdvanceProgram
        (supportedGateValidationAdvanceBits inputLength input)
        supportedGateValidationAdvanceFuel
        (initialNPOracleState inputLength input) =
      some (supportedGateValidationAdvanceOutput input) := by
  let maximumBits :=
    supportedGateValidationAdvanceBits inputLength input
  have hresult :
      natBitLength (supportedGateValidationAdvanceResult input) ≤
        maximumBits :=
    advanceValue_bits (by
      simp [supportedGateValidationAdvanceValues])
  have hcontext :
      natBitLength (supportedGateValidationAdvanceContext input) ≤
        maximumBits :=
    advanceValue_bits (by
      simp [supportedGateValidationAdvanceValues])
  have hpending :
      natBitLength (supportedGateValidationAdvancePending input) ≤
        maximumBits :=
    advanceValue_bits (by
      simp [supportedGateValidationAdvanceValues])
  have haccumulator :
      natBitLength (supportedGateValidationAdvanceAccumulator input) ≤
        maximumBits :=
    advanceValue_bits (by
      simp [supportedGateValidationAdvanceValues])
  have hnext :
      natBitLength (supportedGateValidationAdvanceNext input) ≤ maximumBits :=
    advanceValue_bits (by
      simp [supportedGateValidationAdvanceValues])
  have hrest :
      natBitLength (supportedGateValidationAdvanceRest input) ≤ maximumBits :=
    advanceValue_bits (by
      simp [supportedGateValidationAdvanceValues])
  have hnextAccumulator :
      natBitLength
          (supportedGateValidationAdvanceNextAccumulator input) ≤
        maximumBits :=
    advanceValue_bits (by
      simp [supportedGateValidationAdvanceValues])
  have hnextContext :
      natBitLength (supportedGateValidationAdvanceNextContext input) ≤
        maximumBits :=
    advanceValue_bits (by
      simp [supportedGateValidationAdvanceValues])
  have houtput :
      natBitLength (supportedGateValidationAdvanceOutput input) ≤
        maximumBits :=
    advanceValue_bits (by
      simp [supportedGateValidationAdvanceValues])
  rw [show supportedGateValidationAdvanceFuel = 9 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (program := supportedGateValidationAdvanceProgram)
    (maximumBits := maximumBits) (fuel := 9)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := supportedGateValidationAdvanceResult input)
    (by rfl) rfl
    (by simp [initialNPOracleState,
      supportedGateValidationAdvanceResult])
    hresult]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supportedGateValidationAdvanceProgram)
    (maximumBits := maximumBits) (fuel := 8)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := supportedGateValidationAdvanceContext input)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, supportedGateValidationAdvanceContext])
    hcontext]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := supportedGateValidationAdvanceProgram)
    (maximumBits := maximumBits) (fuel := 7)
    (pc := 2) (source := 3) (destination := 4) (next := 3)
    (value := supportedGateValidationAdvancePending input)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateValidationAdvancePending])
    hpending]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supportedGateValidationAdvanceProgram)
    (maximumBits := maximumBits) (fuel := 6)
    (pc := 3) (source := 3) (destination := 5) (next := 4)
    (value := supportedGateValidationAdvanceAccumulator input)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateValidationAdvanceAccumulator])
    haccumulator]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := supportedGateValidationAdvanceProgram)
    (maximumBits := maximumBits) (fuel := 5)
    (pc := 4) (source := 4) (destination := 6) (next := 5)
    (value := supportedGateValidationAdvanceNext input)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateValidationAdvanceNext])
    hnext]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supportedGateValidationAdvanceProgram)
    (maximumBits := maximumBits) (fuel := 4)
    (pc := 5) (source := 4) (destination := 7) (next := 6)
    (value := supportedGateValidationAdvanceRest input)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateValidationAdvanceRest])
    hrest]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction
    (program := supportedGateValidationAdvanceProgram)
    (maximumBits := maximumBits) (fuel := 3)
    (pc := 6) (left := 5) (right := 2) (destination := 8) (next := 7)
    (value := supportedGateValidationAdvanceNextAccumulator input)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateValidationAdvanceNextAccumulator])
    hnextAccumulator]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (program := supportedGateValidationAdvanceProgram)
    (maximumBits := maximumBits) (fuel := 2)
    (pc := 7) (left := 7) (right := 8) (destination := 9) (next := 8)
    (value := supportedGateValidationAdvanceNextContext input)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateValidationAdvanceNextContext])
    hnextContext]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := supportedGateValidationAdvanceProgram)
    (maximumBits := maximumBits) (fuel := 1)
    (pc := 8) (left := 6) (right := 9) (destination := 0) (next := 9)
    (value := supportedGateValidationAdvanceOutput input)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      supportedGateValidationAdvanceOutput])
    houtput]
  exact run_halt_instruction
    (program := supportedGateValidationAdvanceProgram)
    (maximumBits := maximumBits) (fuel := 0)
    (pc := 9) (outputRegister := 0)
    (value := supportedGateValidationAdvanceOutput input)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## Exact staged field state -/

def supportedGateWeightsValidationResult
    (inputLength raw : ℕ) : ℕ :=
  canonicalIntListValidationOutput inputLength
    (supportedGateWeightsCode raw)

def supportedGateFirstAccumulator
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair (supportedGateInitialAccumulator raw)
    (supportedGateWeightsValidationResult inputLength raw)

def supportedGateThresholdValidationResult (raw : ℕ) : ℕ :=
  unitRationalValidationOutput (supportedGateThresholdCode raw)

def supportedGateSecondAccumulator
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair (supportedGateFirstAccumulator inputLength raw)
    (supportedGateThresholdValidationResult raw)

def supportedGateMembershipValidationResult
    (inputLength raw : ℕ) : ℕ :=
  canonicalBoolListValidationOutput inputLength
    (supportedGateMembershipCode raw)

def supportedGateWeightsStageOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair (supportedGateWeightsValidationResult inputLength raw)
    (supportedGateFieldProjectionContext raw)

def supportedGateFirstAdvanceOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair (supportedGateThresholdCode raw) <|
    Nat.pair (Nat.pair (supportedGateMembershipCode raw) 0)
      (supportedGateFirstAccumulator inputLength raw)

def supportedGateThresholdStageOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair (supportedGateThresholdValidationResult raw) <|
    Nat.pair (Nat.pair (supportedGateMembershipCode raw) 0)
      (supportedGateFirstAccumulator inputLength raw)

def supportedGateSecondAdvanceOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair (supportedGateMembershipCode raw) <|
    Nat.pair 0 (supportedGateSecondAccumulator inputLength raw)

def supportedGateMembershipStageOutput
    (inputLength raw : ℕ) : ℕ :=
  Nat.pair (supportedGateMembershipValidationResult inputLength raw) <|
    Nat.pair 0 (supportedGateSecondAccumulator inputLength raw)

private theorem intListValidationOutput_payload
    (inputLength raw : ℕ)
    (hnonzero : canonicalIntListValidationOutput inputLength raw ≠ 0) :
    (Nat.unpair
      (canonicalIntListValidationOutput inputLength raw)).2 = raw := by
  unfold canonicalIntListValidationOutput balancedValidationAllOutput
  split
  · simp
  · exfalso
    apply hnonzero
    simp [canonicalIntListValidationOutput, balancedValidationAllOutput, *]

private theorem boolListValidationOutput_payload
    (inputLength raw : ℕ)
    (hnonzero : canonicalBoolListValidationOutput inputLength raw ≠ 0) :
    (Nat.unpair
      (canonicalBoolListValidationOutput inputLength raw)).2 = raw := by
  unfold canonicalBoolListValidationOutput balancedValidationAllOutput
  split
  · simp
  · exfalso
    apply hnonzero
    simp [canonicalBoolListValidationOutput, balancedValidationAllOutput, *]

private theorem supportedGateAdvance_weightsStage
    (inputLength raw : ℕ) :
    supportedGateValidationAdvanceOutput
        (supportedGateWeightsStageOutput inputLength raw) =
      supportedGateFirstAdvanceOutput inputLength raw := by
  simp [supportedGateValidationAdvanceOutput,
    supportedGateValidationAdvanceNext,
    supportedGateValidationAdvanceNextContext,
    supportedGateValidationAdvanceNextAccumulator,
    supportedGateValidationAdvanceRest,
    supportedGateValidationAdvancePending,
    supportedGateValidationAdvanceAccumulator,
    supportedGateValidationAdvanceContext,
    supportedGateValidationAdvanceResult,
    supportedGateWeightsStageOutput,
    supportedGateFieldProjectionContext,
    supportedGateRemainingFields,
    supportedGateFirstAdvanceOutput,
    supportedGateFirstAccumulator]

private theorem supportedGateAdvance_thresholdStage
    (inputLength raw : ℕ) :
    supportedGateValidationAdvanceOutput
        (supportedGateThresholdStageOutput inputLength raw) =
      supportedGateSecondAdvanceOutput inputLength raw := by
  simp [supportedGateValidationAdvanceOutput,
    supportedGateValidationAdvanceNext,
    supportedGateValidationAdvanceNextContext,
    supportedGateValidationAdvanceNextAccumulator,
    supportedGateValidationAdvanceRest,
    supportedGateValidationAdvancePending,
    supportedGateValidationAdvanceAccumulator,
    supportedGateValidationAdvanceContext,
    supportedGateValidationAdvanceResult,
    supportedGateThresholdStageOutput,
    supportedGateSecondAdvanceOutput,
    supportedGateSecondAccumulator]

/-! ## Fail-closed field gate -/

def supportedGateFieldValidationOutput
    (inputLength raw : ℕ) : ℕ :=
  if supportedGateTupleFlag raw = 0 then
    0
  else if supportedGateWeightsValidationResult inputLength raw = 0 then
    0
  else if supportedGateThresholdValidationResult raw = 0 then
    0
  else if supportedGateMembershipValidationResult inputLength raw = 0 then
    0
  else
    Nat.pair 1 <|
      Nat.pair (supportedGateThresholdCode raw) <|
        Nat.pair (supportedGateWeightsCode raw)
          (supportedGateMembershipCode raw)

def supportedGateFieldGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .unpairLeft 4 5 4
  , .unpairRight 4 6 5
  , .unpairLeft 5 7 6
  , .unpairRight 5 8 7
  , .unpairLeft 7 9 8
  , .branchZero 9 19 9
  , .branchZero 8 19 10
  , .branchZero 6 19 11
  , .branchZero 2 19 12
  , .unpairRight 7 10 13
  , .unpairRight 8 11 14
  , .unpairRight 2 12 15
  , .pair 11 12 13 16
  , .pair 10 13 14 17
  , .set 15 1 18
  , .pair 15 14 0 20
  , .set 0 0 20
  , .halt 0
  ]

@[simp] theorem supportedGateFieldGateProgram_oracleFree :
    OracleFree supportedGateFieldGateProgram := by
  rfl

def supportedGateFieldGateFuel : ℕ := 21

private def supportedGateFieldGateValues
    (inputLength raw : ℕ) : List ℕ :=
  [ inputLength
  , supportedGateMembershipStageOutput inputLength raw
  , supportedGateMembershipValidationResult inputLength raw
  , Nat.pair 0 (supportedGateSecondAccumulator inputLength raw)
  , supportedGateSecondAccumulator inputLength raw
  , supportedGateFirstAccumulator inputLength raw
  , supportedGateThresholdValidationResult raw
  , supportedGateInitialAccumulator raw
  , supportedGateWeightsValidationResult inputLength raw
  , supportedGateTupleFlag raw
  , supportedGateThresholdCode raw
  , supportedGateWeightsCode raw
  , supportedGateMembershipCode raw
  , Nat.pair (supportedGateWeightsCode raw)
      (supportedGateMembershipCode raw)
  , Nat.pair (supportedGateThresholdCode raw) <|
      Nat.pair (supportedGateWeightsCode raw)
        (supportedGateMembershipCode raw)
  , 0
  , 1
  , Nat.pair 1 <|
      Nat.pair (supportedGateThresholdCode raw) <|
        Nat.pair (supportedGateWeightsCode raw)
          (supportedGateMembershipCode raw)
  , supportedGateFieldValidationOutput inputLength raw
  ]

private def supportedGateFieldGateBits
    (inputLength raw : ℕ) : ℕ :=
  (supportedGateFieldGateValues inputLength raw).map natBitLength
    |>.foldr max 1

private theorem gateValue_bits
    {inputLength raw value : ℕ}
    (hvalue : value ∈ supportedGateFieldGateValues inputLength raw) :
    natBitLength value ≤ supportedGateFieldGateBits inputLength raw := by
  unfold supportedGateFieldGateBits
  exact bitLength_le_values_max hvalue

theorem run_supportedGateFieldGateProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram supportedGateFieldGateProgram
        (supportedGateFieldGateBits inputLength raw)
        supportedGateFieldGateFuel
        (initialNPOracleState inputLength
          (supportedGateMembershipStageOutput inputLength raw)) =
      some (supportedGateFieldValidationOutput inputLength raw) := by
  let maximumBits := supportedGateFieldGateBits inputLength raw
  let membership :=
    supportedGateMembershipValidationResult inputLength raw
  let secondAccumulator :=
    supportedGateSecondAccumulator inputLength raw
  let firstAccumulator :=
    supportedGateFirstAccumulator inputLength raw
  let thresholdResult := supportedGateThresholdValidationResult raw
  let initialAccumulator := supportedGateInitialAccumulator raw
  let weights := supportedGateWeightsValidationResult inputLength raw
  let tupleFlag := supportedGateTupleFlag raw
  let thresholdCode := supportedGateThresholdCode raw
  let weightsCode := supportedGateWeightsCode raw
  let membershipCode := supportedGateMembershipCode raw
  let weightsMembership := Nat.pair weightsCode membershipCode
  let payload := Nat.pair thresholdCode weightsMembership
  let accepted := Nat.pair 1 payload
  have hmembership : natBitLength membership ≤ maximumBits :=
    gateValue_bits (by
      simp [membership, supportedGateFieldGateValues])
  have htail :
      natBitLength (Nat.pair 0 secondAccumulator) ≤ maximumBits :=
    gateValue_bits (by
      simp [secondAccumulator, supportedGateFieldGateValues])
  have hsecondAccumulator :
      natBitLength secondAccumulator ≤ maximumBits :=
    gateValue_bits (by
      simp [secondAccumulator, supportedGateFieldGateValues])
  have hfirstAccumulator :
      natBitLength firstAccumulator ≤ maximumBits :=
    gateValue_bits (by
      simp [firstAccumulator, supportedGateFieldGateValues])
  have hthresholdResult :
      natBitLength thresholdResult ≤ maximumBits :=
    gateValue_bits (by
      simp [thresholdResult, supportedGateFieldGateValues])
  have hinitialAccumulator :
      natBitLength initialAccumulator ≤ maximumBits :=
    gateValue_bits (by
      simp [initialAccumulator, supportedGateFieldGateValues])
  have hweights : natBitLength weights ≤ maximumBits :=
    gateValue_bits (by
      simp [weights, supportedGateFieldGateValues])
  have htupleFlag : natBitLength tupleFlag ≤ maximumBits :=
    gateValue_bits (by
      simp [tupleFlag, supportedGateFieldGateValues])
  have hthresholdCode : natBitLength thresholdCode ≤ maximumBits :=
    gateValue_bits (by
      simp [thresholdCode, supportedGateFieldGateValues])
  have hweightsCode : natBitLength weightsCode ≤ maximumBits :=
    gateValue_bits (by
      simp [weightsCode, supportedGateFieldGateValues])
  have hmembershipCode : natBitLength membershipCode ≤ maximumBits :=
    gateValue_bits (by
      simp [membershipCode, supportedGateFieldGateValues])
  have hweightsMembership :
      natBitLength weightsMembership ≤ maximumBits :=
    gateValue_bits (by
      simp [weightsMembership, weightsCode, membershipCode,
        supportedGateFieldGateValues])
  have hpayload : natBitLength payload ≤ maximumBits :=
    gateValue_bits (by
      simp [payload, thresholdCode, weightsMembership, weightsCode,
        membershipCode, supportedGateFieldGateValues])
  have hzero : natBitLength 0 ≤ maximumBits :=
    gateValue_bits (by
      simp [supportedGateFieldGateValues])
  have hone : natBitLength 1 ≤ maximumBits :=
    gateValue_bits (by
      simp [supportedGateFieldGateValues])
  have haccepted : natBitLength accepted ≤ maximumBits :=
    gateValue_bits (by
      simp [accepted, payload, weightsMembership, thresholdCode, weightsCode,
        membershipCode, supportedGateFieldGateValues])
  rw [show supportedGateFieldGateFuel = 20 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (program := supportedGateFieldGateProgram)
    (maximumBits := maximumBits) (fuel := 20)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := membership)
    (by rfl) rfl
    (by simp [initialNPOracleState, membership,
      supportedGateMembershipStageOutput])
    hmembership]
  rw [show (20 : ℕ) = 19 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supportedGateFieldGateProgram)
    (maximumBits := maximumBits) (fuel := 19)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := Nat.pair 0 secondAccumulator)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, secondAccumulator,
      supportedGateMembershipStageOutput])
    htail]
  rw [show (19 : ℕ) = 18 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supportedGateFieldGateProgram)
    (maximumBits := maximumBits) (fuel := 18)
    (pc := 2) (source := 3) (destination := 4) (next := 3)
    (value := secondAccumulator)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsecondAccumulator]
  rw [show (18 : ℕ) = 17 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := supportedGateFieldGateProgram)
    (maximumBits := maximumBits) (fuel := 17)
    (pc := 3) (source := 4) (destination := 5) (next := 4)
    (value := firstAccumulator)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, secondAccumulator,
      supportedGateSecondAccumulator, firstAccumulator])
    hfirstAccumulator]
  rw [show (17 : ℕ) = 16 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supportedGateFieldGateProgram)
    (maximumBits := maximumBits) (fuel := 16)
    (pc := 4) (source := 4) (destination := 6) (next := 5)
    (value := thresholdResult)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, secondAccumulator,
      supportedGateSecondAccumulator, firstAccumulator, thresholdResult])
    hthresholdResult]
  rw [show (16 : ℕ) = 15 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := supportedGateFieldGateProgram)
    (maximumBits := maximumBits) (fuel := 15)
    (pc := 5) (source := 5) (destination := 7) (next := 6)
    (value := initialAccumulator)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, firstAccumulator,
      supportedGateFirstAccumulator, initialAccumulator])
    hinitialAccumulator]
  rw [show (15 : ℕ) = 14 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supportedGateFieldGateProgram)
    (maximumBits := maximumBits) (fuel := 14)
    (pc := 6) (source := 5) (destination := 8) (next := 7)
    (value := weights)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, firstAccumulator,
      supportedGateFirstAccumulator, initialAccumulator, weights])
    hweights]
  rw [show (14 : ℕ) = 13 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := supportedGateFieldGateProgram)
    (maximumBits := maximumBits) (fuel := 13)
    (pc := 7) (source := 7) (destination := 9) (next := 8)
    (value := tupleFlag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, initialAccumulator,
      supportedGateInitialAccumulator, tupleFlag])
    htupleFlag]
  rw [show (13 : ℕ) = 12 + 1 by omega]
  rw [run_branchZero_instruction
    (program := supportedGateFieldGateProgram)
    (maximumBits := maximumBits) (fuel := 12)
    (pc := 8) (register := 9) (zeroTarget := 19) (nonzeroTarget := 9)
    (by rfl) rfl]
  simp only [NPOracleState.jump]
  by_cases htuple : supportedGateTupleFlag raw = 0
  · rw [if_pos (by simpa [tupleFlag] using htuple)]
    rw [show (12 : ℕ) = 11 + 1 by omega]
    rw [run_set_instruction
      (program := supportedGateFieldGateProgram)
      (maximumBits := maximumBits) (fuel := 11)
      (pc := 19) (register := 0) (value := 0) (next := 20)
      (by rfl) rfl hzero]
    rw [show supportedGateFieldValidationOutput inputLength raw = 0 by
      simp [supportedGateFieldValidationOutput, htuple]]
    exact run_halt_instruction
      (program := supportedGateFieldGateProgram)
      (maximumBits := maximumBits) (fuel := 10)
      (pc := 20) (outputRegister := 0) (value := 0)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hzero
  · rw [if_neg (by simpa [tupleFlag] using htuple)]
    rw [show (12 : ℕ) = 11 + 1 by omega]
    rw [run_branchZero_instruction
      (program := supportedGateFieldGateProgram)
      (maximumBits := maximumBits) (fuel := 11)
      (pc := 9) (register := 8) (zeroTarget := 19) (nonzeroTarget := 10)
      (by rfl) rfl]
    simp only [NPOracleState.jump]
    by_cases hweightsZero :
        supportedGateWeightsValidationResult inputLength raw = 0
    · rw [if_pos (by simpa [weights] using hweightsZero)]
      rw [show (11 : ℕ) = 10 + 1 by omega]
      rw [run_set_instruction
        (program := supportedGateFieldGateProgram)
        (maximumBits := maximumBits) (fuel := 10)
        (pc := 19) (register := 0) (value := 0) (next := 20)
        (by rfl) rfl hzero]
      rw [show supportedGateFieldValidationOutput inputLength raw = 0 by
        simp [supportedGateFieldValidationOutput, htuple, hweightsZero]]
      exact run_halt_instruction
        (program := supportedGateFieldGateProgram)
        (maximumBits := maximumBits) (fuel := 9)
        (pc := 20) (outputRegister := 0) (value := 0)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hzero
    · rw [if_neg (by simpa [weights] using hweightsZero)]
      rw [show (11 : ℕ) = 10 + 1 by omega]
      rw [run_branchZero_instruction
        (program := supportedGateFieldGateProgram)
        (maximumBits := maximumBits) (fuel := 10)
        (pc := 10) (register := 6) (zeroTarget := 19) (nonzeroTarget := 11)
        (by rfl) rfl]
      simp only [NPOracleState.jump]
      by_cases hthresholdZero :
          supportedGateThresholdValidationResult raw = 0
      · rw [if_pos (by simpa [thresholdResult] using hthresholdZero)]
        rw [show (10 : ℕ) = 9 + 1 by omega]
        rw [run_set_instruction
          (program := supportedGateFieldGateProgram)
          (maximumBits := maximumBits) (fuel := 9)
          (pc := 19) (register := 0) (value := 0) (next := 20)
          (by rfl) rfl hzero]
        rw [show supportedGateFieldValidationOutput inputLength raw = 0 by
          simp [supportedGateFieldValidationOutput, htuple, hweightsZero,
            hthresholdZero]]
        exact run_halt_instruction
          (program := supportedGateFieldGateProgram)
          (maximumBits := maximumBits) (fuel := 8)
          (pc := 20) (outputRegister := 0) (value := 0)
          (by rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump]) hzero
      · rw [if_neg (by simpa [thresholdResult] using hthresholdZero)]
        rw [show (10 : ℕ) = 9 + 1 by omega]
        rw [run_branchZero_instruction
          (program := supportedGateFieldGateProgram)
          (maximumBits := maximumBits) (fuel := 9)
          (pc := 11) (register := 2) (zeroTarget := 19) (nonzeroTarget := 12)
          (by rfl) rfl]
        simp only [NPOracleState.jump]
        by_cases hmembershipZero :
            supportedGateMembershipValidationResult inputLength raw = 0
        · rw [if_pos (by simpa [membership] using hmembershipZero)]
          rw [show (9 : ℕ) = 8 + 1 by omega]
          rw [run_set_instruction
            (program := supportedGateFieldGateProgram)
            (maximumBits := maximumBits) (fuel := 8)
            (pc := 19) (register := 0) (value := 0) (next := 20)
            (by rfl) rfl hzero]
          rw [show supportedGateFieldValidationOutput inputLength raw = 0 by
            simp [supportedGateFieldValidationOutput, htuple, hweightsZero,
              hthresholdZero, hmembershipZero]]
          exact run_halt_instruction
            (program := supportedGateFieldGateProgram)
            (maximumBits := maximumBits) (fuel := 7)
            (pc := 20) (outputRegister := 0) (value := 0)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump]) hzero
        · rw [if_neg (by simpa [membership] using hmembershipZero)]
          have hweightsPayload :
              (Nat.unpair weights).2 = weightsCode := by
            simpa [weights, weightsCode,
              supportedGateWeightsValidationResult] using
              intListValidationOutput_payload inputLength
                (supportedGateWeightsCode raw) hweightsZero
          have hmembershipPayload :
              (Nat.unpair membership).2 = membershipCode := by
            simpa [membership, membershipCode,
              supportedGateMembershipValidationResult] using
              boolListValidationOutput_payload inputLength
                (supportedGateMembershipCode raw) hmembershipZero
          rw [show (9 : ℕ) = 8 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := supportedGateFieldGateProgram)
            (maximumBits := maximumBits) (fuel := 8)
            (pc := 12) (source := 7) (destination := 10) (next := 13)
            (value := thresholdCode)
            (by rfl) rfl
            (by simp [NPOracleState.write,
              initialAccumulator, supportedGateInitialAccumulator,
              tupleFlag, thresholdCode])
            hthresholdCode]
          rw [show (8 : ℕ) = 7 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := supportedGateFieldGateProgram)
            (maximumBits := maximumBits) (fuel := 7)
            (pc := 13) (source := 8) (destination := 11) (next := 14)
            (value := weightsCode)
            (by rfl) rfl
            (by
              simpa [NPOracleState.write, NPOracleState.jump] using
                hweightsPayload)
            hweightsCode]
          rw [show (7 : ℕ) = 6 + 1 by omega]
          rw [run_unpairRight_instruction
            (program := supportedGateFieldGateProgram)
            (maximumBits := maximumBits) (fuel := 6)
            (pc := 14) (source := 2) (destination := 12) (next := 15)
            (value := membershipCode)
            (by rfl) rfl
            (by
              simpa [NPOracleState.write, NPOracleState.jump] using
                hmembershipPayload)
            hmembershipCode]
          rw [show (6 : ℕ) = 5 + 1 by omega]
          rw [run_pair_instruction
            (program := supportedGateFieldGateProgram)
            (maximumBits := maximumBits) (fuel := 5)
            (pc := 15) (left := 11) (right := 12)
            (destination := 13) (next := 16)
            (value := weightsMembership)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump,
              weightsMembership])
            hweightsMembership]
          rw [show (5 : ℕ) = 4 + 1 by omega]
          rw [run_pair_instruction
            (program := supportedGateFieldGateProgram)
            (maximumBits := maximumBits) (fuel := 4)
            (pc := 16) (left := 10) (right := 13)
            (destination := 14) (next := 17)
            (value := payload)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump, payload])
            hpayload]
          rw [show (4 : ℕ) = 3 + 1 by omega]
          rw [run_set_instruction
            (program := supportedGateFieldGateProgram)
            (maximumBits := maximumBits) (fuel := 3)
            (pc := 17) (register := 15) (value := 1) (next := 18)
            (by rfl) rfl hone]
          rw [show (3 : ℕ) = 2 + 1 by omega]
          rw [run_pair_instruction
            (program := supportedGateFieldGateProgram)
            (maximumBits := maximumBits) (fuel := 2)
            (pc := 18) (left := 15) (right := 14)
            (destination := 0) (next := 20)
            (value := accepted)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump, accepted])
            haccepted]
          rw [show supportedGateFieldValidationOutput inputLength raw =
              accepted by
            simp [supportedGateFieldValidationOutput, htuple, hweightsZero,
              hthresholdZero, hmembershipZero, accepted, payload,
              weightsMembership, thresholdCode, weightsCode,
              membershipCode]]
          exact run_halt_instruction
            (program := supportedGateFieldGateProgram)
            (maximumBits := maximumBits) (fuel := 1)
            (pc := 20) (outputRegister := 0) (value := accepted)
            (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump]) haccepted

/-! ## Unique composed field prefix -/

def supportedGateFieldValidationProgram : NPOracleProgram :=
  linkPrograms (taggedTupleProgram 3) <|
    linkPrograms supportedGateFieldProjectionProgram <|
      linkPrograms
          (preserveRightProgram canonicalIntListValidationProgram) <|
        linkPrograms supportedGateValidationAdvanceProgram <|
          linkPrograms
              (preserveRightProgram unitRationalValidationProgram) <|
            linkPrograms supportedGateValidationAdvanceProgram <|
              linkPrograms
                  (preserveRightProgram canonicalBoolListValidationProgram)
                supportedGateFieldGateProgram

@[simp] theorem supportedGateFieldValidationProgram_oracleFree :
    OracleFree supportedGateFieldValidationProgram := by
  exact oracleFree_linkPrograms (taggedTupleProgram_oracleFree 3) <|
    oracleFree_linkPrograms
      supportedGateFieldProjectionProgram_oracleFree <|
      oracleFree_linkPrograms
        (preserveRightProgram_oracleFree canonicalIntListValidationProgram
          canonicalIntListValidationProgram_oracleFree) <|
        oracleFree_linkPrograms
          supportedGateValidationAdvanceProgram_oracleFree <|
          oracleFree_linkPrograms
            (preserveRightProgram_oracleFree unitRationalValidationProgram
              unitRationalValidationProgram_oracleFree) <|
            oracleFree_linkPrograms
              supportedGateValidationAdvanceProgram_oracleFree <|
              oracleFree_linkPrograms
                (preserveRightProgram_oracleFree
                  canonicalBoolListValidationProgram
                  canonicalBoolListValidationProgram_oracleFree)
                supportedGateFieldGateProgram_oracleFree

private def supportedGateWeightsStageBits
    (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (canonicalIntListValidationBits inputLength
      (supportedGateWeightsCode raw))
    (supportedGateWeightsCode raw)
    (supportedGateFieldProjectionContext raw)
    (supportedGateWeightsValidationResult inputLength raw)

private def supportedGateThresholdStageBits
    (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (unitRationalValidationBits inputLength
      (supportedGateThresholdCode raw))
    (supportedGateThresholdCode raw)
    (Nat.pair (Nat.pair (supportedGateMembershipCode raw) 0)
      (supportedGateFirstAccumulator inputLength raw))
    (supportedGateThresholdValidationResult raw)

private def supportedGateMembershipStageBits
    (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (canonicalBoolListValidationBits inputLength
      (supportedGateMembershipCode raw))
    (supportedGateMembershipCode raw)
    (Nat.pair 0 (supportedGateSecondAccumulator inputLength raw))
    (supportedGateMembershipValidationResult inputLength raw)

def supportedGateFieldValidationBits
    (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (taggedTupleBits inputLength 3 raw) <|
      max (supportedGateFieldProjectionBits inputLength raw) <|
        max (supportedGateWeightsStageBits inputLength raw) <|
          max
              (supportedGateValidationAdvanceBits inputLength
                (supportedGateWeightsStageOutput inputLength raw)) <|
            max (supportedGateThresholdStageBits inputLength raw) <|
              max
                  (supportedGateValidationAdvanceBits inputLength
                    (supportedGateThresholdStageOutput inputLength raw)) <|
                max (supportedGateMembershipStageBits inputLength raw)
                  (supportedGateFieldGateBits inputLength raw)

def supportedGateFieldValidationFuel
    (inputLength raw : ℕ) : ℕ :=
  linkFuel
      (linkPrograms supportedGateFieldProjectionProgram <|
        linkPrograms
            (preserveRightProgram canonicalIntListValidationProgram) <|
          linkPrograms supportedGateValidationAdvanceProgram <|
            linkPrograms
                (preserveRightProgram unitRationalValidationProgram) <|
              linkPrograms supportedGateValidationAdvanceProgram <|
                linkPrograms
                    (preserveRightProgram canonicalBoolListValidationProgram)
                  supportedGateFieldGateProgram)
      (taggedTupleFuel 3) <|
    linkFuel
        (linkPrograms
            (preserveRightProgram canonicalIntListValidationProgram) <|
          linkPrograms supportedGateValidationAdvanceProgram <|
            linkPrograms
                (preserveRightProgram unitRationalValidationProgram) <|
              linkPrograms supportedGateValidationAdvanceProgram <|
                linkPrograms
                    (preserveRightProgram canonicalBoolListValidationProgram)
                  supportedGateFieldGateProgram)
        supportedGateFieldProjectionFuel <|
      linkFuel
          (linkPrograms supportedGateValidationAdvanceProgram <|
            linkPrograms
                (preserveRightProgram unitRationalValidationProgram) <|
              linkPrograms supportedGateValidationAdvanceProgram <|
                linkPrograms
                    (preserveRightProgram canonicalBoolListValidationProgram)
                  supportedGateFieldGateProgram)
          (preserveRightFuel <|
            canonicalIntListValidationFuel inputLength
              (supportedGateWeightsCode raw)) <|
        linkFuel
            (linkPrograms
                (preserveRightProgram unitRationalValidationProgram) <|
              linkPrograms supportedGateValidationAdvanceProgram <|
                linkPrograms
                    (preserveRightProgram canonicalBoolListValidationProgram)
                  supportedGateFieldGateProgram)
            supportedGateValidationAdvanceFuel <|
          linkFuel
              (linkPrograms supportedGateValidationAdvanceProgram <|
                linkPrograms
                    (preserveRightProgram canonicalBoolListValidationProgram)
                  supportedGateFieldGateProgram)
              (preserveRightFuel <|
                unitRationalValidationFuel inputLength
                  (supportedGateThresholdCode raw)) <|
            linkFuel
                (linkPrograms
                    (preserveRightProgram canonicalBoolListValidationProgram)
                  supportedGateFieldGateProgram)
                supportedGateValidationAdvanceFuel <|
              linkFuel supportedGateFieldGateProgram
                (preserveRightFuel <|
                  canonicalBoolListValidationFuel inputLength
                    (supportedGateMembershipCode raw))
                supportedGateFieldGateFuel

theorem run_supportedGateFieldValidationProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram supportedGateFieldValidationProgram
        (supportedGateFieldValidationBits inputLength raw)
        (supportedGateFieldValidationFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (supportedGateFieldValidationOutput inputLength raw) := by
  let maximumBits :=
    supportedGateFieldValidationBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, supportedGateFieldValidationBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, supportedGateFieldValidationBits]
  have htupleBits :
      taggedTupleBits inputLength 3 raw ≤ maximumBits := by
    simp [maximumBits, supportedGateFieldValidationBits]
  have hprojectionBits :
      supportedGateFieldProjectionBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, supportedGateFieldValidationBits]
  have hweightsBits :
      supportedGateWeightsStageBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, supportedGateFieldValidationBits]
  have hfirstAdvanceBits :
      supportedGateValidationAdvanceBits inputLength
          (supportedGateWeightsStageOutput inputLength raw) ≤
        maximumBits := by
    simp [maximumBits, supportedGateFieldValidationBits]
  have hthresholdBits :
      supportedGateThresholdStageBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, supportedGateFieldValidationBits]
  have hsecondAdvanceBits :
      supportedGateValidationAdvanceBits inputLength
          (supportedGateThresholdStageOutput inputLength raw) ≤
        maximumBits := by
    simp [maximumBits, supportedGateFieldValidationBits]
  have hmembershipBits :
      supportedGateMembershipStageBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, supportedGateFieldValidationBits]
  have hgateBits :
      supportedGateFieldGateBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, supportedGateFieldValidationBits]
  have htuple :=
    run_bits_mono
      (run_taggedTupleProgram inputLength 3 raw) htupleBits
  have hprojection :=
    run_bits_mono
      (run_supportedGateFieldProjectionProgram inputLength raw)
      hprojectionBits
  have hweights :
      runNPOracleProgram
          (preserveRightProgram canonicalIntListValidationProgram)
          maximumBits
          (preserveRightFuel <|
            canonicalIntListValidationFuel inputLength
              (supportedGateWeightsCode raw))
          (initialNPOracleState inputLength
            (supportedGateFieldProjectionOutput raw)) =
        some (supportedGateWeightsStageOutput inputLength raw) := by
    exact run_bits_mono
      (run_preserveRightProgram canonicalIntListValidationProgram
        inputLength
        (canonicalIntListValidationBits inputLength
          (supportedGateWeightsCode raw))
        (canonicalIntListValidationFuel inputLength
          (supportedGateWeightsCode raw))
        (supportedGateWeightsCode raw)
        (supportedGateFieldProjectionContext raw)
        (supportedGateWeightsValidationResult inputLength raw)
        (run_canonicalIntListValidationProgram inputLength
          (supportedGateWeightsCode raw)))
      hweightsBits
  have hfirstAdvance :
      runNPOracleProgram supportedGateValidationAdvanceProgram
          maximumBits supportedGateValidationAdvanceFuel
          (initialNPOracleState inputLength
            (supportedGateWeightsStageOutput inputLength raw)) =
        some (supportedGateFirstAdvanceOutput inputLength raw) := by
    have hrun := run_bits_mono
      (run_supportedGateValidationAdvanceProgram inputLength
        (supportedGateWeightsStageOutput inputLength raw))
      hfirstAdvanceBits
    rw [supportedGateAdvance_weightsStage] at hrun
    exact hrun
  have hthreshold :
      runNPOracleProgram
          (preserveRightProgram unitRationalValidationProgram)
          maximumBits
          (preserveRightFuel <|
            unitRationalValidationFuel inputLength
              (supportedGateThresholdCode raw))
          (initialNPOracleState inputLength
            (supportedGateFirstAdvanceOutput inputLength raw)) =
        some (supportedGateThresholdStageOutput inputLength raw) := by
    have hrun := run_bits_mono
      (run_preserveRightProgram unitRationalValidationProgram
        inputLength
        (unitRationalValidationBits inputLength
          (supportedGateThresholdCode raw))
        (unitRationalValidationFuel inputLength
          (supportedGateThresholdCode raw))
        (supportedGateThresholdCode raw)
        (Nat.pair (Nat.pair (supportedGateMembershipCode raw) 0)
          (supportedGateFirstAccumulator inputLength raw))
        (supportedGateThresholdValidationResult raw)
        (run_unitRationalValidationProgram inputLength
          (supportedGateThresholdCode raw)))
      hthresholdBits
    simpa [supportedGateFirstAdvanceOutput,
      supportedGateThresholdStageOutput] using hrun
  have hsecondAdvance :
      runNPOracleProgram supportedGateValidationAdvanceProgram
          maximumBits supportedGateValidationAdvanceFuel
          (initialNPOracleState inputLength
            (supportedGateThresholdStageOutput inputLength raw)) =
        some (supportedGateSecondAdvanceOutput inputLength raw) := by
    have hrun := run_bits_mono
      (run_supportedGateValidationAdvanceProgram inputLength
        (supportedGateThresholdStageOutput inputLength raw))
      hsecondAdvanceBits
    rw [supportedGateAdvance_thresholdStage] at hrun
    exact hrun
  have hmembership :
      runNPOracleProgram
          (preserveRightProgram canonicalBoolListValidationProgram)
          maximumBits
          (preserveRightFuel <|
            canonicalBoolListValidationFuel inputLength
              (supportedGateMembershipCode raw))
          (initialNPOracleState inputLength
            (supportedGateSecondAdvanceOutput inputLength raw)) =
        some (supportedGateMembershipStageOutput inputLength raw) := by
    have hrun := run_bits_mono
      (run_preserveRightProgram canonicalBoolListValidationProgram
        inputLength
        (canonicalBoolListValidationBits inputLength
          (supportedGateMembershipCode raw))
        (canonicalBoolListValidationFuel inputLength
          (supportedGateMembershipCode raw))
        (supportedGateMembershipCode raw)
        (Nat.pair 0 (supportedGateSecondAccumulator inputLength raw))
        (supportedGateMembershipValidationResult inputLength raw)
        (run_canonicalBoolListValidationProgram inputLength
          (supportedGateMembershipCode raw)))
      hmembershipBits
    simpa [supportedGateSecondAdvanceOutput,
      supportedGateMembershipStageOutput] using hrun
  have hgate :=
    run_bits_mono
      (run_supportedGateFieldGateProgram inputLength raw) hgateBits
  have hmembershipTail :=
    run_linkPrograms hpositive hlength hmembership hgate
  have hsecondAdvanceTail :=
    run_linkPrograms hpositive hlength hsecondAdvance hmembershipTail
  have hthresholdTail :=
    run_linkPrograms hpositive hlength hthreshold hsecondAdvanceTail
  have hfirstAdvanceTail :=
    run_linkPrograms hpositive hlength hfirstAdvance hthresholdTail
  have hweightsTail :=
    run_linkPrograms hpositive hlength hweights hfirstAdvanceTail
  have hprojectionTail :=
    run_linkPrograms hpositive hlength hprojection hweightsTail
  have hrun :=
    run_linkPrograms hpositive hlength htuple hprojectionTail
  simpa only [supportedGateFieldValidationProgram,
    supportedGateFieldValidationFuel, supportedGateTupleOutput] using hrun

/-! ## Exact field semantics -/

theorem supportedGateFieldValidationOutput_ne_zero_iff
    (inputLength raw : ℕ) :
    supportedGateFieldValidationOutput inputLength raw ≠ 0 ↔
      ∃ weightsCode thresholdCode membershipCode,
        decodeTaggedList raw =
            some [weightsCode, thresholdCode, membershipCode] ∧
          (decodeIntList weightsCode).isSome ∧
          (decodeInt thresholdCode).isSome ∧
          (decodeBoolList membershipCode).isSome := by
  constructor
  · intro houtput
    have htuple : supportedGateTupleFlag raw ≠ 0 := by
      intro hzero
      exact houtput <| by
        simp [supportedGateFieldValidationOutput, hzero]
    have hweights :
        supportedGateWeightsValidationResult inputLength raw ≠ 0 := by
      intro hzero
      exact houtput <| by
        simp [supportedGateFieldValidationOutput, hzero]
    have hthreshold :
        supportedGateThresholdValidationResult raw ≠ 0 := by
      intro hzero
      exact houtput <| by
        simp [supportedGateFieldValidationOutput, hzero]
    have hmembership :
        supportedGateMembershipValidationResult inputLength raw ≠ 0 := by
      intro hzero
      exact houtput <| by
        simp [supportedGateFieldValidationOutput, hzero]
    obtain ⟨weightsCode, thresholdCode, membershipCode, hdecode⟩ :=
      (supportedGateTupleFlag_ne_zero_iff raw).1 htuple
    have hcodes := supportedGateCodes_of_decode hdecode
    have hweightsSome :
        (decodeIntList (supportedGateWeightsCode raw)).isSome :=
      (canonicalIntListValidationOutput_ne_zero_iff_decodeIntList
        inputLength (supportedGateWeightsCode raw)).1 hweights
    have hthresholdSome :
        (decodeInt (supportedGateThresholdCode raw)).isSome :=
      (unitRationalValidationOutput_ne_zero_iff
        (supportedGateThresholdCode raw)).1 hthreshold
    have hmembershipSome :
        (decodeBoolList (supportedGateMembershipCode raw)).isSome :=
      (canonicalBoolListValidationOutput_ne_zero_iff_decodeBoolList
        inputLength (supportedGateMembershipCode raw)).1 hmembership
    exact
      ⟨weightsCode, thresholdCode, membershipCode, hdecode,
        hcodes.1 ▸ hweightsSome,
        hcodes.2.1 ▸ hthresholdSome,
        hcodes.2.2 ▸ hmembershipSome⟩
  · rintro ⟨weightsCode, thresholdCode, membershipCode, hdecode,
      hweightsSome, hthresholdSome, hmembershipSome⟩
    have htuple :
        supportedGateTupleFlag raw ≠ 0 :=
      (supportedGateTupleFlag_ne_zero_iff raw).2
        ⟨weightsCode, thresholdCode, membershipCode, hdecode⟩
    have hcodes := supportedGateCodes_of_decode hdecode
    have hweights :
        supportedGateWeightsValidationResult inputLength raw ≠ 0 := by
      apply
        (canonicalIntListValidationOutput_ne_zero_iff_decodeIntList
          inputLength (supportedGateWeightsCode raw)).2
      exact hcodes.1.symm ▸ hweightsSome
    have hthreshold :
        supportedGateThresholdValidationResult raw ≠ 0 := by
      apply
        (unitRationalValidationOutput_ne_zero_iff
          (supportedGateThresholdCode raw)).2
      exact hcodes.2.1.symm ▸ hthresholdSome
    have hmembership :
        supportedGateMembershipValidationResult inputLength raw ≠ 0 := by
      apply
        (canonicalBoolListValidationOutput_ne_zero_iff_decodeBoolList
          inputLength (supportedGateMembershipCode raw)).2
      exact hcodes.2.2.symm ▸ hmembershipSome
    rw [show supportedGateFieldValidationOutput inputLength raw =
        (Nat.pair 1 <|
          Nat.pair (supportedGateThresholdCode raw) <|
            Nat.pair (supportedGateWeightsCode raw)
              (supportedGateMembershipCode raw)) by
      simp [supportedGateFieldValidationOutput, htuple, hweights,
        hthreshold, hmembership]]
    have hpositive :
        1 ≤
          (Nat.pair 1 <|
            Nat.pair (supportedGateThresholdCode raw) <|
              Nat.pair (supportedGateWeightsCode raw)
                (supportedGateMembershipCode raw)) :=
      Nat.left_le_pair 1 _
    exact (Nat.zero_lt_one.trans_le hpositive).ne'

end NearCubicWires.CanonicalSupportedGateValidationProgram
