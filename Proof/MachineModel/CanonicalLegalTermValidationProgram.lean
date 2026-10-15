import Proof.MachineModel.CanonicalRationalValidationProgram
import Proof.MachineModel.CanonicalTaggedTupleProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Canonical legal-term validation

A legal circuit term is the fixed tagged tuple
`[canonical rational coefficient, family-specific circuit]`.  This module
validates that common prefix once and exposes the circuit code only after the
tuple and coefficient have both passed.  The mode-specific circuit validator
therefore has one fail-closed attachment point and never receives a
host-prepared payload.
-/

namespace NearCubicWires.CanonicalLegalTermValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRationalValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Fixed term tuple -/

def legalTermTupleOutput (raw : ℕ) : ℕ :=
  taggedTupleOutput 2 raw

def legalTermTupleFlag (raw : ℕ) : ℕ :=
  (Nat.unpair (legalTermTupleOutput raw)).1

def legalTermTupleFields (raw : ℕ) : ℕ :=
  (Nat.unpair (legalTermTupleOutput raw)).2

def legalTermCoefficientFrame (raw : ℕ) : ℕ :=
  (Nat.unpair (legalTermTupleFields raw)).1

def legalTermCoefficientCode (raw : ℕ) : ℕ :=
  (Nat.unpair (legalTermCoefficientFrame raw)).2

def legalTermCircuitCode (raw : ℕ) : ℕ :=
  (Nat.unpair (legalTermTupleFields raw)).2

theorem legalTermTupleFlag_ne_zero_iff
    (raw : ℕ) :
    legalTermTupleFlag raw ≠ 0 ↔
      ∃ coefficientCode circuitCode,
        decodeTaggedList raw =
          some [coefficientCode, circuitCode] := by
  constructor
  · intro hflag
    have htuple : taggedTupleOutput 2 raw ≠ 0 := by
      intro hzero
      exact hflag <| by
        simp [legalTermTupleFlag, legalTermTupleOutput, hzero]
    obtain ⟨values, hdecode, hlength⟩ :=
      (taggedTupleOutput_ne_zero_iff_decodeTaggedList 2 raw).1 htuple
    cases values with
    | nil => simp at hlength
    | cons coefficientCode rest =>
        cases rest with
        | nil => simp at hlength
        | cons circuitCode rest =>
            cases rest with
            | nil => exact ⟨coefficientCode, circuitCode, hdecode⟩
            | cons extra tail => simp at hlength
  · rintro ⟨coefficientCode, circuitCode, hdecode⟩
    have hraw :
        encodeTaggedList [coefficientCode, circuitCode] = raw :=
      encodeTaggedList_of_decode hdecode
    have htupleDecode :
        decodeTaggedTuple 2 raw =
          some (reversePairFields
            [coefficientCode, circuitCode]) := by
      rw [← hraw]
      exact decodeTaggedTuple_encode [coefficientCode, circuitCode]
    simp [legalTermTupleFlag, legalTermTupleOutput, taggedTupleOutput,
      htupleDecode]

theorem legalTermCodes_of_decode
    {raw coefficientCode circuitCode : ℕ}
    (hdecode :
      decodeTaggedList raw =
        some [coefficientCode, circuitCode]) :
    legalTermCoefficientCode raw = coefficientCode ∧
      legalTermCircuitCode raw = circuitCode := by
  have hraw :
      encodeTaggedList [coefficientCode, circuitCode] = raw :=
    encodeTaggedList_of_decode hdecode
  have htupleDecode :
      decodeTaggedTuple 2 raw =
        some (reversePairFields
          [coefficientCode, circuitCode]) := by
    rw [← hraw]
    exact decodeTaggedTuple_encode [coefficientCode, circuitCode]
  have htupleOutput :
      legalTermTupleOutput raw =
        Nat.pair 1
          (reversePairFields [coefficientCode, circuitCode]) := by
    simp [legalTermTupleOutput, taggedTupleOutput, htupleDecode]
  simp [legalTermCoefficientCode, legalTermCoefficientFrame,
    legalTermCircuitCode, legalTermTupleFields, htupleOutput,
    reversePairFields]

/-! ## Tuple-field projection -/

def legalTermProjectionContext (raw : ℕ) : ℕ :=
  Nat.pair (legalTermTupleFlag raw) (legalTermCircuitCode raw)

def legalTermProjectionOutput (raw : ℕ) : ℕ :=
  Nat.pair (legalTermCoefficientCode raw)
    (legalTermProjectionContext raw)

def legalTermProjectionProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 4 5 4
  , .unpairRight 3 6 5
  , .pair 2 6 7 6
  , .pair 5 7 0 7
  , .halt 0
  ]

@[simp] theorem legalTermProjectionProgram_oracleFree :
    OracleFree legalTermProjectionProgram := by
  rfl

def legalTermProjectionFuel : ℕ := 8

private def legalTermProjectionValues
    (inputLength raw : ℕ) : List ℕ :=
  [ inputLength
  , legalTermTupleOutput raw
  , legalTermTupleFlag raw
  , legalTermTupleFields raw
  , legalTermCoefficientFrame raw
  , legalTermCoefficientCode raw
  , legalTermCircuitCode raw
  , legalTermProjectionContext raw
  , legalTermProjectionOutput raw
  ]

def legalTermProjectionBits
    (inputLength raw : ℕ) : ℕ :=
  (legalTermProjectionValues inputLength raw).map natBitLength
    |>.foldr max 1

private theorem bitLength_le_foldr_max_of_mem
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
    (hvalue : value ∈ legalTermProjectionValues inputLength raw) :
    natBitLength value ≤ legalTermProjectionBits inputLength raw := by
  unfold legalTermProjectionBits
  exact bitLength_le_foldr_max_of_mem hvalue

theorem run_legalTermProjectionProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram legalTermProjectionProgram
        (legalTermProjectionBits inputLength raw)
        legalTermProjectionFuel
        (initialNPOracleState inputLength
          (legalTermTupleOutput raw)) =
      some (legalTermProjectionOutput raw) := by
  let maximumBits := legalTermProjectionBits inputLength raw
  have hflag :
      natBitLength (legalTermTupleFlag raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [legalTermProjectionValues])
  have hfields :
      natBitLength (legalTermTupleFields raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [legalTermProjectionValues])
  have hframe :
      natBitLength (legalTermCoefficientFrame raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [legalTermProjectionValues])
  have hcoefficient :
      natBitLength (legalTermCoefficientCode raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [legalTermProjectionValues])
  have hcircuit :
      natBitLength (legalTermCircuitCode raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [legalTermProjectionValues])
  have hcontext :
      natBitLength (legalTermProjectionContext raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [legalTermProjectionValues])
  have houtput :
      natBitLength (legalTermProjectionOutput raw) ≤ maximumBits :=
    projectionValue_bits (by
      simp [legalTermProjectionValues])
  rw [show legalTermProjectionFuel = 7 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (program := legalTermProjectionProgram)
    (maximumBits := maximumBits) (fuel := 7)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := legalTermTupleFlag raw)
    (by rfl) rfl
    (by simp [initialNPOracleState, legalTermTupleFlag,
      legalTermTupleOutput])
    hflag]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := legalTermProjectionProgram)
    (maximumBits := maximumBits) (fuel := 6)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := legalTermTupleFields raw)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, legalTermTupleFields, legalTermTupleOutput])
    hfields]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := legalTermProjectionProgram)
    (maximumBits := maximumBits) (fuel := 5)
    (pc := 2) (source := 3) (destination := 4) (next := 3)
    (value := legalTermCoefficientFrame raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      legalTermCoefficientFrame])
    hframe]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := legalTermProjectionProgram)
    (maximumBits := maximumBits) (fuel := 4)
    (pc := 3) (source := 4) (destination := 5) (next := 4)
    (value := legalTermCoefficientCode raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      legalTermCoefficientCode])
    hcoefficient]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := legalTermProjectionProgram)
    (maximumBits := maximumBits) (fuel := 3)
    (pc := 4) (source := 3) (destination := 6) (next := 5)
    (value := legalTermCircuitCode raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      legalTermCircuitCode])
    hcircuit]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (program := legalTermProjectionProgram)
    (maximumBits := maximumBits) (fuel := 2)
    (pc := 5) (left := 2) (right := 6) (destination := 7) (next := 6)
    (value := legalTermProjectionContext raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      legalTermProjectionContext])
    hcontext]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := legalTermProjectionProgram)
    (maximumBits := maximumBits) (fuel := 1)
    (pc := 6) (left := 5) (right := 7) (destination := 0) (next := 7)
    (value := legalTermProjectionOutput raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      legalTermProjectionOutput])
    houtput]
  exact run_halt_instruction
    (program := legalTermProjectionProgram)
    (maximumBits := maximumBits) (fuel := 0)
    (pc := 7) (outputRegister := 0)
    (value := legalTermProjectionOutput raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## Rational validation with retained circuit context -/

def legalTermRationalStageProgram : NPOracleProgram :=
  preserveRightProgram rationalValidationProgram

@[simp] theorem legalTermRationalStageProgram_oracleFree :
    OracleFree legalTermRationalStageProgram := by
  exact preserveRightProgram_oracleFree rationalValidationProgram
    rationalValidationProgram_oracleFree

def legalTermRationalStageOutput (raw : ℕ) : ℕ :=
  Nat.pair
    (rationalValidationOutput (legalTermCoefficientCode raw))
    (legalTermProjectionContext raw)

def legalTermRationalStageFuel
    (inputLength raw : ℕ) : ℕ :=
  preserveRightFuel <|
    rationalValidationFuel inputLength (legalTermCoefficientCode raw)

def legalTermRationalStageBits
    (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (rationalValidationBits inputLength
      (legalTermCoefficientCode raw))
    (legalTermCoefficientCode raw)
    (legalTermProjectionContext raw)
    (rationalValidationOutput (legalTermCoefficientCode raw))

theorem run_legalTermRationalStageProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram legalTermRationalStageProgram
        (legalTermRationalStageBits inputLength raw)
        (legalTermRationalStageFuel inputLength raw)
        (initialNPOracleState inputLength
          (legalTermProjectionOutput raw)) =
      some (legalTermRationalStageOutput raw) := by
  exact run_preserveRightProgram rationalValidationProgram
    inputLength
    (rationalValidationBits inputLength
      (legalTermCoefficientCode raw))
    (rationalValidationFuel inputLength
      (legalTermCoefficientCode raw))
    (legalTermCoefficientCode raw)
    (legalTermProjectionContext raw)
    (rationalValidationOutput (legalTermCoefficientCode raw))
    (run_rationalValidationProgram inputLength
      (legalTermCoefficientCode raw))

/-! ## Fail-closed circuit handoff -/

def legalTermCoefficientValidationOutput (raw : ℕ) : ℕ :=
  if legalTermTupleFlag raw = 0 then
    0
  else if rationalValidationOutput
      (legalTermCoefficientCode raw) = 0 then
    0
  else
    Nat.pair 1 <|
      Nat.pair
        (rationalValidationOutput (legalTermCoefficientCode raw))
        (legalTermCircuitCode raw)

def legalTermCoefficientGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .branchZero 4 9 5
  , .branchZero 2 9 6
  , .set 6 1 7
  , .pair 2 5 7 8
  , .pair 6 7 0 10
  , .set 0 0 10
  , .halt 0
  ]

@[simp] theorem legalTermCoefficientGateProgram_oracleFree :
    OracleFree legalTermCoefficientGateProgram := by
  rfl

def legalTermCoefficientGateFuel : ℕ := 11

private def legalTermCoefficientGateValues
    (inputLength raw : ℕ) : List ℕ :=
  [ inputLength
  , legalTermRationalStageOutput raw
  , rationalValidationOutput (legalTermCoefficientCode raw)
  , legalTermProjectionContext raw
  , legalTermTupleFlag raw
  , legalTermCircuitCode raw
  , 0
  , 1
  , Nat.pair
      (rationalValidationOutput (legalTermCoefficientCode raw))
      (legalTermCircuitCode raw)
  , Nat.pair 1 <|
      Nat.pair
        (rationalValidationOutput (legalTermCoefficientCode raw))
        (legalTermCircuitCode raw)
  , legalTermCoefficientValidationOutput raw
  ]

def legalTermCoefficientGateBits
    (inputLength raw : ℕ) : ℕ :=
  (legalTermCoefficientGateValues inputLength raw).map natBitLength
    |>.foldr max 1

private theorem coefficientGateValue_bits
    {inputLength raw value : ℕ}
    (hvalue :
      value ∈ legalTermCoefficientGateValues inputLength raw) :
    natBitLength value ≤
      legalTermCoefficientGateBits inputLength raw := by
  unfold legalTermCoefficientGateBits
  exact bitLength_le_foldr_max_of_mem hvalue

theorem run_legalTermCoefficientGateProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram legalTermCoefficientGateProgram
        (legalTermCoefficientGateBits inputLength raw)
        legalTermCoefficientGateFuel
        (initialNPOracleState inputLength
          (legalTermRationalStageOutput raw)) =
      some (legalTermCoefficientValidationOutput raw) := by
  let rational :=
    rationalValidationOutput (legalTermCoefficientCode raw)
  let context := legalTermProjectionContext raw
  let flag := legalTermTupleFlag raw
  let circuit := legalTermCircuitCode raw
  let payload := Nat.pair rational circuit
  let accepted := Nat.pair 1 payload
  let maximumBits := legalTermCoefficientGateBits inputLength raw
  have hrational : natBitLength rational ≤ maximumBits := by
    apply coefficientGateValue_bits
    simp [legalTermCoefficientGateValues, rational]
  have hcontext : natBitLength context ≤ maximumBits := by
    apply coefficientGateValue_bits
    simp [legalTermCoefficientGateValues, context]
  have hflagBits : natBitLength flag ≤ maximumBits := by
    apply coefficientGateValue_bits
    simp [legalTermCoefficientGateValues, flag]
  have hcircuit : natBitLength circuit ≤ maximumBits := by
    apply coefficientGateValue_bits
    simp [legalTermCoefficientGateValues, circuit]
  have hpayload : natBitLength payload ≤ maximumBits := by
    apply coefficientGateValue_bits
    simp [legalTermCoefficientGateValues, payload, rational, circuit]
  have hzero : natBitLength 0 ≤ maximumBits := by
    apply coefficientGateValue_bits
    simp [legalTermCoefficientGateValues]
  have hone : natBitLength 1 ≤ maximumBits := by
    apply coefficientGateValue_bits
    simp [legalTermCoefficientGateValues]
  have haccepted : natBitLength accepted ≤ maximumBits := by
    apply coefficientGateValue_bits
    simp [legalTermCoefficientGateValues, accepted, payload, rational,
      circuit]
  rw [show legalTermCoefficientGateFuel = 10 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (program := legalTermCoefficientGateProgram)
    (maximumBits := maximumBits) (fuel := 10)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := rational)
    (by rfl) rfl
    (by simp [initialNPOracleState, legalTermRationalStageOutput,
      rational])
    hrational]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := legalTermCoefficientGateProgram)
    (maximumBits := maximumBits) (fuel := 9)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := context)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, legalTermRationalStageOutput,
      rational, context])
    hcontext]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := legalTermCoefficientGateProgram)
    (maximumBits := maximumBits) (fuel := 8)
    (pc := 2) (source := 3) (destination := 4) (next := 3)
    (value := flag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      legalTermProjectionContext, context, flag])
    hflagBits]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := legalTermCoefficientGateProgram)
    (maximumBits := maximumBits) (fuel := 7)
    (pc := 3) (source := 3) (destination := 5) (next := 4)
    (value := circuit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      legalTermProjectionContext, context, flag, circuit])
    hcircuit]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_branchZero_instruction
    (program := legalTermCoefficientGateProgram)
    (maximumBits := maximumBits) (fuel := 6)
    (pc := 4) (register := 4) (zeroTarget := 9)
    (nonzeroTarget := 5)
    (by rfl) rfl]
  by_cases htuple : legalTermTupleFlag raw = 0
  · rw [if_pos (by simpa [flag] using htuple)]
    rw [show (6 : ℕ) = 5 + 1 by omega]
    rw [run_set_instruction
      (program := legalTermCoefficientGateProgram)
      (maximumBits := maximumBits) (fuel := 5)
      (pc := 9) (register := 0) (value := 0) (next := 10)
      (by rfl) rfl hzero]
    rw [show legalTermCoefficientValidationOutput raw = 0 by
      simp [legalTermCoefficientValidationOutput, htuple]]
    exact run_halt_instruction
      (program := legalTermCoefficientGateProgram)
      (maximumBits := maximumBits) (fuel := 4)
      (pc := 10) (outputRegister := 0) (value := 0)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hzero
  · by_cases hrational :
      rationalValidationOutput (legalTermCoefficientCode raw) = 0
    · rw [if_neg (by simpa [flag] using htuple)]
      rw [show (6 : ℕ) = 5 + 1 by omega]
      rw [run_branchZero_instruction
        (program := legalTermCoefficientGateProgram)
        (maximumBits := maximumBits) (fuel := 5)
        (pc := 5) (register := 2) (zeroTarget := 9)
        (nonzeroTarget := 6)
        (by rfl) rfl]
      rw [if_pos (by simpa [rational] using hrational)]
      rw [show (5 : ℕ) = 4 + 1 by omega]
      rw [run_set_instruction
        (program := legalTermCoefficientGateProgram)
        (maximumBits := maximumBits) (fuel := 4)
        (pc := 9) (register := 0) (value := 0) (next := 10)
        (by rfl) rfl hzero]
      rw [show legalTermCoefficientValidationOutput raw = 0 by
        simp [legalTermCoefficientValidationOutput, htuple,
          hrational]]
      exact run_halt_instruction
        (program := legalTermCoefficientGateProgram)
        (maximumBits := maximumBits) (fuel := 3)
        (pc := 10) (outputRegister := 0) (value := 0)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hzero
    · rw [if_neg (by simpa [flag] using htuple)]
      rw [show (6 : ℕ) = 5 + 1 by omega]
      rw [run_branchZero_instruction
        (program := legalTermCoefficientGateProgram)
        (maximumBits := maximumBits) (fuel := 5)
        (pc := 5) (register := 2) (zeroTarget := 9)
        (nonzeroTarget := 6)
        (by rfl) rfl]
      rw [if_neg (by simpa [rational] using hrational)]
      rw [show (5 : ℕ) = 4 + 1 by omega]
      rw [run_set_instruction
        (program := legalTermCoefficientGateProgram)
        (maximumBits := maximumBits) (fuel := 4)
        (pc := 6) (register := 6) (value := 1) (next := 7)
        (by rfl) rfl hone]
      rw [show (4 : ℕ) = 3 + 1 by omega]
      rw [run_pair_instruction
        (program := legalTermCoefficientGateProgram)
        (maximumBits := maximumBits) (fuel := 3)
        (pc := 7) (left := 2) (right := 5)
        (destination := 7) (next := 8) (value := payload)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump,
          payload, rational, circuit])
        hpayload]
      rw [show (3 : ℕ) = 2 + 1 by omega]
      rw [run_pair_instruction
        (program := legalTermCoefficientGateProgram)
        (maximumBits := maximumBits) (fuel := 2)
        (pc := 8) (left := 6) (right := 7)
        (destination := 0) (next := 10) (value := accepted)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump,
          accepted, payload])
        haccepted]
      rw [show legalTermCoefficientValidationOutput raw = accepted by
        simp [legalTermCoefficientValidationOutput, htuple,
          hrational, accepted, payload, rational, circuit]]
      exact run_halt_instruction
        (program := legalTermCoefficientGateProgram)
        (maximumBits := maximumBits) (fuel := 1)
        (pc := 10) (outputRegister := 0) (value := accepted)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) haccepted

/-! ## Unique composed coefficient prefix -/

def legalTermCoefficientValidationProgram : NPOracleProgram :=
  linkPrograms (taggedTupleProgram 2) <|
    linkPrograms legalTermProjectionProgram <|
      linkPrograms legalTermRationalStageProgram
        legalTermCoefficientGateProgram

@[simp] theorem legalTermCoefficientValidationProgram_oracleFree :
    OracleFree legalTermCoefficientValidationProgram := by
  exact oracleFree_linkPrograms (taggedTupleProgram_oracleFree 2) <|
    oracleFree_linkPrograms legalTermProjectionProgram_oracleFree <|
      oracleFree_linkPrograms legalTermRationalStageProgram_oracleFree
        legalTermCoefficientGateProgram_oracleFree

def legalTermCoefficientValidationFuel
    (inputLength raw : ℕ) : ℕ :=
  linkFuel
      (linkPrograms legalTermProjectionProgram <|
        linkPrograms legalTermRationalStageProgram
          legalTermCoefficientGateProgram)
      (taggedTupleFuel 2) <|
    linkFuel
        (linkPrograms legalTermRationalStageProgram
          legalTermCoefficientGateProgram)
        legalTermProjectionFuel <|
      linkFuel legalTermCoefficientGateProgram
        (legalTermRationalStageFuel inputLength raw)
        legalTermCoefficientGateFuel

def legalTermCoefficientValidationBits
    (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (taggedTupleBits inputLength 2 raw) <|
      max (legalTermProjectionBits inputLength raw) <|
        max (legalTermRationalStageBits inputLength raw)
          (legalTermCoefficientGateBits inputLength raw)

theorem run_legalTermCoefficientValidationProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram legalTermCoefficientValidationProgram
        (legalTermCoefficientValidationBits inputLength raw)
        (legalTermCoefficientValidationFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (legalTermCoefficientValidationOutput raw) := by
  let maximumBits :=
    legalTermCoefficientValidationBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, legalTermCoefficientValidationBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, legalTermCoefficientValidationBits]
  have htupleBits :
      taggedTupleBits inputLength 2 raw ≤ maximumBits := by
    simp [maximumBits, legalTermCoefficientValidationBits]
  have hprojectionBits :
      legalTermProjectionBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, legalTermCoefficientValidationBits]
  have hrationalBits :
      legalTermRationalStageBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, legalTermCoefficientValidationBits]
  have hgateBits :
      legalTermCoefficientGateBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, legalTermCoefficientValidationBits]
  have htuple :=
    run_bits_mono
      (run_taggedTupleProgram inputLength 2 raw) htupleBits
  have hprojection :=
    run_bits_mono
      (run_legalTermProjectionProgram inputLength raw)
      hprojectionBits
  have hrational :=
    run_bits_mono
      (run_legalTermRationalStageProgram inputLength raw)
      hrationalBits
  have hgate :=
    run_bits_mono
      (run_legalTermCoefficientGateProgram inputLength raw)
      hgateBits
  have hrationalTail :=
    run_linkPrograms hpositive hlength hrational hgate
  have hprojectionTail :=
    run_linkPrograms hpositive hlength hprojection hrationalTail
  have hrun :=
    run_linkPrograms hpositive hlength htuple hprojectionTail
  simpa [legalTermCoefficientValidationProgram,
    legalTermCoefficientValidationFuel,
    legalTermTupleOutput] using hrun

theorem legalTermCoefficientValidationOutput_ne_zero_iff
    (raw : ℕ) :
    legalTermCoefficientValidationOutput raw ≠ 0 ↔
      ∃ coefficientCode circuitCode coefficient,
        decodeTaggedList raw =
            some [coefficientCode, circuitCode] ∧
          decodeCanonicalRational coefficientCode = some coefficient := by
  constructor
  · intro houtput
    have htuple : legalTermTupleFlag raw ≠ 0 := by
      intro hzero
      exact houtput <| by
        simp [legalTermCoefficientValidationOutput, hzero]
    obtain ⟨coefficientCode, circuitCode, hdecode⟩ :=
      (legalTermTupleFlag_ne_zero_iff raw).1 htuple
    have hcodes := legalTermCodes_of_decode hdecode
    have hrational :
        rationalValidationOutput (legalTermCoefficientCode raw) ≠ 0 := by
      intro hzero
      exact houtput <| by
        simp [legalTermCoefficientValidationOutput, hzero]
    obtain ⟨coefficient, hcoefficient⟩ :=
      (rationalValidationOutput_ne_zero_iff_decodeCanonicalRational
        (legalTermCoefficientCode raw)).1 hrational
    exact
      ⟨coefficientCode, circuitCode, coefficient, hdecode,
        hcodes.1 ▸ hcoefficient⟩
  · rintro ⟨coefficientCode, circuitCode, coefficient,
      hdecode, hcoefficient⟩
    have htuple :
        legalTermTupleFlag raw ≠ 0 :=
      (legalTermTupleFlag_ne_zero_iff raw).2
        ⟨coefficientCode, circuitCode, hdecode⟩
    have hcodes := legalTermCodes_of_decode hdecode
    have hrational :
        rationalValidationOutput (legalTermCoefficientCode raw) ≠ 0 :=
      (rationalValidationOutput_ne_zero_iff_decodeCanonicalRational
        (legalTermCoefficientCode raw)).2
          ⟨coefficient, hcodes.1 ▸ hcoefficient⟩
    rw [show legalTermCoefficientValidationOutput raw =
        Nat.pair 1
          (Nat.pair
            (rationalValidationOutput (legalTermCoefficientCode raw))
            (legalTermCircuitCode raw)) by
      simp [legalTermCoefficientValidationOutput, htuple, hrational]]
    have hpositive :=
      Nat.left_le_pair 1 <|
        Nat.pair
          (rationalValidationOutput (legalTermCoefficientCode raw))
          (legalTermCircuitCode raw)
    omega

@[simp] theorem legalTermCoefficientValidationOutput_code
    {Circuit : CircuitFamily} {n : ℕ}
    (codec : CanonicalCircuitCodec Circuit)
    (term : LegalCircuitTerm Circuit n) :
    legalTermCoefficientValidationOutput (term.code codec) =
      Nat.pair 1
        (Nat.pair
          (rationalValidationOutput
            (encodeCanonicalRational term.coefficient))
          (codec.encode term.circuit)) := by
  have htuple :
      legalTermTupleFlag (term.code codec) ≠ 0 :=
    (legalTermTupleFlag_ne_zero_iff (term.code codec)).2 <|
      ⟨encodeCanonicalRational term.coefficient,
        codec.encode term.circuit, by
          simp [LegalCircuitTerm.code]⟩
  have hcodes :=
    legalTermCodes_of_decode
      (raw := term.code codec)
      (coefficientCode := encodeCanonicalRational term.coefficient)
      (circuitCode := codec.encode term.circuit)
      (by simp [LegalCircuitTerm.code])
  have hrational :
      rationalValidationOutput
          (legalTermCoefficientCode (term.code codec)) ≠ 0 := by
    apply
      (rationalValidationOutput_ne_zero_iff_decodeCanonicalRational
        (legalTermCoefficientCode (term.code codec))).2
    exact
      ⟨term.coefficient, hcodes.1 ▸
        decodeCanonicalRational_encode term.coefficient⟩
  have hrationalEncoded :
      rationalValidationOutput
          (encodeCanonicalRational term.coefficient) ≠ 0 := by
    simpa [hcodes.1] using hrational
  simp [legalTermCoefficientValidationOutput, htuple, hrationalEncoded,
    hcodes.1, hcodes.2]

end NearCubicWires.CanonicalLegalTermValidationProgram
