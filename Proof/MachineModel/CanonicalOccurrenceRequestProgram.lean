import Proof.MachineModel.CanonicalGateAtomHeadListProgram
import Proof.MachineModel.CanonicalSymmetricRowTableProgram

namespace NearCubicWires.CanonicalOccurrenceRequestProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalGateAtomHeadListProgram
open NearCubicWires.CanonicalSignedAtomRequestProgram
open NearCubicWires.CanonicalSignedGateEvaluationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbits : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

private theorem le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

/-! ## §1 The two gate fields a residual request reads

`encodeSupportedNormalizedGate` is a canonical tagged list whose first two
fields are the gate's encoded weight list and its encoded threshold.  Both are
read by fixed `unpair` chains, so no decoder appears below. -/

/-- The weight-list field of a canonical gate code, read structurally. -/
def gateCodeWeights (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair code).2).1

/-- The threshold field of a canonical gate code, read structurally. -/
def gateCodeThreshold (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2).1

@[simp] theorem gateCodeWeights_encodeSupportedNormalizedGate {n : ℕ}
    (gate : SupportedNormalizedGate n) :
    gateCodeWeights (encodeSupportedNormalizedGate gate) =
      encodeBalancedList (gateWeightCodes gate.gate) := by
  simp [gateCodeWeights, encodeSupportedNormalizedGate, encodeTaggedList,
    encodeIntList, gateWeightCodes]

@[simp] theorem gateCodeThreshold_encodeSupportedNormalizedGate {n : ℕ}
    (gate : SupportedNormalizedGate n) :
    gateCodeThreshold (encodeSupportedNormalizedGate gate) =
      encodeInt gate.gate.threshold := by
  simp [gateCodeThreshold, encodeSupportedNormalizedGate, encodeTaggedList]

/-! ## §2 The framing adapter

One straight-line program.  It reads the index, the gate code and the two
masks off its request, extracts the gate's two encoded fields, generates the
four range lengths from the public arity, and assembles §14's input beside the
index it must return. -/

/-- The mask half of one coordinate frame. -/
private def frameMaskFrame (wanted maskCode : ℕ) : ℕ :=
  Nat.pair wanted maskCode

/-- The two mask pairs of a two-block frozen body. -/
private def frameBlockMasks (inputMask liveMask : ℕ) : ℕ :=
  Nat.pair (signedAtomMaskPair liveMask 0)
    (signedAtomMaskPair inputMask liveMask)

/-- The head atom's own data beside a two-block coordinate body. -/
private def frameBlockHead
    (weightsCode thresholdCode inputMask liveMask : ℕ) : ℕ :=
  Nat.pair (gateHeadContext thresholdCode 0)
    (gateAtomBlockContext weightsCode 1 (signedAtomMaskPair liveMask 0)
      (signedAtomMaskPair inputMask liveMask))

/-- The evaluation half's left generator request. -/
private def frameEvaluationLeft
    (arity weightsCode thresholdCode inputMask : ℕ) : ℕ :=
  gateHeadListInput (arity + 1) thresholdCode 0
    (signedAtomContext weightsCode 1 inputMask)

/-- The evaluation half's right generator request. -/
private def frameEvaluationRight
    (arity weightsCode thresholdCode inputMask : ℕ) : ℕ :=
  gateHeadListInput (arity + 1) thresholdCode 1
    (signedAtomContext weightsCode 0 inputMask)

/-- The constant half's left generator request. -/
private def frameConstantLeft
    (arity weightsCode thresholdCode inputMask liveMask : ℕ) : ℕ :=
  gateHeadListInput (2 * arity + 1) thresholdCode 0
    (gateAtomBlockContext weightsCode 1 (signedAtomMaskPair liveMask 0)
      (signedAtomMaskPair inputMask liveMask))

/-- The constant half's right generator request. -/
private def frameConstantRight
    (arity weightsCode thresholdCode inputMask liveMask : ℕ) : ℕ :=
  gateHeadListInput (arity + 1) thresholdCode 1
    (signedAtomContext weightsCode 0 (signedAtomMaskPair inputMask liveMask))

/-- The evaluation half of §14's input. -/
private def frameEvaluationHalf
    (arity weightsCode thresholdCode inputMask : ℕ) : ℕ :=
  Nat.pair (frameEvaluationLeft arity weightsCode thresholdCode inputMask)
    (frameEvaluationRight arity weightsCode thresholdCode inputMask)

/-- The constant half of §14's input. -/
private def frameConstantHalf
    (arity weightsCode thresholdCode inputMask liveMask : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair 0
      (frameConstantLeft arity weightsCode thresholdCode inputMask liveMask))
    (Nat.pair 1
      (frameConstantRight arity weightsCode thresholdCode inputMask liveMask))

/-- **§14's input, as a function of the raw gate fields.**  Every occurrence of
the gate's syntax is one of the two encoded fields the machine reads. -/
def rawResidualVariableRequestInput
    (arity weightsCode thresholdCode inputMask liveMask : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair 0
      (frameEvaluationHalf arity weightsCode thresholdCode inputMask))
    (Nat.pair 1
      (frameConstantHalf arity weightsCode thresholdCode inputMask liveMask))

theorem rawResidualVariableRequestInput_gate {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask : ℕ) :
    rawResidualVariableRequestInput n
        (encodeBalancedList (gateWeightCodes gate)) (encodeInt gate.threshold)
        inputMask liveMask =
      residualVariableRequestInput gate inputMask liveMask :=
  rfl

/-- The framing adapter's request: the pool index beside the encoded gate and
the two masks. -/
def occurrenceFrameInput (index gateCode inputMask liveMask : ℕ) : ℕ :=
  Nat.pair index
    (Nat.pair gateCode (signedAtomMaskPair inputMask liveMask))

/-- The framing adapter's output: §14's input beside the retained index. -/
def occurrenceFrameOutput
    (arity index weightsCode thresholdCode inputMask liveMask : ℕ) : ℕ :=
  Nat.pair
    (rawResidualVariableRequestInput arity weightsCode thresholdCode inputMask
      liveMask)
    index

/-- **The per-occurrence framing adapter.** -/
def occurrenceFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairRight 4 8 7
  , .unpairLeft 8 9 8
  , .unpairRight 8 10 9
  , .unpairRight 10 11 10
  , .unpairLeft 11 12 11
  , .set 13 0 12
  , .set 14 1 13
  , .copy 1 15 14
  , .increment 15 15
  , .add 1 1 16 16
  , .increment 16 17
  , .pair 12 13 17 18
  , .pair 14 6 18 19
  , .pair 9 18 19 20
  , .pair 17 19 20 21
  , .pair 15 20 21 22
  , .pair 12 14 22 23
  , .pair 13 6 23 24
  , .pair 9 23 24 25
  , .pair 22 24 25 26
  , .pair 15 25 26 27
  , .pair 7 13 27 28
  , .pair 27 5 28 29
  , .pair 14 28 29 30
  , .pair 9 29 30 31
  , .pair 17 30 31 32
  , .pair 16 31 32 33
  , .pair 13 5 33 34
  , .pair 9 33 34 35
  , .pair 22 34 35 36
  , .pair 15 35 36 37
  , .pair 21 26 37 38
  , .pair 13 32 38 39
  , .pair 14 36 39 40
  , .pair 38 39 40 41
  , .pair 13 37 41 42
  , .pair 14 40 42 43
  , .pair 41 42 43 44
  , .pair 43 2 0 45
  , .halt 0
  ]

@[simp] theorem occurrenceFrameProgram_oracleFree :
    OracleFree occurrenceFrameProgram := by
  rfl

def occurrenceFrameFuel : ℕ := 46

def occurrenceFrameBits
    (arity index gateCode weightsCode thresholdCode inputMask liveMask : ℕ) :
    ℕ :=
  max (natBitLength (occurrenceFrameInput index gateCode inputMask liveMask))
    (natBitLength
      (occurrenceFrameOutput arity index weightsCode thresholdCode inputMask
        liveMask))

set_option maxHeartbeats 1600000 in
-- Forty-five straight-line instructions at one shared register width; every
-- intermediate is a subterm of the request or of the emitted tree, so the two
-- anchors of `occurrenceFrameBits` bound them all.
/-- **The per-occurrence framing adapter, executed.** -/
theorem run_occurrenceFrameProgram
    (arity index gateCode weightsCode thresholdCode inputMask liveMask
      maximumBits : ℕ)
    (hweights : weightsCode = gateCodeWeights gateCode)
    (hthreshold : thresholdCode = gateCodeThreshold gateCode)
    (hbits :
      occurrenceFrameBits arity index gateCode weightsCode thresholdCode
          inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram occurrenceFrameProgram maximumBits occurrenceFrameFuel
        (initialNPOracleState arity
          (occurrenceFrameInput index gateCode inputMask liveMask)) =
      some
        (occurrenceFrameOutput arity index weightsCode thresholdCode inputMask
          liveMask) := by
  have hinputBits :
      natBitLength
          (Nat.pair index
            (Nat.pair gateCode (signedAtomMaskPair inputMask liveMask))) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have houtputBits :
      natBitLength
          (Nat.pair
            (rawResidualVariableRequestInput arity weightsCode thresholdCode
              inputMask liveMask)
            index) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  have hindexBits : natBitLength index ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hgatePairBits :
      natBitLength
          (Nat.pair gateCode (signedAtomMaskPair inputMask liveMask)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hgateCodeBits : natBitLength gateCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hgatePairBits
  have hmaskPairBits :
      natBitLength (signedAtomMaskPair inputMask liveMask) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hgatePairBits
  have hinputMaskBits : natBitLength inputMask ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hmaskPairBits
  have hliveMaskBits : natBitLength liveMask ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hmaskPairBits
  have hgateTailBits : natBitLength (Nat.unpair gateCode).2 ≤ maximumBits :=
    bits_of_le (Nat.unpair_right_le _) hgateCodeBits
  have hweightsBits : natBitLength weightsCode ≤ maximumBits := by
    rw [hweights]
    exact bits_of_le (Nat.unpair_left_le _) hgateTailBits
  have hgateTailTwoBits :
      natBitLength (Nat.unpair (Nat.unpair gateCode).2).2 ≤ maximumBits :=
    bits_of_le (Nat.unpair_right_le _) hgateTailBits
  have hgateTailThreeBits :
      natBitLength (Nat.unpair (Nat.unpair (Nat.unpair gateCode).2).2).2 ≤
        maximumBits :=
    bits_of_le (Nat.unpair_right_le _) hgateTailTwoBits
  have hthresholdBits : natBitLength thresholdCode ≤ maximumBits := by
    rw [hthreshold]
    exact bits_of_le (Nat.unpair_left_le _) hgateTailThreeBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    bits_of_le (Nat.zero_le inputMask) hinputMaskBits
  have hrawBits :
      natBitLength
          (rawResidualVariableRequestInput arity weightsCode thresholdCode
            inputMask liveMask) ≤
        maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houtputBits
  have htaggedEvaluationBits :
      natBitLength
          (Nat.pair 0
            (frameEvaluationHalf arity weightsCode thresholdCode inputMask)) ≤
        maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hrawBits
  have htaggedConstantBits :
      natBitLength
          (Nat.pair 1
            (frameConstantHalf arity weightsCode thresholdCode inputMask
              liveMask)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hrawBits
  have hevaluationHalfBits :
      natBitLength
          (frameEvaluationHalf arity weightsCode thresholdCode inputMask) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) htaggedEvaluationBits
  have hconstantHalfBits :
      natBitLength
          (frameConstantHalf arity weightsCode thresholdCode inputMask
            liveMask) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) htaggedConstantBits
  have hevalLeftBits :
      natBitLength
          (frameEvaluationLeft arity weightsCode thresholdCode inputMask) ≤
        maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hevaluationHalfBits
  have hevalRightBits :
      natBitLength
          (frameEvaluationRight arity weightsCode thresholdCode inputMask) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hevaluationHalfBits
  have htaggedConstantLeftBits :
      natBitLength
          (Nat.pair 0
            (frameConstantLeft arity weightsCode thresholdCode inputMask
              liveMask)) ≤
        maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hconstantHalfBits
  have htaggedConstantRightBits :
      natBitLength
          (Nat.pair 1
            (frameConstantRight arity weightsCode thresholdCode inputMask
              liveMask)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hconstantHalfBits
  have hconstantLeftBits :
      natBitLength
          (frameConstantLeft arity weightsCode thresholdCode inputMask
            liveMask) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) htaggedConstantLeftBits
  have hconstantRightBits :
      natBitLength
          (frameConstantRight arity weightsCode thresholdCode inputMask
            liveMask) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) htaggedConstantRightBits
  have hsuccBits : natBitLength (arity + 1) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hevalLeftBits
  have hevalLeftHeadBits :
      natBitLength
          (gateAtomHeadContext thresholdCode 0 weightsCode 1 inputMask) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hevalLeftBits
  have hheadZeroBits :
      natBitLength (gateHeadContext thresholdCode 0) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hevalLeftHeadBits
  have hevalLeftContextBits :
      natBitLength (signedAtomContext weightsCode 1 inputMask) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hevalLeftHeadBits
  have honeMaskBits :
      natBitLength (frameMaskFrame 1 inputMask) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hevalLeftContextBits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) honeMaskBits
  have hevalRightHeadBits :
      natBitLength
          (gateAtomHeadContext thresholdCode 1 weightsCode 0 inputMask) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hevalRightBits
  have hheadOneBits :
      natBitLength (gateHeadContext thresholdCode 1) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hevalRightHeadBits
  have hevalRightContextBits :
      natBitLength (signedAtomContext weightsCode 0 inputMask) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hevalRightHeadBits
  have hzeroMaskBits :
      natBitLength (frameMaskFrame 0 inputMask) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hevalRightContextBits
  have hdoubleSuccBits : natBitLength (2 * arity + 1) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hconstantLeftBits
  have hblockHeadBits :
      natBitLength
          (frameBlockHead weightsCode thresholdCode inputMask liveMask) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hconstantLeftBits
  have hblockContextBits :
      natBitLength
          (gateAtomBlockContext weightsCode 1 (signedAtomMaskPair liveMask 0)
            (signedAtomMaskPair inputMask liveMask)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hblockHeadBits
  have hblockFrameBits :
      natBitLength
          (frameMaskFrame 1 (frameBlockMasks inputMask liveMask)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hblockContextBits
  have hblockMasksBits :
      natBitLength (frameBlockMasks inputMask liveMask) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hblockFrameBits
  have hlivePairBits :
      natBitLength (signedAtomMaskPair liveMask 0) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hblockMasksBits
  have hconstantRightHeadBits :
      natBitLength
          (gateAtomHeadContext thresholdCode 1 weightsCode 0
            (signedAtomMaskPair inputMask liveMask)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hconstantRightBits
  have hconstantRightContextBits :
      natBitLength
          (signedAtomContext weightsCode 0
            (signedAtomMaskPair inputMask liveMask)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hconstantRightHeadBits
  have hpairedMaskBits :
      natBitLength
          (frameMaskFrame 0 (signedAtomMaskPair inputMask liveMask)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hconstantRightContextBits
  have harityBits : natBitLength arity ≤ maximumBits :=
    bits_of_le (Nat.le_succ _) hsuccBits
  have hdoubleBits : natBitLength (2 * arity) ≤ maximumBits :=
    bits_of_le (Nat.le_succ _) hdoubleSuccBits
  rw [show occurrenceFrameFuel =
      0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
        1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
        1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := index)
    (by rfl) rfl
    (by simp [initialNPOracleState, occurrenceFrameInput])
    hindexBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair gateCode (signedAtomMaskPair inputMask liveMask))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      occurrenceFrameInput])
    hgatePairBits]
  rw [run_unpairLeft_instruction
    (value := gateCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hgateCodeBits]
  rw [run_unpairRight_instruction
    (value := signedAtomMaskPair inputMask liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hmaskPairBits]
  rw [run_unpairLeft_instruction
    (value := inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomMaskPair])
    hinputMaskBits]
  rw [run_unpairRight_instruction
    (value := liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomMaskPair])
    hliveMaskBits]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair gateCode).2)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hgateTailBits]
  rw [run_unpairLeft_instruction
    (value := weightsCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, gateCodeWeights, hweights])
    hweightsBits]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair gateCode).2).2)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hgateTailTwoBits]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair (Nat.unpair gateCode).2).2).2)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hgateTailThreeBits]
  rw [run_unpairLeft_instruction
    (value := thresholdCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, gateCodeThreshold,
      hthreshold])
    hthresholdBits]
  rw [run_set_instruction (register := 13) (value := 0)
    (next := 12) (by rfl) rfl hzeroBits]
  rw [run_set_instruction (register := 14) (value := 1)
    (next := 13) (by rfl) rfl honeBits]
  rw [run_copy_instruction
    (value := arity)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    harityBits]
  rw [run_increment_instruction
    (value := arity + 1)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsuccBits]
  rw [run_add_instruction
    (value := 2 * arity)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      two_mul])
    hdoubleBits]
  rw [run_increment_instruction
    (value := 2 * arity + 1)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hdoubleSuccBits]
  rw [run_pair_instruction
    (value := gateHeadContext thresholdCode 0)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, gateHeadContext])
    hheadZeroBits]
  rw [run_pair_instruction
    (value := frameMaskFrame 1 inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frameMaskFrame])
    honeMaskBits]
  rw [run_pair_instruction
    (value := signedAtomContext weightsCode 1 inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomContext,
      frameMaskFrame])
    hevalLeftContextBits]
  rw [run_pair_instruction
    (value := gateAtomHeadContext thresholdCode 0 weightsCode 1 inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, gateAtomHeadContext])
    hevalLeftHeadBits]
  rw [run_pair_instruction
    (value := frameEvaluationLeft arity weightsCode thresholdCode inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frameEvaluationLeft,
      gateHeadListInput, generatedBalancedRangeInput,
      gateAtomHeadContext])
    hevalLeftBits]
  rw [run_pair_instruction
    (value := gateHeadContext thresholdCode 1)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, gateHeadContext])
    hheadOneBits]
  rw [run_pair_instruction
    (value := frameMaskFrame 0 inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frameMaskFrame])
    hzeroMaskBits]
  rw [run_pair_instruction
    (value := signedAtomContext weightsCode 0 inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomContext,
      frameMaskFrame])
    hevalRightContextBits]
  rw [run_pair_instruction
    (value := gateAtomHeadContext thresholdCode 1 weightsCode 0 inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, gateAtomHeadContext])
    hevalRightHeadBits]
  rw [run_pair_instruction
    (value := frameEvaluationRight arity weightsCode thresholdCode inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frameEvaluationRight,
      gateHeadListInput, generatedBalancedRangeInput,
      gateAtomHeadContext])
    hevalRightBits]
  rw [run_pair_instruction
    (value := signedAtomMaskPair liveMask 0)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomMaskPair])
    hlivePairBits]
  rw [run_pair_instruction
    (value := frameBlockMasks inputMask liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frameBlockMasks])
    hblockMasksBits]
  rw [run_pair_instruction
    (value := frameMaskFrame 1 (frameBlockMasks inputMask liveMask))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frameMaskFrame])
    hblockFrameBits]
  rw [run_pair_instruction
    (value := gateAtomBlockContext weightsCode 1 (signedAtomMaskPair liveMask 0)
        (signedAtomMaskPair inputMask liveMask))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, gateAtomBlockContext,
      frameMaskFrame, frameBlockMasks])
    hblockContextBits]
  rw [run_pair_instruction
    (value := frameBlockHead weightsCode thresholdCode inputMask liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frameBlockHead])
    hblockHeadBits]
  rw [run_pair_instruction
    (value := frameConstantLeft arity weightsCode thresholdCode inputMask liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frameConstantLeft,
      gateHeadListInput, generatedBalancedRangeInput, frameBlockHead])
    hconstantLeftBits]
  rw [run_pair_instruction
    (value := frameMaskFrame 0 (signedAtomMaskPair inputMask liveMask))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frameMaskFrame])
    hpairedMaskBits]
  rw [run_pair_instruction
    (value := signedAtomContext weightsCode 0 (signedAtomMaskPair inputMask liveMask))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomContext,
      frameMaskFrame])
    hconstantRightContextBits]
  rw [run_pair_instruction
    (value := gateAtomHeadContext thresholdCode 1 weightsCode 0
        (signedAtomMaskPair inputMask liveMask))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, gateAtomHeadContext])
    hconstantRightHeadBits]
  rw [run_pair_instruction
    (value := frameConstantRight arity weightsCode thresholdCode inputMask liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frameConstantRight,
      gateHeadListInput, generatedBalancedRangeInput,
      gateAtomHeadContext])
    hconstantRightBits]
  rw [run_pair_instruction
    (value := frameEvaluationHalf arity weightsCode thresholdCode inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frameEvaluationHalf])
    hevaluationHalfBits]
  rw [run_pair_instruction
    (value := Nat.pair 0 (frameConstantLeft arity weightsCode thresholdCode inputMask liveMask))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htaggedConstantLeftBits]
  rw [run_pair_instruction
    (value := Nat.pair 1 (frameConstantRight arity weightsCode thresholdCode inputMask liveMask))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htaggedConstantRightBits]
  rw [run_pair_instruction
    (value := frameConstantHalf arity weightsCode thresholdCode inputMask liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, frameConstantHalf])
    hconstantHalfBits]
  rw [run_pair_instruction
    (value := Nat.pair 0 (frameEvaluationHalf arity weightsCode thresholdCode inputMask))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htaggedEvaluationBits]
  rw [run_pair_instruction
    (value := Nat.pair 1 (frameConstantHalf arity weightsCode thresholdCode inputMask liveMask))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htaggedConstantBits]
  rw [run_pair_instruction
    (value := rawResidualVariableRequestInput arity weightsCode thresholdCode inputMask liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      rawResidualVariableRequestInput])
    hrawBits]
  rw [run_pair_instruction
    (value := occurrenceFrameOutput arity index weightsCode thresholdCode inputMask
        liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, occurrenceFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value :=
      occurrenceFrameOutput arity index weightsCode thresholdCode inputMask
        liveMask)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

def occurrenceRequestFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 3 2 4 3
  , .pair 1 4 0 4
  , .halt 0
  ]

@[simp] theorem occurrenceRequestFrameProgram_oracleFree :
    OracleFree occurrenceRequestFrameProgram := by
  rfl

def occurrenceRequestFrameBits (arity index requestCode : ℕ) : ℕ :=
  max (natBitLength (Nat.pair requestCode index))
    (natBitLength (nativeInputRequest arity (Nat.pair index requestCode)))

theorem run_occurrenceRequestFrameProgram
    (arity index requestCode maximumBits : ℕ)
    (hbits : occurrenceRequestFrameBits arity index requestCode ≤
      maximumBits) :
    runNPOracleProgram occurrenceRequestFrameProgram maximumBits 5
        (initialNPOracleState arity (Nat.pair requestCode index)) =
      some (nativeInputRequest arity (Nat.pair index requestCode)) := by
  have hinputBits :
      natBitLength (Nat.pair requestCode index) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have houtputBits :
      natBitLength (Nat.pair arity (Nat.pair index requestCode)) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  have hrequestBits : natBitLength requestCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hindexBits : natBitLength index ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hswapBits :
      natBitLength (Nat.pair index requestCode) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputBits
  rw [show (5 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := requestCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hrequestBits]
  rw [run_unpairRight_instruction
    (value := index)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hindexBits]
  rw [run_pair_instruction
    (value := Nat.pair index requestCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hswapBits]
  rw [run_pair_instruction
    (value := nativeInputRequest arity (Nat.pair index requestCode))
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        nativeInputRequest])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := nativeInputRequest arity (Nat.pair index requestCode))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

def occurrenceRequestProgram : NPOracleProgram :=
  linkPrograms occurrenceFrameProgram
    (linkPrograms (preserveRightProgram residualVariableRequestProgram)
      occurrenceRequestFrameProgram)

theorem occurrenceRequestProgram_oracleFree :
    OracleFree occurrenceRequestProgram :=
  oracleFree_linkPrograms occurrenceFrameProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree residualVariableRequestProgram
        residualVariableRequestProgram_oracleFree)
      occurrenceRequestFrameProgram_oracleFree)

/-- The occurrence's own gate, named once. -/
def occurrenceGate {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) : NormalizedThresholdGate q :=
  (occurrences.get index).gate

def occurrenceRequestFuel {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) (inputMask liveMask : ℕ) : ℕ :=
  linkFuel
      (linkPrograms (preserveRightProgram residualVariableRequestProgram)
        occurrenceRequestFrameProgram)
      occurrenceFrameFuel
    (linkFuel occurrenceRequestFrameProgram
      (preserveRightFuel
        (residualVariableRequestFuel (occurrenceGate occurrences index)
          inputMask liveMask))
      5)

def occurrenceRequestStageBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) (inputMask liveMask : ℕ) : List ℕ :=
  [ 1
  , natBitLength q
  , occurrenceFrameBits q index.val
      (encodeSupportedNormalizedGate (occurrences.get index))
      (encodeBalancedList (gateWeightCodes (occurrenceGate occurrences index)))
      (encodeInt (occurrenceGate occurrences index).threshold) inputMask
      liveMask
  , preserveRightBits
      (residualVariableRequestBits (occurrenceGate occurrences index) inputMask
        liveMask)
      (residualVariableRequestInput (occurrenceGate occurrences index)
        inputMask liveMask)
      index.val
      (residualVariableInput (occurrenceGate occurrences index) inputMask
        liveMask)
  , occurrenceRequestFrameBits q index.val
      (residualVariableInput (occurrenceGate occurrences index) inputMask
        liveMask)
  ]

def occurrenceRequestBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) (inputMask liveMask : ℕ) : ℕ :=
  (occurrenceRequestStageBits occurrences index inputMask liveMask).foldr max 1

theorem run_occurrenceRequestProgram {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) (inputMask liveMask maximumBits : ℕ)
    (hbits :
      occurrenceRequestBits occurrences index inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram occurrenceRequestProgram maximumBits
        (occurrenceRequestFuel occurrences index inputMask liveMask)
        (initialNPOracleState q
          (occurrenceFrameInput index.val
            (encodeSupportedNormalizedGate (occurrences.get index)) inputMask
            liveMask)) =
      some (residualAssignmentRequest occurrences inputMask liveMask index) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈ occurrenceRequestStageBits occurrences index inputMask
          liveMask) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [occurrenceRequestStageBits]
  have hlength : natBitLength q ≤ maximumBits := by
    apply bits_of_member
    simp [occurrenceRequestStageBits]
  have hframeBits :
      occurrenceFrameBits q index.val
          (encodeSupportedNormalizedGate (occurrences.get index))
          (encodeBalancedList
            (gateWeightCodes (occurrenceGate occurrences index)))
          (encodeInt (occurrenceGate occurrences index).threshold) inputMask
          liveMask ≤
        maximumBits := by
    apply bits_of_member
    simp [occurrenceRequestStageBits]
  have hpreserveBits :
      preserveRightBits
          (residualVariableRequestBits (occurrenceGate occurrences index)
            inputMask liveMask)
          (residualVariableRequestInput (occurrenceGate occurrences index)
            inputMask liveMask)
          index.val
          (residualVariableInput (occurrenceGate occurrences index) inputMask
            liveMask) ≤
        maximumBits := by
    apply bits_of_member
    simp [occurrenceRequestStageBits]
  have hleafBits :
      occurrenceRequestFrameBits q index.val
          (residualVariableInput (occurrenceGate occurrences index) inputMask
            liveMask) ≤
        maximumBits := by
    apply bits_of_member
    simp [occurrenceRequestStageBits]
  have hframeOutput :
      occurrenceFrameOutput q index.val
          (encodeBalancedList
            (gateWeightCodes (occurrenceGate occurrences index)))
          (encodeInt (occurrenceGate occurrences index).threshold) inputMask
          liveMask =
        Nat.pair
          (residualVariableRequestInput (occurrenceGate occurrences index)
            inputMask liveMask)
          index.val := by
    unfold occurrenceFrameOutput
    rw [rawResidualVariableRequestInput_gate]
  have hframe :
      runNPOracleProgram occurrenceFrameProgram maximumBits
          occurrenceFrameFuel
          (initialNPOracleState q
            (occurrenceFrameInput index.val
              (encodeSupportedNormalizedGate (occurrences.get index)) inputMask
              liveMask)) =
        some
          (Nat.pair
            (residualVariableRequestInput (occurrenceGate occurrences index)
              inputMask liveMask)
            index.val) := by
    rw [← hframeOutput]
    exact run_occurrenceFrameProgram q index.val
      (encodeSupportedNormalizedGate (occurrences.get index))
      (encodeBalancedList (gateWeightCodes (occurrenceGate occurrences index)))
      (encodeInt (occurrenceGate occurrences index).threshold) inputMask
      liveMask maximumBits
      (gateCodeWeights_encodeSupportedNormalizedGate
        (occurrences.get index)).symm
      (gateCodeThreshold_encodeSupportedNormalizedGate
        (occurrences.get index)).symm
      hframeBits
  have hresidual :
      runNPOracleProgram (preserveRightProgram residualVariableRequestProgram)
          maximumBits
          (preserveRightFuel
            (residualVariableRequestFuel (occurrenceGate occurrences index)
              inputMask liveMask))
          (initialNPOracleState q
            (Nat.pair
              (residualVariableRequestInput (occurrenceGate occurrences index)
                inputMask liveMask)
              index.val)) =
        some
          (Nat.pair
            (residualVariableInput (occurrenceGate occurrences index) inputMask
              liveMask)
            index.val) :=
    run_bits_mono
      (run_preserveRightProgram residualVariableRequestProgram q
        (residualVariableRequestBits (occurrenceGate occurrences index)
          inputMask liveMask)
        (residualVariableRequestFuel (occurrenceGate occurrences index)
          inputMask liveMask)
        (residualVariableRequestInput (occurrenceGate occurrences index)
          inputMask liveMask)
        index.val
        (residualVariableInput (occurrenceGate occurrences index) inputMask
          liveMask)
        (run_residualVariableRequestProgram (occurrenceGate occurrences index)
          inputMask liveMask _ le_rfl))
      hpreserveBits
  have hleaf :
      runNPOracleProgram occurrenceRequestFrameProgram maximumBits 5
          (initialNPOracleState q
            (Nat.pair
              (residualVariableInput (occurrenceGate occurrences index)
                inputMask liveMask)
              index.val)) =
        some (residualAssignmentRequest occurrences inputMask liveMask index) :=
    run_occurrenceRequestFrameProgram q index.val
      (residualVariableInput (occurrenceGate occurrences index) inputMask
        liveMask)
      maximumBits hleafBits
  exact run_linkPrograms hpositive hlength hframe
    (run_linkPrograms hpositive hlength hresidual hleaf)

/-- The pool's encoded gates, as one balanced tree. -/
def occurrencePoolTree {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q)) : ℕ :=
  encodeBalancedList (occurrences.map encodeSupportedNormalizedGate)

def occurrenceLookupFrameInput (index population poolTree maskPair : ℕ) : ℕ :=
  Nat.pair index (Nat.pair population (Nat.pair poolTree maskPair))

/-- The lookup request beside the retained index and masks. -/
def occurrenceLookupFrameOutput (index population poolTree maskPair : ℕ) : ℕ :=
  Nat.pair (Nat.pair population (Nat.pair index poolTree))
    (Nat.pair index maskPair)

def occurrenceLookupFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .pair 2 6 8 7
  , .pair 4 8 9 8
  , .pair 2 7 10 9
  , .pair 9 10 0 10
  , .halt 0
  ]

@[simp] theorem occurrenceLookupFrameProgram_oracleFree :
    OracleFree occurrenceLookupFrameProgram := by
  rfl

def occurrenceLookupFrameBits (index population poolTree maskPair : ℕ) : ℕ :=
  max
    (natBitLength
      (occurrenceLookupFrameInput index population poolTree maskPair))
    (natBitLength
      (occurrenceLookupFrameOutput index population poolTree maskPair))

theorem run_occurrenceLookupFrameProgram
    (arity index population poolTree maskPair maximumBits : ℕ)
    (hbits :
      occurrenceLookupFrameBits index population poolTree maskPair ≤
        maximumBits) :
    runNPOracleProgram occurrenceLookupFrameProgram maximumBits 11
        (initialNPOracleState arity
          (occurrenceLookupFrameInput index population poolTree maskPair)) =
      some (occurrenceLookupFrameOutput index population poolTree maskPair) := by
  have hinputBits :
      natBitLength
          (Nat.pair index (Nat.pair population (Nat.pair poolTree maskPair))) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have houtputBits :
      natBitLength
          (Nat.pair (Nat.pair population (Nat.pair index poolTree))
            (Nat.pair index maskPair)) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  have hindexBits : natBitLength index ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have htailBits :
      natBitLength (Nat.pair population (Nat.pair poolTree maskPair)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hpopulationBits : natBitLength population ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) htailBits
  have hpoolPairBits :
      natBitLength (Nat.pair poolTree maskPair) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) htailBits
  have hpoolBits : natBitLength poolTree ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hpoolPairBits
  have hmaskBits : natBitLength maskPair ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hpoolPairBits
  have hlookupBits :
      natBitLength (Nat.pair population (Nat.pair index poolTree)) ≤
        maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houtputBits
  have hindexPoolBits :
      natBitLength (Nat.pair index poolTree) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hlookupBits
  have hindexMaskBits :
      natBitLength (Nat.pair index maskPair) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputBits
  rw [show (11 : ℕ) =
      0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := index)
    (by rfl) rfl
    (by simp [initialNPOracleState, occurrenceLookupFrameInput])
    hindexBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair population (Nat.pair poolTree maskPair))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      occurrenceLookupFrameInput])
    htailBits]
  rw [run_unpairLeft_instruction
    (value := population)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpopulationBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair poolTree maskPair)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpoolPairBits]
  rw [run_unpairLeft_instruction
    (value := poolTree)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpoolBits]
  rw [run_unpairRight_instruction
    (value := maskPair)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hmaskBits]
  rw [run_pair_instruction
    (value := Nat.pair index poolTree)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hindexPoolBits]
  rw [run_pair_instruction
    (value := Nat.pair population (Nat.pair index poolTree))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hlookupBits]
  rw [run_pair_instruction
    (value := Nat.pair index maskPair)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hindexMaskBits]
  rw [run_pair_instruction
    (value := occurrenceLookupFrameOutput index population poolTree maskPair)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceLookupFrameOutput])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := occurrenceLookupFrameOutput index population poolTree maskPair)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Rebuild §2's request from the looked-up gate and the retained context. -/
def occurrenceLookupUnframeProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 5 6 5
  , .pair 4 6 0 6
  , .halt 0
  ]

@[simp] theorem occurrenceLookupUnframeProgram_oracleFree :
    OracleFree occurrenceLookupUnframeProgram := by
  rfl

def occurrenceLookupUnframeBits (index gateCode maskPair : ℕ) : ℕ :=
  max (natBitLength (Nat.pair gateCode (Nat.pair index maskPair)))
    (natBitLength (Nat.pair index (Nat.pair gateCode maskPair)))

theorem run_occurrenceLookupUnframeProgram
    (arity index gateCode maskPair maximumBits : ℕ)
    (hbits : occurrenceLookupUnframeBits index gateCode maskPair ≤
      maximumBits) :
    runNPOracleProgram occurrenceLookupUnframeProgram maximumBits 7
        (initialNPOracleState arity
          (Nat.pair gateCode (Nat.pair index maskPair))) =
      some (Nat.pair index (Nat.pair gateCode maskPair)) := by
  have hinputBits :
      natBitLength (Nat.pair gateCode (Nat.pair index maskPair)) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have houtputBits :
      natBitLength (Nat.pair index (Nat.pair gateCode maskPair)) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  have hgateBits : natBitLength gateCode ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hindexMaskBits :
      natBitLength (Nat.pair index maskPair) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hindexBits : natBitLength index ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hindexMaskBits
  have hmaskBits : natBitLength maskPair ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hindexMaskBits
  have hgateMaskBits :
      natBitLength (Nat.pair gateCode maskPair) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputBits
  rw [show (7 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := gateCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hgateBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair index maskPair)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hindexMaskBits]
  rw [run_unpairLeft_instruction
    (value := index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hindexBits]
  rw [run_unpairRight_instruction
    (value := maskPair)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hmaskBits]
  rw [run_pair_instruction
    (value := Nat.pair gateCode maskPair)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hgateMaskBits]
  rw [run_pair_instruction
    (value := Nat.pair index (Nat.pair gateCode maskPair))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := Nat.pair index (Nat.pair gateCode maskPair))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

def occurrencePoolLeafProgram : NPOracleProgram :=
  linkPrograms occurrenceLookupFrameProgram
    (linkPrograms (preserveRightProgram canonicalBalancedLookupProgram)
      (linkPrograms occurrenceLookupUnframeProgram occurrenceRequestProgram))

theorem occurrencePoolLeafProgram_oracleFree :
    OracleFree occurrencePoolLeafProgram :=
  oracleFree_linkPrograms occurrenceLookupFrameProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree canonicalBalancedLookupProgram
        canonicalBalancedLookupProgram_oracleFree)
      (oracleFree_linkPrograms occurrenceLookupUnframeProgram_oracleFree
        occurrenceRequestProgram_oracleFree))

/-- The pool's encoded gate list, named once. -/
def occurrencePoolCodes {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q)) : List ℕ :=
  occurrences.map encodeSupportedNormalizedGate

@[simp] theorem occurrencePoolCodes_length {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q)) :
    (occurrencePoolCodes occurrences).length = occurrences.length := by
  simp [occurrencePoolCodes]

private theorem occurrencePoolCodes_lookupInput {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q)) (index : ℕ) :
    Nat.pair occurrences.length
        (Nat.pair index (occurrencePoolTree occurrences)) =
      balancedLookupInput (occurrencePoolCodes occurrences) index := by
  simp [balancedLookupInput, occurrencePoolTree, occurrencePoolCodes]

private theorem occurrencePoolCodes_get {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length)
    (hindex : index.val < (occurrencePoolCodes occurrences).length) :
    (occurrencePoolCodes occurrences)[index.val]'hindex =
      encodeSupportedNormalizedGate (occurrences.get index) := by
  simp [occurrencePoolCodes]

def occurrencePoolLeafInput {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (index inputMask liveMask : ℕ) : ℕ :=
  occurrenceLookupFrameInput index occurrences.length
    (occurrencePoolTree occurrences) (signedAtomMaskPair inputMask liveMask)

def occurrencePoolLeafFuel {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) (inputMask liveMask : ℕ) : ℕ :=
  linkFuel
      (linkPrograms (preserveRightProgram canonicalBalancedLookupProgram)
        (linkPrograms occurrenceLookupUnframeProgram
          occurrenceRequestProgram))
      11
    (linkFuel
        (linkPrograms occurrenceLookupUnframeProgram occurrenceRequestProgram)
        (preserveRightFuel
          (balancedLookupFuel (occurrencePoolCodes occurrences) index.val))
      (linkFuel occurrenceRequestProgram 7
        (occurrenceRequestFuel occurrences index inputMask liveMask)))

def occurrencePoolLeafStageBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) (inputMask liveMask : ℕ) : List ℕ :=
  [ 1
  , natBitLength q
  , occurrenceLookupFrameBits index.val occurrences.length
      (occurrencePoolTree occurrences) (signedAtomMaskPair inputMask liveMask)
  , preserveRightBits
      (balancedLookupMaximumBits (occurrencePoolCodes occurrences) index.val)
      (balancedLookupInput (occurrencePoolCodes occurrences) index.val)
      (Nat.pair index.val (signedAtomMaskPair inputMask liveMask))
      (encodeSupportedNormalizedGate (occurrences.get index))
  , occurrenceLookupUnframeBits index.val
      (encodeSupportedNormalizedGate (occurrences.get index))
      (signedAtomMaskPair inputMask liveMask)
  , occurrenceRequestBits occurrences index inputMask liveMask
  ]

def occurrencePoolLeafBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) (inputMask liveMask : ℕ) : ℕ :=
  (occurrencePoolLeafStageBits occurrences index inputMask liveMask).foldr
    max 1

theorem run_occurrencePoolLeafProgram {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) (inputMask liveMask maximumBits : ℕ)
    (hbits :
      occurrencePoolLeafBits occurrences index inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram occurrencePoolLeafProgram maximumBits
        (occurrencePoolLeafFuel occurrences index inputMask liveMask)
        (initialNPOracleState q
          (occurrencePoolLeafInput occurrences index.val inputMask liveMask)) =
      some (residualAssignmentRequest occurrences inputMask liveMask index) := by
  have hindexLt : index.val < (occurrencePoolCodes occurrences).length := by
    simp only [occurrencePoolCodes_length]
    exact index.isLt
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈ occurrencePoolLeafStageBits occurrences index inputMask
          liveMask) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [occurrencePoolLeafStageBits]
  have hlength : natBitLength q ≤ maximumBits := by
    apply bits_of_member
    simp [occurrencePoolLeafStageBits]
  have hframeBits :
      occurrenceLookupFrameBits index.val occurrences.length
          (occurrencePoolTree occurrences)
          (signedAtomMaskPair inputMask liveMask) ≤
        maximumBits := by
    apply bits_of_member
    simp [occurrencePoolLeafStageBits]
  have hpreserveBits :
      preserveRightBits
          (balancedLookupMaximumBits (occurrencePoolCodes occurrences)
            index.val)
          (balancedLookupInput (occurrencePoolCodes occurrences) index.val)
          (Nat.pair index.val (signedAtomMaskPair inputMask liveMask))
          (encodeSupportedNormalizedGate (occurrences.get index)) ≤
        maximumBits := by
    apply bits_of_member
    simp [occurrencePoolLeafStageBits]
  have hunframeBits :
      occurrenceLookupUnframeBits index.val
          (encodeSupportedNormalizedGate (occurrences.get index))
          (signedAtomMaskPair inputMask liveMask) ≤
        maximumBits := by
    apply bits_of_member
    simp [occurrencePoolLeafStageBits]
  have hrequestBits :
      occurrenceRequestBits occurrences index inputMask liveMask ≤
        maximumBits := by
    apply bits_of_member
    simp [occurrencePoolLeafStageBits]
  have hlookup :
      runNPOracleProgram canonicalBalancedLookupProgram
          (balancedLookupMaximumBits (occurrencePoolCodes occurrences)
            index.val)
          (balancedLookupFuel (occurrencePoolCodes occurrences) index.val)
          (initialNPOracleState q
            (balancedLookupInput (occurrencePoolCodes occurrences)
              index.val)) =
        some (encodeSupportedNormalizedGate (occurrences.get index)) := by
    rw [← occurrencePoolCodes_get occurrences index hindexLt]
    exact run_canonicalBalancedLookupProgram (occurrencePoolCodes occurrences)
      index.val q hindexLt
  have hstageOne :
      runNPOracleProgram occurrenceLookupFrameProgram maximumBits 11
          (initialNPOracleState q
            (occurrencePoolLeafInput occurrences index.val inputMask
              liveMask)) =
        some
          (Nat.pair
            (balancedLookupInput (occurrencePoolCodes occurrences) index.val)
            (Nat.pair index.val
              (signedAtomMaskPair inputMask liveMask))) := by
    rw [← occurrencePoolCodes_lookupInput occurrences index.val]
    exact run_occurrenceLookupFrameProgram q index.val occurrences.length
      (occurrencePoolTree occurrences)
      (signedAtomMaskPair inputMask liveMask) maximumBits hframeBits
  have hstageTwo :
      runNPOracleProgram (preserveRightProgram canonicalBalancedLookupProgram)
          maximumBits
          (preserveRightFuel
            (balancedLookupFuel (occurrencePoolCodes occurrences) index.val))
          (initialNPOracleState q
            (Nat.pair
              (balancedLookupInput (occurrencePoolCodes occurrences) index.val)
              (Nat.pair index.val
                (signedAtomMaskPair inputMask liveMask)))) =
        some
          (Nat.pair (encodeSupportedNormalizedGate (occurrences.get index))
            (Nat.pair index.val
              (signedAtomMaskPair inputMask liveMask))) :=
    run_bits_mono
      (run_preserveRightProgram canonicalBalancedLookupProgram q
        (balancedLookupMaximumBits (occurrencePoolCodes occurrences) index.val)
        (balancedLookupFuel (occurrencePoolCodes occurrences) index.val)
        (balancedLookupInput (occurrencePoolCodes occurrences) index.val)
        (Nat.pair index.val (signedAtomMaskPair inputMask liveMask))
        (encodeSupportedNormalizedGate (occurrences.get index)) hlookup)
      hpreserveBits
  have hstageThree :
      runNPOracleProgram occurrenceLookupUnframeProgram maximumBits 7
          (initialNPOracleState q
            (Nat.pair (encodeSupportedNormalizedGate (occurrences.get index))
              (Nat.pair index.val
                (signedAtomMaskPair inputMask liveMask)))) =
        some
          (occurrenceFrameInput index.val
            (encodeSupportedNormalizedGate (occurrences.get index)) inputMask
            liveMask) :=
    run_occurrenceLookupUnframeProgram q index.val
      (encodeSupportedNormalizedGate (occurrences.get index))
      (signedAtomMaskPair inputMask liveMask) maximumBits hunframeBits
  have hstageFour :
      runNPOracleProgram occurrenceRequestProgram maximumBits
          (occurrenceRequestFuel occurrences index inputMask liveMask)
          (initialNPOracleState q
            (occurrenceFrameInput index.val
              (encodeSupportedNormalizedGate (occurrences.get index)) inputMask
              liveMask)) =
        some (residualAssignmentRequest occurrences inputMask liveMask index) :=
    run_occurrenceRequestProgram occurrences index inputMask liveMask
      maximumBits hrequestBits
  exact run_linkPrograms hpositive hlength hstageOne
    (run_linkPrograms hpositive hlength hstageTwo
      (run_linkPrograms hpositive hlength hstageThree hstageFour))

end NearCubicWires.CanonicalOccurrenceRequestProgram
