import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalConditionalTouchProgram
import Proof.MachineModel.CanonicalIntPredecessorProgram
import Proof.Circuits.CanonicalPairedCall
import Proof.MachineModel.CanonicalStructuralGF2EvaluationProgram

open Finset
open scoped BigOperators

namespace NearCubicWires.CanonicalSignedGateEvaluationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalIntPredecessorProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalOccurrencePopulationProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalStructuralGF2EvaluationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.ThresholdCompiler
open NearCubicWires.VerifiedLinker

private theorem le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

/-! ## §1 Signed weights as two natural accumulators

A canonical integer weight splits into two naturals, exactly one of which is
nonzero.  Both halves are summed independently and compared at the very end,
so no intermediate register ever has to represent a negative number. -/

/-- The nonnegative half of a canonical integer weight. -/
def positivePart (value : ℤ) : ℕ := value.toNat

/-- The magnitude of the negative half of a canonical integer weight. -/
def negativePart (value : ℤ) : ℕ := (-value).toNat

theorem positivePart_sub_negativePart (value : ℤ) :
    (positivePart value : ℤ) - (negativePart value : ℤ) = value := by
  unfold positivePart negativePart
  omega

@[simp] theorem positivePart_natAbs_of_nonneg {value : ℤ} (hvalue : 0 ≤ value) :
    positivePart value = value.natAbs := by
  unfold positivePart
  omega

@[simp] theorem negativePart_natAbs_of_neg {value : ℤ} (hvalue : value < 0) :
    negativePart value = value.natAbs := by
  unfold negativePart
  omega

/-- The nonnegative half of a bit-selected weighted sum. -/
def maskedPositiveSum {n : ℕ} (weight : Fin n → ℤ) (bit : Fin n → Bool) : ℕ :=
  ∑ index, if bit index then positivePart (weight index) else 0

/-- The negative half of a bit-selected weighted sum. -/
def maskedNegativeSum {n : ℕ} (weight : Fin n → ℤ) (bit : Fin n → Bool) : ℕ :=
  ∑ index, if bit index then negativePart (weight index) else 0

theorem maskedScore_eq {n : ℕ} (weight : Fin n → ℤ) (bit : Fin n → Bool) :
    (∑ index, weight index * if bit index then (1 : ℤ) else 0) =
      (maskedPositiveSum weight bit : ℤ) -
        (maskedNegativeSum weight bit : ℤ) := by
  have hpositive :
      (maskedPositiveSum weight bit : ℤ) =
        ∑ index, if bit index then (positivePart (weight index) : ℤ) else 0 := by
    unfold maskedPositiveSum
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro index _
    cases bit index <;> simp
  have hnegative :
      (maskedNegativeSum weight bit : ℤ) =
        ∑ index, if bit index then (negativePart (weight index) : ℤ) else 0 := by
    unfold maskedNegativeSum
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro index _
    cases bit index <;> simp
  rw [hpositive, hnegative, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro index _
  cases bit index
  · simp
  · simpa using (positivePart_sub_negativePart (weight index)).symm

/-- **The signed gate comparison in naturals.**  Every later machine stage
compares these two natural totals and nothing else. -/
theorem gate_eval_eq_decide {n : ℕ} (gate : NormalizedThresholdGate n)
    (input : BitInput n) :
    gate.eval input =
      decide
        (positivePart gate.threshold + maskedNegativeSum gate.weight input ≤
          maskedPositiveSum gate.weight input +
            negativePart gate.threshold) := by
  have hthreshold := positivePart_sub_negativePart gate.threshold
  have hscore := maskedScore_eq gate.weight input
  unfold NormalizedThresholdGate.eval
  rw [hscore]
  refine decide_eq_decide.mpr ?_
  omega

/-! ## §2 The score family in the same two accumulators

`liveScore`, `frozenScore`, and `minimumLiveScore` split the same weighted sum
along the live set.  Each is the difference of two `masked…Sum` values with a
different coordinate selector, so `residualConstant` lands on exactly the same
natural comparison as `NormalizedThresholdGate.eval`. -/

/-- The live coordinates as the machine reads them off a mask. -/
def liveSelector {n : ℕ} (liveMask : ℕ) (index : Fin n) : Bool :=
  liveMask.testBit index.val

/-- The frozen coordinates carrying a set input bit, as the machine reads them
off the input and live masks.  On single bits saturating subtraction is
Boolean `AND NOT`, so this is one instruction per coordinate. -/
def frozenSelector {n : ℕ} (inputMask liveMask : ℕ) (index : Fin n) : Bool :=
  inputMask.testBit index.val && !liveMask.testBit index.val

theorem liveSelector_coordinateMask {n : ℕ} (live : Finset (Fin n))
    (index : Fin n) :
    liveSelector (coordinateMask live) index = decide (index ∈ live) := by
  unfold liveSelector
  exact testBit_coordinateMask live index

theorem testBit_encodeBitInput {n : ℕ} (input : BitInput n) (index : Fin n) :
    (encodeBitInput input).testBit index.val = input index := by
  rw [encodeBitInput_eq_ofBits, Nat.testBit_ofBits_lt _ _ index.isLt]

theorem frozenSelector_coordinateMask {n : ℕ} (live : Finset (Fin n))
    (input : BitInput n) (index : Fin n) :
    frozenSelector (encodeBitInput input) (coordinateMask live) index =
      (input index && !decide (index ∈ live)) := by
  unfold frozenSelector
  rw [testBit_encodeBitInput, testBit_coordinateMask]

theorem frozenScore_eq {n : ℕ} (gate : NormalizedThresholdGate n)
    (live : Finset (Fin n)) (input : BitInput n) :
    frozenScore gate live input =
      (maskedPositiveSum gate.weight
          (fun index => input index && !decide (index ∈ live)) : ℤ) -
        (maskedNegativeSum gate.weight
          (fun index => input index && !decide (index ∈ live)) : ℤ) := by
  have hsum :
      (∑ index ∈ Finset.univ \ live, gate.weight index * bitInt (input index)) =
        ∑ index, gate.weight index *
          if (input index && !decide (index ∈ live)) then (1 : ℤ) else 0 := by
    rw [Finset.sdiff_eq_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro index _
    by_cases hmember : index ∈ live
    · simp [hmember]
    · cases input index <;> simp [hmember, bitInt]
  unfold frozenScore
  rw [hsum, maskedScore_eq]

theorem minimumLiveScore_eq {n : ℕ} (gate : NormalizedThresholdGate n)
    (live : Finset (Fin n)) :
    minimumLiveScore gate live =
      -(maskedNegativeSum gate.weight
        (fun index => decide (index ∈ live)) : ℤ) := by
  have hcast :
      (maskedNegativeSum gate.weight (fun index => decide (index ∈ live)) : ℤ) =
        ∑ index, if index ∈ live then
          (negativePart (gate.weight index) : ℤ) else 0 := by
    unfold maskedNegativeSum
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro index _
    by_cases hmember : index ∈ live <;> simp [hmember]
  have houtside : ∀ index ∈ Finset.univ, index ∉ live →
      -(if index ∈ live then (negativePart (gate.weight index) : ℤ) else 0) =
        0 := by
    intro index _ hmember
    simp [hmember]
  have hinside : ∀ index ∈ live,
      (if gate.weight index < 0 then gate.weight index else 0) =
        -(if index ∈ live then
          (negativePart (gate.weight index) : ℤ) else 0) := by
    intro index hmember
    by_cases hnegative : gate.weight index < 0
    · rw [if_pos hnegative, if_pos hmember]
      unfold negativePart
      omega
    · rw [if_neg hnegative, if_pos hmember]
      unfold negativePart
      omega
  unfold minimumLiveScore
  calc
    (∑ index ∈ live, if gate.weight index < 0 then gate.weight index else 0) =
        ∑ index ∈ live,
          -(if index ∈ live then
            (negativePart (gate.weight index) : ℤ) else 0) :=
      Finset.sum_congr rfl hinside
    _ = ∑ index,
          -(if index ∈ live then
            (negativePart (gate.weight index) : ℤ) else 0) :=
      Finset.sum_subset (Finset.subset_univ live) houtside
    _ = -∑ index, if index ∈ live then
          (negativePart (gate.weight index) : ℤ) else 0 := by
      rw [Finset.sum_neg_distrib]
    _ = -(maskedNegativeSum gate.weight
          (fun index => decide (index ∈ live)) : ℤ) := by
      rw [hcast]

/-- **The frozen-side residual bit in naturals.**  Same comparison shape as
`gate_eval_eq_decide`, with the live negative mass moved to the left. -/
theorem residualConstant_eq_decide {n : ℕ} (gate : NormalizedThresholdGate n)
    (live : Finset (Fin n)) (input : BitInput n) :
    residualConstant gate live input =
      decide
        (positivePart gate.threshold +
              maskedNegativeSum gate.weight
                (fun index => decide (index ∈ live)) +
            maskedNegativeSum gate.weight
              (fun index => input index && !decide (index ∈ live)) ≤
          maskedPositiveSum gate.weight
              (fun index => input index && !decide (index ∈ live)) +
            negativePart gate.threshold) := by
  have hthreshold := positivePart_sub_negativePart gate.threshold
  unfold residualConstant
  rw [minimumLiveScore_eq, frozenScore_eq]
  refine decide_eq_decide.mpr ?_
  omega

/-! ## §3 One coordinate's signed contribution, executed

The atom is the canonical integer syntax already stored in the typed
envelope, framed with the requested sign and the coordinate's bit:

```text
    Nat.pair (encodeInt w) (Nat.pair wanted bit)
```

Three fixed stages consume it.  A structural adapter puts the magnitude first
so the shared right-preserving wrapper can hand it to the canonical `encodeNat`
inverse; a final stage then selects the magnitude or zero using saturating
single-bit arithmetic only. -/

/-- One when the atom's sign matches the requested sign and the bit is set.
`s - t` and `t - s` saturate, so their sum is the sign mismatch indicator. -/
def signedContributionSelect (sign wanted bit : ℕ) : ℕ :=
  bit - ((sign - wanted) + (wanted - sign))

/-- The machine's per-atom output, as a function of decoded fields. -/
def signedContributionValue (magnitude sign wanted bit : ℕ) : ℕ :=
  if signedContributionSelect sign wanted bit = 0 then 0 else magnitude

/-- The semantic contribution of one weight to one signed accumulator. -/
def signedContribution (weight : ℤ) (wanted : ℕ) (bit : Bool) : ℕ :=
  signedContributionValue weight.natAbs (intSignCode weight) wanted
    (boolCode bit)

theorem signedContribution_zero (weight : ℤ) (bit : Bool) :
    signedContribution weight 0 bit =
      if bit then positivePart weight else 0 := by
  unfold signedContribution signedContributionValue signedContributionSelect
    intSignCode positivePart
  cases bit
  · simp [boolCode]
  · by_cases hnegative : weight < 0
    · rw [if_pos hnegative]
      have hzero : weight.toNat = 0 := by omega
      simp [boolCode, hzero]
    · rw [if_neg hnegative]
      have hmagnitude : weight.natAbs = weight.toNat := by omega
      simp [boolCode, hmagnitude]

theorem signedContribution_one (weight : ℤ) (bit : Bool) :
    signedContribution weight 1 bit =
      if bit then negativePart weight else 0 := by
  unfold signedContribution signedContributionValue signedContributionSelect
    intSignCode negativePart
  cases bit
  · simp [boolCode]
  · by_cases hnegative : weight < 0
    · rw [if_pos hnegative]
      have hmagnitude : weight.natAbs = (-weight).toNat := by omega
      simp [boolCode, hmagnitude]
    · rw [if_neg hnegative]
      have hzero : (-weight).toNat = 0 := by omega
      simp [boolCode, hzero]

/-- The canonical integer atom framed with its requested sign and bit. -/
def signedAtomCode (weight : ℤ) (wanted : ℕ) (bit : Bool) : ℕ :=
  Nat.pair (encodeInt weight) (Nat.pair wanted (boolCode bit))

/-- The magnitude-first reframing consumed by the shared decoder wrapper. -/
def signedAtomPrepared (weight : ℤ) (wanted : ℕ) (bit : Bool) : ℕ :=
  Nat.pair (encodeNat weight.natAbs)
    (Nat.pair (intSignCode weight) (Nat.pair wanted (boolCode bit)))

private theorem encodeInt_eq_pair (weight : ℤ) :
    encodeInt weight =
      Nat.pair (intSignCode weight) (encodeNat weight.natAbs) := by
  rfl

def signedAtomPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .pair 4 3 6 5
  , .pair 5 6 0 6
  , .halt 0
  ]

@[simp] theorem signedAtomPrepareProgram_oracleFree :
    OracleFree signedAtomPrepareProgram := by
  rfl

def signedAtomPrepareFuel : ℕ := 7

private def signedAtomPrepareValues
    (weight : ℤ) (wanted : ℕ) (bit : Bool) : List ℕ :=
  [ signedAtomCode weight wanted bit
  , encodeInt weight
  , Nat.pair wanted (boolCode bit)
  , intSignCode weight
  , encodeNat weight.natAbs
  , Nat.pair (intSignCode weight) (Nat.pair wanted (boolCode bit))
  , signedAtomPrepared weight wanted bit
  ]

def signedAtomPrepareBits (weight : ℤ) (wanted : ℕ) (bit : Bool) : ℕ :=
  natBitLength ((signedAtomPrepareValues weight wanted bit).foldr max 1)

private theorem signedAtomPrepare_value_bits
    (weight : ℤ) (wanted : ℕ) (bit : Bool) {candidate : ℕ}
    (hcandidate : candidate ∈ signedAtomPrepareValues weight wanted bit) :
    natBitLength candidate ≤ signedAtomPrepareBits weight wanted bit :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

theorem run_signedAtomPrepareProgram
    (inputLength : ℕ) (weight : ℤ) (wanted : ℕ) (bit : Bool)
    (maximumBits : ℕ)
    (hbits : signedAtomPrepareBits weight wanted bit ≤ maximumBits) :
    runNPOracleProgram signedAtomPrepareProgram maximumBits
        signedAtomPrepareFuel
        (initialNPOracleState inputLength (signedAtomCode weight wanted bit)) =
      some (signedAtomPrepared weight wanted bit) := by
  have hweightCode :
      natBitLength (encodeInt weight) ≤ maximumBits :=
    (signedAtomPrepare_value_bits weight wanted bit
      (by simp [signedAtomPrepareValues])).trans hbits
  have htail :
      natBitLength (Nat.pair wanted (boolCode bit)) ≤ maximumBits :=
    (signedAtomPrepare_value_bits weight wanted bit
      (by simp [signedAtomPrepareValues])).trans hbits
  have hsign :
      natBitLength (intSignCode weight) ≤ maximumBits :=
    (signedAtomPrepare_value_bits weight wanted bit
      (by simp [signedAtomPrepareValues])).trans hbits
  have hmagnitudeCode :
      natBitLength (encodeNat weight.natAbs) ≤ maximumBits :=
    (signedAtomPrepare_value_bits weight wanted bit
      (by simp [signedAtomPrepareValues])).trans hbits
  have hsignTail :
      natBitLength
          (Nat.pair (intSignCode weight)
            (Nat.pair wanted (boolCode bit))) ≤ maximumBits :=
    (signedAtomPrepare_value_bits weight wanted bit
      (by simp [signedAtomPrepareValues])).trans hbits
  have hprepared :
      natBitLength (signedAtomPrepared weight wanted bit) ≤ maximumBits :=
    (signedAtomPrepare_value_bits weight wanted bit
      (by simp [signedAtomPrepareValues])).trans hbits
  rw [show signedAtomPrepareFuel = 6 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := encodeInt weight)
    (by rfl) rfl
    (by simp [initialNPOracleState, signedAtomCode])
    hweightCode]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair wanted (boolCode bit))
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        signedAtomCode])
    htail]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := intSignCode weight)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, encodeInt_eq_pair])
    hsign]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := encodeNat weight.natAbs)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, encodeInt_eq_pair])
    hmagnitudeCode]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (intSignCode weight) (Nat.pair wanted (boolCode bit)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsignTail]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (value := signedAtomPrepared weight wanted bit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomPrepared])
    hprepared]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hprepared

/-- The decoded atom handed to the final stage. -/
def signedAtomDecoded (magnitude sign wanted bit : ℕ) : ℕ :=
  Nat.pair magnitude (Nat.pair sign (Nat.pair wanted bit))

def signedAtomFinishProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .subtract 4 6 8 7
  , .subtract 6 4 9 8
  , .add 8 9 8 9
  , .subtract 7 8 8 10
  , .branchZero 8 11 12
  , .set 0 0 13
  , .copy 2 0 13
  , .halt 0
  ]

@[simp] theorem signedAtomFinishProgram_oracleFree :
    OracleFree signedAtomFinishProgram := by
  rfl

def signedAtomFinishFuel : ℕ := 13

private def signedAtomFinishValues
    (magnitude sign wanted bit : ℕ) : List ℕ :=
  [ signedAtomDecoded magnitude sign wanted bit
  , magnitude
  , Nat.pair sign (Nat.pair wanted bit)
  , sign
  , Nat.pair wanted bit
  , wanted
  , bit
  , sign - wanted
  , wanted - sign
  , (sign - wanted) + (wanted - sign)
  , signedContributionSelect sign wanted bit
  , signedContributionValue magnitude sign wanted bit
  ]

def signedAtomFinishBits (magnitude sign wanted bit : ℕ) : ℕ :=
  natBitLength ((signedAtomFinishValues magnitude sign wanted bit).foldr max 1)

private theorem signedAtomFinish_value_bits
    (magnitude sign wanted bit : ℕ) {candidate : ℕ}
    (hcandidate : candidate ∈ signedAtomFinishValues magnitude sign wanted bit) :
    natBitLength candidate ≤ signedAtomFinishBits magnitude sign wanted bit :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

set_option maxHeartbeats 1600000 in
-- Fourteen chained register writes; resolving each register lookup through the
-- whole write chain exceeds the default budget.
/-- Exact execution of the sign-selection stage.  Only saturating subtraction,
one addition, and one data-independent branch are used. -/
theorem run_signedAtomFinishProgram
    (inputLength magnitude sign wanted bit maximumBits : ℕ)
    (hbits : signedAtomFinishBits magnitude sign wanted bit ≤ maximumBits) :
    runNPOracleProgram signedAtomFinishProgram maximumBits
        signedAtomFinishFuel
        (initialNPOracleState inputLength
          (signedAtomDecoded magnitude sign wanted bit)) =
      some (signedContributionValue magnitude sign wanted bit) := by
  have hmagnitude : natBitLength magnitude ≤ maximumBits :=
    (signedAtomFinish_value_bits magnitude sign wanted bit
      (by simp [signedAtomFinishValues])).trans hbits
  have hsignTail :
      natBitLength (Nat.pair sign (Nat.pair wanted bit)) ≤ maximumBits :=
    (signedAtomFinish_value_bits magnitude sign wanted bit
      (by simp [signedAtomFinishValues])).trans hbits
  have hsign : natBitLength sign ≤ maximumBits :=
    (signedAtomFinish_value_bits magnitude sign wanted bit
      (by simp [signedAtomFinishValues])).trans hbits
  have htail : natBitLength (Nat.pair wanted bit) ≤ maximumBits :=
    (signedAtomFinish_value_bits magnitude sign wanted bit
      (by simp [signedAtomFinishValues])).trans hbits
  have hwanted : natBitLength wanted ≤ maximumBits :=
    (signedAtomFinish_value_bits magnitude sign wanted bit
      (by simp [signedAtomFinishValues])).trans hbits
  have hbit : natBitLength bit ≤ maximumBits :=
    (signedAtomFinish_value_bits magnitude sign wanted bit
      (by simp [signedAtomFinishValues])).trans hbits
  have hleftGap : natBitLength (sign - wanted) ≤ maximumBits :=
    (signedAtomFinish_value_bits magnitude sign wanted bit
      (by simp [signedAtomFinishValues])).trans hbits
  have hrightGap : natBitLength (wanted - sign) ≤ maximumBits :=
    (signedAtomFinish_value_bits magnitude sign wanted bit
      (by simp [signedAtomFinishValues])).trans hbits
  have hmismatch :
      natBitLength ((sign - wanted) + (wanted - sign)) ≤ maximumBits :=
    (signedAtomFinish_value_bits magnitude sign wanted bit
      (by simp [signedAtomFinishValues])).trans hbits
  have hselect :
      natBitLength (signedContributionSelect sign wanted bit) ≤ maximumBits :=
    (signedAtomFinish_value_bits magnitude sign wanted bit
      (by simp [signedAtomFinishValues])).trans hbits
  have hvalue :
      natBitLength (signedContributionValue magnitude sign wanted bit) ≤
        maximumBits :=
    (signedAtomFinish_value_bits magnitude sign wanted bit
      (by simp [signedAtomFinishValues])).trans hbits
  have hzeroBits : natBitLength 0 ≤ maximumBits := by
    refine le_trans ?_ hbit
    exact natBitLength_mono (Nat.zero_le bit)
  rw [show signedAtomFinishFuel = 12 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := magnitude)
    (by rfl) rfl
    (by simp [initialNPOracleState, signedAtomDecoded])
    hmagnitude]
  rw [show (12 : ℕ) = 11 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair sign (Nat.pair wanted bit))
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        signedAtomDecoded])
    hsignTail]
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sign)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsign]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair wanted bit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htail]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := wanted)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hwanted]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := bit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hbit]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_subtract_instruction (value := sign - wanted)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hleftGap]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_subtract_instruction (value := wanted - sign)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrightGap]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_add_instruction (value := (sign - wanted) + (wanted - sign))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hmismatch]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_subtract_instruction
    (value := signedContributionSelect sign wanted bit)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        signedContributionSelect])
    hselect]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_branchZero_instruction (register := 8) (zeroTarget := 11)
    (nonzeroTarget := 12) (by rfl) rfl]
  by_cases hselectZero : signedContributionSelect sign wanted bit = 0
  · rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump,
      hselectZero])]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_set_instruction (register := 0) (value := 0) (next := 13)
      (by rfl) rfl hzeroBits]
    refine run_halt_instruction (fuel := 0) (by rfl) rfl ?_ hvalue
    simp [NPOracleState.write, NPOracleState.jump,
      signedContributionValue, hselectZero]
  · rw [if_neg (by
      simp [NPOracleState.write, NPOracleState.jump, hselectZero])]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_copy_instruction (value := magnitude)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hmagnitude]
    refine run_halt_instruction (fuel := 0) (by rfl) rfl ?_ hvalue
    simp [NPOracleState.write, NPOracleState.jump,
      signedContributionValue, hselectZero]

/-- **The per-atom signed contribution machine.**  Structural reframing, the
shared canonical `encodeNat` inverse under a right-preserving wrapper, then the
sign selection. -/
def signedContributionProgram : NPOracleProgram :=
  linkPrograms signedAtomPrepareProgram
    (linkPrograms (preserveRightProgram canonicalNatDecodeProgram)
      signedAtomFinishProgram)

theorem signedContributionProgram_oracleFree :
    OracleFree signedContributionProgram := by
  refine oracleFree_linkPrograms signedAtomPrepareProgram_oracleFree ?_
  refine oracleFree_linkPrograms ?_ signedAtomFinishProgram_oracleFree
  exact preserveRightProgram_oracleFree canonicalNatDecodeProgram
    canonicalNatDecodeProgram_oracleFree

/-- The whole per-atom fuel depends only on the weight's magnitude. -/
def signedContributionFuel (magnitude : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram canonicalNatDecodeProgram)
      signedAtomFinishProgram)
    signedAtomPrepareFuel
    (linkFuel signedAtomFinishProgram
      (preserveRightFuel (canonicalNatDecodeFuel magnitude))
      signedAtomFinishFuel)

def signedContributionBits
    (inputLength : ℕ) (weight : ℤ) (wanted : ℕ) (bit : Bool) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (signedAtomPrepareBits weight wanted bit) <|
      max
        (preserveRightBits (canonicalNatDecodeBits inputLength weight.natAbs)
          (encodeNat weight.natAbs)
          (Nat.pair (intSignCode weight) (Nat.pair wanted (boolCode bit)))
          weight.natAbs)
        (signedAtomFinishBits weight.natAbs (intSignCode weight) wanted
          (boolCode bit))

/-- **One coordinate's signed contribution, executed.**  The atom is the exact
integer syntax stored in the typed envelope; the output is the semantic
contribution to the requested accumulator. -/
theorem run_signedContributionProgram
    (inputLength : ℕ) (weight : ℤ) (wanted : ℕ) (bit : Bool)
    (maximumBits : ℕ)
    (hbits : signedContributionBits inputLength weight wanted bit ≤
      maximumBits) :
    runNPOracleProgram signedContributionProgram maximumBits
        (signedContributionFuel weight.natAbs)
        (initialNPOracleState inputLength (signedAtomCode weight wanted bit)) =
      some (signedContribution weight wanted bit) := by
  have hpositive : 1 ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [signedContributionBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [signedContributionBits]
  have hprepareBits : signedAtomPrepareBits weight wanted bit ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [signedContributionBits]
  have hdecodeBits :
      preserveRightBits (canonicalNatDecodeBits inputLength weight.natAbs)
          (encodeNat weight.natAbs)
          (Nat.pair (intSignCode weight) (Nat.pair wanted (boolCode bit)))
          weight.natAbs ≤
        maximumBits := by
    refine le_trans ?_ hbits
    simp [signedContributionBits]
  have hfinishBits :
      signedAtomFinishBits weight.natAbs (intSignCode weight) wanted
          (boolCode bit) ≤
        maximumBits := by
    refine le_trans ?_ hbits
    simp [signedContributionBits]
  have hprepare :
      runNPOracleProgram signedAtomPrepareProgram maximumBits
          signedAtomPrepareFuel
          (initialNPOracleState inputLength
            (signedAtomCode weight wanted bit)) =
        some (signedAtomPrepared weight wanted bit) :=
    run_signedAtomPrepareProgram inputLength weight wanted bit maximumBits
      hprepareBits
  have hdecode :
      runNPOracleProgram (preserveRightProgram canonicalNatDecodeProgram)
          maximumBits
          (preserveRightFuel (canonicalNatDecodeFuel weight.natAbs))
          (initialNPOracleState inputLength
            (signedAtomPrepared weight wanted bit)) =
        some
          (signedAtomDecoded weight.natAbs (intSignCode weight) wanted
            (boolCode bit)) := by
    refine run_bits_mono ?_ hdecodeBits
    exact run_preserveRightProgram canonicalNatDecodeProgram inputLength
      (canonicalNatDecodeBits inputLength weight.natAbs)
      (canonicalNatDecodeFuel weight.natAbs)
      (encodeNat weight.natAbs)
      (Nat.pair (intSignCode weight) (Nat.pair wanted (boolCode bit)))
      weight.natAbs
      (run_canonicalNatDecodeProgram inputLength weight.natAbs)
  have hfinish :
      runNPOracleProgram signedAtomFinishProgram maximumBits
          signedAtomFinishFuel
          (initialNPOracleState inputLength
            (signedAtomDecoded weight.natAbs (intSignCode weight) wanted
              (boolCode bit))) =
        some (signedContribution weight wanted bit) :=
    run_signedAtomFinishProgram inputLength weight.natAbs (intSignCode weight)
      wanted (boolCode bit) maximumBits hfinishBits
  exact run_linkPrograms hpositive hlength hprepare
    (run_linkPrograms hpositive hlength hdecode hfinish)

/-! ## §4 One signed accumulator over a whole atom list

A single balanced call of the per-atom stage followed by the existing balanced
natural sum produces one accumulator.  The atom list is a plain list of
`(weight, requested sign, bit)` triples: it is the only thing a later producer
has to assemble, and every sum below is an instance of it. -/

/-- One balanced-call request for a signed atom. -/
def signedAtomRequest (inputLength : ℕ) (atom : ℤ × ℕ × Bool) : ℕ :=
  nativeInputRequest inputLength (signedAtomCode atom.1 atom.2.1 atom.2.2)

def signedAtomRequests
    (inputLength : ℕ) (atoms : List (ℤ × ℕ × Bool)) : List ℕ :=
  atoms.map (signedAtomRequest inputLength)

/-- The semantic value of one signed atom. -/
def signedAtomValue (atom : ℤ × ℕ × Bool) : ℕ :=
  signedContribution atom.1 atom.2.1 atom.2.2

/-- The accumulator named by a whole atom list. -/
def signedAtomTotal (atoms : List (ℤ × ℕ × Bool)) : ℕ :=
  (atoms.map signedAtomValue).sum

@[simp] theorem signedAtomTotal_nil : signedAtomTotal [] = 0 := rfl

@[simp] theorem signedAtomTotal_cons
    (atom : ℤ × ℕ × Bool) (atoms : List (ℤ × ℕ × Bool)) :
    signedAtomTotal (atom :: atoms) =
      signedAtomValue atom + signedAtomTotal atoms := by
  simp [signedAtomTotal]

@[simp] theorem signedAtomTotal_append
    (left right : List (ℤ × ℕ × Bool)) :
    signedAtomTotal (left ++ right) =
      signedAtomTotal left + signedAtomTotal right := by
  simp [signedAtomTotal]

/-! Total projections of a raw request.  The balanced-call interface needs the
callee's fuel and output as functions of the request code alone. -/

def signedRequestCode (request : ℕ) : ℕ := (Nat.unpair request).2

def signedRequestWeightCode (request : ℕ) : ℕ :=
  (Nat.unpair (signedRequestCode request)).1

def signedRequestTail (request : ℕ) : ℕ :=
  (Nat.unpair (signedRequestCode request)).2

def signedRequestSign (request : ℕ) : ℕ :=
  (Nat.unpair (signedRequestWeightCode request)).1

def signedRequestMagnitude (request : ℕ) : ℕ :=
  (decodeNat (Nat.unpair (signedRequestWeightCode request)).2).getD 0

def signedRequestWanted (request : ℕ) : ℕ :=
  (Nat.unpair (signedRequestTail request)).1

def signedRequestBit (request : ℕ) : ℕ :=
  (Nat.unpair (signedRequestTail request)).2

def signedRequestOutput (request : ℕ) : ℕ :=
  signedContributionValue (signedRequestMagnitude request)
    (signedRequestSign request) (signedRequestWanted request)
    (signedRequestBit request)

def signedRequestFuel (request : ℕ) : ℕ :=
  signedContributionFuel (signedRequestMagnitude request)

@[simp] theorem signedRequestMagnitude_request
    (inputLength : ℕ) (atom : ℤ × ℕ × Bool) :
    signedRequestMagnitude (signedAtomRequest inputLength atom) =
      atom.1.natAbs := by
  simp [signedRequestMagnitude, signedRequestWeightCode, signedRequestCode,
    signedAtomRequest, nativeInputRequest, signedAtomCode, encodeInt_eq_pair]

@[simp] theorem signedRequestSign_request
    (inputLength : ℕ) (atom : ℤ × ℕ × Bool) :
    signedRequestSign (signedAtomRequest inputLength atom) =
      intSignCode atom.1 := by
  simp [signedRequestSign, signedRequestWeightCode, signedRequestCode,
    signedAtomRequest, nativeInputRequest, signedAtomCode, encodeInt_eq_pair]

@[simp] theorem signedRequestWanted_request
    (inputLength : ℕ) (atom : ℤ × ℕ × Bool) :
    signedRequestWanted (signedAtomRequest inputLength atom) = atom.2.1 := by
  simp [signedRequestWanted, signedRequestTail, signedRequestCode,
    signedAtomRequest, nativeInputRequest, signedAtomCode]

@[simp] theorem signedRequestBit_request
    (inputLength : ℕ) (atom : ℤ × ℕ × Bool) :
    signedRequestBit (signedAtomRequest inputLength atom) =
      boolCode atom.2.2 := by
  simp [signedRequestBit, signedRequestTail, signedRequestCode,
    signedAtomRequest, nativeInputRequest, signedAtomCode]

@[simp] theorem signedRequestOutput_request
    (inputLength : ℕ) (atom : ℤ × ℕ × Bool) :
    signedRequestOutput (signedAtomRequest inputLength atom) =
      signedAtomValue atom := by
  simp [signedRequestOutput, signedAtomValue, signedContribution]

theorem map_signedRequestOutput
    (inputLength : ℕ) (atoms : List (ℤ × ℕ × Bool)) :
    (signedAtomRequests inputLength atoms).map signedRequestOutput =
      atoms.map signedAtomValue := by
  unfold signedAtomRequests
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro atom _
  simp only [Function.comp_apply]
  rw [signedRequestOutput_request]

/-- **One signed accumulator, executed.**  One balanced call of the per-atom
stage, then the existing balanced natural sum. -/
def signedAtomTotalProgram : NPOracleProgram :=
  balancedNatSumAfterProgram (balancedCallProgram signedContributionProgram)

theorem signedAtomTotalProgram_oracleFree :
    OracleFree signedAtomTotalProgram :=
  balancedNatSumAfterProgram_oracleFree
    (balancedCallProgram signedContributionProgram)
    (balancedCallProgram_oracleFree signedContributionProgram_oracleFree)

def signedAtomRequestsBits
    (inputLength : ℕ) (atoms : List (ℤ × ℕ × Bool)) : ℕ :=
  (atoms.map fun atom =>
    signedContributionBits inputLength atom.1 atom.2.1 atom.2.2).foldr max 1

def signedAtomTotalProducerBits
    (inputLength : ℕ) (atoms : List (ℤ × ℕ × Bool)) : ℕ :=
  max
    (balancedCallRequiredBits signedRequestOutput
      (signedAtomRequests inputLength atoms))
    (signedAtomRequestsBits inputLength atoms)

def signedAtomTotalFuel
    (inputLength : ℕ) (atoms : List (ℤ × ℕ × Bool)) : ℕ :=
  balancedNatSumAfterFuel
    (balancedCallFuel signedContributionProgram signedRequestFuel
      (signedAtomRequests inputLength atoms))
    (atoms.map signedAtomValue)

def signedAtomTotalBits
    (inputLength : ℕ) (atoms : List (ℤ × ℕ × Bool)) : ℕ :=
  balancedNatSumAfterBits inputLength
    (signedAtomTotalProducerBits inputLength atoms)
    (atoms.map signedAtomValue)

/-- The exact value of one signed accumulator from its balanced request list. -/
theorem run_signedAtomTotalProgram
    (inputLength : ℕ) (atoms : List (ℤ × ℕ × Bool)) (maximumBits : ℕ)
    (hbits : signedAtomTotalBits inputLength atoms ≤ maximumBits) :
    runNPOracleProgram signedAtomTotalProgram maximumBits
        (signedAtomTotalFuel inputLength atoms)
        (initialNPOracleState inputLength
          (encodeBalancedList (signedAtomRequests inputLength atoms))) =
      some (signedAtomTotal atoms) := by
  have hexec : ∀ request : ℕ,
      request ∈ signedAtomRequests inputLength atoms →
      runNPOracleProgram signedContributionProgram
          (signedAtomTotalProducerBits inputLength atoms)
          (signedRequestFuel request)
          (initialNPOracleState (Nat.unpair request).1
            (Nat.unpair request).2) =
        some (signedRequestOutput request) := by
    intro request hrequest
    obtain ⟨atom, hatom, hrequestEq⟩ := List.mem_map.mp hrequest
    have hatomBits :
        signedContributionBits inputLength atom.1 atom.2.1 atom.2.2 ≤
          signedAtomTotalProducerBits inputLength atoms := by
      refine le_trans ?_ (Nat.le_max_right _ _)
      exact le_foldr_max_of_mem (List.mem_map_of_mem hatom)
    have hrun :=
      run_signedContributionProgram inputLength atom.1 atom.2.1 atom.2.2
        (signedAtomTotalProducerBits inputLength atoms) hatomBits
    have hleft :
        (Nat.unpair (signedAtomRequest inputLength atom)).1 = inputLength := by
      simp [signedAtomRequest, nativeInputRequest]
    have hright :
        (Nat.unpair (signedAtomRequest inputLength atom)).2 =
          signedAtomCode atom.1 atom.2.1 atom.2.2 := by
      simp [signedAtomRequest, nativeInputRequest]
    have hfuel :
        signedRequestFuel (signedAtomRequest inputLength atom) =
          signedContributionFuel atom.1.natAbs := by
      rw [signedRequestFuel, signedRequestMagnitude_request]
    rw [← hrequestEq, hleft, hright, hfuel, signedRequestOutput_request]
    exact hrun
  have hproducer :=
    run_balancedCallProgram_from
      (callee := signedContributionProgram)
      (maximumBits := signedAtomTotalProducerBits inputLength atoms)
      inputLength (signedAtomRequests inputLength atoms)
      signedRequestFuel signedRequestOutput (Nat.le_max_left _ _) hexec
  have hsum :=
    run_balancedNatSumAfterProgram
      (balancedCallProgram signedContributionProgram) inputLength
      (encodeBalancedList (signedAtomRequests inputLength atoms))
      (signedAtomTotalProducerBits inputLength atoms)
      (balancedCallFuel signedContributionProgram signedRequestFuel
        (signedAtomRequests inputLength atoms))
      ((signedAtomRequests inputLength atoms).map signedRequestOutput)
      hproducer
  rw [map_signedRequestOutput] at hsum
  exact run_bits_mono hsum hbits

/-! ## §5 The signed comparison machine

Two atom lists, one paired call of the accumulator, one saturating comparison.
Every quantity of Appendix A.2 is an instance of this single program; only the
two atom lists change. -/

def signedOrderProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .subtract 2 3 4 3
  , .branchZero 4 4 5
  , .set 0 1 6
  , .set 0 0 6
  , .halt 0
  ]

@[simp] theorem signedOrderProgram_oracleFree :
    OracleFree signedOrderProgram := by
  rfl

def signedOrderFuel : ℕ := 6

private def signedOrderValues (left right : ℕ) : List ℕ :=
  [Nat.pair left right, left, right, left - right, 1, 0]

def signedOrderBits (left right : ℕ) : ℕ :=
  natBitLength ((signedOrderValues left right).foldr max 1)

private theorem signedOrder_value_bits
    (left right : ℕ) {candidate : ℕ}
    (hcandidate : candidate ∈ signedOrderValues left right) :
    natBitLength candidate ≤ signedOrderBits left right :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

/-- Exact execution of the final natural comparison. -/
theorem run_signedOrderProgram
    (inputLength left right maximumBits : ℕ)
    (hbits : signedOrderBits left right ≤ maximumBits) :
    runNPOracleProgram signedOrderProgram maximumBits signedOrderFuel
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (boolCode (decide (left ≤ right))) := by
  have hleft : natBitLength left ≤ maximumBits :=
    (signedOrder_value_bits left right (by simp [signedOrderValues])).trans hbits
  have hright : natBitLength right ≤ maximumBits :=
    (signedOrder_value_bits left right (by simp [signedOrderValues])).trans hbits
  have hgap : natBitLength (left - right) ≤ maximumBits :=
    (signedOrder_value_bits left right (by simp [signedOrderValues])).trans hbits
  have hone : natBitLength 1 ≤ maximumBits :=
    (signedOrder_value_bits left right (by simp [signedOrderValues])).trans hbits
  have hzero : natBitLength 0 ≤ maximumBits :=
    (signedOrder_value_bits left right (by simp [signedOrderValues])).trans hbits
  rw [show signedOrderFuel = 5 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := left)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hleft]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := right)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hright]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_subtract_instruction (value := left - right)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hgap]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_branchZero_instruction (register := 4) (zeroTarget := 4)
    (nonzeroTarget := 5) (by rfl) rfl]
  by_cases horder : left ≤ right
  · have hgapZero : left - right = 0 := by omega
    rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump, hgapZero])]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_set_instruction (register := 0) (value := 1) (next := 6)
      (by rfl) rfl hone]
    rw [show boolCode (decide (left ≤ right)) = 1 by simp [boolCode, horder]]
    refine run_halt_instruction (fuel := 0) (by rfl) rfl ?_ hone
    simp [NPOracleState.write, NPOracleState.jump]
  · have hgapPositive : left - right ≠ 0 := by omega
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump, hgapPositive])]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_set_instruction (register := 0) (value := 0) (next := 6)
      (by rfl) rfl hzero]
    rw [show boolCode (decide (left ≤ right)) = 0 by simp [boolCode, horder]]
    refine run_halt_instruction (fuel := 0) (by rfl) rfl ?_ hzero
    simp [NPOracleState.write, NPOracleState.jump]

/-- **The signed comparison machine.**  One paired accumulator call, then one
saturating comparison. -/
def signedComparisonProgram : NPOracleProgram :=
  linkPrograms (pairedCallProgram signedAtomTotalProgram) signedOrderProgram

theorem signedComparisonProgram_oracleFree :
    OracleFree signedComparisonProgram :=
  oracleFree_linkPrograms
    (pairedCallProgram_oracleFree signedAtomTotalProgram
      signedAtomTotalProgram_oracleFree)
    signedOrderProgram_oracleFree

/-- The comparison machine's input: the two balanced request lists. -/
def signedComparisonInput
    (inputLength : ℕ) (left right : List (ℤ × ℕ × Bool)) : ℕ :=
  Nat.pair (encodeBalancedList (signedAtomRequests inputLength left))
    (encodeBalancedList (signedAtomRequests inputLength right))

def signedComparisonFuel
    (inputLength : ℕ) (left right : List (ℤ × ℕ × Bool)) : ℕ :=
  linkFuel signedOrderProgram
    (pairedCallFuel signedAtomTotalProgram
      (signedAtomTotalFuel inputLength left)
      (signedAtomTotalFuel inputLength right))
    signedOrderFuel

def signedComparisonBits
    (inputLength : ℕ) (left right : List (ℤ × ℕ × Bool)) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max
      (pairedCallBits inputLength (signedAtomTotalBits inputLength left)
        (signedAtomTotalBits inputLength right)
        (encodeBalancedList (signedAtomRequests inputLength left))
        (encodeBalancedList (signedAtomRequests inputLength right))
        (signedAtomTotal left) (signedAtomTotal right))
      (signedOrderBits (signedAtomTotal left) (signedAtomTotal right))

/-- **One signed comparison, executed.**  The output is the Boolean code of
`signedAtomTotal left ≤ signedAtomTotal right`, with both totals computed by the
same fixed accumulator. -/
theorem run_signedComparisonProgram
    (inputLength : ℕ) (left right : List (ℤ × ℕ × Bool)) (maximumBits : ℕ)
    (hbits : signedComparisonBits inputLength left right ≤ maximumBits) :
    runNPOracleProgram signedComparisonProgram maximumBits
        (signedComparisonFuel inputLength left right)
        (initialNPOracleState inputLength
          (signedComparisonInput inputLength left right)) =
      some
        (boolCode (decide (signedAtomTotal left ≤ signedAtomTotal right))) := by
  have hpositive : 1 ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [signedComparisonBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [signedComparisonBits]
  have hpairedBits :
      pairedCallBits inputLength (signedAtomTotalBits inputLength left)
          (signedAtomTotalBits inputLength right)
          (encodeBalancedList (signedAtomRequests inputLength left))
          (encodeBalancedList (signedAtomRequests inputLength right))
          (signedAtomTotal left) (signedAtomTotal right) ≤
        maximumBits := by
    refine le_trans ?_ hbits
    simp [signedComparisonBits]
  have horderBits :
      signedOrderBits (signedAtomTotal left) (signedAtomTotal right) ≤
        maximumBits := by
    refine le_trans ?_ hbits
    simp [signedComparisonBits]
  have hpaired :
      runNPOracleProgram (pairedCallProgram signedAtomTotalProgram) maximumBits
          (pairedCallFuel signedAtomTotalProgram
            (signedAtomTotalFuel inputLength left)
            (signedAtomTotalFuel inputLength right))
          (initialNPOracleState inputLength
            (signedComparisonInput inputLength left right)) =
        some (Nat.pair (signedAtomTotal left) (signedAtomTotal right)) := by
    refine run_bits_mono ?_ hpairedBits
    exact run_pairedCallProgram signedAtomTotalProgram inputLength
      (signedAtomTotalBits inputLength left)
      (signedAtomTotalBits inputLength right)
      (signedAtomTotalFuel inputLength left)
      (signedAtomTotalFuel inputLength right)
      (encodeBalancedList (signedAtomRequests inputLength left))
      (encodeBalancedList (signedAtomRequests inputLength right))
      (signedAtomTotal left) (signedAtomTotal right)
      (run_signedAtomTotalProgram inputLength left
        (signedAtomTotalBits inputLength left) le_rfl)
      (run_signedAtomTotalProgram inputLength right
        (signedAtomTotalBits inputLength right) le_rfl)
  have horder :=
    run_signedOrderProgram inputLength (signedAtomTotal left)
      (signedAtomTotal right) maximumBits horderBits
  exact run_linkPrograms hpositive hlength hpaired horder

/-! ## §6 Threshold-gate evaluation and the frozen-side residual bit

Both are the same comparison machine on two different atom lists.  The
threshold contributes one extra atom on each side — its own two nonnegative
parts — so no stage ever handles a negative register. -/

/-- The atoms of one masked accumulator over a gate's coordinates. -/
def gateAtoms {n : ℕ} (gate : NormalizedThresholdGate n) (wanted : ℕ)
    (bit : Fin n → Bool) : List (ℤ × ℕ × Bool) :=
  List.ofFn fun index => (gate.weight index, wanted, bit index)

theorem signedAtomTotal_gateAtoms_positive {n : ℕ}
    (gate : NormalizedThresholdGate n) (bit : Fin n → Bool) :
    signedAtomTotal (gateAtoms gate 0 bit) =
      maskedPositiveSum gate.weight bit := by
  unfold signedAtomTotal gateAtoms maskedPositiveSum
  rw [List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl ?_
  intro index _
  exact signedContribution_zero (gate.weight index) (bit index)

theorem signedAtomTotal_gateAtoms_negative {n : ℕ}
    (gate : NormalizedThresholdGate n) (bit : Fin n → Bool) :
    signedAtomTotal (gateAtoms gate 1 bit) =
      maskedNegativeSum gate.weight bit := by
  unfold signedAtomTotal gateAtoms maskedNegativeSum
  rw [List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl ?_
  intro index _
  exact signedContribution_one (gate.weight index) (bit index)

/-- The left atom list of `NormalizedThresholdGate.eval`. -/
def gateEvaluationLeftAtoms {n : ℕ} (gate : NormalizedThresholdGate n)
    (bit : Fin n → Bool) : List (ℤ × ℕ × Bool) :=
  (gate.threshold, 0, true) :: gateAtoms gate 1 bit

/-- The right atom list of `NormalizedThresholdGate.eval`. -/
def gateEvaluationRightAtoms {n : ℕ} (gate : NormalizedThresholdGate n)
    (bit : Fin n → Bool) : List (ℤ × ℕ × Bool) :=
  (gate.threshold, 1, true) :: gateAtoms gate 0 bit

theorem signedAtomTotal_gateEvaluationLeftAtoms {n : ℕ}
    (gate : NormalizedThresholdGate n) (bit : Fin n → Bool) :
    signedAtomTotal (gateEvaluationLeftAtoms gate bit) =
      positivePart gate.threshold + maskedNegativeSum gate.weight bit := by
  unfold gateEvaluationLeftAtoms
  rw [signedAtomTotal_cons, signedAtomTotal_gateAtoms_negative]
  have hhead : signedAtomValue (gate.threshold, 0, true) =
      positivePart gate.threshold := by
    unfold signedAtomValue
    simpa using signedContribution_zero gate.threshold true
  rw [hhead]

theorem signedAtomTotal_gateEvaluationRightAtoms {n : ℕ}
    (gate : NormalizedThresholdGate n) (bit : Fin n → Bool) :
    signedAtomTotal (gateEvaluationRightAtoms gate bit) =
      negativePart gate.threshold + maskedPositiveSum gate.weight bit := by
  unfold gateEvaluationRightAtoms
  rw [signedAtomTotal_cons, signedAtomTotal_gateAtoms_positive]
  have hhead : signedAtomValue (gate.threshold, 1, true) =
      negativePart gate.threshold := by
    unfold signedAtomValue
    simpa using signedContribution_one gate.threshold true
  rw [hhead]

/-- **The gate as one signed comparison.** -/
theorem gate_eval_eq_signedComparison {n : ℕ}
    (gate : NormalizedThresholdGate n) (input : BitInput n) :
    gate.eval input =
      decide
        (signedAtomTotal (gateEvaluationLeftAtoms gate input) ≤
          signedAtomTotal (gateEvaluationRightAtoms gate input)) := by
  rw [gate_eval_eq_decide, signedAtomTotal_gateEvaluationLeftAtoms,
    signedAtomTotal_gateEvaluationRightAtoms]
  refine decide_eq_decide.mpr ?_
  omega

/-- **Threshold-gate evaluation, executed.**  The coordinate bits are read off
an abstract input mask. -/
theorem run_signedComparisonProgram_gateEvaluation {n : ℕ}
    (gate : NormalizedThresholdGate n) (input : BitInput n)
    (bit : Fin n → Bool) (maximumBits : ℕ)
    (hbit : ∀ index, bit index = input index)
    (hbits :
      signedComparisonBits n (gateEvaluationLeftAtoms gate bit)
          (gateEvaluationRightAtoms gate bit) ≤
        maximumBits) :
    runNPOracleProgram signedComparisonProgram maximumBits
        (signedComparisonFuel n (gateEvaluationLeftAtoms gate bit)
          (gateEvaluationRightAtoms gate bit))
        (initialNPOracleState n
          (signedComparisonInput n (gateEvaluationLeftAtoms gate bit)
            (gateEvaluationRightAtoms gate bit))) =
      some (boolCode (gate.eval input)) := by
  have hfunction : bit = input := funext hbit
  subst hfunction
  rw [gate_eval_eq_signedComparison]
  exact run_signedComparisonProgram n (gateEvaluationLeftAtoms gate bit)
    (gateEvaluationRightAtoms gate bit) maximumBits hbits

/-- The left atom list of `residualConstant`: the threshold's nonnegative part,
the live negative mass `-minimumLiveScore`, and the frozen negative half. -/
def residualConstantLeftAtoms {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : List (ℤ × ℕ × Bool) :=
  (gate.threshold, 0, true) ::
    (gateAtoms gate 1 (liveSelector liveMask) ++
      gateAtoms gate 1 (frozenSelector inputMask liveMask))

/-- The right atom list of `residualConstant`. -/
def residualConstantRightAtoms {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : List (ℤ × ℕ × Bool) :=
  (gate.threshold, 1, true) ::
    gateAtoms gate 0 (frozenSelector inputMask liveMask)

theorem signedAtomTotal_residualConstantLeftAtoms {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask : ℕ) :
    signedAtomTotal (residualConstantLeftAtoms gate inputMask liveMask) =
      positivePart gate.threshold +
        (maskedNegativeSum gate.weight (liveSelector liveMask) +
          maskedNegativeSum gate.weight
            (frozenSelector inputMask liveMask)) := by
  unfold residualConstantLeftAtoms
  rw [signedAtomTotal_cons, signedAtomTotal_append,
    signedAtomTotal_gateAtoms_negative, signedAtomTotal_gateAtoms_negative]
  have hhead : signedAtomValue (gate.threshold, 0, true) =
      positivePart gate.threshold := by
    unfold signedAtomValue
    simpa using signedContribution_zero gate.threshold true
  rw [hhead]

theorem signedAtomTotal_residualConstantRightAtoms {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask : ℕ) :
    signedAtomTotal (residualConstantRightAtoms gate inputMask liveMask) =
      negativePart gate.threshold +
        maskedPositiveSum gate.weight
          (frozenSelector inputMask liveMask) := by
  unfold residualConstantRightAtoms
  rw [signedAtomTotal_cons, signedAtomTotal_gateAtoms_positive]
  have hhead : signedAtomValue (gate.threshold, 1, true) =
      negativePart gate.threshold := by
    unfold signedAtomValue
    simpa using signedContribution_one gate.threshold true
  rw [hhead]

/-- **The frozen-side residual bit as one signed comparison.**  The live set
enters only through the abstract mask premise. -/
theorem residualConstant_eq_signedComparison {n : ℕ}
    (gate : NormalizedThresholdGate n) (live : Finset (Fin n))
    (input : BitInput n) (inputMask liveMask : ℕ)
    (hinput : inputMask = encodeBitInput input)
    (hlive : liveMask = coordinateMask live) :
    residualConstant gate live input =
      decide
        (signedAtomTotal (residualConstantLeftAtoms gate inputMask liveMask) ≤
          signedAtomTotal
            (residualConstantRightAtoms gate inputMask liveMask)) := by
  have hliveSelector :
      liveSelector (n := n) liveMask = fun index => decide (index ∈ live) := by
    funext index
    rw [hlive]
    exact liveSelector_coordinateMask live index
  have hfrozenSelector :
      frozenSelector (n := n) inputMask liveMask =
        fun index => input index && !decide (index ∈ live) := by
    funext index
    rw [hinput, hlive]
    exact frozenSelector_coordinateMask live input index
  rw [signedAtomTotal_residualConstantLeftAtoms,
    signedAtomTotal_residualConstantRightAtoms, hliveSelector,
    hfrozenSelector, residualConstant_eq_decide]
  refine decide_eq_decide.mpr ?_
  omega

/-- **The frozen-side residual bit, executed.** -/
theorem run_signedComparisonProgram_residualConstant {n : ℕ}
    (gate : NormalizedThresholdGate n) (live : Finset (Fin n))
    (input : BitInput n) (inputMask liveMask maximumBits : ℕ)
    (hinput : inputMask = encodeBitInput input)
    (hlive : liveMask = coordinateMask live)
    (hbits :
      signedComparisonBits n (residualConstantLeftAtoms gate inputMask liveMask)
          (residualConstantRightAtoms gate inputMask liveMask) ≤
        maximumBits) :
    runNPOracleProgram signedComparisonProgram maximumBits
        (signedComparisonFuel n
          (residualConstantLeftAtoms gate inputMask liveMask)
          (residualConstantRightAtoms gate inputMask liveMask))
        (initialNPOracleState n
          (signedComparisonInput n
            (residualConstantLeftAtoms gate inputMask liveMask)
            (residualConstantRightAtoms gate inputMask liveMask))) =
      some (boolCode (residualConstant gate live input)) := by
  rw [residualConstant_eq_signedComparison gate live input inputMask liveMask
    hinput hlive]
  exact run_signedComparisonProgram n
    (residualConstantLeftAtoms gate inputMask liveMask)
    (residualConstantRightAtoms gate inputMask liveMask) maximumBits hbits

/-! ## §7 The two score halves, executed

`frozenScore` and `minimumLiveScore` are integers, so their executable content
is the pair of nonnegative halves the accumulator produces.  §2 already
identifies each score with those halves; the theorems below run them. -/

/-- The input coordinates as the machine reads them off a mask. -/
def inputSelector {n : ℕ} (inputMask : ℕ) (index : Fin n) : Bool :=
  inputMask.testBit index.val

theorem inputSelector_encodeBitInput {n : ℕ} (input : BitInput n) :
    inputSelector (n := n) (encodeBitInput input) = input := by
  funext index
  exact testBit_encodeBitInput input index

theorem liveSelector_eq_of_mask {n : ℕ} (live : Finset (Fin n)) {liveMask : ℕ}
    (hlive : liveMask = coordinateMask live) :
    liveSelector (n := n) liveMask = fun index => decide (index ∈ live) := by
  funext index
  rw [hlive]
  exact liveSelector_coordinateMask live index

theorem frozenSelector_eq_of_mask {n : ℕ} (live : Finset (Fin n))
    (input : BitInput n) {inputMask liveMask : ℕ}
    (hinput : inputMask = encodeBitInput input)
    (hlive : liveMask = coordinateMask live) :
    frozenSelector (n := n) inputMask liveMask =
      fun index => input index && !decide (index ∈ live) := by
  funext index
  rw [hinput, hlive]
  exact frozenSelector_coordinateMask live input index

/-- The frozen score is the difference of the two executed halves. -/
theorem frozenScore_eq_halves {n : ℕ} (gate : NormalizedThresholdGate n)
    (live : Finset (Fin n)) (input : BitInput n) (inputMask liveMask : ℕ)
    (hinput : inputMask = encodeBitInput input)
    (hlive : liveMask = coordinateMask live) :
    frozenScore gate live input =
      (maskedPositiveSum gate.weight
          (frozenSelector inputMask liveMask) : ℤ) -
        (maskedNegativeSum gate.weight
          (frozenSelector inputMask liveMask) : ℤ) := by
  rw [frozenSelector_eq_of_mask live input hinput hlive]
  exact frozenScore_eq gate live input

/-- The minimum live score is the negation of one executed half. -/
theorem minimumLiveScore_eq_half {n : ℕ} (gate : NormalizedThresholdGate n)
    (live : Finset (Fin n)) (liveMask : ℕ)
    (hlive : liveMask = coordinateMask live) :
    minimumLiveScore gate live =
      -(maskedNegativeSum gate.weight (liveSelector liveMask) : ℤ) := by
  rw [liveSelector_eq_of_mask live hlive]
  exact minimumLiveScore_eq gate live

/-- **The positive half of one masked score, executed.** -/
theorem run_signedAtomTotalProgram_positiveHalf {n : ℕ}
    (gate : NormalizedThresholdGate n) (bit : Fin n → Bool)
    (maximumBits : ℕ)
    (hbits : signedAtomTotalBits n (gateAtoms gate 0 bit) ≤ maximumBits) :
    runNPOracleProgram signedAtomTotalProgram maximumBits
        (signedAtomTotalFuel n (gateAtoms gate 0 bit))
        (initialNPOracleState n
          (encodeBalancedList
            (signedAtomRequests n (gateAtoms gate 0 bit)))) =
      some (maskedPositiveSum gate.weight bit) := by
  rw [← signedAtomTotal_gateAtoms_positive gate bit]
  exact run_signedAtomTotalProgram n (gateAtoms gate 0 bit) maximumBits hbits

/-- **The negative half of one masked score, executed.** -/
theorem run_signedAtomTotalProgram_negativeHalf {n : ℕ}
    (gate : NormalizedThresholdGate n) (bit : Fin n → Bool)
    (maximumBits : ℕ)
    (hbits : signedAtomTotalBits n (gateAtoms gate 1 bit) ≤ maximumBits) :
    runNPOracleProgram signedAtomTotalProgram maximumBits
        (signedAtomTotalFuel n (gateAtoms gate 1 bit))
        (initialNPOracleState n
          (encodeBalancedList
            (signedAtomRequests n (gateAtoms gate 1 bit)))) =
      some (maskedNegativeSum gate.weight bit) := by
  rw [← signedAtomTotal_gateAtoms_negative gate bit]
  exact run_signedAtomTotalProgram n (gateAtoms gate 1 bit) maximumBits hbits

/-! ## §8 The residual variable

`residualVariable = eval xor residualConstant`.  Both bits come from the same
comparison machine under one paired call, so the whole residue is one fixed
oracle-free program over the gate's envelope syntax, the input mask, and the
abstract live mask. -/

def exclusiveOrProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .branchZero 2 3 4
  , .copy 3 0 6
  , .set 4 1 5
  , .subtract 4 3 0 6
  , .halt 0
  ]

@[simp] theorem exclusiveOrProgram_oracleFree :
    OracleFree exclusiveOrProgram := by
  rfl

def exclusiveOrFuel : ℕ := 6

private def exclusiveOrValues (left right : Bool) : List ℕ :=
  [ Nat.pair (boolCode left) (boolCode right)
  , boolCode left
  , boolCode right
  , 1
  , 1 - boolCode right
  , 0
  ]

def exclusiveOrBits (left right : Bool) : ℕ :=
  natBitLength ((exclusiveOrValues left right).foldr max 1)

private theorem exclusiveOr_value_bits
    (left right : Bool) {candidate : ℕ}
    (hcandidate : candidate ∈ exclusiveOrValues left right) :
    natBitLength candidate ≤ exclusiveOrBits left right :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

/-- Exact execution of the residue's exclusive-or. -/
theorem run_exclusiveOrProgram
    (inputLength : ℕ) (left right : Bool) (maximumBits : ℕ)
    (hbits : exclusiveOrBits left right ≤ maximumBits) :
    runNPOracleProgram exclusiveOrProgram maximumBits exclusiveOrFuel
        (initialNPOracleState inputLength
          (Nat.pair (boolCode left) (boolCode right))) =
      some (boolCode (xor left right)) := by
  have hleft : natBitLength (boolCode left) ≤ maximumBits :=
    (exclusiveOr_value_bits left right (by simp [exclusiveOrValues])).trans hbits
  have hright : natBitLength (boolCode right) ≤ maximumBits :=
    (exclusiveOr_value_bits left right (by simp [exclusiveOrValues])).trans hbits
  have hone : natBitLength 1 ≤ maximumBits :=
    (exclusiveOr_value_bits left right (by simp [exclusiveOrValues])).trans hbits
  have hflip : natBitLength (1 - boolCode right) ≤ maximumBits :=
    (exclusiveOr_value_bits left right (by simp [exclusiveOrValues])).trans hbits
  rw [show exclusiveOrFuel = 5 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := boolCode left)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hleft]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := boolCode right)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hright]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_branchZero_instruction (register := 2) (zeroTarget := 3)
    (nonzeroTarget := 4) (by rfl) rfl]
  cases left
  · rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump, boolCode])]
    rw [show (3 : ℕ) = 2 + 1 by omega]
    rw [run_copy_instruction (value := boolCode right)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hright]
    refine run_halt_instruction (fuel := 1) (by rfl) rfl ?_ ?_
    · simp [NPOracleState.write, NPOracleState.jump]
    · simpa using hright
  · rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump, boolCode])]
    rw [show (3 : ℕ) = 2 + 1 by omega]
    rw [run_set_instruction (register := 4) (value := 1) (next := 5)
      (by rfl) rfl hone]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_subtract_instruction (value := 1 - boolCode right)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hflip]
    have houtput : boolCode (xor true right) = 1 - boolCode right := by
      cases right <;> simp [boolCode]
    rw [houtput]
    refine run_halt_instruction (fuel := 0) (by rfl) rfl ?_ hflip
    simp [NPOracleState.write, NPOracleState.jump]

/-- The gate bit named by an input mask, before it is identified with
`NormalizedThresholdGate.eval`. -/
def gateEvaluationOutput {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask : ℕ) : Bool :=
  decide
    (signedAtomTotal (gateEvaluationLeftAtoms gate (inputSelector inputMask)) ≤
      signedAtomTotal (gateEvaluationRightAtoms gate (inputSelector inputMask)))

/-- The frozen-side bit named by the two masks. -/
def residualConstantOutput {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : Bool :=
  decide
    (signedAtomTotal (residualConstantLeftAtoms gate inputMask liveMask) ≤
      signedAtomTotal (residualConstantRightAtoms gate inputMask liveMask))

/-- **The residual-variable machine.**  One paired call of the comparison
machine, then one exclusive-or. -/
def residualVariableProgram : NPOracleProgram :=
  linkPrograms (pairedCallProgram signedComparisonProgram) exclusiveOrProgram

theorem residualVariableProgram_oracleFree :
    OracleFree residualVariableProgram :=
  oracleFree_linkPrograms
    (pairedCallProgram_oracleFree signedComparisonProgram
      signedComparisonProgram_oracleFree)
    exclusiveOrProgram_oracleFree

def residualVariableEvaluationInput {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask : ℕ) : ℕ :=
  signedComparisonInput n (gateEvaluationLeftAtoms gate (inputSelector inputMask))
    (gateEvaluationRightAtoms gate (inputSelector inputMask))

def residualVariableConstantInput {n : ℕ}
    (gate : NormalizedThresholdGate n) (inputMask liveMask : ℕ) : ℕ :=
  signedComparisonInput n (residualConstantLeftAtoms gate inputMask liveMask)
    (residualConstantRightAtoms gate inputMask liveMask)

def residualVariableInput {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  Nat.pair (residualVariableEvaluationInput gate inputMask)
    (residualVariableConstantInput gate inputMask liveMask)

def residualVariableFuel {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  linkFuel exclusiveOrProgram
    (pairedCallFuel signedComparisonProgram
      (signedComparisonFuel n
        (gateEvaluationLeftAtoms gate (inputSelector inputMask))
        (gateEvaluationRightAtoms gate (inputSelector inputMask)))
      (signedComparisonFuel n
        (residualConstantLeftAtoms gate inputMask liveMask)
        (residualConstantRightAtoms gate inputMask liveMask)))
    exclusiveOrFuel

def residualVariableBits {n : ℕ} (gate : NormalizedThresholdGate n)
    (inputMask liveMask : ℕ) : ℕ :=
  max 1 <| max (natBitLength n) <|
    max
      (pairedCallBits n
        (signedComparisonBits n
          (gateEvaluationLeftAtoms gate (inputSelector inputMask))
          (gateEvaluationRightAtoms gate (inputSelector inputMask)))
        (signedComparisonBits n
          (residualConstantLeftAtoms gate inputMask liveMask)
          (residualConstantRightAtoms gate inputMask liveMask))
        (residualVariableEvaluationInput gate inputMask)
        (residualVariableConstantInput gate inputMask liveMask)
        (boolCode (gateEvaluationOutput gate inputMask))
        (boolCode (residualConstantOutput gate inputMask liveMask)))
      (exclusiveOrBits (gateEvaluationOutput gate inputMask)
        (residualConstantOutput gate inputMask liveMask))

/-- **The nonconstant residue of one gate, executed.**  The live set enters
only through the abstract mask premise `hlive`. -/
theorem run_residualVariableProgram {n : ℕ}
    (gate : NormalizedThresholdGate n) (live : Finset (Fin n))
    (input : BitInput n) (inputMask liveMask maximumBits : ℕ)
    (hinput : inputMask = encodeBitInput input)
    (hlive : liveMask = coordinateMask live)
    (hbits : residualVariableBits gate inputMask liveMask ≤ maximumBits) :
    runNPOracleProgram residualVariableProgram maximumBits
        (residualVariableFuel gate inputMask liveMask)
        (initialNPOracleState n
          (residualVariableInput gate inputMask liveMask)) =
      some (boolCode (residualVariable gate live input)) := by
  have hpositive : 1 ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [residualVariableBits]
  have hlength : natBitLength n ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [residualVariableBits]
  have hpairedBits :
      pairedCallBits n
          (signedComparisonBits n
            (gateEvaluationLeftAtoms gate (inputSelector inputMask))
            (gateEvaluationRightAtoms gate (inputSelector inputMask)))
          (signedComparisonBits n
            (residualConstantLeftAtoms gate inputMask liveMask)
            (residualConstantRightAtoms gate inputMask liveMask))
          (residualVariableEvaluationInput gate inputMask)
          (residualVariableConstantInput gate inputMask liveMask)
          (boolCode (gateEvaluationOutput gate inputMask))
          (boolCode (residualConstantOutput gate inputMask liveMask)) ≤
        maximumBits := by
    refine le_trans ?_ hbits
    simp [residualVariableBits]
  have hexclusiveBits :
      exclusiveOrBits (gateEvaluationOutput gate inputMask)
          (residualConstantOutput gate inputMask liveMask) ≤
        maximumBits := by
    refine le_trans ?_ hbits
    simp [residualVariableBits]
  have hevaluation :
      runNPOracleProgram signedComparisonProgram
          (signedComparisonBits n
            (gateEvaluationLeftAtoms gate (inputSelector inputMask))
            (gateEvaluationRightAtoms gate (inputSelector inputMask)))
          (signedComparisonFuel n
            (gateEvaluationLeftAtoms gate (inputSelector inputMask))
            (gateEvaluationRightAtoms gate (inputSelector inputMask)))
          (initialNPOracleState n
            (residualVariableEvaluationInput gate inputMask)) =
        some (boolCode (gateEvaluationOutput gate inputMask)) :=
    run_signedComparisonProgram n
      (gateEvaluationLeftAtoms gate (inputSelector inputMask))
      (gateEvaluationRightAtoms gate (inputSelector inputMask)) _ le_rfl
  have hconstant :
      runNPOracleProgram signedComparisonProgram
          (signedComparisonBits n
            (residualConstantLeftAtoms gate inputMask liveMask)
            (residualConstantRightAtoms gate inputMask liveMask))
          (signedComparisonFuel n
            (residualConstantLeftAtoms gate inputMask liveMask)
            (residualConstantRightAtoms gate inputMask liveMask))
          (initialNPOracleState n
            (residualVariableConstantInput gate inputMask liveMask)) =
        some (boolCode (residualConstantOutput gate inputMask liveMask)) :=
    run_signedComparisonProgram n
      (residualConstantLeftAtoms gate inputMask liveMask)
      (residualConstantRightAtoms gate inputMask liveMask) _ le_rfl
  have hpaired :
      runNPOracleProgram (pairedCallProgram signedComparisonProgram)
          maximumBits
          (pairedCallFuel signedComparisonProgram
            (signedComparisonFuel n
              (gateEvaluationLeftAtoms gate (inputSelector inputMask))
              (gateEvaluationRightAtoms gate (inputSelector inputMask)))
            (signedComparisonFuel n
              (residualConstantLeftAtoms gate inputMask liveMask)
              (residualConstantRightAtoms gate inputMask liveMask)))
          (initialNPOracleState n
            (residualVariableInput gate inputMask liveMask)) =
        some
          (Nat.pair (boolCode (gateEvaluationOutput gate inputMask))
            (boolCode (residualConstantOutput gate inputMask liveMask))) := by
    refine run_bits_mono ?_ hpairedBits
    exact run_pairedCallProgram signedComparisonProgram n _ _ _ _
      (residualVariableEvaluationInput gate inputMask)
      (residualVariableConstantInput gate inputMask liveMask)
      (boolCode (gateEvaluationOutput gate inputMask))
      (boolCode (residualConstantOutput gate inputMask liveMask))
      hevaluation hconstant
  have hexclusive :=
    run_exclusiveOrProgram n (gateEvaluationOutput gate inputMask)
      (residualConstantOutput gate inputMask liveMask) maximumBits
      hexclusiveBits
  have hvalue :
      xor (gateEvaluationOutput gate inputMask)
          (residualConstantOutput gate inputMask liveMask) =
        residualVariable gate live input := by
    have hevalBit : gateEvaluationOutput gate inputMask = gate.eval input := by
      unfold gateEvaluationOutput
      rw [hinput, inputSelector_encodeBitInput]
      exact (gate_eval_eq_signedComparison gate input).symm
    have hconstantBit :
        residualConstantOutput gate inputMask liveMask =
          residualConstant gate live input := by
      unfold residualConstantOutput
      exact
        (residualConstant_eq_signedComparison gate live input inputMask
          liveMask hinput hlive).symm
    rw [hevalBit, hconstantBit]
    rfl
  rw [← hvalue]
  exact run_linkPrograms hpositive hlength hpaired hexclusive

/-- **One occurrence's residual variable, executed.**  This is the per-gate
producer of the fourfold row table's residual assignment. -/
theorem run_residualVariableProgram_occurrence {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (index : Fin occurrences.length)
    (inputMask liveMask maximumBits : ℕ)
    (hinput : inputMask = encodeBitInput input)
    (hlive : liveMask = coordinateMask live)
    (hbits :
      residualVariableBits (occurrences.get index).gate inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram residualVariableProgram maximumBits
        (residualVariableFuel (occurrences.get index).gate inputMask liveMask)
        (initialNPOracleState q
          (residualVariableInput (occurrences.get index).gate inputMask
            liveMask)) =
      some
        (boolCode
          (occurrenceResidualVariable occurrences live input index)) := by
  exact run_residualVariableProgram (occurrences.get index).gate live input
    inputMask liveMask maximumBits hinput hlive hbits

/-! ## §9 The whole occurrence pool: the residual assignment table

The fourfold row table is `finiteAssignmentContext` of the pool's residual
assignment.  One balanced call of §8 over the pool, then the population is
paired back on.  The occurrence index rides inside each request so the map's
output is a projection of the request the balanced-call interface consumes;
the callee discards it in one instruction. -/

/-- The pool's residual assignment: the fourfold row table's own bit vector. -/
def poolResidualAssignment {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q) :
    Fin occurrences.length → Bool :=
  fun index => occurrenceResidualVariable occurrences live input index

/-- Total index-indexed view of the assignment. -/
def poolResidualVariableAt {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q) (index : ℕ) : Bool :=
  if hindex : index < occurrences.length then
    poolResidualAssignment occurrences live input ⟨index, hindex⟩
  else false

theorem poolResidualVariableAt_val {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (index : Fin occurrences.length) :
    poolResidualVariableAt occurrences live input index.val =
      poolResidualAssignment occurrences live input index := by
  unfold poolResidualVariableAt
  rw [dif_pos index.isLt]

/-- One balanced-call request for one occurrence's residue. -/
def residualAssignmentRequest {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) (index : Fin occurrences.length) : ℕ :=
  nativeInputRequest q
    (Nat.pair index.val
      (residualVariableInput (occurrences.get index).gate inputMask liveMask))

def residualAssignmentRequests {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) : List ℕ :=
  List.ofFn (residualAssignmentRequest occurrences inputMask liveMask)

/-- The index a request carries, read structurally. -/
def residualAssignmentRequestIndex (raw : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair raw).2).1

@[simp] theorem residualAssignmentRequestIndex_request {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) (index : Fin occurrences.length) :
    residualAssignmentRequestIndex
        (residualAssignmentRequest occurrences inputMask liveMask index) =
      index.val := by
  simp [residualAssignmentRequestIndex, residualAssignmentRequest,
    nativeInputRequest]

/-- The map's output, as a total function of the request. -/
def residualAssignmentOutput {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q) (raw : ℕ) : ℕ :=
  boolCode
    (poolResidualVariableAt occurrences live input
      (residualAssignmentRequestIndex raw))

theorem residualAssignmentOutput_request {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (inputMask liveMask : ℕ) (index : Fin occurrences.length) :
    residualAssignmentOutput occurrences live input
        (residualAssignmentRequest occurrences inputMask liveMask index) =
      boolCode (poolResidualAssignment occurrences live input index) := by
  unfold residualAssignmentOutput
  rw [residualAssignmentRequestIndex_request, poolResidualVariableAt_val]

/-- The callee: discard the index, then run the residue machine. -/
def residualAssignmentCalleeProgram : NPOracleProgram :=
  linkPrograms rightProjectionProgram residualVariableProgram

theorem residualAssignmentCalleeProgram_oracleFree :
    OracleFree residualAssignmentCalleeProgram :=
  oracleFree_linkPrograms rightProjectionProgram_oracleFree
    residualVariableProgram_oracleFree

def poolResidualFuelAt {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) (index : ℕ) : ℕ :=
  if hindex : index < occurrences.length then
    linkFuel residualVariableProgram 2
      (residualVariableFuel (occurrences.get ⟨index, hindex⟩).gate inputMask
        liveMask)
  else 0

theorem poolResidualFuelAt_val {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) (index : Fin occurrences.length) :
    poolResidualFuelAt occurrences inputMask liveMask index.val =
      linkFuel residualVariableProgram 2
        (residualVariableFuel (occurrences.get index).gate inputMask
          liveMask) := by
  unfold poolResidualFuelAt
  rw [dif_pos index.isLt]

def residualAssignmentCalleeFuel {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) (raw : ℕ) : ℕ :=
  poolResidualFuelAt occurrences inputMask liveMask
    (residualAssignmentRequestIndex raw)

private def residualAssignmentEntryBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) (index : Fin occurrences.length) : ℕ :=
  max 1 <| max (natBitLength q) <|
    max
      (rightProjectionBits index.val
        (residualVariableInput (occurrences.get index).gate inputMask liveMask))
      (residualVariableBits (occurrences.get index).gate inputMask liveMask)

def residualAssignmentCalleeBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) : ℕ :=
  (List.ofFn (residualAssignmentEntryBits occurrences inputMask
    liveMask)).foldr max 1

private theorem residualAssignmentEntryBits_le {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) (index : Fin occurrences.length) :
    residualAssignmentEntryBits occurrences inputMask liveMask index ≤
      residualAssignmentCalleeBits occurrences inputMask liveMask :=
  le_foldr_max_of_mem (List.mem_ofFn.mpr ⟨index, rfl⟩)

theorem run_residualAssignmentCalleeProgram {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (index : Fin occurrences.length)
    (inputMask liveMask maximumBits : ℕ)
    (hinput : inputMask = encodeBitInput input)
    (hlive : liveMask = coordinateMask live)
    (hbits :
      residualAssignmentEntryBits occurrences inputMask liveMask index ≤
        maximumBits) :
    runNPOracleProgram residualAssignmentCalleeProgram maximumBits
        (poolResidualFuelAt occurrences inputMask liveMask index.val)
        (initialNPOracleState q
          (Nat.pair index.val
            (residualVariableInput (occurrences.get index).gate inputMask
              liveMask))) =
      some (boolCode (poolResidualAssignment occurrences live input index)) := by
  have hpositive : 1 ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [residualAssignmentEntryBits]
  have hlength : natBitLength q ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [residualAssignmentEntryBits]
  have hprojectionBits :
      rightProjectionBits index.val
          (residualVariableInput (occurrences.get index).gate inputMask
            liveMask) ≤
        maximumBits := by
    refine le_trans ?_ hbits
    simp [residualAssignmentEntryBits]
  have hresidueBits :
      residualVariableBits (occurrences.get index).gate inputMask liveMask ≤
        maximumBits := by
    refine le_trans ?_ hbits
    simp [residualAssignmentEntryBits]
  have hprojection :
      runNPOracleProgram rightProjectionProgram maximumBits 2
          (initialNPOracleState q
            (Nat.pair index.val
              (residualVariableInput (occurrences.get index).gate inputMask
                liveMask))) =
        some
          (residualVariableInput (occurrences.get index).gate inputMask
            liveMask) :=
    run_bits_mono
      (run_rightProjectionProgram q index.val
        (residualVariableInput (occurrences.get index).gate inputMask liveMask))
      hprojectionBits
  have hresidue :
      runNPOracleProgram residualVariableProgram maximumBits
          (residualVariableFuel (occurrences.get index).gate inputMask liveMask)
          (initialNPOracleState q
            (residualVariableInput (occurrences.get index).gate inputMask
              liveMask)) =
        some
          (boolCode (poolResidualAssignment occurrences live input index)) :=
    run_residualVariableProgram_occurrence occurrences live input index
      inputMask liveMask maximumBits hinput hlive hresidueBits
  rw [poolResidualFuelAt_val]
  exact run_linkPrograms hpositive hlength hprojection hresidue

/-- The balanced map of §8 over the whole pool. -/
def residualAssignmentMapProgram : NPOracleProgram :=
  balancedCallProgram residualAssignmentCalleeProgram

theorem residualAssignmentMapProgram_oracleFree :
    OracleFree residualAssignmentMapProgram :=
  balancedCallProgram_oracleFree residualAssignmentCalleeProgram_oracleFree

def residualAssignmentMapFuel {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) : ℕ :=
  balancedCallFuel residualAssignmentCalleeProgram
    (residualAssignmentCalleeFuel occurrences inputMask liveMask)
    (residualAssignmentRequests occurrences inputMask liveMask)

def residualAssignmentMapBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (inputMask liveMask : ℕ) : ℕ :=
  max
    (balancedCallRequiredBits (residualAssignmentOutput occurrences live input)
      (residualAssignmentRequests occurrences inputMask liveMask))
    (residualAssignmentCalleeBits occurrences inputMask liveMask)

theorem map_residualAssignmentOutput {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q) (inputMask liveMask : ℕ) :
    (residualAssignmentRequests occurrences inputMask liveMask).map
        (residualAssignmentOutput occurrences live input) =
      finiteAssignmentTable (poolResidualAssignment occurrences live input) := by
  have hfunction :
      (residualAssignmentOutput occurrences live input ∘
          residualAssignmentRequest occurrences inputMask liveMask) =
        fun index => boolCode
          (poolResidualAssignment occurrences live input index) :=
    funext fun index =>
      residualAssignmentOutput_request occurrences live input inputMask
        liveMask index
  unfold residualAssignmentRequests finiteAssignmentTable
  rw [List.map_ofFn, hfunction]

/-- **The pool's residual table, executed.**  One balanced call of the residue
machine over the whole occurrence pool. -/
theorem run_residualAssignmentMapProgram {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (inputMask liveMask maximumBits : ℕ)
    (hinput : inputMask = encodeBitInput input)
    (hlive : liveMask = coordinateMask live)
    (hbits :
      residualAssignmentMapBits occurrences live input inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram residualAssignmentMapProgram maximumBits
        (residualAssignmentMapFuel occurrences inputMask liveMask)
        (initialNPOracleState q
          (encodeBalancedList
            (residualAssignmentRequests occurrences inputMask liveMask))) =
      some
        (encodeBalancedList
          (finiteAssignmentTable
            (poolResidualAssignment occurrences live input))) := by
  have hexec : ∀ raw : ℕ,
      raw ∈ residualAssignmentRequests occurrences inputMask liveMask →
      runNPOracleProgram residualAssignmentCalleeProgram
          (residualAssignmentMapBits occurrences live input inputMask liveMask)
          (residualAssignmentCalleeFuel occurrences inputMask liveMask raw)
          (initialNPOracleState (Nat.unpair raw).1 (Nat.unpair raw).2) =
        some (residualAssignmentOutput occurrences live input raw) := by
    intro raw hraw
    obtain ⟨index, hindex⟩ := List.mem_ofFn.mp hraw
    have hentry :
        residualAssignmentEntryBits occurrences inputMask liveMask index ≤
          residualAssignmentMapBits occurrences live input inputMask liveMask :=
      (residualAssignmentEntryBits_le occurrences inputMask liveMask
        index).trans (Nat.le_max_right _ _)
    have hleft :
        (Nat.unpair
            (residualAssignmentRequest occurrences inputMask liveMask
              index)).1 =
          q := by
      simp [residualAssignmentRequest, nativeInputRequest]
    have hright :
        (Nat.unpair
            (residualAssignmentRequest occurrences inputMask liveMask
              index)).2 =
          Nat.pair index.val
            (residualVariableInput (occurrences.get index).gate inputMask
              liveMask) := by
      simp [residualAssignmentRequest, nativeInputRequest]
    have hfuel :
        residualAssignmentCalleeFuel occurrences inputMask liveMask
            (residualAssignmentRequest occurrences inputMask liveMask index) =
          poolResidualFuelAt occurrences inputMask liveMask index.val := by
      unfold residualAssignmentCalleeFuel
      rw [residualAssignmentRequestIndex_request]
    rw [← hindex, hleft, hright, hfuel,
      residualAssignmentOutput_request occurrences live input inputMask
        liveMask index]
    exact run_residualAssignmentCalleeProgram occurrences live input index
      inputMask liveMask _ hinput hlive hentry
  have hmap :=
    run_balancedCallProgram_from
      (callee := residualAssignmentCalleeProgram)
      (maximumBits :=
        residualAssignmentMapBits occurrences live input inputMask liveMask)
      q (residualAssignmentRequests occurrences inputMask liveMask)
      (residualAssignmentCalleeFuel occurrences inputMask liveMask)
      (residualAssignmentOutput occurrences live input)
      (Nat.le_max_left _ _) hexec
  rw [map_residualAssignmentOutput] at hmap
  exact run_bits_mono hmap hbits

/-! ## §10 The fourfold row table

Pairing the population back onto the mapped bit list is exactly
`finiteAssignmentContext`, the row table the fourfold row evaluator consumes.
The request list and the population arrive together in one canonical pair. -/

/-- **The residual assignment table machine.** -/
def residualAssignmentTableProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram residualAssignmentMapProgram)
    swapPairProgram

theorem residualAssignmentTableProgram_oracleFree :
    OracleFree residualAssignmentTableProgram :=
  oracleFree_linkPrograms
    (preserveRightProgram_oracleFree residualAssignmentMapProgram
      residualAssignmentMapProgram_oracleFree)
    swapPairProgram_oracleFree

/-- The table machine's input: the pool's request list beside its population. -/
def residualAssignmentTableInput {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) : ℕ :=
  Nat.pair
    (encodeBalancedList
      (residualAssignmentRequests occurrences inputMask liveMask))
    occurrences.length

def residualAssignmentTableFuel {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputMask liveMask : ℕ) : ℕ :=
  linkFuel swapPairProgram
    (preserveRightFuel
      (residualAssignmentMapFuel occurrences inputMask liveMask))
    4

def residualAssignmentTableBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (inputMask liveMask : ℕ) : ℕ :=
  max 1 <| max (natBitLength q) <|
    max
      (preserveRightBits
        (residualAssignmentMapBits occurrences live input inputMask liveMask)
        (encodeBalancedList
          (residualAssignmentRequests occurrences inputMask liveMask))
        occurrences.length
        (encodeBalancedList
          (finiteAssignmentTable
            (poolResidualAssignment occurrences live input))))
      (swapPairBits
        (encodeBalancedList
          (finiteAssignmentTable
            (poolResidualAssignment occurrences live input)))
        occurrences.length)

/-- **The pool's residual assignment context, executed.**  This is the row
table in exactly the shape `structuralForkRowEvaluatorProgram` consumes. -/
theorem run_residualAssignmentTableProgram {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (inputMask liveMask maximumBits : ℕ)
    (hinput : inputMask = encodeBitInput input)
    (hlive : liveMask = coordinateMask live)
    (hbits :
      residualAssignmentTableBits occurrences live input inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram residualAssignmentTableProgram maximumBits
        (residualAssignmentTableFuel occurrences inputMask liveMask)
        (initialNPOracleState q
          (residualAssignmentTableInput occurrences inputMask liveMask)) =
      some
        (finiteAssignmentContext
          (poolResidualAssignment occurrences live input)) := by
  have hpositive : 1 ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [residualAssignmentTableBits]
  have hlength : natBitLength q ≤ maximumBits := by
    refine le_trans ?_ hbits
    simp [residualAssignmentTableBits]
  have hpreserveBits :
      preserveRightBits
          (residualAssignmentMapBits occurrences live input inputMask liveMask)
          (encodeBalancedList
            (residualAssignmentRequests occurrences inputMask liveMask))
          occurrences.length
          (encodeBalancedList
            (finiteAssignmentTable
              (poolResidualAssignment occurrences live input))) ≤
        maximumBits := by
    refine le_trans ?_ hbits
    simp [residualAssignmentTableBits]
  have hswapBits :
      swapPairBits
          (encodeBalancedList
            (finiteAssignmentTable
              (poolResidualAssignment occurrences live input)))
          occurrences.length ≤
        maximumBits := by
    refine le_trans ?_ hbits
    simp [residualAssignmentTableBits]
  have hpreserve :
      runNPOracleProgram (preserveRightProgram residualAssignmentMapProgram)
          maximumBits
          (preserveRightFuel
            (residualAssignmentMapFuel occurrences inputMask liveMask))
          (initialNPOracleState q
            (residualAssignmentTableInput occurrences inputMask liveMask)) =
        some
          (Nat.pair
            (encodeBalancedList
              (finiteAssignmentTable
                (poolResidualAssignment occurrences live input)))
            occurrences.length) := by
    refine run_bits_mono ?_ hpreserveBits
    exact run_preserveRightProgram residualAssignmentMapProgram q
      (residualAssignmentMapBits occurrences live input inputMask liveMask)
      (residualAssignmentMapFuel occurrences inputMask liveMask)
      (encodeBalancedList
        (residualAssignmentRequests occurrences inputMask liveMask))
      occurrences.length
      (encodeBalancedList
        (finiteAssignmentTable
          (poolResidualAssignment occurrences live input)))
      (run_residualAssignmentMapProgram occurrences live input inputMask
        liveMask _ hinput hlive le_rfl)
  have hswap :
      runNPOracleProgram swapPairProgram maximumBits 4
          (initialNPOracleState q
            (Nat.pair
              (encodeBalancedList
                (finiteAssignmentTable
                  (poolResidualAssignment occurrences live input)))
              occurrences.length)) =
        some
          (finiteAssignmentContext
            (poolResidualAssignment occurrences live input)) :=
    run_bits_mono
      (run_swapPairProgram q
        (encodeBalancedList
          (finiteAssignmentTable
            (poolResidualAssignment occurrences live input)))
        occurrences.length)
      hswapBits
  exact run_linkPrograms hpositive hlength hpreserve hswap

/-- **The symmetric row's residual assignment context, executed.**  This is the
`htable` premise of `run_structuralForkRowEvaluatorProgram_symmetricRow` with
the greedy live-set selector left abstract in `hlive`. -/
theorem run_symmetricRowResidualAssignmentTableProgram
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) (input : BitInput request.q)
    (inputMask liveMask maximumBits : ℕ)
    (hinput : inputMask = encodeBitInput input)
    (hlive :
      liveMask =
        coordinateMask
          (normalizedLiveSet (symmetricFourfoldOccurrences request)
            liveScale))
    (hbits :
      residualAssignmentTableBits (symmetricFourfoldOccurrences request)
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
          input inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram residualAssignmentTableProgram maximumBits
        (residualAssignmentTableFuel (symmetricFourfoldOccurrences request)
          inputMask liveMask)
        (initialNPOracleState request.q
          (residualAssignmentTableInput (symmetricFourfoldOccurrences request)
            inputMask liveMask)) =
      some
        (finiteAssignmentContext
          (symmetricRowResidualAssignment request liveScale input)) := by
  have hassignment :
      poolResidualAssignment (symmetricFourfoldOccurrences request)
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
          input =
        symmetricRowResidualAssignment request liveScale input :=
    rfl
  rw [← hassignment]
  exact run_residualAssignmentTableProgram (symmetricFourfoldOccurrences request)
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale) input
    inputMask liveMask maximumBits hinput hlive hbits

end NearCubicWires.CanonicalSignedGateEvaluationProgram
