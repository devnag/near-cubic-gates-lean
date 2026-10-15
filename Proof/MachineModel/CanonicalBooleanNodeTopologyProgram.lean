import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.MachineModel.CanonicalBalancedLookupProgram
import Proof.MachineModel.CanonicalBooleanRangeAggregationProgram
import Proof.MachineModel.CanonicalBooleanNodeValidationProgram
import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.Circuits.CanonicalPairedCall
import Proof.MachineModel.PreserveRightProgram
import Proof.Circuits.RegisterBounds
import Proof.Foundations.VerifiedLinker

/-!
# Indexed Boolean-node topology validation

Structural node validation produces a compact descriptor.  This module turns
one descriptor and its machine-generated index into two explicit native
less-than requests, executes both through the sole native-call/paired-call
path, and conjoins the results.  Unary cases use a fixed true comparison;
malformed descriptors use a fixed false comparison.
-/

namespace NearCubicWires.CanonicalBooleanNodeTopologyProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanNodeValidationProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RegisterBounds
open NearCubicWires.VerifiedLinker

def nativeLtRequest (left right : ℕ) : ℕ :=
  nativeInputRequest right left

def nativeLtRequestOutput (request : ℕ) : ℕ :=
  decide ((Nat.unpair request).2 < (Nat.unpair request).1) |>.toNat

@[simp] theorem nativeLtRequestOutput_nativeLtRequest (left right : ℕ) :
    nativeLtRequestOutput (nativeLtRequest left right) =
      (decide (left < right)).toNat := by
  simp [nativeLtRequestOutput, nativeLtRequest, nativeInputRequest]

def topologyTrueRequest : ℕ :=
  nativeLtRequest 0 1

def topologyFalseRequest : ℕ :=
  nativeLtRequest 1 0

def booleanTopologyComparisonRequests
    (inputLength descriptor index : ℕ) : ℕ :=
  if descriptor = 0 then
    Nat.pair topologyFalseRequest topologyFalseRequest
  else
    let presence := (Nat.unpair descriptor).1
    let body := (Nat.unpair descriptor).2
    if presence = 0 then
      Nat.pair topologyFalseRequest topologyFalseRequest
    else
      let tag := (Nat.unpair body).1
      let argument := (Nat.unpair body).2
      if tag = 0 then
        Nat.pair topologyTrueRequest topologyTrueRequest
      else if tag = 1 then
        Nat.pair (nativeLtRequest argument inputLength)
          topologyTrueRequest
      else if tag = 2 then
        Nat.pair (nativeLtRequest argument index) topologyTrueRequest
      else if tag = 3 ∨ tag = 4 then
        Nat.pair
          (nativeLtRequest (Nat.unpair argument).1 index)
          (nativeLtRequest (Nat.unpair argument).2 index)
      else
        Nat.pair topologyFalseRequest topologyFalseRequest

/-! ## Descriptor-to-comparison lowering -/

private def booleanTopologyComparisonPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .branchZero 2 35 3
  , .unpairLeft 2 4 4
  , .unpairRight 2 5 5
  , .branchZero 4 35 6
  , .unpairLeft 5 4 7
  , .unpairRight 5 6 8
  , .branchZero 4 24 9
  , .decrement 4 10
  , .branchZero 4 27 11
  , .decrement 4 12
  , .branchZero 4 29 13
  , .decrement 4 14
  , .branchZero 4 31 15
  , .decrement 4 16
  , .branchZero 4 31 35
  , .branchZero 0 35 35
  , .branchZero 0 35 35
  , .branchZero 0 35 35
  , .branchZero 0 35 35
  , .branchZero 0 35 35
  , .branchZero 0 35 35
  , .branchZero 0 35 35
  , .set 7 1 25
  , .pair 7 4 8 26
  , .copy 8 9 43
  , .pair 1 6 8 38
  , .branchZero 0 35 35
  , .pair 3 6 8 38
  , .branchZero 0 35 35
  , .unpairLeft 6 10 32
  , .unpairRight 6 11 33
  , .pair 3 10 8 34
  , .pair 3 11 9 43
  , .set 7 1 36
  , .set 4 0 37
  , .pair 4 7 8 40
  , .set 7 1 39
  , .set 4 0 41
  , .copy 8 9 43
  , .pair 7 4 9 43
  , .branchZero 0 35 35
  , .pair 8 9 0 44
  , .halt 0
  ]

private theorem booleanTopologyComparisonPrepareProgram_oracleFree :
    OracleFree booleanTopologyComparisonPrepareProgram := by
  rfl

private def booleanTopologyComparisonPrepareBase
    (inputLength descriptor index : ℕ) : ℕ :=
  max 1 (max inputLength (Nat.pair descriptor index))

private def booleanTopologyComparisonPrepareBits
    (inputLength descriptor index : ℕ) : ℕ :=
  natBitLength <|
    pairIter 2
      (booleanTopologyComparisonPrepareBase
        inputLength descriptor index)

private def booleanTopologyComparisonPrepareFuel : ℕ := 30

private theorem topologyPrepare_base_one
    (inputLength descriptor index : ℕ) :
    1 ≤ booleanTopologyComparisonPrepareBase
      inputLength descriptor index := by
  simp [booleanTopologyComparisonPrepareBase]

private theorem topologyPrepare_inputLength_le
    (inputLength descriptor index : ℕ) :
    inputLength ≤ booleanTopologyComparisonPrepareBase
      inputLength descriptor index := by
  simp [booleanTopologyComparisonPrepareBase]

private theorem topologyPrepare_descriptor_le
    (inputLength descriptor index : ℕ) :
    descriptor ≤ booleanTopologyComparisonPrepareBase
      inputLength descriptor index := by
  apply le_trans (Nat.left_le_pair descriptor index)
  simp [booleanTopologyComparisonPrepareBase]

private theorem topologyPrepare_index_le
    (inputLength descriptor index : ℕ) :
    index ≤ booleanTopologyComparisonPrepareBase
      inputLength descriptor index := by
  apply le_trans (Nat.right_le_pair descriptor index)
  simp [booleanTopologyComparisonPrepareBase]

private theorem topologyPrepare_value_bits
    {inputLength descriptor index value : ℕ}
    (hvalue :
      value ≤ pairIter 2
        (booleanTopologyComparisonPrepareBase
          inputLength descriptor index)) :
    natBitLength value ≤
      booleanTopologyComparisonPrepareBits
        inputLength descriptor index := by
  exact natBitLength_mono hvalue

private theorem topologyPrepare_base_bits
    (inputLength descriptor index : ℕ) :
    natBitLength
        (booleanTopologyComparisonPrepareBase
          inputLength descriptor index) ≤
      booleanTopologyComparisonPrepareBits
        inputLength descriptor index :=
  topologyPrepare_value_bits
    (value_le_pairIter 2
      (booleanTopologyComparisonPrepareBase
        inputLength descriptor index))

private theorem topologyPrepare_pair_bits
    {inputLength descriptor index left right : ℕ}
    (hleft :
      left ≤ booleanTopologyComparisonPrepareBase
        inputLength descriptor index)
    (hright :
      right ≤ booleanTopologyComparisonPrepareBase
        inputLength descriptor index) :
    natBitLength (Nat.pair left right) ≤
      booleanTopologyComparisonPrepareBits
        inputLength descriptor index := by
  apply topologyPrepare_value_bits
  apply (pair_mono hleft hright).trans
  exact value_le_pairIter 1 _

private theorem topologyPrepare_output_bits
    {inputLength descriptor index first second : ℕ}
    (hfirst :
      first ≤ pairIter 1
        (booleanTopologyComparisonPrepareBase
          inputLength descriptor index))
    (hsecond :
      second ≤ pairIter 1
        (booleanTopologyComparisonPrepareBase
          inputLength descriptor index)) :
    natBitLength (Nat.pair first second) ≤
      booleanTopologyComparisonPrepareBits
        inputLength descriptor index := by
  apply topologyPrepare_value_bits
  simpa only [pairIter_succ, pairIter_zero] using
    pair_mono hfirst hsecond

private theorem topologyPrepare_trueRequest_le
    (inputLength descriptor index : ℕ) :
    topologyTrueRequest ≤ pairIter 1
      (booleanTopologyComparisonPrepareBase
        inputLength descriptor index) := by
  unfold topologyTrueRequest nativeLtRequest nativeInputRequest
  simpa only [pairIter_succ, pairIter_zero] using
    pair_mono
      (topologyPrepare_base_one inputLength descriptor index)
      (Nat.zero_le _)

private theorem topologyPrepare_falseRequest_le
    (inputLength descriptor index : ℕ) :
    topologyFalseRequest ≤ pairIter 1
      (booleanTopologyComparisonPrepareBase
        inputLength descriptor index) := by
  unfold topologyFalseRequest nativeLtRequest nativeInputRequest
  simpa only [pairIter_succ, pairIter_zero] using
    pair_mono
      (Nat.zero_le _)
      (topologyPrepare_base_one inputLength descriptor index)

private theorem run_booleanTopologyPrepareInvalid
    (inputLength descriptor index extra : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 35) :
    runNPOracleProgram booleanTopologyComparisonPrepareProgram
        (booleanTopologyComparisonPrepareBits inputLength descriptor index)
        (extra + 6) state =
      some
        (Nat.pair topologyFalseRequest topologyFalseRequest) := by
  let maximumBits :=
    booleanTopologyComparisonPrepareBits inputLength descriptor index
  have honeBits : natBitLength 1 ≤ maximumBits := by
    exact topologyPrepare_value_bits <|
      (topologyPrepare_base_one inputLength descriptor index).trans
        (value_le_pairIter 2 _)
  have hzeroBits : natBitLength 0 ≤ maximumBits := by
    exact (natBitLength_mono (Nat.zero_le 1)).trans honeBits
  have hfalseBits :
      natBitLength topologyFalseRequest ≤ maximumBits := by
    exact topologyPrepare_value_bits <|
      (topologyPrepare_falseRequest_le inputLength descriptor index).trans
        (value_le_pairIter 1 _)
  have houtputBits :
      natBitLength
          (Nat.pair topologyFalseRequest topologyFalseRequest) ≤
        maximumBits :=
    topologyPrepare_output_bits
      (topologyPrepare_falseRequest_le inputLength descriptor index)
      (topologyPrepare_falseRequest_le inputLength descriptor index)
  rw [show extra + 6 = (extra + 5) + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) hpc honeBits]
  rw [show extra + 5 = (extra + 4) + 1 by omega]
  rw [run_set_instruction (value := 0)
    (by rfl) rfl hzeroBits]
  rw [show extra + 4 = (extra + 3) + 1 by omega]
  rw [run_pair_instruction (value := topologyFalseRequest)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        topologyFalseRequest, nativeLtRequest, nativeInputRequest])
    hfalseBits]
  rw [show extra + 3 = (extra + 2) + 1 by omega]
  rw [run_copy_instruction (value := topologyFalseRequest)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    hfalseBits]
  rw [show extra + 2 = (extra + 1) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair topologyFalseRequest topologyFalseRequest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := extra) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

private theorem run_booleanTopologyPrepareConst
    (inputLength descriptor index extra : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 24)
    (htag : state.registers 4 = 0) :
    runNPOracleProgram booleanTopologyComparisonPrepareProgram
        (booleanTopologyComparisonPrepareBits inputLength descriptor index)
        (extra + 5) state =
      some (Nat.pair topologyTrueRequest topologyTrueRequest) := by
  let maximumBits :=
    booleanTopologyComparisonPrepareBits inputLength descriptor index
  have honeBits : natBitLength 1 ≤ maximumBits := by
    exact topologyPrepare_value_bits <|
      (topologyPrepare_base_one inputLength descriptor index).trans
        (value_le_pairIter 2 _)
  have htrueBits : natBitLength topologyTrueRequest ≤ maximumBits := by
    exact topologyPrepare_value_bits <|
      (topologyPrepare_trueRequest_le inputLength descriptor index).trans
        (value_le_pairIter 1 _)
  have houtputBits :
      natBitLength
          (Nat.pair topologyTrueRequest topologyTrueRequest) ≤
        maximumBits :=
    topologyPrepare_output_bits
      (topologyPrepare_trueRequest_le inputLength descriptor index)
      (topologyPrepare_trueRequest_le inputLength descriptor index)
  rw [show extra + 5 = (extra + 4) + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) hpc honeBits]
  rw [show extra + 4 = (extra + 3) + 1 by omega]
  rw [run_pair_instruction (value := topologyTrueRequest)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, htag,
        topologyTrueRequest, nativeLtRequest, nativeInputRequest])
    htrueBits]
  rw [show extra + 3 = (extra + 2) + 1 by omega]
  rw [run_copy_instruction (value := topologyTrueRequest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htrueBits]
  rw [show extra + 2 = (extra + 1) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair topologyTrueRequest topologyTrueRequest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := extra) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

private theorem run_booleanTopologyPrepareUnary
    (inputLength descriptor index extra right argument handler : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = handler)
    (hhandler : handler = 27 ∨ handler = 29)
    (hright :
      (if handler = 27 then state.registers 1 else state.registers 3) =
        right)
    (hargument : state.registers 6 = argument)
    (hrightBound :
      right ≤ booleanTopologyComparisonPrepareBase
        inputLength descriptor index)
    (hargumentBound :
      argument ≤ booleanTopologyComparisonPrepareBase
        inputLength descriptor index) :
    runNPOracleProgram booleanTopologyComparisonPrepareProgram
        (booleanTopologyComparisonPrepareBits inputLength descriptor index)
        (extra + 6) state =
      some
        (Nat.pair (nativeLtRequest argument right)
          topologyTrueRequest) := by
  rcases hhandler with rfl | rfl
  · have hrequestBits :
        natBitLength (nativeLtRequest argument right) ≤
          booleanTopologyComparisonPrepareBits
            inputLength descriptor index := by
      exact topologyPrepare_pair_bits hrightBound hargumentBound
    have htrueBits :
        natBitLength topologyTrueRequest ≤
          booleanTopologyComparisonPrepareBits
            inputLength descriptor index := by
      exact topologyPrepare_value_bits <|
        (topologyPrepare_trueRequest_le inputLength descriptor index).trans
          (value_le_pairIter 1 _)
    have hrequestBound :
        nativeLtRequest argument right ≤ pairIter 1
          (booleanTopologyComparisonPrepareBase
            inputLength descriptor index) := by
      unfold nativeLtRequest nativeInputRequest
      simpa only [pairIter_succ, pairIter_zero] using
        pair_mono hrightBound hargumentBound
    have houtputBits :
        natBitLength
            (Nat.pair (nativeLtRequest argument right)
              topologyTrueRequest) ≤
          booleanTopologyComparisonPrepareBits
            inputLength descriptor index :=
      topologyPrepare_output_bits hrequestBound
        (topologyPrepare_trueRequest_le inputLength descriptor index)
    have honeBits :
        natBitLength 1 ≤
          booleanTopologyComparisonPrepareBits
            inputLength descriptor index := by
      exact topologyPrepare_value_bits <|
        (topologyPrepare_base_one inputLength descriptor index).trans
          (value_le_pairIter 2 _)
    have hzeroBits :
        natBitLength 0 ≤
          booleanTopologyComparisonPrepareBits
            inputLength descriptor index :=
      (natBitLength_mono (Nat.zero_le 1)).trans honeBits
    have hright' : state.registers 1 = right := by
      simpa using hright
    rw [show extra + 6 = (extra + 5) + 1 by omega]
    rw [run_pair_instruction
      (value := nativeLtRequest argument right)
      (by rfl) hpc
      (by
        simp [hargument, hright', nativeLtRequest, nativeInputRequest])
      hrequestBits]
    rw [show extra + 5 = (extra + 4) + 1 by omega]
    rw [run_set_instruction (value := 1)
      (by rfl) rfl honeBits]
    rw [show extra + 4 = (extra + 3) + 1 by omega]
    rw [run_set_instruction (value := 0)
      (by rfl) rfl hzeroBits]
    rw [show extra + 3 = (extra + 2) + 1 by omega]
    rw [run_pair_instruction (value := topologyTrueRequest)
      (by rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          topologyTrueRequest, nativeLtRequest, nativeInputRequest])
      htrueBits]
    rw [show extra + 2 = (extra + 1) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair (nativeLtRequest argument right)
          topologyTrueRequest)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      houtputBits]
    exact run_halt_instruction (fuel := extra) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      houtputBits
  · have hrequestBits :
        natBitLength (nativeLtRequest argument right) ≤
          booleanTopologyComparisonPrepareBits
            inputLength descriptor index := by
      exact topologyPrepare_pair_bits hrightBound hargumentBound
    have htrueBits :
        natBitLength topologyTrueRequest ≤
          booleanTopologyComparisonPrepareBits
            inputLength descriptor index := by
      exact topologyPrepare_value_bits <|
        (topologyPrepare_trueRequest_le inputLength descriptor index).trans
          (value_le_pairIter 1 _)
    have hrequestBound :
        nativeLtRequest argument right ≤ pairIter 1
          (booleanTopologyComparisonPrepareBase
            inputLength descriptor index) := by
      unfold nativeLtRequest nativeInputRequest
      simpa only [pairIter_succ, pairIter_zero] using
        pair_mono hrightBound hargumentBound
    have houtputBits :
        natBitLength
            (Nat.pair (nativeLtRequest argument right)
              topologyTrueRequest) ≤
          booleanTopologyComparisonPrepareBits
            inputLength descriptor index :=
      topologyPrepare_output_bits hrequestBound
        (topologyPrepare_trueRequest_le inputLength descriptor index)
    have honeBits :
        natBitLength 1 ≤
          booleanTopologyComparisonPrepareBits
            inputLength descriptor index := by
      exact topologyPrepare_value_bits <|
        (topologyPrepare_base_one inputLength descriptor index).trans
          (value_le_pairIter 2 _)
    have hzeroBits :
        natBitLength 0 ≤
          booleanTopologyComparisonPrepareBits
            inputLength descriptor index :=
      (natBitLength_mono (Nat.zero_le 1)).trans honeBits
    have hright' : state.registers 3 = right := by
      simpa using hright
    rw [show extra + 6 = (extra + 5) + 1 by omega]
    rw [run_pair_instruction
      (value := nativeLtRequest argument right)
      (by rfl) hpc
      (by
        simp [hargument, hright', nativeLtRequest, nativeInputRequest])
      hrequestBits]
    rw [show extra + 5 = (extra + 4) + 1 by omega]
    rw [run_set_instruction (value := 1)
      (by rfl) rfl honeBits]
    rw [show extra + 4 = (extra + 3) + 1 by omega]
    rw [run_set_instruction (value := 0)
      (by rfl) rfl hzeroBits]
    rw [show extra + 3 = (extra + 2) + 1 by omega]
    rw [run_pair_instruction (value := topologyTrueRequest)
      (by rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          topologyTrueRequest, nativeLtRequest, nativeInputRequest])
      htrueBits]
    rw [show extra + 2 = (extra + 1) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair (nativeLtRequest argument right)
          topologyTrueRequest)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      houtputBits]
    exact run_halt_instruction (fuel := extra) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      houtputBits

private theorem run_booleanTopologyPrepareBinary
    (inputLength descriptor index extra argument : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 31)
    (hindex : state.registers 3 = index)
    (hargument : state.registers 6 = argument)
    (hargumentBound :
      argument ≤ booleanTopologyComparisonPrepareBase
        inputLength descriptor index) :
    runNPOracleProgram booleanTopologyComparisonPrepareProgram
        (booleanTopologyComparisonPrepareBits inputLength descriptor index)
        (extra + 6) state =
      some
        (Nat.pair
          (nativeLtRequest (Nat.unpair argument).1 index)
          (nativeLtRequest (Nat.unpair argument).2 index)) := by
  let left := (Nat.unpair argument).1
  let right := (Nat.unpair argument).2
  let base :=
    booleanTopologyComparisonPrepareBase inputLength descriptor index
  let maximumBits :=
    booleanTopologyComparisonPrepareBits inputLength descriptor index
  have hindexBound : index ≤ base :=
    topologyPrepare_index_le inputLength descriptor index
  have hleftBound : left ≤ base := by
    exact (Nat.unpair_left_le argument).trans hargumentBound
  have hrightBound : right ≤ base := by
    exact (Nat.unpair_right_le argument).trans hargumentBound
  have hleftBits : natBitLength left ≤ maximumBits :=
    topologyPrepare_value_bits <|
      hleftBound.trans (value_le_pairIter 2 base)
  have hrightBits : natBitLength right ≤ maximumBits :=
    topologyPrepare_value_bits <|
      hrightBound.trans (value_le_pairIter 2 base)
  have hfirstBits :
      natBitLength (nativeLtRequest left index) ≤ maximumBits := by
    exact topologyPrepare_pair_bits hindexBound hleftBound
  have hsecondBits :
      natBitLength (nativeLtRequest right index) ≤ maximumBits := by
    exact topologyPrepare_pair_bits hindexBound hrightBound
  have hfirstBound :
      nativeLtRequest left index ≤ pairIter 1 base := by
    unfold nativeLtRequest nativeInputRequest
    simpa only [pairIter_succ, pairIter_zero] using
      pair_mono hindexBound hleftBound
  have hsecondBound :
      nativeLtRequest right index ≤ pairIter 1 base := by
    unfold nativeLtRequest nativeInputRequest
    simpa only [pairIter_succ, pairIter_zero] using
      pair_mono hindexBound hrightBound
  have houtputBits :
      natBitLength
          (Nat.pair (nativeLtRequest left index)
            (nativeLtRequest right index)) ≤ maximumBits :=
    topologyPrepare_output_bits hfirstBound hsecondBound
  rw [show extra + 6 = (extra + 5) + 1 by omega]
  rw [run_unpairLeft_instruction (value := left)
    (by rfl) hpc
    (by simp [hargument, left])
    hleftBits]
  rw [show extra + 5 = (extra + 4) + 1 by omega]
  rw [run_unpairRight_instruction (value := right)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      hargument, right])
    hrightBits]
  rw [show extra + 4 = (extra + 3) + 1 by omega]
  rw [run_pair_instruction (value := nativeLtRequest left index)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hindex,
        nativeLtRequest, nativeInputRequest, left])
    hfirstBits]
  rw [show extra + 3 = (extra + 2) + 1 by omega]
  rw [run_pair_instruction (value := nativeLtRequest right index)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hindex,
        nativeLtRequest, nativeInputRequest, right])
    hsecondBits]
  rw [show extra + 2 = (extra + 1) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (nativeLtRequest left index)
        (nativeLtRequest right index))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := extra) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, left, right])
    houtputBits

private theorem run_booleanTopologyComparisonPrepareProgram
    (inputLength descriptor index : ℕ) :
    runNPOracleProgram booleanTopologyComparisonPrepareProgram
        (booleanTopologyComparisonPrepareBits inputLength descriptor index)
        booleanTopologyComparisonPrepareFuel
        (initialNPOracleState inputLength
          (Nat.pair descriptor index)) =
      some
        (booleanTopologyComparisonRequests
          inputLength descriptor index) := by
  let presence := (Nat.unpair descriptor).1
  let body := (Nat.unpair descriptor).2
  let tag := (Nat.unpair body).1
  let argument := (Nat.unpair body).2
  let base :=
    booleanTopologyComparisonPrepareBase inputLength descriptor index
  let maximumBits :=
    booleanTopologyComparisonPrepareBits inputLength descriptor index
  have hdescriptorBound : descriptor ≤ base :=
    topologyPrepare_descriptor_le inputLength descriptor index
  have hindexBound : index ≤ base :=
    topologyPrepare_index_le inputLength descriptor index
  have hinputLengthBound : inputLength ≤ base :=
    topologyPrepare_inputLength_le inputLength descriptor index
  have hdescriptorBits : natBitLength descriptor ≤ maximumBits :=
    topologyPrepare_value_bits <|
      hdescriptorBound.trans (value_le_pairIter 2 base)
  have hindexBits : natBitLength index ≤ maximumBits :=
    topologyPrepare_value_bits <|
      hindexBound.trans (value_le_pairIter 2 base)
  have hpresenceBound : presence ≤ base := by
    exact (Nat.unpair_left_le descriptor).trans hdescriptorBound
  have hbodyBound : body ≤ base := by
    exact (Nat.unpair_right_le descriptor).trans hdescriptorBound
  have hpresenceBits : natBitLength presence ≤ maximumBits :=
    topologyPrepare_value_bits <|
      hpresenceBound.trans (value_le_pairIter 2 base)
  have hbodyBits : natBitLength body ≤ maximumBits :=
    topologyPrepare_value_bits <|
      hbodyBound.trans (value_le_pairIter 2 base)
  have htagBound : tag ≤ base := by
    exact (Nat.unpair_left_le body).trans hbodyBound
  have hargumentBound : argument ≤ base := by
    exact (Nat.unpair_right_le body).trans hbodyBound
  have htagBits : natBitLength tag ≤ maximumBits :=
    topologyPrepare_value_bits <|
      htagBound.trans (value_le_pairIter 2 base)
  have hargumentBits : natBitLength argument ≤ maximumBits :=
    topologyPrepare_value_bits <|
      hargumentBound.trans (value_le_pairIter 2 base)
  rw [show booleanTopologyComparisonPrepareFuel = 29 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := descriptor)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hdescriptorBits]
  rw [show 29 = 28 + 1 by omega]
  rw [run_unpairRight_instruction (value := index)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    hindexBits]
  rw [show 28 = 27 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  by_cases hdescriptor : descriptor = 0
  · rw [if_pos (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, hdescriptor])]
    rw [show
      booleanTopologyComparisonRequests inputLength descriptor index =
          Nat.pair topologyFalseRequest topologyFalseRequest by
        simp [booleanTopologyComparisonRequests, hdescriptor]]
    exact run_booleanTopologyPrepareInvalid
      inputLength descriptor index 21 _ rfl
  · rw [if_neg (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, hdescriptor])]
    rw [show 27 = 26 + 1 by omega]
    rw [run_unpairLeft_instruction (value := presence)
      (by rfl) rfl
      (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, presence])
      hpresenceBits]
    rw [show 26 = 25 + 1 by omega]
    rw [run_unpairRight_instruction (value := body)
      (by rfl) rfl
      (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, body])
      hbodyBits]
    rw [show 25 = 24 + 1 by omega]
    rw [run_branchZero_instruction (by rfl) rfl]
    by_cases hpresence : presence = 0
    · rw [if_pos (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, hpresence])]
      rw [show
        booleanTopologyComparisonRequests inputLength descriptor index =
            Nat.pair topologyFalseRequest topologyFalseRequest by
          simp [booleanTopologyComparisonRequests, hdescriptor,
            presence, hpresence]]
      exact run_booleanTopologyPrepareInvalid
        inputLength descriptor index 18 _ rfl
    · rw [if_neg (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, hpresence])]
      rw [show 24 = 23 + 1 by omega]
      rw [run_unpairLeft_instruction (value := tag)
        (by rfl) rfl
        (by
          simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump, tag])
        htagBits]
      rw [show 23 = 22 + 1 by omega]
      rw [run_unpairRight_instruction (value := argument)
        (by rfl) rfl
        (by
          simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump, argument])
        hargumentBits]
      rw [show 22 = 21 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      by_cases htag0 : tag = 0
      · rw [if_pos (by
          simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump, htag0])]
        rw [show
          booleanTopologyComparisonRequests inputLength descriptor index =
              Nat.pair topologyTrueRequest topologyTrueRequest by
            simp [booleanTopologyComparisonRequests, hdescriptor,
              presence, body, tag, hpresence, htag0]]
        apply run_booleanTopologyPrepareConst
          inputLength descriptor index 16
        · rfl
        · simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump, htag0]
      · rw [if_neg (by
          simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump, htag0])]
        let tag1 := tag - 1
        have htag1Bits : natBitLength tag1 ≤ maximumBits :=
          (decrement_bits_le tag).trans htagBits
        rw [show 21 = 20 + 1 by omega]
        rw [run_decrement_instruction (value := tag1)
          (by rfl) rfl
          (by
            simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, tag1])
          htag1Bits]
        rw [show 20 = 19 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        by_cases htag1 : tag = 1
        · have htag1zero : tag1 = 0 := by
            simp [tag1, htag1]
          rw [if_pos (by
            simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, htag1zero])]
          rw [show
            booleanTopologyComparisonRequests inputLength descriptor index =
                Nat.pair (nativeLtRequest argument inputLength)
                  topologyTrueRequest by
              simp [booleanTopologyComparisonRequests, hdescriptor,
                presence, body, tag, argument, hpresence, htag1]]
          apply run_booleanTopologyPrepareUnary
            inputLength descriptor index 13 inputLength argument 27
          · rfl
          · exact Or.inl rfl
          · simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump]
          · simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, argument]
          · exact hinputLengthBound
          · exact hargumentBound
        · have htag1nonzero : tag1 ≠ 0 := by
            simp [tag1]
            omega
          rw [if_neg (by
            simp [initialNPOracleState, NPOracleState.write,
              NPOracleState.jump, htag1nonzero])]
          let tag2 := tag1 - 1
          have htag2Bits : natBitLength tag2 ≤ maximumBits :=
            (decrement_bits_le tag1).trans htag1Bits
          rw [show 19 = 18 + 1 by omega]
          rw [run_decrement_instruction (value := tag2)
            (by rfl) rfl
            (by
              simp [initialNPOracleState, NPOracleState.write,
                NPOracleState.jump, tag2])
            htag2Bits]
          rw [show 18 = 17 + 1 by omega]
          rw [run_branchZero_instruction (by rfl) rfl]
          by_cases htag2 : tag = 2
          · have htag2zero : tag2 = 0 := by
              simp [tag2, tag1, htag2]
            rw [if_pos (by
              simp [initialNPOracleState, NPOracleState.write,
                NPOracleState.jump, htag2zero])]
            rw [show
              booleanTopologyComparisonRequests inputLength descriptor index =
                  Nat.pair (nativeLtRequest argument index)
                    topologyTrueRequest by
                simp [booleanTopologyComparisonRequests, hdescriptor,
                  presence, body, tag, argument, hpresence, htag2]]
            apply run_booleanTopologyPrepareUnary
              inputLength descriptor index 11 index argument 29
            · rfl
            · exact Or.inr rfl
            · simp [initialNPOracleState, NPOracleState.write,
                NPOracleState.jump]
            · simp [initialNPOracleState, NPOracleState.write,
                NPOracleState.jump, argument]
            · exact hindexBound
            · exact hargumentBound
          · have htag2nonzero : tag2 ≠ 0 := by
              simp [tag2, tag1]
              omega
            rw [if_neg (by
              simp [initialNPOracleState, NPOracleState.write,
                NPOracleState.jump, htag2nonzero])]
            let tag3 := tag2 - 1
            have htag3Bits : natBitLength tag3 ≤ maximumBits :=
              (decrement_bits_le tag2).trans htag2Bits
            rw [show 17 = 16 + 1 by omega]
            rw [run_decrement_instruction (value := tag3)
              (by rfl) rfl
              (by
                simp [initialNPOracleState, NPOracleState.write,
                  NPOracleState.jump, tag3])
              htag3Bits]
            rw [show 16 = 15 + 1 by omega]
            rw [run_branchZero_instruction (by rfl) rfl]
            by_cases htag3 : tag = 3
            · have htag3zero : tag3 = 0 := by
                simp [tag3, tag2, tag1, htag3]
              rw [if_pos (by
                simp [initialNPOracleState, NPOracleState.write,
                  NPOracleState.jump, htag3zero])]
              rw [show
                booleanTopologyComparisonRequests inputLength descriptor index =
                    Nat.pair
                      (nativeLtRequest (Nat.unpair argument).1 index)
                      (nativeLtRequest (Nat.unpair argument).2 index) by
                  simp [booleanTopologyComparisonRequests, hdescriptor,
                    presence, body, tag, argument, hpresence, htag3]]
              apply run_booleanTopologyPrepareBinary
                inputLength descriptor index 9 argument
              · rfl
              · simp [initialNPOracleState, NPOracleState.write,
                  NPOracleState.jump]
              · simp [initialNPOracleState, NPOracleState.write,
                  NPOracleState.jump, argument]
              · exact hargumentBound
            · have htag3nonzero : tag3 ≠ 0 := by
                simp [tag3, tag2, tag1]
                omega
              rw [if_neg (by
                simp [initialNPOracleState, NPOracleState.write,
                  NPOracleState.jump, htag3nonzero])]
              let tag4 := tag3 - 1
              have htag4Bits : natBitLength tag4 ≤ maximumBits :=
                (decrement_bits_le tag3).trans htag3Bits
              rw [show 15 = 14 + 1 by omega]
              rw [run_decrement_instruction (value := tag4)
                (by rfl) rfl
                (by
                  simp [initialNPOracleState, NPOracleState.write,
                    NPOracleState.jump, tag4])
                htag4Bits]
              rw [show 14 = 13 + 1 by omega]
              rw [run_branchZero_instruction (by rfl) rfl]
              by_cases htag4 : tag = 4
              · have htag4zero : tag4 = 0 := by
                  simp [tag4, tag3, tag2, tag1, htag4]
                rw [if_pos (by
                  simp [initialNPOracleState, NPOracleState.write,
                    NPOracleState.jump, htag4zero])]
                rw [show
                  booleanTopologyComparisonRequests
                      inputLength descriptor index =
                    Nat.pair
                      (nativeLtRequest (Nat.unpair argument).1 index)
                      (nativeLtRequest (Nat.unpair argument).2 index) by
                    simp [booleanTopologyComparisonRequests, hdescriptor,
                      presence, body, tag, argument, hpresence, htag4]]
                apply run_booleanTopologyPrepareBinary
                  inputLength descriptor index 7 argument
                · rfl
                · simp [initialNPOracleState, NPOracleState.write,
                    NPOracleState.jump]
                · simp [initialNPOracleState, NPOracleState.write,
                    NPOracleState.jump, argument]
                · exact hargumentBound
              · have htag4nonzero : tag4 ≠ 0 := by
                  simp [tag4, tag3, tag2, tag1]
                  omega
                rw [if_neg (by
                  simp [initialNPOracleState, NPOracleState.write,
                    NPOracleState.jump, htag4nonzero])]
                rw [show
                  booleanTopologyComparisonRequests
                      inputLength descriptor index =
                    Nat.pair topologyFalseRequest
                      topologyFalseRequest by
                    simp [booleanTopologyComparisonRequests, hdescriptor,
                      presence, body, tag, hpresence, htag0,
                      htag1, htag2, htag3, htag4]]
                exact run_booleanTopologyPrepareInvalid
                  inputLength descriptor index 7 _ rfl

/-! ## Fixed native less-than calls -/

def nativeLtRequestProgram : NPOracleProgram :=
  nativeCallProgram binaryNatLtProgram

theorem nativeLtRequestProgram_oracleFree :
    OracleFree nativeLtRequestProgram :=
  nativeCallProgram_oracleFree binaryNatLtProgram_oracleFree

def nativeLtRequestBits (outerInputLength request : ℕ) : ℕ :=
  let right := (Nat.unpair request).1
  let left := (Nat.unpair request).2
  nativeCallBits outerInputLength right left
    (decide (left < right)).toNat
    (binaryNatLtBits left right)

def nativeLtRequestFuel (request : ℕ) : ℕ :=
  let right := (Nat.unpair request).1
  let left := (Nat.unpair request).2
  nativeCallFuel binaryNatLtProgram
    (2 + binaryNatLtLoopFuel left right) right left

theorem run_nativeLtRequestProgram
    (outerInputLength request : ℕ) :
    runNPOracleProgram nativeLtRequestProgram
        (nativeLtRequestBits outerInputLength request)
        (nativeLtRequestFuel request)
        (initialNPOracleState outerInputLength request) =
      some (nativeLtRequestOutput request) := by
  let right := (Nat.unpair request).1
  let left := (Nat.unpair request).2
  have hrequest : nativeInputRequest right left = request := by
    exact Nat.pair_unpair request
  have hcallee :
      runNPOracleProgram binaryNatLtProgram
          (binaryNatLtBits left right)
          (2 + binaryNatLtLoopFuel left right)
          (initialNPOracleState right left) =
        some (decide (left < right)).toNat :=
    run_binaryNatLtProgram left right
      (binaryNatLtBits left right) (le_refl _)
  have hrun :=
    run_nativeCallProgram binaryNatLtProgram outerInputLength
      right left (decide (left < right)).toNat
      (binaryNatLtBits left right)
      (2 + binaryNatLtLoopFuel left right) hcallee
  simpa [nativeLtRequestProgram, nativeLtRequestBits,
    nativeLtRequestFuel, nativeLtRequestOutput, right, left, hrequest]
    using hrun

private def booleanTopologyComparisonCallProgram : NPOracleProgram :=
  pairedCallProgram nativeLtRequestProgram

private theorem booleanTopologyComparisonCallProgram_oracleFree :
    OracleFree booleanTopologyComparisonCallProgram :=
  pairedCallProgram_oracleFree nativeLtRequestProgram
    nativeLtRequestProgram_oracleFree

private def booleanTopologyComparisonCallBits
    (inputLength first second : ℕ) : ℕ :=
  pairedCallBits inputLength
    (nativeLtRequestBits inputLength first)
    (nativeLtRequestBits inputLength second)
    first second
    (nativeLtRequestOutput first)
    (nativeLtRequestOutput second)

private def booleanTopologyComparisonCallFuel
    (first second : ℕ) : ℕ :=
  pairedCallFuel nativeLtRequestProgram
    (nativeLtRequestFuel first)
    (nativeLtRequestFuel second)

private theorem run_booleanTopologyComparisonCallProgram
    (inputLength first second : ℕ) :
    runNPOracleProgram booleanTopologyComparisonCallProgram
        (booleanTopologyComparisonCallBits inputLength first second)
        (booleanTopologyComparisonCallFuel first second)
        (initialNPOracleState inputLength (Nat.pair first second)) =
      some
        (Nat.pair (nativeLtRequestOutput first)
          (nativeLtRequestOutput second)) := by
  exact run_pairedCallProgram nativeLtRequestProgram
    inputLength
    (nativeLtRequestBits inputLength first)
    (nativeLtRequestBits inputLength second)
    (nativeLtRequestFuel first)
    (nativeLtRequestFuel second)
    first second
    (nativeLtRequestOutput first)
    (nativeLtRequestOutput second)
    (run_nativeLtRequestProgram inputLength first)
    (run_nativeLtRequestProgram inputLength second)

/-! ## Boolean conjunction tail -/

def booleanTopologyAndOutput (left right : ℕ) : ℕ :=
  if left = 0 ∨ right = 0 then 0 else 1

private def booleanTopologyAndProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .branchZero 2 6 3
  , .branchZero 3 6 4
  , .set 0 1 7
  , .branchZero 0 6 6
  , .set 0 0 7
  , .halt 0
  ]

private theorem booleanTopologyAndProgram_oracleFree :
    OracleFree booleanTopologyAndProgram := by
  rfl

private def booleanTopologyAndBits (left right : ℕ) : ℕ :=
  max (natBitLength (Nat.pair left right)) (natBitLength 1)

private def booleanTopologyAndFuel : ℕ := 6

private theorem run_booleanTopologyAndProgram
    (inputLength left right : ℕ) :
    runNPOracleProgram booleanTopologyAndProgram
        (booleanTopologyAndBits left right)
        booleanTopologyAndFuel
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (booleanTopologyAndOutput left right) := by
  have hinput :
      natBitLength (Nat.pair left right) ≤
        booleanTopologyAndBits left right :=
    Nat.le_max_left _ _
  have hleft :
      natBitLength left ≤ booleanTopologyAndBits left right := by
    exact
      (natBitLength_mono (Nat.left_le_pair left right)).trans hinput
  have hright :
      natBitLength right ≤ booleanTopologyAndBits left right := by
    exact
      (natBitLength_mono (Nat.right_le_pair left right)).trans hinput
  have hone :
      natBitLength 1 ≤ booleanTopologyAndBits left right :=
    Nat.le_max_right _ _
  have hzero :
      natBitLength 0 ≤ booleanTopologyAndBits left right :=
    (natBitLength_mono (Nat.zero_le 1)).trans hone
  rw [show booleanTopologyAndFuel = 5 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := left)
    (by rfl) rfl (by simp [initialNPOracleState]) hleft]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := right)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    hright]
  rw [show 4 = 3 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  by_cases hleftZero : left = 0
  · rw [if_pos (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, hleftZero])]
    rw [show 3 = 2 + 1 by omega]
    rw [run_set_instruction (value := 0)
      (by rfl) rfl hzero]
    rw [show booleanTopologyAndOutput left right = 0 by
      simp [booleanTopologyAndOutput, hleftZero]]
    exact run_halt_instruction (fuel := 1) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hzero
  · rw [if_neg (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, hleftZero])]
    rw [show 3 = 2 + 1 by omega]
    rw [run_branchZero_instruction (by rfl) rfl]
    by_cases hrightZero : right = 0
    · rw [if_pos (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, hrightZero])]
      rw [show booleanTopologyAndOutput left right = 0 by
        simp [booleanTopologyAndOutput, hrightZero]]
      rw [show 2 = 1 + 1 by omega]
      rw [run_set_instruction (value := 0)
        (by rfl) rfl hzero]
      exact run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hzero
    · rw [if_neg (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, hrightZero])]
      rw [show 2 = 1 + 1 by omega]
      rw [run_set_instruction (value := 1)
        (by rfl) rfl hone]
      rw [show booleanTopologyAndOutput left right = 1 by
        simp [booleanTopologyAndOutput, hleftZero, hrightZero]]
      exact run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hone

/-! ## Closed descriptor-topology program -/

def booleanNodeTopologyOutput
    (inputLength descriptor index : ℕ) : ℕ :=
  let requests :=
    booleanTopologyComparisonRequests inputLength descriptor index
  booleanTopologyAndOutput
    (nativeLtRequestOutput (Nat.unpair requests).1)
    (nativeLtRequestOutput (Nat.unpair requests).2)

@[simp] theorem booleanNodeTopologyOutput_encodeBooleanNode
    {inputLength : ℕ} (node : BooleanNode inputLength) (index : ℕ) :
    booleanNodeTopologyOutput inputLength
        (booleanNodeStructuralOutput (encodeBooleanNode node)) index =
      (decide (node.WellFormedAt index)).toNat := by
  cases node with
  | const value =>
      cases value <;>
        simp [booleanNodeTopologyOutput, booleanTopologyComparisonRequests,
          booleanTopologyAndOutput, topologyTrueRequest,
          BooleanNode.WellFormedAt]
  | input input =>
      simp [booleanNodeTopologyOutput, booleanTopologyComparisonRequests,
        booleanTopologyAndOutput, topologyTrueRequest,
        BooleanNode.WellFormedAt, input.isLt]
  | not child =>
      by_cases hchild : child < index
      · simp [booleanNodeTopologyOutput, booleanTopologyComparisonRequests,
          booleanTopologyAndOutput, topologyTrueRequest,
          BooleanNode.WellFormedAt, hchild]
      · simp [booleanNodeTopologyOutput, booleanTopologyComparisonRequests,
          booleanTopologyAndOutput, topologyTrueRequest,
          BooleanNode.WellFormedAt, hchild]
  | and left right =>
      by_cases hleft : left < index
      · by_cases hright : right < index
        · simp [booleanNodeTopologyOutput, booleanTopologyComparisonRequests,
            booleanTopologyAndOutput, BooleanNode.WellFormedAt,
            hleft, hright]
        · simp [booleanNodeTopologyOutput, booleanTopologyComparisonRequests,
            booleanTopologyAndOutput, BooleanNode.WellFormedAt,
            hleft, hright]
      · simp [booleanNodeTopologyOutput, booleanTopologyComparisonRequests,
          booleanTopologyAndOutput, BooleanNode.WellFormedAt,
          hleft]
  | or left right =>
      by_cases hleft : left < index
      · by_cases hright : right < index
        · simp [booleanNodeTopologyOutput, booleanTopologyComparisonRequests,
            booleanTopologyAndOutput, BooleanNode.WellFormedAt,
            hleft, hright]
        · simp [booleanNodeTopologyOutput, booleanTopologyComparisonRequests,
            booleanTopologyAndOutput, BooleanNode.WellFormedAt,
            hleft, hright]
      · simp [booleanNodeTopologyOutput, booleanTopologyComparisonRequests,
          booleanTopologyAndOutput, BooleanNode.WellFormedAt,
          hleft]

def booleanNodeTopologyProgram : NPOracleProgram :=
  linkPrograms booleanTopologyComparisonPrepareProgram <|
    linkPrograms booleanTopologyComparisonCallProgram
      booleanTopologyAndProgram

@[simp] theorem booleanNodeTopologyProgram_oracleFree :
    OracleFree booleanNodeTopologyProgram := by
  exact oracleFree_linkPrograms
    booleanTopologyComparisonPrepareProgram_oracleFree <|
      oracleFree_linkPrograms
        booleanTopologyComparisonCallProgram_oracleFree
        booleanTopologyAndProgram_oracleFree

def booleanNodeTopologyBits
    (inputLength descriptor index : ℕ) : ℕ :=
  let requests :=
    booleanTopologyComparisonRequests inputLength descriptor index
  let first := (Nat.unpair requests).1
  let second := (Nat.unpair requests).2
  let firstOutput := nativeLtRequestOutput first
  let secondOutput := nativeLtRequestOutput second
  max
    (booleanTopologyComparisonPrepareBits
      inputLength descriptor index) <|
    max
      (booleanTopologyComparisonCallBits inputLength first second)
      (booleanTopologyAndBits firstOutput secondOutput)

def booleanNodeTopologyFuel
    (inputLength descriptor index : ℕ) : ℕ :=
  let requests :=
    booleanTopologyComparisonRequests inputLength descriptor index
  let first := (Nat.unpair requests).1
  let second := (Nat.unpair requests).2
  linkFuel
    (linkPrograms booleanTopologyComparisonCallProgram
      booleanTopologyAndProgram)
    booleanTopologyComparisonPrepareFuel <|
      linkFuel booleanTopologyAndProgram
        (booleanTopologyComparisonCallFuel first second)
        booleanTopologyAndFuel

theorem run_booleanNodeTopologyProgram
    (inputLength descriptor index : ℕ) :
    runNPOracleProgram booleanNodeTopologyProgram
        (booleanNodeTopologyBits inputLength descriptor index)
        (booleanNodeTopologyFuel inputLength descriptor index)
        (initialNPOracleState inputLength
          (Nat.pair descriptor index)) =
      some (booleanNodeTopologyOutput inputLength descriptor index) := by
  let requests :=
    booleanTopologyComparisonRequests inputLength descriptor index
  let first := (Nat.unpair requests).1
  let second := (Nat.unpair requests).2
  let firstOutput := nativeLtRequestOutput first
  let secondOutput := nativeLtRequestOutput second
  let maximumBits :=
    booleanNodeTopologyBits inputLength descriptor index
  have hprepareBits :
      booleanTopologyComparisonPrepareBits
          inputLength descriptor index ≤ maximumBits := by
    simp [maximumBits, booleanNodeTopologyBits]
  have hcallBits :
      booleanTopologyComparisonCallBits inputLength first second ≤
        maximumBits := by
    simp [maximumBits, booleanNodeTopologyBits, first, second,
      requests]
  have handBits :
      booleanTopologyAndBits firstOutput secondOutput ≤ maximumBits := by
    simp [maximumBits, booleanNodeTopologyBits, first, second,
      firstOutput, secondOutput, requests]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply (show natBitLength inputLength ≤
      booleanTopologyComparisonPrepareBits
        inputLength descriptor index from ?_).trans hprepareBits
    exact topologyPrepare_value_bits <|
      (topologyPrepare_inputLength_le
        inputLength descriptor index).trans
        (value_le_pairIter 2 _)
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hprepare :
      runNPOracleProgram booleanTopologyComparisonPrepareProgram
          maximumBits booleanTopologyComparisonPrepareFuel
          (initialNPOracleState inputLength
            (Nat.pair descriptor index)) =
        some requests := by
    exact run_bits_mono
      (run_booleanTopologyComparisonPrepareProgram
        inputLength descriptor index)
      hprepareBits
  have hcall :
      runNPOracleProgram booleanTopologyComparisonCallProgram
          maximumBits
          (booleanTopologyComparisonCallFuel first second)
          (initialNPOracleState inputLength requests) =
        some (Nat.pair firstOutput secondOutput) := by
    have hrun :=
      run_bits_mono
        (run_booleanTopologyComparisonCallProgram
          inputLength first second)
        hcallBits
    simpa [requests, first, second, firstOutput, secondOutput] using hrun
  have hand :
      runNPOracleProgram booleanTopologyAndProgram maximumBits
          booleanTopologyAndFuel
          (initialNPOracleState inputLength
            (Nat.pair firstOutput secondOutput)) =
        some
          (booleanTopologyAndOutput firstOutput secondOutput) := by
    exact run_bits_mono
      (run_booleanTopologyAndProgram
        inputLength firstOutput secondOutput)
      handBits
  have htail :
      runNPOracleProgram
          (linkPrograms booleanTopologyComparisonCallProgram
            booleanTopologyAndProgram)
          maximumBits
          (linkFuel booleanTopologyAndProgram
            (booleanTopologyComparisonCallFuel first second)
            booleanTopologyAndFuel)
          (initialNPOracleState inputLength requests) =
        some
          (booleanTopologyAndOutput firstOutput secondOutput) :=
    run_linkPrograms hpositive hlength hcall hand
  have hrun :=
    run_linkPrograms hpositive hlength hprepare htail
  simpa [booleanNodeTopologyProgram, booleanNodeTopologyFuel,
    booleanNodeTopologyOutput, requests, first, second,
    firstOutput, secondOutput] using hrun

/-! ## Indexed lookup wrapper for the generated range -/

def booleanNodeTopologyLookupRequest
    (descriptors : List ℕ) (index : ℕ) : ℕ :=
  Nat.pair index
    (Nat.pair descriptors.length (encodeBalancedList descriptors))

private def booleanNodeTopologyLookupPrepareOutput
    (descriptors : List ℕ) (index : ℕ) : ℕ :=
  Nat.pair (balancedLookupInput descriptors index) index

private def booleanNodeTopologyLookupPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 5 6 5
  , .pair 4 6 6 6
  , .pair 6 2 0 7
  , .halt 0
  ]

private theorem booleanNodeTopologyLookupPrepareProgram_oracleFree :
    OracleFree booleanNodeTopologyLookupPrepareProgram := by
  rfl

private def booleanNodeTopologyLookupPrepareBits
    (descriptors : List ℕ) (index : ℕ) : ℕ :=
  let tree := encodeBalancedList descriptors
  let indexTree := Nat.pair index tree
  let lookup := balancedLookupInput descriptors index
  max
    (natBitLength (booleanNodeTopologyLookupRequest descriptors index)) <|
    max (natBitLength descriptors.length) <|
      max (natBitLength tree) <|
        max (natBitLength indexTree) <|
          max (natBitLength lookup)
            (natBitLength
              (booleanNodeTopologyLookupPrepareOutput descriptors index))

private theorem run_booleanNodeTopologyLookupPrepareProgram
    (inputLength : ℕ) (descriptors : List ℕ) (index : ℕ) :
    runNPOracleProgram booleanNodeTopologyLookupPrepareProgram
        (booleanNodeTopologyLookupPrepareBits descriptors index) 8
        (initialNPOracleState inputLength
          (booleanNodeTopologyLookupRequest descriptors index)) =
      some
        (booleanNodeTopologyLookupPrepareOutput descriptors index) := by
  let tree := encodeBalancedList descriptors
  let context := Nat.pair descriptors.length tree
  let input := Nat.pair index context
  let indexTree := Nat.pair index tree
  let lookup := balancedLookupInput descriptors index
  let output := Nat.pair lookup index
  let maximumBits :=
    booleanNodeTopologyLookupPrepareBits descriptors index
  have hinput : natBitLength input ≤ maximumBits := by
    change
      natBitLength
          (booleanNodeTopologyLookupRequest descriptors index) ≤
        booleanNodeTopologyLookupPrepareBits descriptors index
    exact Nat.le_max_left _ _
  have hlength : natBitLength descriptors.length ≤ maximumBits := by
    simp [maximumBits, booleanNodeTopologyLookupPrepareBits]
  have htree : natBitLength tree ≤ maximumBits := by
    simp [maximumBits, booleanNodeTopologyLookupPrepareBits, tree]
  have hindexTree : natBitLength indexTree ≤ maximumBits := by
    change
      natBitLength (Nat.pair index (encodeBalancedList descriptors)) ≤
        booleanNodeTopologyLookupPrepareBits descriptors index
    exact
      (Nat.le_max_left _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            Nat.le_max_right _ _
  have hlookup : natBitLength lookup ≤ maximumBits := by
    simp [maximumBits, booleanNodeTopologyLookupPrepareBits, lookup]
  have houtput : natBitLength output ≤ maximumBits := by
    simp [maximumBits, booleanNodeTopologyLookupPrepareBits, output,
      booleanNodeTopologyLookupPrepareOutput, lookup]
  have hindex : natBitLength index ≤ maximumBits := by
    exact
      (natBitLength_mono (Nat.left_le_pair index context)).trans hinput
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := index)
    (by rfl) rfl
    (by
      simp [initialNPOracleState,
        booleanNodeTopologyLookupRequest])
    hindex]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, booleanNodeTopologyLookupRequest,
        context, tree])
    (by
      exact
        (natBitLength_mono (Nat.right_le_pair index context)).trans
          hinput)]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := descriptors.length)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context])
    hlength]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := tree)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context])
    htree]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := indexTree)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, indexTree])
    hindexTree]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := lookup)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, lookup,
        balancedLookupInput, indexTree, tree])
    hlookup]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        booleanNodeTopologyLookupPrepareOutput, lookup])
    houtput

def booleanNodeTopologyLookupProgram : NPOracleProgram :=
  linkPrograms booleanNodeTopologyLookupPrepareProgram <|
    linkPrograms
      (preserveRightProgram canonicalBalancedLookupProgram)
      booleanNodeTopologyProgram

@[simp] theorem booleanNodeTopologyLookupProgram_oracleFree :
    OracleFree booleanNodeTopologyLookupProgram := by
  exact oracleFree_linkPrograms
    booleanNodeTopologyLookupPrepareProgram_oracleFree <|
      oracleFree_linkPrograms
        (preserveRightProgram_oracleFree
          canonicalBalancedLookupProgram
          canonicalBalancedLookupProgram_oracleFree)
        booleanNodeTopologyProgram_oracleFree

def booleanNodeTopologyLookupBits
    (inputLength : ℕ) (descriptors : List ℕ) (index : ℕ) : ℕ :=
  let lookup := balancedLookupInput descriptors index
  let descriptor := descriptors[index]!
  max (booleanNodeTopologyLookupPrepareBits descriptors index) <|
    max
      (preserveRightBits
        (balancedLookupMaximumBits descriptors index)
        lookup index descriptor)
      (booleanNodeTopologyBits inputLength descriptor index)

def booleanNodeTopologyLookupFuel
    (inputLength : ℕ) (descriptors : List ℕ) (index : ℕ) : ℕ :=
  let descriptor := descriptors[index]!
  linkFuel
    (linkPrograms
      (preserveRightProgram canonicalBalancedLookupProgram)
      booleanNodeTopologyProgram)
    8 <|
      linkFuel booleanNodeTopologyProgram
        (preserveRightFuel (balancedLookupFuel descriptors index))
        (booleanNodeTopologyFuel inputLength descriptor index)

theorem run_booleanNodeTopologyLookupProgram
    (inputLength : ℕ) (descriptors : List ℕ) (index : ℕ)
    (hindex : index < descriptors.length) :
    runNPOracleProgram booleanNodeTopologyLookupProgram
        (booleanNodeTopologyLookupBits inputLength descriptors index)
        (booleanNodeTopologyLookupFuel inputLength descriptors index)
        (initialNPOracleState inputLength
          (booleanNodeTopologyLookupRequest descriptors index)) =
      some
        (booleanNodeTopologyOutput
          inputLength descriptors[index] index) := by
  let lookup := balancedLookupInput descriptors index
  let descriptor := descriptors[index]
  let maximumBits :=
    booleanNodeTopologyLookupBits inputLength descriptors index
  have hdescriptorBang : descriptors[index]! = descriptor := by
    exact getElem!_pos descriptors index hindex
  have hprepareBits :
      booleanNodeTopologyLookupPrepareBits descriptors index ≤
        maximumBits := by
    simp [maximumBits, booleanNodeTopologyLookupBits]
  have hlookupBits :
      preserveRightBits
          (balancedLookupMaximumBits descriptors index)
          lookup index descriptor ≤ maximumBits := by
    change
      preserveRightBits
          (balancedLookupMaximumBits descriptors index)
          lookup index descriptor ≤
        max
          (booleanNodeTopologyLookupPrepareBits descriptors index)
          (max
            (preserveRightBits
              (balancedLookupMaximumBits descriptors index)
              lookup index descriptors[index]!)
            (booleanNodeTopologyBits
              inputLength descriptors[index]! index))
    rw [hdescriptorBang]
    exact
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have htopologyBits :
      booleanNodeTopologyBits inputLength descriptor index ≤
        maximumBits := by
    change
      booleanNodeTopologyBits inputLength descriptor index ≤
        max
          (booleanNodeTopologyLookupPrepareBits descriptors index)
          (max
            (preserveRightBits
              (balancedLookupMaximumBits descriptors index)
              (balancedLookupInput descriptors index)
              index descriptors[index]!)
            (booleanNodeTopologyBits
              inputLength descriptors[index]! index))
    rw [hdescriptorBang]
    exact
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlength : natBitLength inputLength ≤ maximumBits := by
    let base :=
      booleanTopologyComparisonPrepareBase
        inputLength descriptor index
    have hprepare :
        natBitLength inputLength ≤
          booleanTopologyComparisonPrepareBits
            inputLength descriptor index :=
      topologyPrepare_value_bits <|
        (topologyPrepare_inputLength_le
          inputLength descriptor index).trans
          (value_le_pairIter 2 base)
    have htopology :
        natBitLength inputLength ≤
          booleanNodeTopologyBits inputLength descriptor index :=
      hprepare.trans (Nat.le_max_left _ _)
    exact htopology.trans htopologyBits
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hprepare :
      runNPOracleProgram booleanNodeTopologyLookupPrepareProgram
          maximumBits 8
          (initialNPOracleState inputLength
            (booleanNodeTopologyLookupRequest descriptors index)) =
        some (Nat.pair lookup index) := by
    exact run_bits_mono
      (run_booleanNodeTopologyLookupPrepareProgram
        inputLength descriptors index)
      hprepareBits
  have hlookup :
      runNPOracleProgram
          (preserveRightProgram canonicalBalancedLookupProgram)
          maximumBits
          (preserveRightFuel (balancedLookupFuel descriptors index))
          (initialNPOracleState inputLength
            (Nat.pair lookup index)) =
        some (Nat.pair descriptor index) := by
    have hrun :=
      run_preserveRightProgram canonicalBalancedLookupProgram
        inputLength
        (balancedLookupMaximumBits descriptors index)
        (balancedLookupFuel descriptors index)
        lookup index descriptor
        (run_canonicalBalancedLookupProgram
          descriptors index inputLength hindex)
    exact run_bits_mono hrun hlookupBits
  have htopology :
      runNPOracleProgram booleanNodeTopologyProgram
          maximumBits
          (booleanNodeTopologyFuel inputLength descriptor index)
          (initialNPOracleState inputLength
            (Nat.pair descriptor index)) =
        some
          (booleanNodeTopologyOutput inputLength descriptor index) :=
    run_bits_mono
      (run_booleanNodeTopologyProgram
        inputLength descriptor index)
      htopologyBits
  have htail :
      runNPOracleProgram
          (linkPrograms
            (preserveRightProgram canonicalBalancedLookupProgram)
            booleanNodeTopologyProgram)
          maximumBits
          (linkFuel booleanNodeTopologyProgram
            (preserveRightFuel
              (balancedLookupFuel descriptors index))
            (booleanNodeTopologyFuel inputLength descriptor index))
          (initialNPOracleState inputLength
            (Nat.pair lookup index)) =
        some
          (booleanNodeTopologyOutput inputLength descriptor index) :=
    run_linkPrograms hpositive hlength hlookup htopology
  have hrun :=
    run_linkPrograms hpositive hlength hprepare htail
  simpa [booleanNodeTopologyLookupProgram,
    booleanNodeTopologyLookupFuel, descriptor, hdescriptorBang]
    using hrun

private theorem run_booleanNodeTopologyLookupProgram_bang
    (inputLength : ℕ) (descriptors : List ℕ) (index : ℕ)
    (hindex : index < descriptors.length) :
    runNPOracleProgram booleanNodeTopologyLookupProgram
        (booleanNodeTopologyLookupBits inputLength descriptors index)
        (booleanNodeTopologyLookupFuel inputLength descriptors index)
        (initialNPOracleState inputLength
          (booleanNodeTopologyLookupRequest descriptors index)) =
      some
        (booleanNodeTopologyOutput
          inputLength descriptors[index]! index) := by
  rw [getElem!_pos descriptors index hindex]
  exact run_booleanNodeTopologyLookupProgram
    inputLength descriptors index hindex

/-! ## All-node topology aggregation -/

def booleanNodeTopologyRangeContext (descriptors : List ℕ) : ℕ :=
  Nat.pair descriptors.length (encodeBalancedList descriptors)

def booleanNodeTopologyRangeIndex (request : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair request).2).1

def booleanNodeTopologyRangeValue
    (inputLength : ℕ) (descriptors : List ℕ) (request : ℕ) : Bool :=
  decide
    (booleanNodeTopologyOutput inputLength
      descriptors[booleanNodeTopologyRangeIndex request]!
      (booleanNodeTopologyRangeIndex request) ≠ 0)

def encodedBooleanNodeDescriptors {inputLength : ℕ}
    (nodes : List (BooleanNode inputLength)) : List ℕ :=
  nodes.map fun node =>
    booleanNodeStructuralOutput (encodeBooleanNode node)

@[simp] theorem encodedBooleanNodeDescriptors_length
    {inputLength : ℕ} (nodes : List (BooleanNode inputLength)) :
    (encodedBooleanNodeDescriptors nodes).length = nodes.length := by
  simp [encodedBooleanNodeDescriptors]

theorem booleanNodeTopologyRangeValue_encodeBooleanNode
    {inputLength : ℕ} (nodes : List (BooleanNode inputLength))
    (index : ℕ) (hindex : index < nodes.length) :
    booleanNodeTopologyRangeValue inputLength
        (encodedBooleanNodeDescriptors nodes)
        (balancedRangeRequestAtom inputLength index
          (booleanNodeTopologyRangeContext
            (encodedBooleanNodeDescriptors nodes))) =
      decide ((nodes[index]'hindex).WellFormedAt index) := by
  have hdescriptor :
      (encodedBooleanNodeDescriptors nodes)[index]! =
        booleanNodeStructuralOutput
          (encodeBooleanNode (nodes[index]'hindex)) := by
    rw [getElem!_pos _ _ (by simpa using hindex)]
    simp [encodedBooleanNodeDescriptors]
  unfold booleanNodeTopologyRangeValue
  simp only [booleanNodeTopologyRangeIndex, balancedRangeRequestAtom,
    Nat.unpair_pair]
  rw [hdescriptor]
  rw [booleanNodeTopologyOutput_encodeBooleanNode]
  by_cases hwell : (nodes[index]'hindex).WellFormedAt index <;>
    simp [hwell]

private theorem booleanTopologyAndOutput_boolCode
    (left right : ℕ) :
    boolCode
        (decide (booleanTopologyAndOutput left right ≠ 0)) =
      booleanTopologyAndOutput left right := by
  by_cases hleft : left = 0
  · simp [booleanTopologyAndOutput, hleft, boolCode]
  · by_cases hright : right = 0
    · simp [booleanTopologyAndOutput, hright, boolCode]
    · simp [booleanTopologyAndOutput, hleft, hright, boolCode]

private theorem booleanNodeTopologyOutput_boolCode
    (inputLength descriptor index : ℕ) :
    boolCode
        (decide
          (booleanNodeTopologyOutput
            inputLength descriptor index ≠ 0)) =
      booleanNodeTopologyOutput inputLength descriptor index := by
  unfold booleanNodeTopologyOutput
  exact booleanTopologyAndOutput_boolCode _ _

private def booleanNodeTopologyRangeCalleeBits
    (inputLength : ℕ) (descriptors : List ℕ) : ℕ :=
  ((fixedBooleanRangeRequests inputLength descriptors.length
      (booleanNodeTopologyRangeContext descriptors)).map fun request =>
    booleanNodeTopologyLookupBits inputLength descriptors
      (booleanNodeTopologyRangeIndex request)).foldr max 1

private def booleanNodeTopologyRangeCalleeFuel
    (inputLength : ℕ) (descriptors : List ℕ) (request : ℕ) : ℕ :=
  booleanNodeTopologyLookupFuel inputLength descriptors
    (booleanNodeTopologyRangeIndex request)

def booleanNodeTopologyRangeProgram : NPOracleProgram :=
  fixedBooleanRangeAggregationProgram
    booleanNodeTopologyLookupProgram

@[simp] theorem booleanNodeTopologyRangeProgram_oracleFree :
    OracleFree booleanNodeTopologyRangeProgram :=
  fixedBooleanRangeAggregationProgram_oracleFree
    booleanNodeTopologyLookupProgram
    booleanNodeTopologyLookupProgram_oracleFree

def booleanNodeTopologyRangeBits
    (inputLength : ℕ) (descriptors : List ℕ) : ℕ :=
  fixedBooleanRangeAggregationBits
    (booleanNodeTopologyRangeCalleeBits inputLength descriptors)
    inputLength descriptors.length
    (booleanNodeTopologyRangeContext descriptors)
    (booleanNodeTopologyRangeValue inputLength descriptors)

def booleanNodeTopologyRangeFuel
    (inputLength : ℕ) (descriptors : List ℕ) : ℕ :=
  fixedBooleanRangeAggregationFuel
    booleanNodeTopologyLookupProgram
    (booleanNodeTopologyRangeCalleeFuel inputLength descriptors)
    inputLength descriptors.length
    (booleanNodeTopologyRangeContext descriptors)
    (booleanNodeTopologyRangeValue inputLength descriptors)

def booleanNodeTopologyRangeOutput
    (inputLength : ℕ) (descriptors : List ℕ) : ℕ :=
  fixedBooleanRangeAggregationOutput
    inputLength descriptors.length
    (booleanNodeTopologyRangeContext descriptors)
    (booleanNodeTopologyRangeValue inputLength descriptors)

private theorem fixedBooleanRangeValues_encodeNodes
    {inputLength : ℕ} (nodes : List (BooleanNode inputLength))
    (hwellFormed :
      ∀ index : Fin nodes.length,
        (nodes.get index).WellFormedAt index.val) :
    fixedBooleanRangeValues inputLength nodes.length
        (booleanNodeTopologyRangeContext
          (encodedBooleanNodeDescriptors nodes))
        (booleanNodeTopologyRangeValue inputLength
          (encodedBooleanNodeDescriptors nodes)) =
      (List.range nodes.length).map fun _ => true := by
  unfold fixedBooleanRangeValues fixedBooleanRangeRequests
  rw [balancedRangeRequestAtoms_eq_map_range, List.map_map]
  simp only [Nat.zero_add]
  apply List.map_congr_left
  intro index hindex
  simp only [Function.comp_apply]
  rw [booleanNodeTopologyRangeValue_encodeBooleanNode
    nodes index (List.mem_range.mp hindex)]
  rw [decide_eq_true_eq]
  exact hwellFormed
    ⟨index, List.mem_range.mp hindex⟩

private theorem nonzeroSupportCount_map_true
    {α : Type} (values : List α) :
    nonzeroSupportCount (values.map fun _ => true) = values.length := by
  induction values with
  | nil => rfl
  | cons _ values ih =>
      simp only [List.map_cons, nonzeroSupportCount, if_true,
        List.length_cons, ih]
      omega

theorem booleanNodeTopologyRangeOutput_encodeNodes
    {inputLength : ℕ} (nodes : List (BooleanNode inputLength))
    (hwellFormed :
      ∀ index : Fin nodes.length,
        (nodes.get index).WellFormedAt index.val) :
    booleanNodeTopologyRangeOutput inputLength
        (encodedBooleanNodeDescriptors nodes) =
      Nat.pair nodes.length
        (booleanNodeTopologyRangeContext
          (encodedBooleanNodeDescriptors nodes)) := by
  unfold booleanNodeTopologyRangeOutput fixedBooleanRangeAggregationOutput
  rw [encodedBooleanNodeDescriptors_length]
  rw [fixedBooleanRangeValues_encodeNodes nodes hwellFormed,
    nonzeroSupportCount_map_true]
  simp

@[simp] theorem booleanNodeTopologyRangeOutput_encodeBooleanCircuit
    {inputLength : ℕ} (circuit : BooleanCircuit inputLength) :
    booleanNodeTopologyRangeOutput inputLength
        (encodedBooleanNodeDescriptors circuit.nodes) =
      Nat.pair circuit.nodes.length
        (booleanNodeTopologyRangeContext
          (encodedBooleanNodeDescriptors circuit.nodes)) :=
  booleanNodeTopologyRangeOutput_encodeNodes
    circuit.nodes circuit.wellFormed

private theorem topologyRange_value_le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 1 := by
  induction values with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (ih hmem).trans (Nat.le_max_right _ _)

private theorem fixedBooleanRangeRequests_eq_indexMap
    (inputLength : ℕ) (descriptors : List ℕ) :
    fixedBooleanRangeRequests inputLength descriptors.length
        (booleanNodeTopologyRangeContext descriptors) =
      (List.range descriptors.length).map fun index =>
        balancedRangeRequestAtom inputLength index
          (booleanNodeTopologyRangeContext descriptors) := by
  unfold fixedBooleanRangeRequests
  rw [balancedRangeRequestAtoms_eq_map_range]
  simp

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- Unfolding the fixed range ABI and its linked callee budget exceeds the
-- default elaboration allowance; execution and proof recursion remain bounded.
private theorem run_booleanNodeTopologyRangeCallee
    (inputLength : ℕ) (descriptors : List ℕ) (request : ℕ)
    (hrequest :
      request ∈
        fixedBooleanRangeRequests inputLength descriptors.length
          (booleanNodeTopologyRangeContext descriptors)) :
    runNPOracleProgram booleanNodeTopologyLookupProgram
        (booleanNodeTopologyRangeCalleeBits inputLength descriptors)
        (booleanNodeTopologyRangeCalleeFuel
          inputLength descriptors request)
        (initialNPOracleState
          (Nat.unpair request).1 (Nat.unpair request).2) =
      some
        (boolCode
          (booleanNodeTopologyRangeValue
            inputLength descriptors request)) := by
  have hrequestMap := hrequest
  rw [fixedBooleanRangeRequests_eq_indexMap
    inputLength descriptors] at hrequestMap
  rcases List.mem_map.mp hrequestMap with
    ⟨index, hindexRange, rfl⟩
  have hindex : index < descriptors.length :=
    List.mem_range.mp hindexRange
  have hrequestMember :
      balancedRangeRequestAtom inputLength index
          (booleanNodeTopologyRangeContext descriptors) ∈
        fixedBooleanRangeRequests inputLength descriptors.length
          (booleanNodeTopologyRangeContext descriptors) :=
    hrequest
  have hcalleeBits :
      booleanNodeTopologyLookupBits inputLength descriptors index ≤
        booleanNodeTopologyRangeCalleeBits
          inputLength descriptors := by
    apply topologyRange_value_le_foldr_max_of_mem
    exact List.mem_map.mpr ⟨
      balancedRangeRequestAtom inputLength index
        (booleanNodeTopologyRangeContext descriptors),
      hrequestMember, by
        simp [booleanNodeTopologyRangeIndex,
          balancedRangeRequestAtom]⟩
  have hrun :=
    run_bits_mono
      (run_booleanNodeTopologyLookupProgram_bang
        inputLength descriptors index hindex)
      hcalleeBits
  have hrequestLength :
      (Nat.unpair
        (balancedRangeRequestAtom inputLength index
          (booleanNodeTopologyRangeContext descriptors))).1 =
        inputLength := by
    simp [balancedRangeRequestAtom]
  have hrequestCode :
      (Nat.unpair
        (balancedRangeRequestAtom inputLength index
          (booleanNodeTopologyRangeContext descriptors))).2 =
        booleanNodeTopologyLookupRequest descriptors index := by
    simp [balancedRangeRequestAtom, booleanNodeTopologyRangeContext,
      booleanNodeTopologyLookupRequest]
  have hrequestIndex :
      booleanNodeTopologyRangeIndex
          (balancedRangeRequestAtom inputLength index
            (booleanNodeTopologyRangeContext descriptors)) =
        index := by
    simp [booleanNodeTopologyRangeIndex, balancedRangeRequestAtom]
  have hfuel :
      booleanNodeTopologyRangeCalleeFuel inputLength descriptors
          (balancedRangeRequestAtom inputLength index
            (booleanNodeTopologyRangeContext descriptors)) =
        booleanNodeTopologyLookupFuel inputLength descriptors index := by
    simp [booleanNodeTopologyRangeCalleeFuel, hrequestIndex]
  have hvalue :
      boolCode
          (booleanNodeTopologyRangeValue inputLength descriptors
            (balancedRangeRequestAtom inputLength index
              (booleanNodeTopologyRangeContext descriptors))) =
        booleanNodeTopologyOutput inputLength descriptors[index]! index := by
    rw [booleanNodeTopologyRangeValue, hrequestIndex]
    exact booleanNodeTopologyOutput_boolCode
      inputLength descriptors[index]! index
  rw [hrequestLength, hrequestCode, hfuel, hvalue]
  exact hrun

theorem run_booleanNodeTopologyRangeProgram
    (inputLength : ℕ) (descriptors : List ℕ) :
    runNPOracleProgram booleanNodeTopologyRangeProgram
        (booleanNodeTopologyRangeBits inputLength descriptors)
        (booleanNodeTopologyRangeFuel inputLength descriptors)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput descriptors.length
            (booleanNodeTopologyRangeContext descriptors))) =
      some
        (booleanNodeTopologyRangeOutput
          inputLength descriptors) := by
  exact run_fixedBooleanRangeAggregationProgram
    booleanNodeTopologyLookupProgram
    (booleanNodeTopologyRangeCalleeBits inputLength descriptors)
    inputLength descriptors.length
    (booleanNodeTopologyRangeContext descriptors)
    (booleanNodeTopologyRangeCalleeFuel inputLength descriptors)
    (booleanNodeTopologyRangeValue inputLength descriptors)
    (run_booleanNodeTopologyRangeCallee inputLength descriptors)

end NearCubicWires.CanonicalBooleanNodeTopologyProgram
