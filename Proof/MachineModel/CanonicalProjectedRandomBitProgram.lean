import Proof.MachineModel.CanonicalBitSerialModProgram
import Proof.Circuits.CanonicalPairedCall
import Proof.MachineModel.PreserveRightProgram

/-!
# Fixed projected-random-bit evaluation

The public projection table stores an encoded `ProjectedRandomBit`, while the
structural compiler must evaluate that code at a run-time randomness word.
This module implements the total public decoder with one fixed program.  Both
remainders use the bit-serial implementation, so arbitrary imported codes
cannot induce value-linear controller traces.
-/

namespace NearCubicWires.CanonicalProjectedRandomBitProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialModProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

def projectedRandomBitInput
    (width projectionCode randomnessCode : ℕ) : ℕ :=
  Nat.pair width (Nat.pair projectionCode randomnessCode)

def projectedRandomBitOutput
    (width projectionCode randomnessCode : ℕ) : ℕ :=
  ((decodeProjectedRandomBit width projectionCode).eval fun bit =>
    randomnessCode.testBit bit.val).toNat

private def projectedRandomBitTag (projectionCode : ℕ) : ℕ :=
  (Nat.unpair projectionCode).1

private def projectedRandomBitPayload (projectionCode : ℕ) : ℕ :=
  (Nat.unpair projectionCode).2

/- The canonical remainder program returns zero on divisor zero.  The decoded
projection ignores its index in that case, so normalizing here gives one total
ABI without adding a second arithmetic implementation. -/
private def projectedRandomBitIndex
    (width projectionCode : ℕ) : ℕ :=
  if width = 0 then 0
  else projectedRandomBitPayload projectionCode % width

private def projectedRandomBitModRequests
    (width projectionCode : ℕ) : ℕ :=
  Nat.pair
    (bitSerialModInput
      (projectedRandomBitPayload projectionCode) width)
    (bitSerialModInput
      (projectedRandomBitTag projectionCode) 3)

private def projectedRandomBitContext
    (width projectionCode randomnessCode : ℕ) : ℕ :=
  Nat.pair width <|
    Nat.pair randomnessCode
      (projectedRandomBitPayload projectionCode)

private def projectedRandomBitPreparedInput
    (width projectionCode randomnessCode : ℕ) : ℕ :=
  Nat.pair
    (projectedRandomBitModRequests width projectionCode)
    (projectedRandomBitContext width projectionCode randomnessCode)

/-! ## Public request adapter -/

private def projectedRandomBitAdapterProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 4 6 5
  , .unpairRight 4 7 6
  , .set 8 3 7
  , .pair 7 2 9 8
  , .pair 6 8 10 9
  , .pair 9 10 11 10
  , .pair 5 7 12 11
  , .pair 2 12 13 12
  , .pair 11 13 0 13
  , .halt 0
  ]

private def projectedRandomBitAdapterBound
    (width projectionCode randomnessCode : ℕ) : ℕ :=
  max
    (projectedRandomBitInput width projectionCode randomnessCode) <|
    max
      (projectedRandomBitPreparedInput
        width projectionCode randomnessCode)
      3

private def projectedRandomBitAdapterBits
    (width projectionCode randomnessCode : ℕ) : ℕ :=
  natBitLength <|
    projectedRandomBitAdapterBound
      width projectionCode randomnessCode

@[simp] private theorem projectedRandomBitAdapterProgram_oracleFree :
    OracleFree projectedRandomBitAdapterProgram := by
  rfl

private theorem run_projectedRandomBitAdapterProgram
    (inputLength width projectionCode randomnessCode : ℕ) :
    runNPOracleProgram projectedRandomBitAdapterProgram
        (projectedRandomBitAdapterBits
          width projectionCode randomnessCode)
        14
        (initialNPOracleState inputLength
          (projectedRandomBitInput
            width projectionCode randomnessCode)) =
      some
        (projectedRandomBitPreparedInput
          width projectionCode randomnessCode) := by
  let input :=
    projectedRandomBitInput width projectionCode randomnessCode
  let tag := projectedRandomBitTag projectionCode
  let payload := projectedRandomBitPayload projectionCode
  let leftRequest := bitSerialModInput payload width
  let rightRequest := bitSerialModInput tag 3
  let requests := Nat.pair leftRequest rightRequest
  let retained := Nat.pair randomnessCode payload
  let context := Nat.pair width retained
  let prepared := Nat.pair requests context
  let bound :=
    projectedRandomBitAdapterBound
      width projectionCode randomnessCode
  let bits :=
    projectedRandomBitAdapterBits
      width projectionCode randomnessCode
  have hinput : input ≤ bound := by
    exact Nat.le_max_left _ _
  have hprepared : prepared ≤ bound := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hthree : 3 ≤ bound := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hbitsOf : ∀ {value : ℕ}, value ≤ bound →
      natBitLength value ≤ bits := by
    intro value hvalue
    exact natBitLength_mono hvalue
  have hwidth : width ≤ bound := by
    exact (Nat.left_le_pair width
      (Nat.pair projectionCode randomnessCode)).trans hinput
  have hprojection : projectionCode ≤ bound := by
    exact
      (Nat.left_le_pair projectionCode randomnessCode).trans <|
        (Nat.right_le_pair width
          (Nat.pair projectionCode randomnessCode)).trans hinput
  have hrandomness : randomnessCode ≤ bound := by
    exact
      (Nat.right_le_pair projectionCode randomnessCode).trans <|
        (Nat.right_le_pair width
          (Nat.pair projectionCode randomnessCode)).trans hinput
  have htag : tag ≤ bound := by
    exact (Nat.unpair_left_le projectionCode).trans hprojection
  have hpayload : payload ≤ bound := by
    exact (Nat.unpair_right_le projectionCode).trans hprojection
  have hleftRequest : leftRequest ≤ bound := by
    exact (Nat.left_le_pair leftRequest rightRequest).trans <|
      (Nat.left_le_pair requests context).trans hprepared
  have hrightRequest : rightRequest ≤ bound := by
    exact (Nat.right_le_pair leftRequest rightRequest).trans <|
      (Nat.left_le_pair requests context).trans hprepared
  have hrequests : requests ≤ bound :=
    (Nat.left_le_pair requests context).trans hprepared
  have hretained : retained ≤ bound := by
    exact (Nat.right_le_pair width retained).trans <|
      (Nat.right_le_pair requests context).trans hprepared
  have hcontext : context ≤ bound :=
    (Nat.right_le_pair requests context).trans hprepared
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width)
    (by rfl) rfl
    (by simp [initialNPOracleState, projectedRandomBitInput])
    (hbitsOf hwidth)]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair projectionCode randomnessCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, projectedRandomBitInput])
    (hbitsOf <|
      (Nat.right_le_pair width
        (Nat.pair projectionCode randomnessCode)).trans hinput)]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairLeft_instruction (value := projectionCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    (hbitsOf hprojection)]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction (value := randomnessCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    (hbitsOf hrandomness)]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tag)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, tag, projectedRandomBitTag])
    (hbitsOf htag)]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := payload)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, payload, projectedRandomBitPayload])
    (hbitsOf hpayload)]
  rw [show 8 = 7 + 1 by omega]
  rw [run_set_instruction (value := 3)
    (by rfl) rfl (hbitsOf hthree)]
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction (value := leftRequest)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, leftRequest, bitSerialModInput])
    (hbitsOf hleftRequest)]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := rightRequest)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, rightRequest, bitSerialModInput])
    (hbitsOf hrightRequest)]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := requests)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, requests])
    (hbitsOf hrequests)]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := retained)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, retained])
    (hbitsOf hretained)]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := context)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, context])
    (hbitsOf hcontext)]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := prepared)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, prepared])
    (hbitsOf hprepared)]
  have hpreparedEq :
      prepared =
        projectedRandomBitPreparedInput
          width projectionCode randomnessCode := by
    rfl
  rw [← hpreparedEq]
  exact run_halt_instruction (fuel := 0)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (hbitsOf hprepared)

/-! ## Boolean evaluator after the two canonical remainders -/

private def projectedRandomBitEvaluatedInput
    (width projectionCode randomnessCode : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair
      (projectedRandomBitIndex width projectionCode)
      (projectedRandomBitTag projectionCode % 3))
    (projectedRandomBitContext width projectionCode randomnessCode)

private def projectedRandomBitEvaluatorProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairLeft 3 6 5
  , .unpairRight 3 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .branchZero 6 17 9
  , .testBit 8 4 10 10
  , .branchZero 5 14 11
  , .decrement 5 12
  , .branchZero 5 16 13
  , .copy 5 5 17
  , .copy 10 0 15
  , .halt 0
  , .branchZero 10 20 22
  , .set 11 0 18
  , .testBit 9 11 0 19
  , .halt 0
  , .set 0 1 21
  , .halt 0
  , .set 0 0 23
  , .halt 0
  ]

private def projectedRandomBitEvaluatorFuel
    (width projectionCode _randomnessCode : ℕ) : ℕ :=
  if width = 0 then 12
  else if projectedRandomBitTag projectionCode % 3 = 0 then 13
  else if projectedRandomBitTag projectionCode % 3 = 1 then 16
  else 17

private def projectedRandomBitEvaluatorBits
    (width projectionCode randomnessCode : ℕ) : ℕ :=
  natBitLength <|
    max
      (projectedRandomBitEvaluatedInput
        width projectionCode randomnessCode)
      1

@[simp] private theorem projectedRandomBitEvaluatorProgram_oracleFree :
    OracleFree projectedRandomBitEvaluatorProgram := by
  rfl

private def projectedRandomBitEvaluatorParsedState
    (inputLength width projectionCode randomnessCode : ℕ) :
    NPOracleState :=
  let tag := projectedRandomBitTag projectionCode
  let payload := projectedRandomBitPayload projectionCode
  let index := projectedRandomBitIndex width projectionCode
  let kind := tag % 3
  let state0 :=
    initialNPOracleState inputLength
      (projectedRandomBitEvaluatedInput
        width projectionCode randomnessCode)
  let state1 := (state0.write 2 (Nat.pair index kind)).jump 1
  let state2 :=
    (state1.write 3
      (projectedRandomBitContext
        width projectionCode randomnessCode)).jump 2
  let state3 := (state2.write 4 index).jump 3
  let state4 := (state3.write 5 kind).jump 4
  let state5 := (state4.write 6 width).jump 5
  let state6 :=
    (state5.write 7 (Nat.pair randomnessCode payload)).jump 6
  let state7 := (state6.write 8 randomnessCode).jump 7
  (state7.write 9 payload).jump 8

private theorem run_projectedRandomBitEvaluator_parse
    (inputLength width projectionCode randomnessCode maximumBits extra : ℕ)
    (houtputs :
      natBitLength
          (Nat.pair
            (projectedRandomBitIndex width projectionCode)
            (projectedRandomBitTag projectionCode % 3)) ≤
        maximumBits)
    (hcontext :
      natBitLength
          (projectedRandomBitContext
            width projectionCode randomnessCode) ≤
        maximumBits)
    (hindex :
      natBitLength
          (projectedRandomBitIndex width projectionCode) ≤
        maximumBits)
    (hkind :
      natBitLength
          (projectedRandomBitTag projectionCode % 3) ≤
        maximumBits)
    (hwidth : natBitLength width ≤ maximumBits)
    (hretained :
      natBitLength
          (Nat.pair randomnessCode
            (projectedRandomBitPayload projectionCode)) ≤
        maximumBits)
    (hrandomness : natBitLength randomnessCode ≤ maximumBits)
    (hpayload :
      natBitLength (projectedRandomBitPayload projectionCode) ≤
        maximumBits) :
    runNPOracleProgram projectedRandomBitEvaluatorProgram maximumBits
        (extra + 8)
        (initialNPOracleState inputLength
          (projectedRandomBitEvaluatedInput
            width projectionCode randomnessCode)) =
      runNPOracleProgram projectedRandomBitEvaluatorProgram maximumBits
        extra
        (projectedRandomBitEvaluatorParsedState
          inputLength width projectionCode randomnessCode) := by
  let tag := projectedRandomBitTag projectionCode
  let payload := projectedRandomBitPayload projectionCode
  let index := projectedRandomBitIndex width projectionCode
  let kind := tag % 3
  let outputs := Nat.pair index kind
  let context :=
    projectedRandomBitContext width projectionCode randomnessCode
  let retained := Nat.pair randomnessCode payload
  rw [show extra + 8 = (extra + 7) + 1 by omega]
  rw [run_unpairLeft_instruction (value := outputs)
    (by rfl) rfl
    (by simp [initialNPOracleState,
      projectedRandomBitEvaluatedInput, outputs, index, kind,
      tag])
    (by simpa [outputs, index, kind, tag, payload] using houtputs)]
  rw [show extra + 7 = (extra + 6) + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, projectedRandomBitEvaluatedInput,
      context])
    (by simpa [context] using hcontext)]
  rw [show extra + 6 = (extra + 5) + 1 by omega]
  rw [run_unpairLeft_instruction (value := index)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, outputs])
    (by simpa [index, payload] using hindex)]
  rw [show extra + 5 = (extra + 4) + 1 by omega]
  rw [run_unpairRight_instruction (value := kind)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, outputs])
    (by simpa [kind, tag] using hkind)]
  rw [show extra + 4 = (extra + 3) + 1 by omega]
  rw [run_unpairLeft_instruction (value := width)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, context,
      projectedRandomBitContext])
    hwidth]
  rw [show extra + 3 = (extra + 2) + 1 by omega]
  rw [run_unpairRight_instruction (value := retained)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, context, retained,
      projectedRandomBitContext, payload])
    (by simpa [retained, payload] using hretained)]
  rw [show extra + 2 = (extra + 1) + 1 by omega]
  rw [run_unpairLeft_instruction (value := randomnessCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, retained])
    hrandomness]
  rw [show extra + 1 = extra + 1 by rfl]
  rw [run_unpairRight_instruction (value := payload)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, retained])
    (by exact hpayload)]
  rfl

private theorem run_projectedRandomBitEvaluatorProgram
    (inputLength width projectionCode randomnessCode : ℕ) :
    runNPOracleProgram projectedRandomBitEvaluatorProgram
        (projectedRandomBitEvaluatorBits
          width projectionCode randomnessCode)
        (projectedRandomBitEvaluatorFuel
          width projectionCode randomnessCode)
        (initialNPOracleState inputLength
          (projectedRandomBitEvaluatedInput
            width projectionCode randomnessCode)) =
      some
        (projectedRandomBitOutput
          width projectionCode randomnessCode) := by
  let tag := projectedRandomBitTag projectionCode
  let payload := projectedRandomBitPayload projectionCode
  let index := projectedRandomBitIndex width projectionCode
  let kind := tag % 3
  let bit := randomnessCode.testBit index
  let retained := Nat.pair randomnessCode payload
  let context := Nat.pair width retained
  let outputs := Nat.pair index kind
  let evaluated := Nat.pair outputs context
  let bound := max evaluated 1
  let bits :=
    projectedRandomBitEvaluatorBits
      width projectionCode randomnessCode
  have hevaluated : evaluated ≤ bound := Nat.le_max_left _ _
  have hone : 1 ≤ bound := Nat.le_max_right _ _
  have hbitsOf : ∀ {value : ℕ}, value ≤ bound →
      natBitLength value ≤ bits := by
    intro value hvalue
    exact natBitLength_mono hvalue
  have houtputs : outputs ≤ bound :=
    (Nat.left_le_pair outputs context).trans hevaluated
  have hcontext : context ≤ bound :=
    (Nat.right_le_pair outputs context).trans hevaluated
  have hindex : index ≤ bound :=
    (Nat.left_le_pair index kind).trans houtputs
  have hkind : kind ≤ bound :=
    (Nat.right_le_pair index kind).trans houtputs
  have hwidth : width ≤ bound :=
    (Nat.left_le_pair width retained).trans hcontext
  have hretained : retained ≤ bound :=
    (Nat.right_le_pair width retained).trans hcontext
  have hrandomness : randomnessCode ≤ bound :=
    (Nat.left_le_pair randomnessCode payload).trans hretained
  have hpayload : payload ≤ bound :=
    (Nat.right_le_pair randomnessCode payload).trans hretained
  have hbit : bit.toNat ≤ bound :=
    (Bool.toNat_le bit).trans hone
  have hpayloadBit : (payload.testBit 0).toNat ≤ bound :=
    (Bool.toNat_le (payload.testBit 0)).trans hone
  have hzero : 0 ≤ bound := Nat.zero_le _
  have hkindPred : kind.pred ≤ bound :=
    (Nat.pred_le kind).trans hkind
  have hevaluatedEq :
      evaluated =
        projectedRandomBitEvaluatedInput
          width projectionCode randomnessCode := by
    rfl
  have hbitsEq :
      bits =
        natBitLength bound := by
    rfl
  have hparse (extra : ℕ) :
      runNPOracleProgram projectedRandomBitEvaluatorProgram bits
          (extra + 8)
          (initialNPOracleState inputLength evaluated) =
        runNPOracleProgram projectedRandomBitEvaluatorProgram bits
          extra
          (projectedRandomBitEvaluatorParsedState
            inputLength width projectionCode randomnessCode) := by
    rw [hevaluatedEq]
    exact run_projectedRandomBitEvaluator_parse
      inputLength width projectionCode randomnessCode bits extra
      (hbitsOf houtputs)
      (hbitsOf hcontext)
      (hbitsOf hindex)
      (hbitsOf hkind)
      (hbitsOf hwidth)
      (hbitsOf hretained)
      (hbitsOf hrandomness)
      (hbitsOf hpayload)
  by_cases hwidthZero : width = 0
  · rw [show
      projectedRandomBitEvaluatorFuel
          width projectionCode randomnessCode =
        4 + 8 by
      simp [projectedRandomBitEvaluatorFuel, hwidthZero]]
    rw [show
      initialNPOracleState inputLength
          (projectedRandomBitEvaluatedInput
            width projectionCode randomnessCode) =
        initialNPOracleState inputLength evaluated by
      rw [hevaluatedEq]]
    rw [hparse 4]
    rw [show 4 = 3 + 1 by omega]
    rw [run_branchZero_instruction
      (pc := 8) (register := 6)
      (zeroTarget := 17) (nonzeroTarget := 9)
      (by rfl)
      (by simp [projectedRandomBitEvaluatorParsedState,
        NPOracleState.write, NPOracleState.jump, hwidthZero])]
    rw [show 3 = 2 + 1 by omega]
    rw [run_set_instruction
      (pc := 17) (register := 11) (value := 0) (next := 18)
      (by rfl)
      (by simp [projectedRandomBitEvaluatorParsedState,
        NPOracleState.write, NPOracleState.jump, hwidthZero])
      (hbitsOf hzero)]
    rw [show 2 = 1 + 1 by omega]
    rw [run_testBit_instruction
      (pc := 18) (source := 9) (index := 11)
      (destination := 0) (next := 19)
      (value := (payload.testBit 0).toNat)
      (by rfl)
      (by simp [projectedRandomBitEvaluatorParsedState,
        NPOracleState.write, NPOracleState.jump])
      (by simp [projectedRandomBitEvaluatorParsedState,
        NPOracleState.write, NPOracleState.jump, payload,
        projectedRandomBitPayload])
      (hbitsOf hpayloadBit)]
    have houtput :
        projectedRandomBitOutput
            width projectionCode randomnessCode =
          (payload.testBit 0).toNat := by
      simp [projectedRandomBitOutput, decodeProjectedRandomBit,
        SourceInterfaces.ProjectedRandomBit.eval, hwidthZero,
        payload, projectedRandomBitPayload]
    rw [houtput]
    exact run_halt_instruction
      (program := projectedRandomBitEvaluatorProgram)
      (maximumBits := bits)
      (fuel := 0)
      (pc := 19)
      (outputRegister := 0)
      (value := (payload.testBit 0).toNat)
      (by rfl)
      (by simp [projectedRandomBitEvaluatorParsedState,
        NPOracleState.write, NPOracleState.jump])
      (by rfl)
      (hbitsOf hpayloadBit)
  · have hwidthPositive : 0 < width := Nat.pos_of_ne_zero hwidthZero
    have hindexEq : index = payload % width := by
      simp [index, projectedRandomBitIndex, hwidthZero, payload]
    have hdecodedIndex :
        (Nat.unpair projectionCode).2 % width = index := by
      rw [hindexEq]
      rfl
    have hindexLt : index < width := by
      rw [hindexEq]
      exact Nat.mod_lt payload hwidthPositive
    have hkindLt : kind < 3 := by
      simpa [kind] using Nat.mod_lt tag (by omega : 0 < 3)
    by_cases hkindZero : kind = 0
    · have hkindZeroRaw :
          projectedRandomBitTag projectionCode % 3 = 0 := by
        simpa [kind, tag] using hkindZero
      have htagZero :
          (Nat.unpair projectionCode).1 % 3 = 0 := by
        exact hkindZeroRaw
      rw [show
        projectedRandomBitEvaluatorFuel
            width projectionCode randomnessCode =
          5 + 8 by
        simp [projectedRandomBitEvaluatorFuel, hwidthZero,
          show projectedRandomBitTag projectionCode % 3 = 0 by
            exact hkindZero]]
      rw [show
        initialNPOracleState inputLength
            (projectedRandomBitEvaluatedInput
              width projectionCode randomnessCode) =
          initialNPOracleState inputLength evaluated by
        rw [hevaluatedEq]]
      rw [hparse 5]
      rw [show 5 = 4 + 1 by omega]
      rw [run_branchZero_instruction
        (pc := 8) (register := 6)
        (zeroTarget := 17) (nonzeroTarget := 9)
        (by rfl)
        (by simp [projectedRandomBitEvaluatorParsedState,
          NPOracleState.write, NPOracleState.jump])]
      rw [show 4 = 3 + 1 by omega]
      rw [run_testBit_instruction
        (pc := 9) (source := 8) (index := 4)
        (destination := 10) (next := 10)
        (value := bit.toNat)
        (by rfl)
        (by simp [projectedRandomBitEvaluatorParsedState,
          NPOracleState.write, NPOracleState.jump, hwidthZero])
        (by simp [projectedRandomBitEvaluatorParsedState,
          NPOracleState.write, NPOracleState.jump, bit, index])
        (hbitsOf hbit)]
      rw [show 3 = 2 + 1 by omega]
      rw [run_branchZero_instruction
        (pc := 10) (register := 5)
        (zeroTarget := 14) (nonzeroTarget := 11)
        (by rfl)
        (by simp [projectedRandomBitEvaluatorParsedState,
          NPOracleState.write, NPOracleState.jump])]
      rw [show 2 = 1 + 1 by omega]
      rw [run_copy_instruction
        (pc := 14) (source := 10) (destination := 0)
        (next := 15) (value := bit.toNat)
        (by rfl)
        (by simp [projectedRandomBitEvaluatorParsedState,
          NPOracleState.write, NPOracleState.jump,
          hkindZeroRaw])
        (by simp [NPOracleState.write, NPOracleState.jump])
        (hbitsOf hbit)]
      have houtput :
          projectedRandomBitOutput
              width projectionCode randomnessCode =
            bit.toNat := by
        simp [projectedRandomBitOutput, decodeProjectedRandomBit,
          SourceInterfaces.ProjectedRandomBit.eval, hwidthZero,
          htagZero, hdecodedIndex, index, bit]
      rw [houtput]
      exact run_halt_instruction
        (program := projectedRandomBitEvaluatorProgram)
        (maximumBits := bits)
        (fuel := 0)
        (pc := 15)
        (outputRegister := 0)
        (value := bit.toNat)
        (by rfl)
        (by simp [projectedRandomBitEvaluatorParsedState,
          NPOracleState.write, NPOracleState.jump,
          hkindZeroRaw])
        (by rfl)
        (hbitsOf hbit)
    · by_cases hkindOne : kind = 1
      · have hkindZeroRaw :
            projectedRandomBitTag projectionCode % 3 ≠ 0 := by
          simpa [kind, tag] using hkindZero
        have hkindOneRaw :
            projectedRandomBitTag projectionCode % 3 = 1 := by
          simpa [kind, tag] using hkindOne
        have htagOne :
            (Nat.unpair projectionCode).1 % 3 = 1 := by
          exact hkindOneRaw
        rw [show
          projectedRandomBitEvaluatorFuel
              width projectionCode randomnessCode =
            8 + 8 by
          simp [projectedRandomBitEvaluatorFuel, hwidthZero,
            hkindOneRaw]]
        rw [show
          initialNPOracleState inputLength
              (projectedRandomBitEvaluatedInput
                width projectionCode randomnessCode) =
            initialNPOracleState inputLength evaluated by
          rw [hevaluatedEq]]
        rw [hparse 8]
        rw [show 8 = 7 + 1 by omega]
        rw [run_branchZero_instruction
          (pc := 8) (register := 6)
          (zeroTarget := 17) (nonzeroTarget := 9)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump])]
        rw [show 7 = 6 + 1 by omega]
        rw [run_testBit_instruction
          (pc := 9) (source := 8) (index := 4)
          (destination := 10) (next := 10)
          (value := bit.toNat)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump, hwidthZero])
          (by rfl)
          (hbitsOf hbit)]
        rw [show 6 = 5 + 1 by omega]
        rw [run_branchZero_instruction
          (pc := 10) (register := 5)
          (zeroTarget := 14) (nonzeroTarget := 11)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump])]
        rw [show 5 = 4 + 1 by omega]
        rw [run_decrement_instruction
          (pc := 11) (register := 5) (next := 12)
          (value := 0)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump,
            hkindZeroRaw])
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump,
            hkindOneRaw])
          (hbitsOf hzero)]
        rw [show 4 = 3 + 1 by omega]
        rw [run_branchZero_instruction
          (pc := 12) (register := 5)
          (zeroTarget := 16) (nonzeroTarget := 13)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump])]
        cases hrawBit : randomnessCode.testBit index
        · have hbitFalse : bit = false := by
            exact hrawBit
          have hdecodedBitFalse :
              randomnessCode.testBit
                  ((Nat.unpair projectionCode).2 % width) =
                false := by
            simpa only [hdecodedIndex] using hrawBit
          rw [show 3 = 2 + 1 by omega]
          rw [run_branchZero_instruction
            (pc := 16) (register := 10)
            (zeroTarget := 20) (nonzeroTarget := 22)
            (by rfl)
            (by simp [projectedRandomBitEvaluatorParsedState,
              NPOracleState.write, NPOracleState.jump,
              hbitFalse])]
          rw [show 2 = 1 + 1 by omega]
          rw [run_set_instruction
            (pc := 20) (register := 0) (value := 1) (next := 21)
            (by rfl)
            (by simp [projectedRandomBitEvaluatorParsedState,
              NPOracleState.write, NPOracleState.jump,
              hbitFalse])
            (hbitsOf hone)]
          have houtput :
              projectedRandomBitOutput
                  width projectionCode randomnessCode =
                1 := by
            simp [projectedRandomBitOutput, decodeProjectedRandomBit,
              SourceInterfaces.ProjectedRandomBit.eval, hwidthZero,
              htagOne, hdecodedBitFalse]
          rw [houtput]
          exact run_halt_instruction
            (program := projectedRandomBitEvaluatorProgram)
            (maximumBits := bits)
            (fuel := 0)
            (pc := 21)
            (outputRegister := 0)
            (value := 1)
            (by rfl)
            (by simp [projectedRandomBitEvaluatorParsedState,
              NPOracleState.write, NPOracleState.jump,
              hbitFalse])
            (by rfl)
            (hbitsOf hone)
        · have hbitTrue : bit = true := by
            exact hrawBit
          have hdecodedBitTrue :
              randomnessCode.testBit
                  ((Nat.unpair projectionCode).2 % width) =
                true := by
            simpa only [hdecodedIndex] using hrawBit
          rw [show 3 = 2 + 1 by omega]
          rw [run_branchZero_instruction
            (pc := 16) (register := 10)
            (zeroTarget := 20) (nonzeroTarget := 22)
            (by rfl)
            (by simp [projectedRandomBitEvaluatorParsedState,
              NPOracleState.write, NPOracleState.jump,
              hbitTrue])]
          rw [show 2 = 1 + 1 by omega]
          rw [run_set_instruction
            (pc := 22) (register := 0) (value := 0) (next := 23)
            (by rfl)
            (by simp [projectedRandomBitEvaluatorParsedState,
              NPOracleState.write, NPOracleState.jump,
              hbitTrue])
            (hbitsOf hzero)]
          have houtput :
              projectedRandomBitOutput
                  width projectionCode randomnessCode =
                0 := by
            simp [projectedRandomBitOutput, decodeProjectedRandomBit,
              SourceInterfaces.ProjectedRandomBit.eval, hwidthZero,
              htagOne, hdecodedBitTrue]
          rw [houtput]
          exact run_halt_instruction
            (program := projectedRandomBitEvaluatorProgram)
            (maximumBits := bits)
            (fuel := 0)
            (pc := 23)
            (outputRegister := 0)
            (value := 0)
            (by rfl)
            (by simp [projectedRandomBitEvaluatorParsedState,
              NPOracleState.write, NPOracleState.jump,
              hbitTrue])
            (by rfl)
            (hbitsOf hzero)
      · have hkindTwo : kind = 2 := by omega
        have hkindZeroRaw :
            projectedRandomBitTag projectionCode % 3 ≠ 0 := by
          simpa [kind, tag] using hkindZero
        have hkindOneRaw :
            projectedRandomBitTag projectionCode % 3 ≠ 1 := by
          simpa [kind, tag] using hkindOne
        have hkindTwoRaw :
            projectedRandomBitTag projectionCode % 3 = 2 := by
          simpa [kind, tag] using hkindTwo
        have htagNeZero :
            (Nat.unpair projectionCode).1 % 3 ≠ 0 := by
          exact hkindZeroRaw
        have htagNeOne :
            (Nat.unpair projectionCode).1 % 3 ≠ 1 := by
          exact hkindOneRaw
        rw [show
            projectedRandomBitEvaluatorFuel
                width projectionCode randomnessCode =
              9 + 8 by
            simp [projectedRandomBitEvaluatorFuel, hwidthZero,
              hkindZeroRaw, hkindOneRaw]]
        rw [show
          initialNPOracleState inputLength
              (projectedRandomBitEvaluatedInput
                width projectionCode randomnessCode) =
            initialNPOracleState inputLength evaluated by
          rw [hevaluatedEq]]
        rw [hparse 9]
        rw [show 9 = 8 + 1 by omega]
        rw [run_branchZero_instruction
          (pc := 8) (register := 6)
          (zeroTarget := 17) (nonzeroTarget := 9)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump])]
        rw [show 8 = 7 + 1 by omega]
        rw [run_testBit_instruction
          (pc := 9) (source := 8) (index := 4)
          (destination := 10) (next := 10)
          (value := bit.toNat)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump, hwidthZero])
          (by rfl)
          (hbitsOf hbit)]
        rw [show 7 = 6 + 1 by omega]
        rw [run_branchZero_instruction
          (pc := 10) (register := 5)
          (zeroTarget := 14) (nonzeroTarget := 11)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump])]
        rw [show 6 = 5 + 1 by omega]
        rw [run_decrement_instruction
          (pc := 11) (register := 5) (next := 12)
          (value := 1)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump,
            hkindZeroRaw])
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump,
            hkindTwoRaw])
          (hbitsOf hone)]
        rw [show 5 = 4 + 1 by omega]
        rw [run_branchZero_instruction
          (pc := 12) (register := 5)
          (zeroTarget := 16) (nonzeroTarget := 13)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump])]
        rw [show 4 = 3 + 1 by omega]
        rw [run_copy_instruction
          (pc := 13) (source := 5) (destination := 5)
          (next := 17) (value := 1)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump])
          (hbitsOf hone)]
        rw [show 3 = 2 + 1 by omega]
        rw [run_set_instruction
          (pc := 17) (register := 11) (value := 0) (next := 18)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump])
          (hbitsOf hzero)]
        rw [show 2 = 1 + 1 by omega]
        rw [run_testBit_instruction
          (pc := 18) (source := 9) (index := 11)
          (destination := 0) (next := 19)
          (value := (payload.testBit 0).toNat)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump])
          (by rfl)
          (hbitsOf hpayloadBit)]
        have houtput :
            projectedRandomBitOutput
                width projectionCode randomnessCode =
              (payload.testBit 0).toNat := by
          simp [projectedRandomBitOutput, decodeProjectedRandomBit,
            SourceInterfaces.ProjectedRandomBit.eval, hwidthZero,
            htagNeZero, htagNeOne, payload,
            projectedRandomBitPayload]
        rw [houtput]
        exact run_halt_instruction
          (program := projectedRandomBitEvaluatorProgram)
          (maximumBits := bits)
          (fuel := 0)
          (pc := 19)
          (outputRegister := 0)
          (value := (payload.testBit 0).toNat)
          (by rfl)
          (by simp [projectedRandomBitEvaluatorParsedState,
            NPOracleState.write, NPOracleState.jump])
          (by rfl)
          (hbitsOf hpayloadBit)

/- `bitSerialModProgram` treats a zero divisor as an invalid public request and
returns zero.  Projected-bit decoding deliberately uses that total branch
because the zero-width semantic case ignores the computed index. -/
private theorem run_bitSerialModProgram_zero
    (inputLength numerator : ℕ) :
    runNPOracleProgram bitSerialModProgram
        (bitSerialModBits numerator 0)
        (bitSerialModFuel numerator 0)
        (initialNPOracleState inputLength
          (bitSerialModInput numerator 0)) =
      some 0 := by
  let bound := bitSerialModRegisterBound numerator 0
  let bits := bitSerialModBits numerator 0
  have hinput :
      bitSerialModInput numerator 0 ≤ bound :=
    Nat.le_max_left _ _
  have hnumerator : numerator ≤ bound :=
    (Nat.left_le_pair numerator 0).trans hinput
  have hbitsOf : ∀ {value : ℕ}, value ≤ bound →
      natBitLength value ≤ bits := by
    intro value hvalue
    exact natBitLength_mono hvalue
  rw [show bitSerialModFuel numerator 0 = 5 by
    simp [bitSerialModFuel]]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction
    (pc := 0) (source := 0) (destination := 4) (next := 1)
    (value := numerator)
    (by rfl) rfl
    (by simp [initialNPOracleState, bitSerialModInput])
    (hbitsOf hnumerator)]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (pc := 1) (source := 0) (destination := 5) (next := 2)
    (value := 0)
    (by rfl)
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, bitSerialModInput])
    (hbitsOf (Nat.zero_le _))]
  rw [show 3 = 2 + 1 by omega]
  rw [run_branchZero_instruction
    (pc := 2) (register := 5)
    (zeroTarget := 31) (nonzeroTarget := 3)
    (by rfl)
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])]
  rw [show 2 = 1 + 1 by omega]
  rw [run_set_instruction
    (pc := 31) (register := 0) (value := 0) (next := 32)
    (by rfl)
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    (hbitsOf (Nat.zero_le _))]
  exact run_halt_instruction
    (program := bitSerialModProgram)
    (maximumBits := bits)
    (fuel := 0)
    (pc := 32)
    (outputRegister := 0)
    (value := 0)
    (by rfl)
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    (by rfl)
    (hbitsOf (Nat.zero_le _))

/-! ## Fixed public entry point -/

def projectedRandomBitProgram : NPOracleProgram :=
  linkPrograms projectedRandomBitAdapterProgram <|
    linkPrograms
      (preserveRightProgram <|
        pairedCallProgram bitSerialModProgram)
      projectedRandomBitEvaluatorProgram

@[simp] theorem projectedRandomBitProgram_oracleFree :
    OracleFree projectedRandomBitProgram := by
  apply oracleFree_linkPrograms
  · exact projectedRandomBitAdapterProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact preserveRightProgram_oracleFree _
        (pairedCallProgram_oracleFree bitSerialModProgram
          bitSerialModProgram_oracleFree)
    · exact projectedRandomBitEvaluatorProgram_oracleFree

def projectedRandomBitFuel
    (width projectionCode randomnessCode : ℕ) : ℕ :=
  let payload := projectedRandomBitPayload projectionCode
  let tag := projectedRandomBitTag projectionCode
  linkFuel
    (linkPrograms
      (preserveRightProgram <|
        pairedCallProgram bitSerialModProgram)
      projectedRandomBitEvaluatorProgram)
    14 <|
    linkFuel projectedRandomBitEvaluatorProgram
      (preserveRightFuel <|
        pairedCallFuel bitSerialModProgram
          (bitSerialModFuel payload width)
          (bitSerialModFuel tag 3))
      (projectedRandomBitEvaluatorFuel
        width projectionCode randomnessCode)

def projectedRandomBitBits
    (inputLength width projectionCode randomnessCode : ℕ) : ℕ :=
  let payload := projectedRandomBitPayload projectionCode
  let tag := projectedRandomBitTag projectionCode
  let leftRequest := bitSerialModInput payload width
  let rightRequest := bitSerialModInput tag 3
  let leftOutput := projectedRandomBitIndex width projectionCode
  let rightOutput := tag % 3
  let context :=
    projectedRandomBitContext width projectionCode randomnessCode
  let calls := Nat.pair leftRequest rightRequest
  let outputs := Nat.pair leftOutput rightOutput
  max (natBitLength inputLength) <|
    max
      (projectedRandomBitAdapterBits
        width projectionCode randomnessCode) <|
      max
        (preserveRightBits
          (pairedCallBits inputLength
            (bitSerialModBits payload width)
            (bitSerialModBits tag 3)
            leftRequest rightRequest leftOutput rightOutput)
          calls context outputs)
        (projectedRandomBitEvaluatorBits
          width projectionCode randomnessCode)

theorem run_projectedRandomBitProgram
    (inputLength width projectionCode randomnessCode : ℕ) :
    runNPOracleProgram projectedRandomBitProgram
        (projectedRandomBitBits
          inputLength width projectionCode randomnessCode)
        (projectedRandomBitFuel
          width projectionCode randomnessCode)
        (initialNPOracleState inputLength
          (projectedRandomBitInput
            width projectionCode randomnessCode)) =
      some
        (projectedRandomBitOutput
          width projectionCode randomnessCode) := by
  let payload := projectedRandomBitPayload projectionCode
  let tag := projectedRandomBitTag projectionCode
  let leftRequest := bitSerialModInput payload width
  let rightRequest := bitSerialModInput tag 3
  let leftOutput := projectedRandomBitIndex width projectionCode
  let rightOutput := tag % 3
  let context :=
    projectedRandomBitContext width projectionCode randomnessCode
  let calls := Nat.pair leftRequest rightRequest
  let outputs := Nat.pair leftOutput rightOutput
  let pairedBits :=
    pairedCallBits inputLength
      (bitSerialModBits payload width)
      (bitSerialModBits tag 3)
      leftRequest rightRequest leftOutput rightOutput
  let pairedFuel :=
    pairedCallFuel bitSerialModProgram
      (bitSerialModFuel payload width)
      (bitSerialModFuel tag 3)
  let preservedBits :=
    preserveRightBits pairedBits calls context outputs
  let preservedFuel := preserveRightFuel pairedFuel
  let evaluatorBits :=
    projectedRandomBitEvaluatorBits
      width projectionCode randomnessCode
  let evaluatorFuel :=
    projectedRandomBitEvaluatorFuel
      width projectionCode randomnessCode
  let maximumBits :=
    projectedRandomBitBits
      inputLength width projectionCode randomnessCode
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, projectedRandomBitBits]
  have hadapterBits :
      projectedRandomBitAdapterBits
          width projectionCode randomnessCode ≤
        maximumBits := by
    simp [maximumBits, projectedRandomBitBits]
  have hpreservedBits : preservedBits ≤ maximumBits := by
    simp [maximumBits, projectedRandomBitBits, preservedBits,
      pairedBits, payload, tag, leftRequest, rightRequest,
      leftOutput, rightOutput, context, calls, outputs]
  have hevaluatorBits : evaluatorBits ≤ maximumBits := by
    simp [maximumBits, projectedRandomBitBits, evaluatorBits]
  have hpositive : 1 ≤ maximumBits := by
    have hpairedPositive : 1 ≤ pairedBits := by
      simp [pairedBits, pairedCallBits]
    have hpreservedPositive : 1 ≤ preservedBits :=
      hpairedPositive.trans (Nat.le_max_left _ _)
    exact hpreservedPositive.trans hpreservedBits
  have hleft :
      runNPOracleProgram bitSerialModProgram
          (bitSerialModBits payload width)
          (bitSerialModFuel payload width)
          (initialNPOracleState inputLength leftRequest) =
        some leftOutput := by
    by_cases hwidthZero : width = 0
    · subst width
      simpa [leftRequest, leftOutput, projectedRandomBitIndex] using
        (run_bitSerialModProgram_zero inputLength payload)
    · have hrun :=
        run_bitSerialModProgram inputLength payload width
          (Nat.pos_of_ne_zero hwidthZero)
      simpa [leftRequest, leftOutput, projectedRandomBitIndex,
        hwidthZero] using hrun
  have hright :
      runNPOracleProgram bitSerialModProgram
          (bitSerialModBits tag 3)
          (bitSerialModFuel tag 3)
          (initialNPOracleState inputLength rightRequest) =
        some rightOutput := by
    simpa [rightRequest, rightOutput] using
      (run_bitSerialModProgram inputLength tag 3 (by omega))
  have hpaired :
      runNPOracleProgram
          (pairedCallProgram bitSerialModProgram)
          pairedBits pairedFuel
          (initialNPOracleState inputLength calls) =
        some outputs := by
    exact run_pairedCallProgram bitSerialModProgram inputLength
      (bitSerialModBits payload width)
      (bitSerialModBits tag 3)
      (bitSerialModFuel payload width)
      (bitSerialModFuel tag 3)
      leftRequest rightRequest leftOutput rightOutput
      hleft hright
  have hpreservedOwn :
      runNPOracleProgram
          (preserveRightProgram <|
            pairedCallProgram bitSerialModProgram)
          preservedBits preservedFuel
          (initialNPOracleState inputLength
            (Nat.pair calls context)) =
        some (Nat.pair outputs context) := by
    exact run_preserveRightProgram
      (pairedCallProgram bitSerialModProgram)
      inputLength pairedBits pairedFuel calls context outputs hpaired
  have hpreserved :
      runNPOracleProgram
          (preserveRightProgram <|
            pairedCallProgram bitSerialModProgram)
          maximumBits preservedFuel
          (initialNPOracleState inputLength
            (projectedRandomBitPreparedInput
              width projectionCode randomnessCode)) =
        some
          (projectedRandomBitEvaluatedInput
            width projectionCode randomnessCode) := by
    have hrun := run_bits_mono hpreservedOwn hpreservedBits
    simpa [projectedRandomBitPreparedInput,
      projectedRandomBitModRequests, projectedRandomBitEvaluatedInput,
      payload, tag, leftRequest, rightRequest, leftOutput,
      rightOutput, context, calls, outputs] using hrun
  have hevaluatorOwn :=
    run_projectedRandomBitEvaluatorProgram
      inputLength width projectionCode randomnessCode
  have hevaluator :
      runNPOracleProgram projectedRandomBitEvaluatorProgram
          maximumBits evaluatorFuel
          (initialNPOracleState inputLength
            (projectedRandomBitEvaluatedInput
              width projectionCode randomnessCode)) =
        some
          (projectedRandomBitOutput
            width projectionCode randomnessCode) := by
    exact run_bits_mono hevaluatorOwn hevaluatorBits
  have hadapter :
      runNPOracleProgram projectedRandomBitAdapterProgram
          maximumBits 14
          (initialNPOracleState inputLength
            (projectedRandomBitInput
              width projectionCode randomnessCode)) =
        some
          (projectedRandomBitPreparedInput
            width projectionCode randomnessCode) := by
    exact run_bits_mono
      (run_projectedRandomBitAdapterProgram
        inputLength width projectionCode randomnessCode)
      hadapterBits
  have hinner :
      runNPOracleProgram
          (linkPrograms
            (preserveRightProgram <|
              pairedCallProgram bitSerialModProgram)
            projectedRandomBitEvaluatorProgram)
          maximumBits
          (linkFuel projectedRandomBitEvaluatorProgram
            preservedFuel evaluatorFuel)
          (initialNPOracleState inputLength
            (projectedRandomBitPreparedInput
              width projectionCode randomnessCode)) =
        some
          (projectedRandomBitOutput
            width projectionCode randomnessCode) := by
    exact run_linkPrograms hpositive hlength hpreserved hevaluator
  have hrun :=
    run_linkPrograms hpositive hlength hadapter hinner
  simpa [projectedRandomBitProgram, projectedRandomBitFuel,
    maximumBits, payload, tag, pairedFuel, preservedFuel,
    evaluatorFuel] using hrun

/-! ## Polynomial runner package -/

structure ProjectedRandomBitRequest where
  inputLength : ℕ
  width : ℕ
  projectionCode : ℕ
  randomnessCode : ℕ

def ProjectedRandomBitRequest.code
    (request : ProjectedRandomBitRequest) : ℕ :=
  projectedRandomBitInput request.width request.projectionCode
    request.randomnessCode

def ProjectedRandomBitRequest.output
    (request : ProjectedRandomBitRequest) : ℕ :=
  projectedRandomBitOutput request.width request.projectionCode
    request.randomnessCode

/-- The charged size is the exact closed execution envelope of the fixed
binary controller.  This keeps the runner usable under any outer polynomial
measure without pretending that a binary width is a unary value. -/
def ProjectedRandomBitRequest.measure
    (request : ProjectedRandomBitRequest) : ℕ :=
  max
    (natBitLength
      (max request.inputLength request.code))
    (max
      (projectedRandomBitFuel request.width request.projectionCode
        request.randomnessCode)
      (projectedRandomBitBits request.inputLength request.width
        request.projectionCode request.randomnessCode))

private theorem projectedRandomBitFuel_le_budget
    (request : ProjectedRandomBitRequest) :
    projectedRandomBitFuel request.width request.projectionCode
        request.randomnessCode ≤
      polynomialBudget 1 1 request.measure := by
  rw [show polynomialBudget 1 1 request.measure =
      request.measure + 1 by simp [polynomialBudget]]
  apply le_trans ?_ (Nat.le_succ request.measure)
  unfold ProjectedRandomBitRequest.measure
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

private theorem projectedRandomBitBits_le_budget
    (request : ProjectedRandomBitRequest) :
    projectedRandomBitBits request.inputLength request.width
        request.projectionCode request.randomnessCode ≤
      polynomialBudget 1 1 request.measure := by
  rw [show polynomialBudget 1 1 request.measure =
      request.measure + 1 by simp [polynomialBudget]]
  apply le_trans ?_ (Nat.le_succ request.measure)
  unfold ProjectedRandomBitRequest.measure
  exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

def projectedRandomBitRunner :
    PolynomialNatProgram ProjectedRandomBitRequest
      ProjectedRandomBitRequest.inputLength
      ProjectedRandomBitRequest.code
      ProjectedRandomBitRequest.measure where
  program := projectedRandomBitProgram
  coefficient := 1
  coefficientPositive := by omega
  degree := 1
  initialBitsFit := by
    intro request
    rw [show polynomialBudget 1 1 request.measure =
        request.measure + 1 by simp [polynomialBudget]]
    apply le_trans ?_ (Nat.le_succ request.measure)
    exact Nat.le_max_left _ _
  halts := by
    intro request
    refine ⟨request.output, ?_⟩
    let budget := polynomialBudget 1 1 request.measure
    have hexact :=
      run_projectedRandomBitProgram request.inputLength request.width
        request.projectionCode request.randomnessCode
    have hwiden :=
      run_bits_mono hexact
        (projectedRandomBitBits_le_budget request)
    have hpadded :=
      run_fuel_add hwiden
        (budget -
          projectedRandomBitFuel request.width request.projectionCode
            request.randomnessCode)
    have htotal :
        projectedRandomBitFuel request.width request.projectionCode
            request.randomnessCode +
            (budget -
              projectedRandomBitFuel request.width request.projectionCode
                request.randomnessCode) =
          budget :=
      Nat.add_sub_of_le (projectedRandomBitFuel_le_budget request)
    simpa [budget, htotal, ProjectedRandomBitRequest.code,
      ProjectedRandomBitRequest.output] using hpadded

def projectedRandomBitRunnerWitness :
    PolynomialNatProgramWitness ProjectedRandomBitRequest
      ProjectedRandomBitRequest.inputLength
      ProjectedRandomBitRequest.code
      ProjectedRandomBitRequest.measure
      ProjectedRandomBitRequest.output where
  runner := projectedRandomBitRunner
  computes := by
    intro request
    let budget := polynomialBudget 1 1 request.measure
    have hexact :=
      run_projectedRandomBitProgram request.inputLength request.width
        request.projectionCode request.randomnessCode
    have hwiden :=
      run_bits_mono hexact
        (projectedRandomBitBits_le_budget request)
    have hpadded :=
      run_fuel_add hwiden
        (budget -
          projectedRandomBitFuel request.width request.projectionCode
            request.randomnessCode)
    have htotal :
        projectedRandomBitFuel request.width request.projectionCode
            request.randomnessCode +
            (budget -
              projectedRandomBitFuel request.width request.projectionCode
                request.randomnessCode) =
          budget :=
      Nat.add_sub_of_le (projectedRandomBitFuel_le_budget request)
    simpa [PolynomialNatProgram.budget, projectedRandomBitRunner,
      budget, htotal, ProjectedRandomBitRequest.code,
      ProjectedRandomBitRequest.output] using hpadded

@[simp] theorem projectedRandomBitRunner_execute
    (request : ProjectedRandomBitRequest) :
    projectedRandomBitRunner.execute request = request.output := by
  exact projectedRandomBitRunnerWitness.execute_eq request

end NearCubicWires.CanonicalProjectedRandomBitProgram
