import Proof.Circuits.CallableRelocation
import Proof.MachineModel.CanonicalBitSerialModProgram
import Proof.MachineModel.CanonicalNatValidationProgram
import Proof.MachineModel.CanonicalTaggedTupleProgram
import Proof.Circuits.CanonicalWitnessCodec
import Proof.MachineModel.PreserveRightProgram
import Proof.Circuits.RegisterBounds
import Proof.Foundations.VerifiedLinker

/-!
# Total canonical-rational validation

A legal coefficient has one public representation: a two-cell tagged tuple
containing a canonical signed numerator and a positive canonical denominator.
This module validates that representation with one fixed interpreter pipeline.
Reducedness is decided by an executable Euclidean controller whose only
remainder implementation is the shared bit-serial modulo program.
-/

namespace NearCubicWires.CanonicalRationalValidationProgram

open NearCubicWires
open NearCubicWires.CallableRelocation
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialModProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RegisterBounds
open NearCubicWires.VerifiedLinker

/-! ## Euclidean gcd with one relocated modulo implementation -/

def euclideanGcd : ℕ → ℕ → ℕ
  | left, 0 => left
  | left, right + 1 => euclideanGcd (right + 1) (left % (right + 1))
termination_by _ right => right
decreasing_by
  exact Nat.mod_lt _ (by omega)

theorem euclideanGcd_eq_gcd (left right : ℕ) :
    euclideanGcd left right = Nat.gcd left right := by
  induction right using Nat.strong_induction_on generalizing left with
  | h right inductionHypothesis =>
      cases right with
      | zero =>
          simp [euclideanGcd]
      | succ right =>
          rw [euclideanGcd]
          rw [inductionHypothesis (left % (right + 1))
            (Nat.mod_lt _ (by omega))]
          calc
            Nat.gcd (right + 1) (left % (right + 1)) =
                Nat.gcd (left % (right + 1)) (right + 1) :=
              Nat.gcd_comm _ _
            _ = Nat.gcd (right + 1) left := by
              rw [← Nat.gcd_rec]
            _ = Nat.gcd left (right + 1) :=
              Nat.gcd_comm _ _

def gcdCalleeRegisterBase : ℕ := 10

def gcdCalleeSpan : ℕ :=
  programRegisterSpan bitSerialModProgram

def gcdLoopPc : ℕ := 2

def gcdResetBase : ℕ := 3

def gcdPrepareBase : ℕ :=
  gcdResetBase + gcdCalleeSpan

def gcdCalleeBase : ℕ :=
  gcdPrepareBase + 4

def gcdReturnPc : ℕ :=
  gcdCalleeBase + bitSerialModProgram.length

def gcdSuccessPc : ℕ :=
  gcdReturnPc + 4

/-- Register ABI:

* `r1`: immutable public input length;
* `r2/r3`: current Euclidean pair;
* `r4`: paired modulo request;
* `r5`: relocated-call accumulator;
* `r6/r7`: remainder and zero scratch;
* `r10...`: isolated bit-serial modulo bank.
-/
def canonicalGcdPrefix : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 gcdLoopPc
  , .branchZero 3 gcdSuccessPc gcdResetBase
  ]

def canonicalGcdPrepareProgram : NPOracleProgram :=
  [ .pair 2 3 4 (gcdPrepareBase + 1)
  , .copy 4 gcdCalleeRegisterBase (gcdPrepareBase + 2)
  , .copy 1 (gcdCalleeRegisterBase + 1) (gcdPrepareBase + 3)
  , .set 5 0 gcdCalleeBase
  ]

def canonicalGcdReturnProgram : NPOracleProgram :=
  [ .unpairRight 5 6 (gcdReturnPc + 1)
  , .copy 3 2 (gcdReturnPc + 2)
  , .copy 6 3 (gcdReturnPc + 3)
  , .decrement 7 gcdLoopPc
  , .copy 2 0 (gcdSuccessPc + 1)
  , .halt 0
  ]

def canonicalGcdProgram : NPOracleProgram :=
  canonicalGcdPrefix ++
  resetRegisters gcdCalleeRegisterBase gcdCalleeSpan gcdResetBase ++
  canonicalGcdPrepareProgram ++
  bitSerialModProgram.map
    (callableInstruction gcdCalleeBase gcdCalleeRegisterBase 5 gcdReturnPc) ++
  canonicalGcdReturnProgram

@[simp] private theorem canonicalGcdPrefix_length :
    canonicalGcdPrefix.length = 3 := rfl

@[simp] private theorem canonicalGcdPrepareProgram_length :
    canonicalGcdPrepareProgram.length = 4 := rfl

private theorem canonicalGcdProgram_prefixAt
    (index : ℕ) (hindex : index < canonicalGcdPrefix.length) :
    canonicalGcdProgram[index]? = canonicalGcdPrefix[index]? := by
  change index < 3 at hindex
  simp only [canonicalGcdProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      canonicalGcdPrefix_length, resetRegisters_length,
      canonicalGcdPrepareProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, canonicalGcdPrefix_length,
      resetRegisters_length, canonicalGcdPrepareProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, canonicalGcdPrefix_length,
      resetRegisters_length]
    omega)]
  exact List.getElem?_append_left hindex

private theorem canonicalGcdProgram_prepareAt
    (index : ℕ) (hindex : index < canonicalGcdPrepareProgram.length) :
    canonicalGcdProgram[gcdPrepareBase + index]? =
      canonicalGcdPrepareProgram[index]? := by
  change index < 4 at hindex
  simp only [canonicalGcdProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      canonicalGcdPrefix_length, resetRegisters_length,
      canonicalGcdPrepareProgram_length]
    simp [gcdPrepareBase, gcdResetBase]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, canonicalGcdPrefix_length,
      resetRegisters_length, canonicalGcdPrepareProgram_length]
    simp [gcdPrepareBase, gcdResetBase]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, canonicalGcdPrefix_length,
      resetRegisters_length]
    simp [gcdPrepareBase, gcdResetBase])]
  simp only [List.length_append, canonicalGcdPrefix_length,
    resetRegisters_length]
  rw [show gcdPrepareBase + index - (3 + gcdCalleeSpan) = index by
    simp [gcdPrepareBase, gcdResetBase]]

private theorem canonicalGcdProgram_returnAt
    (index : ℕ) (_hindex : index < canonicalGcdReturnProgram.length) :
    canonicalGcdProgram[gcdReturnPc + index]? =
      canonicalGcdReturnProgram[index]? := by
  simp only [canonicalGcdProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      canonicalGcdPrefix_length, resetRegisters_length,
      canonicalGcdPrepareProgram_length]
    simp [gcdReturnPc, gcdCalleeBase, gcdPrepareBase, gcdResetBase])]
  simp only [List.length_append, List.length_map,
    canonicalGcdPrefix_length, resetRegisters_length,
    canonicalGcdPrepareProgram_length]
  rw [show gcdReturnPc + index -
      (3 + gcdCalleeSpan + 4 + bitSerialModProgram.length) = index by
    simp [gcdReturnPc, gcdCalleeBase, gcdPrepareBase, gcdResetBase]]

private theorem canonicalGcdProgram_resetAt :
    ResetProgramAt canonicalGcdProgram gcdCalleeRegisterBase gcdCalleeSpan
      gcdResetBase := by
  intro index hindex
  simp only [canonicalGcdProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      canonicalGcdPrefix_length, resetRegisters_length,
      canonicalGcdPrepareProgram_length]
    simp [gcdResetBase]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, canonicalGcdPrefix_length,
      resetRegisters_length, canonicalGcdPrepareProgram_length]
    simp [gcdResetBase]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, canonicalGcdPrefix_length,
      resetRegisters_length]
    simp [gcdResetBase]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [canonicalGcdPrefix_length]
    simp [gcdResetBase])]
  simp only [canonicalGcdPrefix_length]
  rw [show gcdResetBase + index - 3 = index by
    simp [gcdResetBase]]
  simp only [resetRegisters, List.getElem?_map]
  rw [List.getElem?_range hindex]
  rfl

private theorem canonicalGcdProgram_callableAt :
    ProgramCallableAt canonicalGcdProgram bitSerialModProgram
      gcdCalleeBase gcdCalleeRegisterBase 5 gcdReturnPc := by
  intro pc instruction hlookup
  have hpc : pc < bitSerialModProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [canonicalGcdProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, canonicalGcdPrefix_length,
      resetRegisters_length, canonicalGcdPrepareProgram_length,
      List.length_map]
    simp [gcdCalleeBase, gcdPrepareBase, gcdResetBase]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, canonicalGcdPrefix_length,
      resetRegisters_length, canonicalGcdPrepareProgram_length]
    simp [gcdCalleeBase, gcdPrepareBase, gcdResetBase])]
  simp only [List.length_append, canonicalGcdPrefix_length,
    resetRegisters_length, canonicalGcdPrepareProgram_length]
  rw [show gcdCalleeBase + pc -
      (3 + gcdCalleeSpan + 4) = pc by
    simp [gcdCalleeBase, gcdPrepareBase, gcdResetBase]]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem canonicalGcdProgram_inputLeft :
    canonicalGcdProgram[0]? = some (.unpairLeft 0 2 1) := by
  simpa [canonicalGcdPrefix] using
    canonicalGcdProgram_prefixAt 0 (by decide)

private theorem canonicalGcdProgram_inputRight :
    canonicalGcdProgram[1]? = some (.unpairRight 0 3 gcdLoopPc) := by
  simpa [canonicalGcdPrefix] using
    canonicalGcdProgram_prefixAt 1 (by decide)

private theorem canonicalGcdProgram_loop :
    canonicalGcdProgram[gcdLoopPc]? =
      some (.branchZero 3 gcdSuccessPc gcdResetBase) := by
  simpa [canonicalGcdPrefix, gcdLoopPc] using
    canonicalGcdProgram_prefixAt 2 (by decide)

private theorem canonicalGcdProgram_prepareRequest :
    canonicalGcdProgram[gcdPrepareBase]? =
      some (.pair 2 3 4 (gcdPrepareBase + 1)) := by
  simpa [canonicalGcdPrepareProgram] using
    canonicalGcdProgram_prepareAt 0 (by decide)

private theorem canonicalGcdProgram_loadRequest :
    canonicalGcdProgram[gcdPrepareBase + 1]? =
      some (.copy 4 gcdCalleeRegisterBase (gcdPrepareBase + 2)) := by
  simpa [canonicalGcdPrepareProgram] using
    canonicalGcdProgram_prepareAt 1 (by decide)

private theorem canonicalGcdProgram_loadLength :
    canonicalGcdProgram[gcdPrepareBase + 2]? =
      some (.copy 1 (gcdCalleeRegisterBase + 1)
        (gcdPrepareBase + 3)) := by
  simpa [canonicalGcdPrepareProgram] using
    canonicalGcdProgram_prepareAt 2 (by decide)

private theorem canonicalGcdProgram_clearAccumulator :
    canonicalGcdProgram[gcdPrepareBase + 3]? =
      some (.set 5 0 gcdCalleeBase) := by
  simpa [canonicalGcdPrepareProgram] using
    canonicalGcdProgram_prepareAt 3 (by decide)

private theorem canonicalGcdProgram_unpackRemainder :
    canonicalGcdProgram[gcdReturnPc]? =
      some (.unpairRight 5 6 (gcdReturnPc + 1)) := by
  simpa [canonicalGcdReturnProgram] using
    canonicalGcdProgram_returnAt 0 (by decide)

private theorem canonicalGcdProgram_rotateLeft :
    canonicalGcdProgram[gcdReturnPc + 1]? =
      some (.copy 3 2 (gcdReturnPc + 2)) := by
  simpa [canonicalGcdReturnProgram] using
    canonicalGcdProgram_returnAt 1 (by decide)

private theorem canonicalGcdProgram_rotateRight :
    canonicalGcdProgram[gcdReturnPc + 2]? =
      some (.copy 6 3 (gcdReturnPc + 3)) := by
  simpa [canonicalGcdReturnProgram] using
    canonicalGcdProgram_returnAt 2 (by decide)

private theorem canonicalGcdProgram_loopBack :
    canonicalGcdProgram[gcdReturnPc + 3]? =
      some (.decrement 7 gcdLoopPc) := by
  simpa [canonicalGcdReturnProgram] using
    canonicalGcdProgram_returnAt 3 (by decide)

private theorem canonicalGcdProgram_success :
    canonicalGcdProgram[gcdSuccessPc]? =
      some (.copy 2 0 (gcdSuccessPc + 1)) := by
  simpa [canonicalGcdReturnProgram, gcdSuccessPc] using
    canonicalGcdProgram_returnAt 4 (by decide)

private theorem canonicalGcdProgram_halt :
    canonicalGcdProgram[gcdSuccessPc + 1]? = some (.halt 0) := by
  simpa [canonicalGcdReturnProgram, gcdSuccessPc] using
    canonicalGcdProgram_returnAt 5 (by decide)

@[simp] theorem canonicalGcdProgram_oracleFree :
    OracleFree canonicalGcdProgram := by
  rw [oracleFree_iff_containsSAT_false]
  have hcallee :
      containsSAT bitSerialModProgram = false :=
    (oracleFree_iff_containsSAT_false bitSerialModProgram).mp
      bitSerialModProgram_oracleFree
  unfold containsSAT at hcallee ⊢
  simp only [canonicalGcdProgram, List.any_append, resetRegisters,
    List.any_map]
  change
    (false || bitSerialModProgram.any (fun instruction =>
      match callableInstruction gcdCalleeBase gcdCalleeRegisterBase 5
          gcdReturnPc instruction with
      | .sat _ _ _ => true
      | _ => false)) = false
  simp only [Bool.false_or]
  exact
    (any_callableInstruction bitSerialModProgram gcdCalleeBase
      gcdCalleeRegisterBase 5 gcdReturnPc).trans hcallee

def canonicalGcdLoopFuel : ℕ → ℕ → ℕ
  | _left, 0 => 3
  | left, right + 1 =>
      9 + gcdCalleeSpan + bitSerialModFuel left (right + 1) +
        canonicalGcdLoopFuel (right + 1) (left % (right + 1))
termination_by _ right => right
decreasing_by
  exact Nat.mod_lt _ (by omega)

def canonicalGcdFuel (left right : ℕ) : ℕ :=
  2 + canonicalGcdLoopFuel left right

def canonicalGcdRegisterBound (inputLength magnitude : ℕ) : ℕ :=
  max 1 <| max inputLength <|
    max (Nat.pair magnitude magnitude) <|
      max (natBitLength magnitude) (2 * magnitude + 1)

def canonicalGcdEnvelopeBits (inputLength magnitude : ℕ) : ℕ :=
  natBitLength (canonicalGcdRegisterBound inputLength magnitude)

def canonicalGcdBits (inputLength left right : ℕ) : ℕ :=
  canonicalGcdEnvelopeBits inputLength (max left right)

private theorem bitsLength_le_natBitLength (value : ℕ) :
    value.bits.length ≤ natBitLength value := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  simpa [natBitLength, Nat.succ_eq_add_one] using
    (Nat.lt_pow_succ_log_self (b := 2) (by omega) value)

private theorem one_le_canonicalGcdRegisterBound
    (inputLength magnitude : ℕ) :
    1 ≤ canonicalGcdRegisterBound inputLength magnitude := by
  simp [canonicalGcdRegisterBound]

private theorem inputLength_le_canonicalGcdRegisterBound
    (inputLength magnitude : ℕ) :
    inputLength ≤ canonicalGcdRegisterBound inputLength magnitude := by
  simp [canonicalGcdRegisterBound]

private theorem pairMagnitude_le_canonicalGcdRegisterBound
    (inputLength magnitude : ℕ) :
    Nat.pair magnitude magnitude ≤
      canonicalGcdRegisterBound inputLength magnitude := by
  simp [canonicalGcdRegisterBound]

private theorem magnitudeBits_le_canonicalGcdRegisterBound
    (inputLength magnitude : ℕ) :
    natBitLength magnitude ≤
      canonicalGcdRegisterBound inputLength magnitude := by
  simp [canonicalGcdRegisterBound]

private theorem doubledMagnitude_le_canonicalGcdRegisterBound
    (inputLength magnitude : ℕ) :
    2 * magnitude + 1 ≤
      canonicalGcdRegisterBound inputLength magnitude := by
  simp [canonicalGcdRegisterBound]

private theorem value_bits_le_canonicalGcdEnvelope
    (inputLength magnitude value : ℕ) (hvalue : value ≤ magnitude) :
    natBitLength value ≤ canonicalGcdEnvelopeBits inputLength magnitude := by
  unfold canonicalGcdEnvelopeBits
  apply natBitLength_mono
  exact hvalue.trans <|
    (Nat.left_le_pair magnitude magnitude).trans <|
      pairMagnitude_le_canonicalGcdRegisterBound inputLength magnitude

private theorem inputLength_bits_le_canonicalGcdEnvelope
    (inputLength magnitude : ℕ) :
    natBitLength inputLength ≤
      canonicalGcdEnvelopeBits inputLength magnitude := by
  unfold canonicalGcdEnvelopeBits
  exact natBitLength_mono <|
    inputLength_le_canonicalGcdRegisterBound inputLength magnitude

private theorem request_bits_le_canonicalGcdEnvelope
    (inputLength magnitude left right : ℕ)
    (hleft : left ≤ magnitude) (hright : right ≤ magnitude) :
    natBitLength (Nat.pair left right) ≤
      canonicalGcdEnvelopeBits inputLength magnitude := by
  unfold canonicalGcdEnvelopeBits
  apply natBitLength_mono
  exact (pair_mono hleft hright).trans <|
    pairMagnitude_le_canonicalGcdRegisterBound inputLength magnitude

private theorem bitSerialModRegisterBound_le_canonicalGcdRegisterBound
    (inputLength magnitude left right : ℕ)
    (hleft : left ≤ magnitude) (hright : right ≤ magnitude) :
    bitSerialModRegisterBound left right ≤
      canonicalGcdRegisterBound inputLength magnitude := by
  unfold bitSerialModRegisterBound bitSerialModInput
  apply max_le
  · exact (pair_mono hleft hright).trans <|
      pairMagnitude_le_canonicalGcdRegisterBound inputLength magnitude
  · apply max_le
    · exact (bitsLength_le_natBitLength left).trans <|
        (natBitLength_mono hleft).trans <|
          magnitudeBits_le_canonicalGcdRegisterBound inputLength magnitude
    · exact (by omega : 2 * right + 1 ≤ 2 * magnitude + 1) |>.trans <|
        doubledMagnitude_le_canonicalGcdRegisterBound inputLength magnitude

private theorem modulo_bits_le_canonicalGcdEnvelope
    (inputLength magnitude left right : ℕ)
    (hleft : left ≤ magnitude) (hright : right ≤ magnitude) :
    bitSerialModBits left right ≤
      canonicalGcdEnvelopeBits inputLength magnitude := by
  unfold bitSerialModBits canonicalGcdEnvelopeBits
  exact natBitLength_mono <|
    bitSerialModRegisterBound_le_canonicalGcdRegisterBound
      inputLength magnitude left right hleft hright

private theorem accumulator_bits_le_canonicalGcdEnvelope
    (inputLength magnitude remainder : ℕ)
    (hremainder : remainder ≤ magnitude) :
    natBitLength (Nat.pair 0 remainder) ≤
      canonicalGcdEnvelopeBits inputLength magnitude := by
  unfold canonicalGcdEnvelopeBits
  apply natBitLength_mono
  exact (pair_mono (Nat.zero_le magnitude) hremainder).trans <|
    pairMagnitude_le_canonicalGcdRegisterBound inputLength magnitude

private theorem one_bits_le_canonicalGcdEnvelope
    (inputLength magnitude : ℕ) :
    natBitLength 1 ≤ canonicalGcdEnvelopeBits inputLength magnitude := by
  unfold canonicalGcdEnvelopeBits
  exact natBitLength_mono <|
    one_le_canonicalGcdRegisterBound inputLength magnitude

private def canonicalGcdCallEntry
    (inputLength request : ℕ) (state : NPOracleState) : NPOracleState :=
  (((((zeroRegisterRange gcdCalleeRegisterBase gcdCalleeSpan state).write
      4 request).write gcdCalleeRegisterBase request).write
      (gcdCalleeRegisterBase + 1) inputLength).write 5 0).jump
        gcdCalleeBase

private theorem canonicalGcdCallEntry_eq_active
    (inputLength request : ℕ) (state : NPOracleState) :
    let entry := canonicalGcdCallEntry inputLength request state
    entry =
      relocateActiveState gcdCalleeBase gcdCalleeRegisterBase gcdCalleeSpan
        entry.registers (initialNPOracleState inputLength request) := by
  let entry := canonicalGcdCallEntry inputLength request state
  change entry =
    relocateActiveState gcdCalleeBase gcdCalleeRegisterBase gcdCalleeSpan
      entry.registers (initialNPOracleState inputLength request)
  apply state_ext
  · simp [entry, canonicalGcdCallEntry, relocateActiveState,
      initialNPOracleState]
  · funext candidate
    by_cases hinside :
        gcdCalleeRegisterBase ≤ candidate ∧
          candidate < gcdCalleeRegisterBase + gcdCalleeSpan
    · rcases hinside with ⟨hlower, hupper⟩
      by_cases hzero : candidate = gcdCalleeRegisterBase
      · subst candidate
        simp [entry, canonicalGcdCallEntry, relocateActiveState,
          initialNPOracleState, gcdCalleeRegisterBase]
      · by_cases hone : candidate = gcdCalleeRegisterBase + 1
        · subst candidate
          simp [entry, canonicalGcdCallEntry, relocateActiveState,
            initialNPOracleState, gcdCalleeRegisterBase]
        · have hreset :
              (zeroRegisterRange gcdCalleeRegisterBase gcdCalleeSpan state).registers
                candidate = 0 :=
            zeroRegisterRange_inside state hlower hupper
          have hfour : candidate ≠ 4 := by
            simp [gcdCalleeRegisterBase] at hlower
            omega
          have hfive : candidate ≠ 5 := by
            simp [gcdCalleeRegisterBase] at hlower
            omega
          have hsubZero :
              candidate - gcdCalleeRegisterBase ≠ 0 := by
            omega
          have hsubOne :
              candidate - gcdCalleeRegisterBase ≠ 1 := by
            omega
          simp [entry, canonicalGcdCallEntry, relocateActiveState,
            initialNPOracleState, hlower, hupper, hzero, hone, hfour, hfive,
            hsubZero, hsubOne, hreset]
    · simp [relocateActiveState, hinside]

set_option maxHeartbeats 3000000 in
-- The Euclidean induction elaborates a relocated modulo trace at every step.
theorem run_canonicalGcdLoop
    (inputLength magnitude maximumBits left right extra : ℕ)
    (state : NPOracleState)
    (hleftBound : left ≤ magnitude)
    (hrightBound : right ≤ magnitude)
    (hpc : state.pc = gcdLoopPc)
    (hlength : state.registers 1 = inputLength)
    (hleft : state.registers 2 = left)
    (hright : state.registers 3 = right)
    (hscratch : state.registers 7 = 0)
    (hbits :
      canonicalGcdEnvelopeBits inputLength magnitude ≤ maximumBits) :
    runNPOracleProgram canonicalGcdProgram maximumBits
        (canonicalGcdLoopFuel left right + extra) state =
      some (euclideanGcd left right) := by
  induction right using Nat.strong_induction_on generalizing left state extra with
  | h right inductionHypothesis =>
      cases right with
      | zero =>
          have hleftBits : natBitLength left ≤ maximumBits :=
            (value_bits_le_canonicalGcdEnvelope inputLength magnitude left
              hleftBound).trans hbits
          rw [canonicalGcdLoopFuel.eq_1 left]
          rw [show 3 + extra = (2 + extra) + 1 by omega]
          rw [run_branchZero_instruction canonicalGcdProgram_loop hpc]
          rw [hright, if_pos rfl]
          rw [show 2 + extra = 1 + extra + 1 by omega]
          rw [run_copy_instruction (fuel := 1 + extra)
            (state := state.jump gcdSuccessPc)
            canonicalGcdProgram_success (by rfl) hleft hleftBits]
          rw [show 1 + extra = extra + 1 by omega]
          simp only [runNPOracleProgram]
          rw [show
            (((state.jump gcdSuccessPc).write 0 left).jump
                (gcdSuccessPc + 1)).pc = gcdSuccessPc + 1 by rfl]
          rw [canonicalGcdProgram_halt]
          simp only
          rw [show
            (((state.jump gcdSuccessPc).write 0 left).jump
                (gcdSuccessPc + 1)).registers 0 = left by
              simp [NPOracleState.write]]
          simpa [hleftBits] using
            congrArg some (euclideanGcd.eq_1 left).symm
      | succ right =>
          let divisor := right + 1
          let remainder := left % divisor
          let request := Nat.pair left divisor
          have hdivisorBound : divisor ≤ magnitude := by
            simpa [divisor] using hrightBound
          have hpositive : 0 < divisor := by simp [divisor]
          have hremainderLt : remainder < divisor := by
            exact Nat.mod_lt _ hpositive
          have hremainderBound : remainder ≤ magnitude :=
            (Nat.le_of_lt hremainderLt).trans hdivisorBound
          have hbitsPositive : 1 ≤ maximumBits := by
            simpa [natBitLength] using
              (one_bits_le_canonicalGcdEnvelope inputLength magnitude).trans
                hbits
          have hlengthBits : natBitLength inputLength ≤ maximumBits :=
            (inputLength_bits_le_canonicalGcdEnvelope inputLength
              magnitude).trans hbits
          have hleftBits : natBitLength left ≤ maximumBits :=
            (value_bits_le_canonicalGcdEnvelope inputLength magnitude left
              hleftBound).trans hbits
          have hdivisorBits : natBitLength divisor ≤ maximumBits :=
            (value_bits_le_canonicalGcdEnvelope inputLength magnitude divisor
              hdivisorBound).trans hbits
          have hrequestBits : natBitLength request ≤ maximumBits := by
            exact (request_bits_le_canonicalGcdEnvelope inputLength magnitude
              left divisor hleftBound hdivisorBound).trans hbits
          have hmoduloBits :
              bitSerialModBits left divisor ≤ maximumBits :=
            (modulo_bits_le_canonicalGcdEnvelope inputLength magnitude left
              divisor hleftBound hdivisorBound).trans hbits
          have haccumulatorBits :
              natBitLength (Nat.pair 0 remainder) ≤ maximumBits := by
            exact (accumulator_bits_le_canonicalGcdEnvelope inputLength
              magnitude remainder hremainderBound).trans hbits
          have hremainderBits : natBitLength remainder ≤ maximumBits :=
            (value_bits_le_canonicalGcdEnvelope inputLength magnitude
              remainder hremainderBound).trans hbits
          let resetState :=
            (zeroRegisterRange gcdCalleeRegisterBase gcdCalleeSpan state).jump
              gcdPrepareBase
          let requestState :=
            (resetState.write 4 request).jump (gcdPrepareBase + 1)
          let loadedRequest :=
            (requestState.write gcdCalleeRegisterBase request).jump
              (gcdPrepareBase + 2)
          let loadedLength :=
            (loadedRequest.write (gcdCalleeRegisterBase + 1)
              inputLength).jump (gcdPrepareBase + 3)
          let callEntry :=
            (loadedLength.write 5 0).jump gcdCalleeBase
          have hcallEntry :
              callEntry = canonicalGcdCallEntry inputLength request state := by
            simp [callEntry, loadedLength, loadedRequest, requestState,
              resetState, canonicalGcdCallEntry, request, NPOracleState.jump]
            rfl
          have hentryActive :
              callEntry =
                relocateActiveState gcdCalleeBase gcdCalleeRegisterBase
                  gcdCalleeSpan callEntry.registers
                    (initialNPOracleState inputLength request) := by
            rw [hcallEntry]
            simpa using
              canonicalGcdCallEntry_eq_active inputLength request state
          have hentryAccumulator : callEntry.registers 5 = 0 := by
            simp [callEntry, loadedLength, NPOracleState.write]
          have hentryLength : callEntry.registers 1 = inputLength := by
            simp [callEntry, loadedLength, loadedRequest, requestState,
              resetState, zeroRegisterRange_below, gcdCalleeRegisterBase,
              hlength, NPOracleState.write]
          have hentryLeft : callEntry.registers 2 = left := by
            simp [callEntry, loadedLength, loadedRequest, requestState,
              resetState, zeroRegisterRange_below, gcdCalleeRegisterBase,
              hleft, NPOracleState.write]
          have hentryRight : callEntry.registers 3 = divisor := by
            simp [callEntry, loadedLength, loadedRequest, requestState,
              resetState, zeroRegisterRange_below, gcdCalleeRegisterBase,
              hright, divisor, NPOracleState.write]
          have hentryScratch : callEntry.registers 7 = 0 := by
            simp [callEntry, loadedLength, loadedRequest, requestState,
              resetState, zeroRegisterRange_below, gcdCalleeRegisterBase,
              hscratch, NPOracleState.write]
          have hresetLeft : resetState.registers 2 = left := by
            change
              (zeroRegisterRange gcdCalleeRegisterBase gcdCalleeSpan state).registers
                2 = left
            rw [zeroRegisterRange_below state (by
              simp [gcdCalleeRegisterBase])]
            exact hleft
          have hresetRight : resetState.registers 3 = divisor := by
            change
              (zeroRegisterRange gcdCalleeRegisterBase gcdCalleeSpan state).registers
                3 = divisor
            rw [zeroRegisterRange_below state (by
              simp [gcdCalleeRegisterBase])]
            simpa [divisor] using hright
          rw [canonicalGcdLoopFuel.eq_2 left right]
          change
            runNPOracleProgram canonicalGcdProgram maximumBits
                (9 + gcdCalleeSpan + bitSerialModFuel left divisor +
                  canonicalGcdLoopFuel divisor remainder + extra) state =
              some (euclideanGcd left divisor)
          rw [show
            9 + gcdCalleeSpan + bitSerialModFuel left divisor +
                canonicalGcdLoopFuel divisor remainder + extra =
              (8 + gcdCalleeSpan + bitSerialModFuel left divisor +
                canonicalGcdLoopFuel divisor remainder + extra) + 1 by
            omega]
          rw [run_branchZero_instruction canonicalGcdProgram_loop hpc]
          simp only [hright, divisor, if_neg (by omega : right + 1 ≠ 0)]
          rw [show
            8 + gcdCalleeSpan + bitSerialModFuel left divisor +
                canonicalGcdLoopFuel divisor remainder + extra =
              gcdCalleeSpan +
                (8 + bitSerialModFuel left divisor +
                  canonicalGcdLoopFuel divisor remainder + extra) by
            omega]
          apply run_resetProgramAt hbitsPositive
            canonicalGcdProgram_resetAt
          change
            runNPOracleProgram canonicalGcdProgram maximumBits
                (8 + bitSerialModFuel left divisor +
                  canonicalGcdLoopFuel divisor remainder + extra) resetState =
              some (euclideanGcd left divisor)
          rw [show
            8 + bitSerialModFuel left divisor +
                canonicalGcdLoopFuel divisor remainder + extra =
              (7 + bitSerialModFuel left divisor +
                canonicalGcdLoopFuel divisor remainder + extra) + 1 by
            omega]
          rw [run_pair_instruction canonicalGcdProgram_prepareRequest
            (by rfl) (by simp [hresetLeft, hresetRight, request])
            hrequestBits]
          change
            runNPOracleProgram canonicalGcdProgram maximumBits
                (7 + bitSerialModFuel left divisor +
                  canonicalGcdLoopFuel divisor remainder + extra)
                requestState =
              some (euclideanGcd left divisor)
          rw [show
            7 + bitSerialModFuel left divisor +
                canonicalGcdLoopFuel divisor remainder + extra =
              (6 + bitSerialModFuel left divisor +
                canonicalGcdLoopFuel divisor remainder + extra) + 1 by
            omega]
          rw [run_copy_instruction canonicalGcdProgram_loadRequest
            (by rfl) (by simp [requestState]) hrequestBits]
          change
            runNPOracleProgram canonicalGcdProgram maximumBits
                (6 + bitSerialModFuel left divisor +
                  canonicalGcdLoopFuel divisor remainder + extra)
                loadedRequest =
              some (euclideanGcd left divisor)
          rw [show
            6 + bitSerialModFuel left divisor +
                canonicalGcdLoopFuel divisor remainder + extra =
              (5 + bitSerialModFuel left divisor +
                canonicalGcdLoopFuel divisor remainder + extra) + 1 by
            omega]
          rw [run_copy_instruction canonicalGcdProgram_loadLength
            (by rfl) (by
              simp [loadedRequest, requestState, resetState,
                zeroRegisterRange_below, gcdCalleeRegisterBase, hlength])
            hlengthBits]
          change
            runNPOracleProgram canonicalGcdProgram maximumBits
                (5 + bitSerialModFuel left divisor +
                  canonicalGcdLoopFuel divisor remainder + extra)
                loadedLength =
              some (euclideanGcd left divisor)
          rw [show
            5 + bitSerialModFuel left divisor +
                canonicalGcdLoopFuel divisor remainder + extra =
              (4 + bitSerialModFuel left divisor +
                canonicalGcdLoopFuel divisor remainder + extra) + 1 by
            omega]
          rw [run_set_instruction canonicalGcdProgram_clearAccumulator
            (by rfl) (by simpa [natBitLength] using hbitsPositive)]
          change
            runNPOracleProgram canonicalGcdProgram maximumBits
                (4 + bitSerialModFuel left divisor +
                  canonicalGcdLoopFuel divisor remainder + extra) callEntry =
              some (euclideanGcd left divisor)
          rw [show
            4 + bitSerialModFuel left divisor +
                canonicalGcdLoopFuel divisor remainder + extra =
              bitSerialModFuel left divisor +
                (4 + canonicalGcdLoopFuel divisor remainder + extra) by
            omega]
          rw [hentryActive]
          apply run_callable_active callEntry.registers
            (by simp [gcdCalleeRegisterBase])
            (le_refl gcdCalleeSpan)
            canonicalGcdProgram_callableAt
            (run_bits_mono
              (run_bitSerialModProgram inputLength left divisor hpositive)
              hmoduloBits)
          · simpa [hentryAccumulator, remainder] using haccumulatorBits
          · intro haltState unused
            let atReturn :=
              (((relocateState gcdCalleeBase gcdCalleeRegisterBase
                callEntry.registers haltState).write 5
                  (Nat.pair (callEntry.registers 5) remainder)).jump
                    gcdReturnPc)
            let remainderState :=
              (atReturn.write 6 remainder).jump (gcdReturnPc + 1)
            let leftState :=
              (remainderState.write 2 divisor).jump (gcdReturnPc + 2)
            let rightState :=
              (leftState.write 3 remainder).jump (gcdReturnPc + 3)
            let loopState :=
              (rightState.write 7 0).jump gcdLoopPc
            have hatReturnAccumulator :
                (Nat.unpair (atReturn.registers 5)).2 = remainder := by
              simp [atReturn, hentryAccumulator]
            have hatReturnRight : atReturn.registers 3 = divisor := by
              simp [atReturn, relocateState, gcdCalleeRegisterBase,
                hentryRight, NPOracleState.write]
            have hatReturnScratch : atReturn.registers 7 = 0 := by
              simp [atReturn, relocateState, gcdCalleeRegisterBase,
                hentryScratch, NPOracleState.write]
            rw [show
              unused +
                  (4 + canonicalGcdLoopFuel divisor remainder + extra) =
                (unused + 3 + canonicalGcdLoopFuel divisor remainder +
                  extra) + 1 by omega]
            rw [run_unpairRight_instruction
              canonicalGcdProgram_unpackRemainder (by rfl)
              hatReturnAccumulator hremainderBits]
            change
              runNPOracleProgram canonicalGcdProgram maximumBits
                  (unused + 3 + canonicalGcdLoopFuel divisor remainder +
                    extra) remainderState =
                some (euclideanGcd left divisor)
            rw [show
              unused + 3 + canonicalGcdLoopFuel divisor remainder + extra =
                (unused + 2 + canonicalGcdLoopFuel divisor remainder +
                  extra) + 1 by omega]
            rw [run_copy_instruction canonicalGcdProgram_rotateLeft
              (by rfl) (by simp [remainderState, hatReturnRight])
              hdivisorBits]
            change
              runNPOracleProgram canonicalGcdProgram maximumBits
                  (unused + 2 + canonicalGcdLoopFuel divisor remainder +
                    extra) leftState =
                some (euclideanGcd left divisor)
            rw [show
              unused + 2 + canonicalGcdLoopFuel divisor remainder + extra =
                (unused + 1 + canonicalGcdLoopFuel divisor remainder +
                  extra) + 1 by omega]
            rw [run_copy_instruction canonicalGcdProgram_rotateRight
              (by rfl) (by simp [leftState, remainderState])
              hremainderBits]
            change
              runNPOracleProgram canonicalGcdProgram maximumBits
                  (unused + 1 + canonicalGcdLoopFuel divisor remainder +
                    extra) rightState =
                some (euclideanGcd left divisor)
            rw [show
              unused + 1 + canonicalGcdLoopFuel divisor remainder + extra =
                (unused + canonicalGcdLoopFuel divisor remainder + extra) +
                  1 by omega]
            rw [run_decrement_instruction (value := 0)
              canonicalGcdProgram_loopBack
              (by rfl) (by simp [rightState, leftState, remainderState,
                hatReturnScratch])
              (by simpa [natBitLength] using hbitsPositive)]
            change
              runNPOracleProgram canonicalGcdProgram maximumBits
                  (unused + canonicalGcdLoopFuel divisor remainder + extra)
                  loopState =
                some (euclideanGcd left divisor)
            have hrecursive :=
              inductionHypothesis remainder hremainderLt divisor
                (unused + extra) loopState hdivisorBound hremainderBound
                (by rfl)
                (by simp [loopState, rightState, leftState, remainderState,
                  atReturn, relocateState, gcdCalleeRegisterBase,
                  hentryLength, NPOracleState.write])
                (by simp [loopState, rightState, leftState])
                (by simp [loopState, rightState])
                (by simp [loopState])
            rw [show
              unused + canonicalGcdLoopFuel divisor remainder + extra =
                canonicalGcdLoopFuel divisor remainder +
                  (unused + extra) by omega]
            rw [euclideanGcd.eq_2 left right]
            simpa [divisor, remainder] using hrecursive

/-- Exact total execution of the fixed Euclidean controller.  The public width
depends only on the initial maximum magnitude, which every Euclidean state
preserves. -/
theorem run_canonicalGcdProgram (inputLength left right : ℕ) :
    runNPOracleProgram canonicalGcdProgram
        (canonicalGcdBits inputLength left right)
        (canonicalGcdFuel left right)
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (Nat.gcd left right) := by
  let magnitude := max left right
  let maximumBits := canonicalGcdEnvelopeBits inputLength magnitude
  let initial :=
    initialNPOracleState inputLength (Nat.pair left right)
  let leftState := (initial.write 2 left).jump 1
  let loopState := (leftState.write 3 right).jump gcdLoopPc
  have hleftBound : left ≤ magnitude := by
    simp [magnitude]
  have hrightBound : right ≤ magnitude := by
    simp [magnitude]
  have hleftBits : natBitLength left ≤ maximumBits :=
    value_bits_le_canonicalGcdEnvelope inputLength magnitude left hleftBound
  have hrightBits : natBitLength right ≤ maximumBits :=
    value_bits_le_canonicalGcdEnvelope inputLength magnitude right hrightBound
  change
    runNPOracleProgram canonicalGcdProgram maximumBits
        (2 + canonicalGcdLoopFuel left right) initial =
      some (Nat.gcd left right)
  rw [show
    2 + canonicalGcdLoopFuel left right =
      (1 + canonicalGcdLoopFuel left right) + 1 by omega]
  rw [run_unpairLeft_instruction canonicalGcdProgram_inputLeft (by rfl)
    (by simp [initial, initialNPOracleState]) hleftBits]
  change
    runNPOracleProgram canonicalGcdProgram maximumBits
        (1 + canonicalGcdLoopFuel left right) leftState =
      some (Nat.gcd left right)
  rw [show
    1 + canonicalGcdLoopFuel left right =
      canonicalGcdLoopFuel left right + 1 by omega]
  rw [run_unpairRight_instruction canonicalGcdProgram_inputRight (by rfl)
    (by simp [leftState, initial, initialNPOracleState]) hrightBits]
  change
    runNPOracleProgram canonicalGcdProgram maximumBits
        (canonicalGcdLoopFuel left right) loopState =
      some (Nat.gcd left right)
  have hloop :=
    run_canonicalGcdLoop inputLength magnitude maximumBits left right 0
      loopState hleftBound hrightBound (by rfl)
      (by simp [loopState, leftState, initial, initialNPOracleState])
      (by simp [loopState, leftState])
      (by simp [loopState])
      (by simp [loopState, leftState, initial, initialNPOracleState])
      (le_refl maximumBits)
  rw [euclideanGcd_eq_gcd] at hloop
  simpa using hloop

/-! ## The polynomial charge of the Euclidean controller

Each Euclidean step charges one relocated bit-serial remainder, whose budget is
linear in the numerator's binary width.  What remains is the step count: a
remainder is at most half of its own dividend, so two steps at least halve the
second operand and the controller runs for at most `2 * natBitLength right + 2`
steps.  Neither factor contains an operand magnitude. -/

/-- The uniform charge of one Euclidean step whose operands stay below
`bound`: the controller's fixed plumbing, its callee register bank, and the
width-linear bit-serial remainder. -/
def canonicalGcdStepCharge (bound : ℕ) : ℕ :=
  9 + gcdCalleeSpan + (13 * natBitLength bound + 10)

private theorem mod_le_half {left right : ℕ}
    (hpositive : 0 < right) (hle : right ≤ left) :
    left % right ≤ left / 2 := by
  have hmod : left % right < right := Nat.mod_lt _ hpositive
  by_cases hbig : 2 * right ≤ left
  · omega
  · have hsub : left % right = left - right := by
      rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
    omega

private theorem natBitLength_half_lt {value : ℕ} (hvalue : 2 ≤ value) :
    natBitLength (value / 2) < natBitLength value := by
  have hlog : 1 ≤ Nat.log 2 value :=
    Nat.log_pos (by norm_num) hvalue
  have hdiv : Nat.log 2 (value / 2) = Nat.log 2 value - 1 :=
    Nat.log_div_base 2 value
  unfold natBitLength
  omega

private theorem canonicalGcdLoopFuel_zero (left : ℕ) :
    canonicalGcdLoopFuel left 0 = 3 :=
  canonicalGcdLoopFuel.eq_1 left

private theorem canonicalGcdLoopFuel_succ (left divisor : ℕ) :
    canonicalGcdLoopFuel left (divisor + 1) =
      9 + gcdCalleeSpan + bitSerialModFuel left (divisor + 1) +
        canonicalGcdLoopFuel (divisor + 1) (left % (divisor + 1)) :=
  canonicalGcdLoopFuel.eq_2 left divisor

private theorem canonicalGcdStep_le
    (bound left right : ℕ) (hleft : left ≤ bound) :
    9 + gcdCalleeSpan + bitSerialModFuel left right ≤
      canonicalGcdStepCharge bound := by
  have hcharge := bitSerialModFuel_le_natBitLength left right
  have hmono : natBitLength left ≤ natBitLength bound :=
    natBitLength_mono hleft
  unfold canonicalGcdStepCharge
  omega

private theorem canonicalGcdLoopFuel_le_aux (bound right : ℕ) :
    ∀ left : ℕ, left ≤ bound → right ≤ bound →
      canonicalGcdLoopFuel left right ≤
        (2 * natBitLength right + 2) * canonicalGcdStepCharge bound + 3 := by
  induction right using Nat.strong_induction_on with
  | h right inductionHypothesis =>
      intro left hleft hright
      cases right with
      | zero =>
          rw [canonicalGcdLoopFuel_zero left]
          omega
      | succ divisor =>
          have hfirstStep :
              9 + gcdCalleeSpan + bitSerialModFuel left (divisor + 1) ≤
                canonicalGcdStepCharge bound :=
            canonicalGcdStep_le bound left (divisor + 1) hleft
          rw [canonicalGcdLoopFuel_succ left divisor]
          rcases Nat.eq_zero_or_pos (left % (divisor + 1)) with
            hzero | hpositive
          · rw [hzero, canonicalGcdLoopFuel_zero (divisor + 1)]
            have hfactor :
                1 * canonicalGcdStepCharge bound ≤
                  (2 * natBitLength (divisor + 1) + 2) *
                    canonicalGcdStepCharge bound :=
              Nat.mul_le_mul_right _ (by omega)
            omega
          · obtain ⟨tail, htail⟩ :=
              Nat.exists_eq_succ_of_ne_zero
                (by omega : left % (divisor + 1) ≠ 0)
            have htailEq : left % (divisor + 1) = tail + 1 := htail
            have hremainderLt : tail + 1 < divisor + 1 := by
              have hmod : left % (divisor + 1) < divisor + 1 :=
                Nat.mod_lt left (by omega)
              omega
            have hsecondStep :
                9 + gcdCalleeSpan +
                    bitSerialModFuel (divisor + 1) (tail + 1) ≤
                  canonicalGcdStepCharge bound :=
              canonicalGcdStep_le bound (divisor + 1) (tail + 1) hright
            have hhalf :
                (divisor + 1) % (tail + 1) ≤ (divisor + 1) / 2 :=
              mod_le_half (by omega) (by omega)
            have hnarrow :
                natBitLength ((divisor + 1) % (tail + 1)) <
                  natBitLength (divisor + 1) :=
              lt_of_le_of_lt (natBitLength_mono hhalf)
                (natBitLength_half_lt (by omega))
            have hnextLt : (divisor + 1) % (tail + 1) < divisor + 1 := by
              omega
            have hrecursive :=
              inductionHypothesis ((divisor + 1) % (tail + 1)) hnextLt
                (tail + 1) (by omega) (by omega)
            rw [htailEq, canonicalGcdLoopFuel_succ (divisor + 1) tail]
            refine le_trans
              (Nat.add_le_add hfirstStep
                (Nat.add_le_add hsecondStep hrecursive)) ?_
            have hexpand :
                canonicalGcdStepCharge bound +
                    (canonicalGcdStepCharge bound +
                      ((2 * natBitLength ((divisor + 1) % (tail + 1)) + 2) *
                        canonicalGcdStepCharge bound + 3)) =
                  (2 * natBitLength ((divisor + 1) % (tail + 1)) + 4) *
                    canonicalGcdStepCharge bound + 3 := by
              ring
            have hmonotone :
                (2 * natBitLength ((divisor + 1) % (tail + 1)) + 4) *
                    canonicalGcdStepCharge bound ≤
                  (2 * natBitLength (divisor + 1) + 2) *
                    canonicalGcdStepCharge bound :=
              Nat.mul_le_mul_right _ (by omega)
            rw [hexpand]
            exact Nat.add_le_add_right hmonotone 3

/-- **The Euclidean controller's charge is polynomial in the operand widths.**
Both the number of steps and the charge of each step are bounded by the binary
width of the operands; no operand magnitude survives. -/
theorem canonicalGcdLoopFuel_le (bound left right : ℕ)
    (hleft : left ≤ bound) (hright : right ≤ bound) :
    canonicalGcdLoopFuel left right ≤
      (2 * natBitLength right + 2) * canonicalGcdStepCharge bound + 3 :=
  canonicalGcdLoopFuel_le_aux bound right left hleft hright

theorem canonicalGcdFuel_le (bound left right : ℕ)
    (hleft : left ≤ bound) (hright : right ≤ bound) :
    canonicalGcdFuel left right ≤
      (2 * natBitLength bound + 2) * canonicalGcdStepCharge bound + 5 := by
  have hloop := canonicalGcdLoopFuel_le bound left right hleft hright
  have hmonotone :
      (2 * natBitLength right + 2) * canonicalGcdStepCharge bound ≤
        (2 * natBitLength bound + 2) * canonicalGcdStepCharge bound := by
    refine Nat.mul_le_mul_right _ ?_
    have hwidth : natBitLength right ≤ natBitLength bound :=
      natBitLength_mono hright
    omega
  unfold canonicalGcdFuel
  omega

/-! ## Fixed rational-field projection and canonical Nat stages -/

def rationalTupleOutput (raw : ℕ) : ℕ :=
  taggedTupleOutput 2 raw

def rationalTupleProgram : NPOracleProgram :=
  taggedTupleProgram 2

@[simp] theorem rationalTupleProgram_oracleFree :
    OracleFree rationalTupleProgram :=
  taggedTupleProgram_oracleFree 2

def rationalTupleFuel : ℕ :=
  taggedTupleFuel 2

def rationalTupleBits (inputLength raw : ℕ) : ℕ :=
  taggedTupleBits inputLength 2 raw

theorem run_rationalTupleProgram (inputLength raw : ℕ) :
    runNPOracleProgram rationalTupleProgram
        (rationalTupleBits inputLength raw) rationalTupleFuel
        (initialNPOracleState inputLength raw) =
      some (rationalTupleOutput raw) :=
  run_taggedTupleProgram inputLength 2 raw

def rationalTupleFlag (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalTupleOutput raw)).1

def rationalTupleFields (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalTupleOutput raw)).2

def rationalNumeratorFrame (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalTupleFields raw)).1

def rationalNumeratorCode (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalNumeratorFrame raw)).2

def rationalDenominatorCode (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalTupleFields raw)).2

def rationalSign (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalNumeratorCode raw)).1

def rationalMagnitudeCode (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalNumeratorCode raw)).2

def rationalProjectionContext (raw : ℕ) : ℕ :=
  Nat.pair (rationalTupleFlag raw)
    (Nat.pair (rationalSign raw) (rationalDenominatorCode raw))

def rationalProjectionOutput (raw : ℕ) : ℕ :=
  Nat.pair (rationalMagnitudeCode raw) (rationalProjectionContext raw)

def rationalProjectionProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 4 5 4
  , .unpairRight 3 6 5
  , .unpairLeft 5 7 6
  , .unpairRight 5 8 7
  , .pair 7 6 9 8
  , .pair 2 9 10 9
  , .pair 8 10 0 10
  , .halt 0
  ]

@[simp] theorem rationalProjectionProgram_oracleFree :
    OracleFree rationalProjectionProgram := by
  rfl

def rationalProjectionFuel : ℕ := 11

private def rationalProjectionValues
    (inputLength raw : ℕ) : List ℕ :=
  [ inputLength
  , rationalTupleOutput raw
  , rationalTupleFlag raw
  , rationalTupleFields raw
  , rationalNumeratorFrame raw
  , rationalNumeratorCode raw
  , rationalDenominatorCode raw
  , rationalSign raw
  , rationalMagnitudeCode raw
  , Nat.pair (rationalSign raw) (rationalDenominatorCode raw)
  , rationalProjectionContext raw
  , rationalProjectionOutput raw
  ]

def rationalProjectionBits (inputLength raw : ℕ) : ℕ :=
  (rationalProjectionValues inputLength raw).map natBitLength |>.foldr max 1

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
      · exact le_max_left _ _
      · exact (inductionHypothesis htail).trans (le_max_right _ _)

private theorem rationalProjectionValue_bits
    (inputLength raw value : ℕ)
    (hvalue : value ∈ rationalProjectionValues inputLength raw) :
    natBitLength value ≤ rationalProjectionBits inputLength raw :=
  bitLength_le_foldr_max_of_mem hvalue

theorem run_rationalProjectionProgram (inputLength raw : ℕ) :
    runNPOracleProgram rationalProjectionProgram
        (rationalProjectionBits inputLength raw) rationalProjectionFuel
        (initialNPOracleState inputLength (rationalTupleOutput raw)) =
      some (rationalProjectionOutput raw) := by
  have hflag :
      natBitLength (rationalTupleFlag raw) ≤
        rationalProjectionBits inputLength raw :=
    rationalProjectionValue_bits inputLength raw _ (by
      simp [rationalProjectionValues])
  have hfields :
      natBitLength (rationalTupleFields raw) ≤
        rationalProjectionBits inputLength raw :=
    rationalProjectionValue_bits inputLength raw _ (by
      simp [rationalProjectionValues])
  have hframe :
      natBitLength (rationalNumeratorFrame raw) ≤
        rationalProjectionBits inputLength raw :=
    rationalProjectionValue_bits inputLength raw _ (by
      simp [rationalProjectionValues])
  have hnumerator :
      natBitLength (rationalNumeratorCode raw) ≤
        rationalProjectionBits inputLength raw :=
    rationalProjectionValue_bits inputLength raw _ (by
      simp [rationalProjectionValues])
  have hdenominator :
      natBitLength (rationalDenominatorCode raw) ≤
        rationalProjectionBits inputLength raw :=
    rationalProjectionValue_bits inputLength raw _ (by
      simp [rationalProjectionValues])
  have hsign :
      natBitLength (rationalSign raw) ≤
        rationalProjectionBits inputLength raw :=
    rationalProjectionValue_bits inputLength raw _ (by
      simp [rationalProjectionValues])
  have hmagnitude :
      natBitLength (rationalMagnitudeCode raw) ≤
        rationalProjectionBits inputLength raw :=
    rationalProjectionValue_bits inputLength raw _ (by
      simp [rationalProjectionValues])
  have hsignDenominator :
      natBitLength
          (Nat.pair (rationalSign raw) (rationalDenominatorCode raw)) ≤
        rationalProjectionBits inputLength raw :=
    rationalProjectionValue_bits inputLength raw _ (by
      simp [rationalProjectionValues])
  have hcontext :
      natBitLength (rationalProjectionContext raw) ≤
        rationalProjectionBits inputLength raw :=
    rationalProjectionValue_bits inputLength raw _ (by
      simp [rationalProjectionValues])
  have houtput :
      natBitLength (rationalProjectionOutput raw) ≤
        rationalProjectionBits inputLength raw :=
    rationalProjectionValue_bits inputLength raw _ (by
      simp [rationalProjectionValues])
  have hflag' :
      natBitLength (Nat.unpair (rationalTupleOutput raw)).1 ≤
        rationalProjectionBits inputLength raw := by
    simpa [rationalTupleFlag] using hflag
  have hfields' :
      natBitLength (Nat.unpair (rationalTupleOutput raw)).2 ≤
        rationalProjectionBits inputLength raw := by
    simpa [rationalTupleFields] using hfields
  have hframe' :
      natBitLength
          (Nat.unpair (Nat.unpair (rationalTupleOutput raw)).2).1 ≤
        rationalProjectionBits inputLength raw := by
    simpa [rationalNumeratorFrame, rationalTupleFields] using hframe
  have hnumerator' :
      natBitLength
          (Nat.unpair
            (Nat.unpair
              (Nat.unpair (rationalTupleOutput raw)).2).1).2 ≤
        rationalProjectionBits inputLength raw := by
    simpa [rationalNumeratorCode, rationalNumeratorFrame,
      rationalTupleFields] using hnumerator
  have hdenominator' :
      natBitLength
          (Nat.unpair (Nat.unpair (rationalTupleOutput raw)).2).2 ≤
        rationalProjectionBits inputLength raw := by
    simpa [rationalDenominatorCode, rationalTupleFields] using hdenominator
  have hsign' :
      natBitLength
          (Nat.unpair
            (Nat.unpair
              (Nat.unpair
                (Nat.unpair (rationalTupleOutput raw)).2).1).2).1 ≤
        rationalProjectionBits inputLength raw := by
    simpa [rationalSign, rationalNumeratorCode, rationalNumeratorFrame,
      rationalTupleFields] using hsign
  have hmagnitude' :
      natBitLength
          (Nat.unpair
            (Nat.unpair
              (Nat.unpair
                (Nat.unpair (rationalTupleOutput raw)).2).1).2).2 ≤
        rationalProjectionBits inputLength raw := by
    simpa [rationalMagnitudeCode, rationalNumeratorCode,
      rationalNumeratorFrame, rationalTupleFields] using hmagnitude
  have hsignDenominator' :
      natBitLength
          (Nat.pair
            (Nat.unpair
              (Nat.unpair
                (Nat.unpair
                  (Nat.unpair (rationalTupleOutput raw)).2).1).2).1
            (Nat.unpair (Nat.unpair (rationalTupleOutput raw)).2).2) ≤
        rationalProjectionBits inputLength raw := by
    simpa [rationalSign, rationalNumeratorCode, rationalNumeratorFrame,
      rationalDenominatorCode, rationalTupleFields] using hsignDenominator
  have hcontext' :
      natBitLength
          (Nat.pair (Nat.unpair (rationalTupleOutput raw)).1
            (Nat.pair
              (Nat.unpair
                (Nat.unpair
                  (Nat.unpair
                    (Nat.unpair (rationalTupleOutput raw)).2).1).2).1
              (Nat.unpair (Nat.unpair (rationalTupleOutput raw)).2).2)) ≤
        rationalProjectionBits inputLength raw := by
    simpa [rationalProjectionContext, rationalTupleFlag, rationalSign,
      rationalNumeratorCode, rationalNumeratorFrame,
      rationalDenominatorCode, rationalTupleFields] using hcontext
  have houtput' :
      natBitLength
          (Nat.pair
            (Nat.unpair
              (Nat.unpair
                (Nat.unpair
                  (Nat.unpair (rationalTupleOutput raw)).2).1).2).2
            (Nat.pair (Nat.unpair (rationalTupleOutput raw)).1
              (Nat.pair
                (Nat.unpair
                  (Nat.unpair
                    (Nat.unpair
                      (Nat.unpair (rationalTupleOutput raw)).2).1).2).1
                (Nat.unpair (Nat.unpair (rationalTupleOutput raw)).2).2))) ≤
        rationalProjectionBits inputLength raw := by
    simpa [rationalProjectionOutput, rationalProjectionContext,
      rationalMagnitudeCode, rationalTupleFlag, rationalSign,
      rationalNumeratorCode, rationalNumeratorFrame,
      rationalDenominatorCode, rationalTupleFields] using houtput
  simp [rationalProjectionProgram, rationalProjectionFuel,
    runNPOracleProgram, initialNPOracleState, NPOracleState.boundedWrite,
    rationalTupleFlag, rationalTupleFields, rationalNumeratorFrame,
    rationalNumeratorCode, rationalDenominatorCode, rationalSign,
    rationalMagnitudeCode, rationalProjectionContext,
    rationalProjectionOutput, hflag', hfields', hframe', hnumerator',
    hdenominator', hsign', hmagnitude', hsignDenominator', hcontext',
    houtput']

def rationalMagnitudeStageOutput (raw : ℕ) : ℕ :=
  Nat.pair
    (canonicalNatValidationOutput (rationalMagnitudeCode raw))
    (rationalProjectionContext raw)

def rationalMagnitudeStageProgram : NPOracleProgram :=
  preserveRightProgram canonicalNatValidationProgram

@[simp] theorem rationalMagnitudeStageProgram_oracleFree :
    OracleFree rationalMagnitudeStageProgram :=
  preserveRightProgram_oracleFree canonicalNatValidationProgram
    canonicalNatValidationProgram_oracleFree

def rationalMagnitudeStageFuel (raw : ℕ) : ℕ :=
  preserveRightFuel <|
    canonicalNatValidationFuel (rationalMagnitudeCode raw)

def rationalMagnitudeStageBits (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (canonicalNatValidationBits inputLength (rationalMagnitudeCode raw))
    (rationalMagnitudeCode raw)
    (rationalProjectionContext raw)
    (canonicalNatValidationOutput (rationalMagnitudeCode raw))

theorem run_rationalMagnitudeStageProgram (inputLength raw : ℕ) :
    runNPOracleProgram rationalMagnitudeStageProgram
        (rationalMagnitudeStageBits inputLength raw)
        (rationalMagnitudeStageFuel raw)
        (initialNPOracleState inputLength (rationalProjectionOutput raw)) =
      some (rationalMagnitudeStageOutput raw) := by
  exact run_preserveRightProgram canonicalNatValidationProgram inputLength
    (canonicalNatValidationBits inputLength (rationalMagnitudeCode raw))
    (canonicalNatValidationFuel (rationalMagnitudeCode raw))
    (rationalMagnitudeCode raw)
    (rationalProjectionContext raw)
    (canonicalNatValidationOutput (rationalMagnitudeCode raw))
    (run_canonicalNatValidationProgram inputLength (rationalMagnitudeCode raw))

def rationalMagnitudeValidation (raw : ℕ) : ℕ :=
  canonicalNatValidationOutput (rationalMagnitudeCode raw)

def rationalDenominatorLoweringContext (raw : ℕ) : ℕ :=
  Nat.pair (rationalMagnitudeValidation raw)
    (Nat.pair (rationalTupleFlag raw) (rationalSign raw))

def rationalDenominatorLoweringOutput (raw : ℕ) : ℕ :=
  Nat.pair (rationalDenominatorCode raw)
    (rationalDenominatorLoweringContext raw)

def rationalDenominatorLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .pair 4 6 8 7
  , .pair 2 8 9 8
  , .pair 7 9 0 9
  , .halt 0
  ]

@[simp] theorem rationalDenominatorLoweringProgram_oracleFree :
    OracleFree rationalDenominatorLoweringProgram := by
  rfl

def rationalDenominatorLoweringFuel : ℕ := 10

private def rationalDenominatorLoweringValues
    (inputLength raw : ℕ) : List ℕ :=
  [ inputLength
  , rationalMagnitudeStageOutput raw
  , rationalMagnitudeValidation raw
  , rationalProjectionContext raw
  , rationalTupleFlag raw
  , Nat.pair (rationalSign raw) (rationalDenominatorCode raw)
  , rationalSign raw
  , rationalDenominatorCode raw
  , Nat.pair (rationalTupleFlag raw) (rationalSign raw)
  , rationalDenominatorLoweringContext raw
  , rationalDenominatorLoweringOutput raw
  ]

def rationalDenominatorLoweringBits (inputLength raw : ℕ) : ℕ :=
  (rationalDenominatorLoweringValues inputLength raw).map natBitLength
    |>.foldr max 1

private theorem rationalDenominatorLoweringValue_bits
    (inputLength raw value : ℕ)
    (hvalue :
      value ∈ rationalDenominatorLoweringValues inputLength raw) :
    natBitLength value ≤
      rationalDenominatorLoweringBits inputLength raw :=
  bitLength_le_foldr_max_of_mem hvalue

theorem run_rationalDenominatorLoweringProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram rationalDenominatorLoweringProgram
        (rationalDenominatorLoweringBits inputLength raw)
        rationalDenominatorLoweringFuel
        (initialNPOracleState inputLength
          (rationalMagnitudeStageOutput raw)) =
      some (rationalDenominatorLoweringOutput raw) := by
  have hmagnitude :
      natBitLength (rationalMagnitudeValidation raw) ≤
        rationalDenominatorLoweringBits inputLength raw :=
    rationalDenominatorLoweringValue_bits inputLength raw _ (by
      simp [rationalDenominatorLoweringValues])
  have hmagnitudeCode :
      natBitLength
          (canonicalNatValidationOutput (rationalMagnitudeCode raw)) ≤
        rationalDenominatorLoweringBits inputLength raw := by
    simpa only [rationalMagnitudeValidation] using hmagnitude
  have hprojection :
      natBitLength (rationalProjectionContext raw) ≤
        rationalDenominatorLoweringBits inputLength raw :=
    rationalDenominatorLoweringValue_bits inputLength raw _ (by
      simp [rationalDenominatorLoweringValues])
  have hprojectionCode :
      natBitLength
          (Nat.pair (rationalTupleFlag raw)
            (Nat.pair (rationalSign raw) (rationalDenominatorCode raw))) ≤
        rationalDenominatorLoweringBits inputLength raw := by
    simpa only [rationalProjectionContext] using hprojection
  have htuple :
      natBitLength (rationalTupleFlag raw) ≤
        rationalDenominatorLoweringBits inputLength raw :=
    rationalDenominatorLoweringValue_bits inputLength raw _ (by
      simp [rationalDenominatorLoweringValues])
  have hsignDenominator :
      natBitLength
          (Nat.pair (rationalSign raw) (rationalDenominatorCode raw)) ≤
        rationalDenominatorLoweringBits inputLength raw :=
    rationalDenominatorLoweringValue_bits inputLength raw _ (by
      simp [rationalDenominatorLoweringValues])
  have hsign :
      natBitLength (rationalSign raw) ≤
        rationalDenominatorLoweringBits inputLength raw :=
    rationalDenominatorLoweringValue_bits inputLength raw _ (by
      simp [rationalDenominatorLoweringValues])
  have hdenominator :
      natBitLength (rationalDenominatorCode raw) ≤
        rationalDenominatorLoweringBits inputLength raw :=
    rationalDenominatorLoweringValue_bits inputLength raw _ (by
      simp [rationalDenominatorLoweringValues])
  have htupleSign :
      natBitLength (Nat.pair (rationalTupleFlag raw) (rationalSign raw)) ≤
        rationalDenominatorLoweringBits inputLength raw :=
    rationalDenominatorLoweringValue_bits inputLength raw _ (by
      simp [rationalDenominatorLoweringValues])
  have hcontext :
      natBitLength (rationalDenominatorLoweringContext raw) ≤
        rationalDenominatorLoweringBits inputLength raw :=
    rationalDenominatorLoweringValue_bits inputLength raw _ (by
      simp [rationalDenominatorLoweringValues])
  have hcontextCode :
      natBitLength
          (Nat.pair
            (canonicalNatValidationOutput (rationalMagnitudeCode raw))
            (Nat.pair (rationalTupleFlag raw) (rationalSign raw))) ≤
        rationalDenominatorLoweringBits inputLength raw := by
    simpa only [rationalDenominatorLoweringContext,
      rationalMagnitudeValidation] using hcontext
  have houtput :
      natBitLength (rationalDenominatorLoweringOutput raw) ≤
        rationalDenominatorLoweringBits inputLength raw :=
    rationalDenominatorLoweringValue_bits inputLength raw _ (by
      simp [rationalDenominatorLoweringValues])
  have houtputCode :
      natBitLength
          (Nat.pair (rationalDenominatorCode raw)
            (Nat.pair
              (canonicalNatValidationOutput (rationalMagnitudeCode raw))
              (Nat.pair (rationalTupleFlag raw) (rationalSign raw)))) ≤
        rationalDenominatorLoweringBits inputLength raw := by
    simpa only [rationalDenominatorLoweringOutput,
      rationalDenominatorLoweringContext, rationalMagnitudeValidation] using
        houtput
  simp [rationalDenominatorLoweringProgram,
    rationalDenominatorLoweringFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    rationalMagnitudeStageOutput, rationalMagnitudeValidation,
    rationalProjectionContext, rationalDenominatorLoweringContext,
    rationalDenominatorLoweringOutput, hmagnitudeCode, hprojectionCode, htuple,
    hsignDenominator, hsign, hdenominator, htupleSign, hcontextCode,
    houtputCode]

def rationalDenominatorValidation (raw : ℕ) : ℕ :=
  canonicalNatValidationOutput (rationalDenominatorCode raw)

def rationalDenominatorStageOutput (raw : ℕ) : ℕ :=
  Nat.pair (rationalDenominatorValidation raw)
    (rationalDenominatorLoweringContext raw)

def rationalDenominatorStageProgram : NPOracleProgram :=
  preserveRightProgram canonicalNatValidationProgram

@[simp] theorem rationalDenominatorStageProgram_oracleFree :
    OracleFree rationalDenominatorStageProgram :=
  preserveRightProgram_oracleFree canonicalNatValidationProgram
    canonicalNatValidationProgram_oracleFree

def rationalDenominatorStageFuel (raw : ℕ) : ℕ :=
  preserveRightFuel <|
    canonicalNatValidationFuel (rationalDenominatorCode raw)

def rationalDenominatorStageBits (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (canonicalNatValidationBits inputLength (rationalDenominatorCode raw))
    (rationalDenominatorCode raw)
    (rationalDenominatorLoweringContext raw)
    (rationalDenominatorValidation raw)

theorem run_rationalDenominatorStageProgram (inputLength raw : ℕ) :
    runNPOracleProgram rationalDenominatorStageProgram
        (rationalDenominatorStageBits inputLength raw)
        (rationalDenominatorStageFuel raw)
        (initialNPOracleState inputLength
          (rationalDenominatorLoweringOutput raw)) =
      some (rationalDenominatorStageOutput raw) := by
  exact run_preserveRightProgram canonicalNatValidationProgram inputLength
    (canonicalNatValidationBits inputLength (rationalDenominatorCode raw))
    (canonicalNatValidationFuel (rationalDenominatorCode raw))
    (rationalDenominatorCode raw)
    (rationalDenominatorLoweringContext raw)
    (rationalDenominatorValidation raw)
    (run_canonicalNatValidationProgram inputLength
      (rationalDenominatorCode raw))

def rationalMagnitudeValue (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalMagnitudeValidation raw)).2

def rationalDenominatorValue (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalDenominatorValidation raw)).2

def rationalGcdRequest (raw : ℕ) : ℕ :=
  Nat.pair (rationalMagnitudeValue raw) (rationalDenominatorValue raw)

def rationalGcdLoweringOutput (raw : ℕ) : ℕ :=
  Nat.pair (rationalGcdRequest raw) (rationalDenominatorStageOutput raw)

def rationalGcdLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 2 5 4
  , .unpairRight 4 6 5
  , .pair 6 5 7 6
  , .pair 7 0 0 7
  , .halt 0
  ]

@[simp] theorem rationalGcdLoweringProgram_oracleFree :
    OracleFree rationalGcdLoweringProgram := by
  rfl

def rationalGcdLoweringFuel : ℕ := 8

private def rationalGcdLoweringValues
    (inputLength raw : ℕ) : List ℕ :=
  [ inputLength
  , rationalDenominatorStageOutput raw
  , rationalDenominatorValidation raw
  , rationalDenominatorLoweringContext raw
  , rationalMagnitudeValidation raw
  , rationalDenominatorValue raw
  , rationalMagnitudeValue raw
  , rationalGcdRequest raw
  , rationalGcdLoweringOutput raw
  ]

def rationalGcdLoweringBits (inputLength raw : ℕ) : ℕ :=
  (rationalGcdLoweringValues inputLength raw).map natBitLength
    |>.foldr max 1

private theorem rationalGcdLoweringValue_bits
    (inputLength raw value : ℕ)
    (hvalue : value ∈ rationalGcdLoweringValues inputLength raw) :
    natBitLength value ≤ rationalGcdLoweringBits inputLength raw :=
  bitLength_le_foldr_max_of_mem hvalue

theorem run_rationalGcdLoweringProgram (inputLength raw : ℕ) :
    runNPOracleProgram rationalGcdLoweringProgram
        (rationalGcdLoweringBits inputLength raw)
        rationalGcdLoweringFuel
        (initialNPOracleState inputLength
          (rationalDenominatorStageOutput raw)) =
      some (rationalGcdLoweringOutput raw) := by
  have hdenominatorValidation :
      natBitLength (rationalDenominatorValidation raw) ≤
        rationalGcdLoweringBits inputLength raw :=
    rationalGcdLoweringValue_bits inputLength raw _ (by
      simp [rationalGcdLoweringValues])
  have hcontext :
      natBitLength (rationalDenominatorLoweringContext raw) ≤
        rationalGcdLoweringBits inputLength raw :=
    rationalGcdLoweringValue_bits inputLength raw _ (by
      simp [rationalGcdLoweringValues])
  have hcontextCode :
      natBitLength
          (Nat.pair (rationalMagnitudeValidation raw)
            (Nat.pair (rationalTupleFlag raw) (rationalSign raw))) ≤
        rationalGcdLoweringBits inputLength raw := by
    simpa only [rationalDenominatorLoweringContext] using hcontext
  have hmagnitudeValidation :
      natBitLength (rationalMagnitudeValidation raw) ≤
        rationalGcdLoweringBits inputLength raw :=
    rationalGcdLoweringValue_bits inputLength raw _ (by
      simp [rationalGcdLoweringValues])
  have hdenominator :
      natBitLength (rationalDenominatorValue raw) ≤
        rationalGcdLoweringBits inputLength raw :=
    rationalGcdLoweringValue_bits inputLength raw _ (by
      simp [rationalGcdLoweringValues])
  have hdenominatorCode :
      natBitLength (Nat.unpair (rationalDenominatorValidation raw)).2 ≤
        rationalGcdLoweringBits inputLength raw := by
    simpa only [rationalDenominatorValue] using hdenominator
  have hmagnitude :
      natBitLength (rationalMagnitudeValue raw) ≤
        rationalGcdLoweringBits inputLength raw :=
    rationalGcdLoweringValue_bits inputLength raw _ (by
      simp [rationalGcdLoweringValues])
  have hmagnitudeCode :
      natBitLength (Nat.unpair (rationalMagnitudeValidation raw)).2 ≤
        rationalGcdLoweringBits inputLength raw := by
    simpa only [rationalMagnitudeValue] using hmagnitude
  have hrequest :
      natBitLength (rationalGcdRequest raw) ≤
        rationalGcdLoweringBits inputLength raw :=
    rationalGcdLoweringValue_bits inputLength raw _ (by
      simp [rationalGcdLoweringValues])
  have houtput :
      natBitLength (rationalGcdLoweringOutput raw) ≤
        rationalGcdLoweringBits inputLength raw :=
    rationalGcdLoweringValue_bits inputLength raw _ (by
      simp [rationalGcdLoweringValues])
  have hrequestCode :
      natBitLength
          (Nat.pair
            (Nat.unpair (rationalMagnitudeValidation raw)).2
            (Nat.unpair (rationalDenominatorValidation raw)).2) ≤
        rationalGcdLoweringBits inputLength raw := by
    simpa only [rationalGcdRequest, rationalMagnitudeValue,
      rationalDenominatorValue] using hrequest
  have houtputCode :
      natBitLength
          (Nat.pair
            (Nat.pair
              (Nat.unpair (rationalMagnitudeValidation raw)).2
              (Nat.unpair (rationalDenominatorValidation raw)).2)
            (rationalDenominatorStageOutput raw)) ≤
        rationalGcdLoweringBits inputLength raw := by
    simpa only [rationalGcdLoweringOutput, rationalGcdRequest,
      rationalMagnitudeValue, rationalDenominatorValue] using houtput
  have houtputExpanded :
      natBitLength
          (Nat.pair
            (Nat.pair
              (Nat.unpair (rationalMagnitudeValidation raw)).2
              (Nat.unpair (rationalDenominatorValidation raw)).2)
            (Nat.pair (rationalDenominatorValidation raw)
              (Nat.pair (rationalMagnitudeValidation raw)
                (Nat.pair (rationalTupleFlag raw) (rationalSign raw))))) ≤
        rationalGcdLoweringBits inputLength raw := by
    simpa only [rationalDenominatorStageOutput,
      rationalDenominatorLoweringContext] using houtputCode
  simp [rationalGcdLoweringProgram, rationalGcdLoweringFuel,
    runNPOracleProgram, initialNPOracleState, NPOracleState.boundedWrite,
    rationalDenominatorStageOutput, rationalDenominatorLoweringContext,
    rationalGcdLoweringOutput, rationalGcdRequest, rationalMagnitudeValue,
    rationalDenominatorValue, hdenominatorValidation, hcontextCode,
    hmagnitudeValidation, hdenominatorCode, hmagnitudeCode, hrequestCode,
    houtputExpanded]

def rationalGcdValue (raw : ℕ) : ℕ :=
  Nat.gcd (rationalMagnitudeValue raw) (rationalDenominatorValue raw)

def rationalGcdStageOutput (raw : ℕ) : ℕ :=
  Nat.pair (rationalGcdValue raw) (rationalDenominatorStageOutput raw)

def rationalGcdStageProgram : NPOracleProgram :=
  preserveRightProgram canonicalGcdProgram

@[simp] theorem rationalGcdStageProgram_oracleFree :
    OracleFree rationalGcdStageProgram :=
  preserveRightProgram_oracleFree canonicalGcdProgram
    canonicalGcdProgram_oracleFree

def rationalGcdStageFuel (raw : ℕ) : ℕ :=
  preserveRightFuel <|
    canonicalGcdFuel (rationalMagnitudeValue raw)
      (rationalDenominatorValue raw)

def rationalGcdStageBits (inputLength raw : ℕ) : ℕ :=
  preserveRightBits
    (canonicalGcdBits inputLength (rationalMagnitudeValue raw)
      (rationalDenominatorValue raw))
    (rationalGcdRequest raw)
    (rationalDenominatorStageOutput raw)
    (rationalGcdValue raw)

theorem run_rationalGcdStageProgram (inputLength raw : ℕ) :
    runNPOracleProgram rationalGcdStageProgram
        (rationalGcdStageBits inputLength raw)
        (rationalGcdStageFuel raw)
        (initialNPOracleState inputLength (rationalGcdLoweringOutput raw)) =
      some (rationalGcdStageOutput raw) := by
  exact run_preserveRightProgram canonicalGcdProgram inputLength
    (canonicalGcdBits inputLength (rationalMagnitudeValue raw)
      (rationalDenominatorValue raw))
    (canonicalGcdFuel (rationalMagnitudeValue raw)
      (rationalDenominatorValue raw))
    (rationalGcdRequest raw)
    (rationalDenominatorStageOutput raw)
    (rationalGcdValue raw)
    (run_canonicalGcdProgram inputLength (rationalMagnitudeValue raw)
      (rationalDenominatorValue raw))

def rationalMagnitudeFlag (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalMagnitudeValidation raw)).1

def rationalDenominatorFlag (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalDenominatorValidation raw)).1

def rationalValidationAccepts (raw : ℕ) : Prop :=
  rationalTupleFlag raw ≠ 0 ∧
  rationalMagnitudeFlag raw ≠ 0 ∧
  rationalDenominatorFlag raw ≠ 0 ∧
  rationalDenominatorValue raw ≠ 0 ∧
  rationalGcdValue raw = 1 ∧
  (rationalSign raw = 0 ∨
    (rationalSign raw = 1 ∧ rationalMagnitudeValue raw ≠ 0))

private instance (raw : ℕ) : Decidable (rationalValidationAccepts raw) := by
  unfold rationalValidationAccepts
  infer_instance

def rationalValidationOutput (raw : ℕ) : ℕ :=
  if rationalValidationAccepts raw then
    Nat.pair 1 <|
      Nat.pair (rationalSign raw) <|
        Nat.pair (rationalMagnitudeValue raw) (rationalDenominatorValue raw)
  else
    0

def rationalValidationGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .unpairLeft 4 10 9
  , .unpairRight 4 11 10
  , .unpairLeft 6 12 11
  , .unpairRight 6 13 12
  , .branchZero 8 29 13
  , .branchZero 12 29 14
  , .branchZero 10 29 15
  , .branchZero 11 29 16
  , .branchZero 2 29 17
  , .decrement 2 18
  , .branchZero 2 19 29
  , .branchZero 9 24 20
  , .copy 9 14 21
  , .decrement 14 22
  , .branchZero 14 23 29
  , .branchZero 13 29 24
  , .set 15 1 25
  , .pair 13 11 16 26
  , .pair 9 16 17 27
  , .pair 15 17 0 28
  , .halt 0
  , .set 0 0 28
  ]

@[simp] theorem rationalValidationGateProgram_oracleFree :
    OracleFree rationalValidationGateProgram := by
  rfl

def rationalValidationGateFuel : ℕ := 29

private def rationalValidationGateValues
    (inputLength raw : ℕ) : List ℕ :=
  [ inputLength
  , rationalGcdStageOutput raw
  , rationalGcdValue raw
  , rationalDenominatorStageOutput raw
  , rationalDenominatorValidation raw
  , rationalDenominatorLoweringContext raw
  , rationalMagnitudeValidation raw
  , Nat.pair (rationalTupleFlag raw) (rationalSign raw)
  , rationalTupleFlag raw
  , rationalSign raw
  , rationalDenominatorFlag raw
  , rationalDenominatorValue raw
  , rationalMagnitudeFlag raw
  , rationalMagnitudeValue raw
  , (rationalGcdValue raw).pred
  , (rationalSign raw).pred
  , Nat.pair (rationalMagnitudeValue raw) (rationalDenominatorValue raw)
  , Nat.pair (rationalSign raw)
      (Nat.pair (rationalMagnitudeValue raw) (rationalDenominatorValue raw))
  , Nat.pair 1
      (Nat.pair (rationalSign raw)
        (Nat.pair (rationalMagnitudeValue raw)
          (rationalDenominatorValue raw)))
  , rationalValidationOutput raw
  , 0
  , 1
  ]

def rationalValidationGateBits (inputLength raw : ℕ) : ℕ :=
  (rationalValidationGateValues inputLength raw).map natBitLength
    |>.foldr max 1

private theorem rationalValidationGateValue_bits
    (inputLength raw value : ℕ)
    (hvalue : value ∈ rationalValidationGateValues inputLength raw) :
    natBitLength value ≤ rationalValidationGateBits inputLength raw :=
  bitLength_le_foldr_max_of_mem hvalue

private def rationalValidationGateParsedState
    (inputLength raw : ℕ) : NPOracleState :=
  let state₀ :=
    initialNPOracleState inputLength (rationalGcdStageOutput raw)
  let state₁ := (state₀.write 2 (rationalGcdValue raw)).jump 1
  let state₂ :=
    (state₁.write 3 (rationalDenominatorStageOutput raw)).jump 2
  let state₃ :=
    (state₂.write 4 (rationalDenominatorValidation raw)).jump 3
  let state₄ :=
    (state₃.write 5 (rationalDenominatorLoweringContext raw)).jump 4
  let state₅ :=
    (state₄.write 6 (rationalMagnitudeValidation raw)).jump 5
  let state₆ :=
    (state₅.write 7
      (Nat.pair (rationalTupleFlag raw) (rationalSign raw))).jump 6
  let state₇ := (state₆.write 8 (rationalTupleFlag raw)).jump 7
  let state₈ := (state₇.write 9 (rationalSign raw)).jump 8
  let state₉ := (state₈.write 10 (rationalDenominatorFlag raw)).jump 9
  let state₁₀ :=
    (state₉.write 11 (rationalDenominatorValue raw)).jump 10
  let state₁₁ := (state₁₀.write 12 (rationalMagnitudeFlag raw)).jump 11
  (state₁₁.write 13 (rationalMagnitudeValue raw)).jump 12

@[simp] private theorem rationalValidationGateParsedState_pc
    (inputLength raw : ℕ) :
    (rationalValidationGateParsedState inputLength raw).pc = 12 := by
  rfl

@[simp] private theorem rationalValidationGateParsedState_register2
    (inputLength raw : ℕ) :
    (rationalValidationGateParsedState inputLength raw).registers 2 =
      rationalGcdValue raw := by
  simp [rationalValidationGateParsedState, initialNPOracleState,
    NPOracleState.write, NPOracleState.jump]

@[simp] private theorem rationalValidationGateParsedState_register8
    (inputLength raw : ℕ) :
    (rationalValidationGateParsedState inputLength raw).registers 8 =
      rationalTupleFlag raw := by
  simp [rationalValidationGateParsedState, initialNPOracleState,
    NPOracleState.write, NPOracleState.jump]

@[simp] private theorem rationalValidationGateParsedState_register9
    (inputLength raw : ℕ) :
    (rationalValidationGateParsedState inputLength raw).registers 9 =
      rationalSign raw := by
  simp [rationalValidationGateParsedState, initialNPOracleState,
    NPOracleState.write, NPOracleState.jump]

@[simp] private theorem rationalValidationGateParsedState_register10
    (inputLength raw : ℕ) :
    (rationalValidationGateParsedState inputLength raw).registers 10 =
      rationalDenominatorFlag raw := by
  simp [rationalValidationGateParsedState, initialNPOracleState,
    NPOracleState.write, NPOracleState.jump]

@[simp] private theorem rationalValidationGateParsedState_register11
    (inputLength raw : ℕ) :
    (rationalValidationGateParsedState inputLength raw).registers 11 =
      rationalDenominatorValue raw := by
  simp [rationalValidationGateParsedState, initialNPOracleState,
    NPOracleState.write, NPOracleState.jump]

@[simp] private theorem rationalValidationGateParsedState_register12
    (inputLength raw : ℕ) :
    (rationalValidationGateParsedState inputLength raw).registers 12 =
      rationalMagnitudeFlag raw := by
  simp [rationalValidationGateParsedState, initialNPOracleState,
    NPOracleState.write, NPOracleState.jump]

@[simp] private theorem rationalValidationGateParsedState_register13
    (inputLength raw : ℕ) :
    (rationalValidationGateParsedState inputLength raw).registers 13 =
      rationalMagnitudeValue raw := by
  simp [rationalValidationGateParsedState, initialNPOracleState,
    NPOracleState.write, NPOracleState.jump]

/-- The two mutation snapshots are the only states carried across gate
branches. Naming them keeps control-flow proofs independent of the parse trace. -/
private def rationalValidationGateGcdState
    (inputLength raw : ℕ) : NPOracleState :=
  (rationalValidationGateParsedState inputLength raw).write
    2 (rationalGcdValue raw).pred

private def rationalValidationGateSignState
    (inputLength raw : ℕ) : NPOracleState :=
  ((rationalValidationGateGcdState inputLength raw).write
    14 (rationalSign raw)).write 14 (rationalSign raw).pred

private theorem npOracleState_write_same
    (state : NPOracleState) (register value : ℕ) :
    (state.write register value).registers register = value := by
  simp [NPOracleState.write]

@[simp] private theorem rationalValidationGateGcdState_register9
    (inputLength raw : ℕ) :
    (rationalValidationGateGcdState inputLength raw).registers 9 =
      rationalSign raw := by
  simp [rationalValidationGateGcdState, NPOracleState.write]

@[simp] private theorem rationalValidationGateGcdState_register11
    (inputLength raw : ℕ) :
    (rationalValidationGateGcdState inputLength raw).registers 11 =
      rationalDenominatorValue raw := by
  simp [rationalValidationGateGcdState, NPOracleState.write]

@[simp] private theorem rationalValidationGateGcdState_register13
    (inputLength raw : ℕ) :
    (rationalValidationGateGcdState inputLength raw).registers 13 =
      rationalMagnitudeValue raw := by
  simp [rationalValidationGateGcdState, NPOracleState.write]

@[simp] private theorem rationalValidationGateSignState_register9
    (inputLength raw : ℕ) :
    (rationalValidationGateSignState inputLength raw).registers 9 =
      rationalSign raw := by
  simpa only [rationalValidationGateSignState, NPOracleState.write,
    if_neg (by decide : (9 : ℕ) ≠ 14)] using
      rationalValidationGateGcdState_register9 inputLength raw

@[simp] private theorem rationalValidationGateSignState_register11
    (inputLength raw : ℕ) :
    (rationalValidationGateSignState inputLength raw).registers 11 =
      rationalDenominatorValue raw := by
  simpa only [rationalValidationGateSignState, NPOracleState.write,
    if_neg (by decide : (11 : ℕ) ≠ 14)] using
      rationalValidationGateGcdState_register11 inputLength raw

@[simp] private theorem rationalValidationGateSignState_register13
    (inputLength raw : ℕ) :
    (rationalValidationGateSignState inputLength raw).registers 13 =
      rationalMagnitudeValue raw := by
  simpa only [rationalValidationGateSignState, NPOracleState.write,
    if_neg (by decide : (13 : ℕ) ≠ 14)] using
      rationalValidationGateGcdState_register13 inputLength raw

@[simp] private theorem rationalValidationGateSignState_register14
    (inputLength raw : ℕ) :
    (rationalValidationGateSignState inputLength raw).registers 14 =
      (rationalSign raw).pred := by
  exact npOracleState_write_same _ 14 (rationalSign raw).pred

private theorem run_rationalValidationGatePrefix (inputLength raw : ℕ) :
    runNPOracleProgram rationalValidationGateProgram
        (rationalValidationGateBits inputLength raw)
        rationalValidationGateFuel
        (initialNPOracleState inputLength (rationalGcdStageOutput raw)) =
      runNPOracleProgram rationalValidationGateProgram
        (rationalValidationGateBits inputLength raw) 17
        (rationalValidationGateParsedState inputLength raw) := by
  rw [show rationalValidationGateFuel = 28 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 28) (pc := 0) (source := 0) (destination := 2)
    (next := 1) (value := rationalGcdValue raw)
    (by rfl) (by rfl)
    (by simp [initialNPOracleState, rationalGcdStageOutput])
    (rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues]))]
  rw [show (28 : ℕ) = 27 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 27) (pc := 1) (source := 0) (destination := 3)
    (next := 2) (value := rationalDenominatorStageOutput raw)
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, rationalGcdStageOutput])
    (rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues]))]
  rw [show (27 : ℕ) = 26 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 26) (pc := 2) (source := 3) (destination := 4)
    (next := 3) (value := rationalDenominatorValidation raw)
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, rationalDenominatorStageOutput])
    (rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues]))]
  rw [show (26 : ℕ) = 25 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 25) (pc := 3) (source := 3) (destination := 5)
    (next := 4) (value := rationalDenominatorLoweringContext raw)
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, rationalDenominatorStageOutput])
    (rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues]))]
  rw [show (25 : ℕ) = 24 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 24) (pc := 4) (source := 5) (destination := 6)
    (next := 5) (value := rationalMagnitudeValidation raw)
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, rationalDenominatorLoweringContext])
    (rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues]))]
  rw [show (24 : ℕ) = 23 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 23) (pc := 5) (source := 5) (destination := 7)
    (next := 6)
    (value := Nat.pair (rationalTupleFlag raw) (rationalSign raw))
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, rationalDenominatorLoweringContext])
    (rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues]))]
  rw [show (23 : ℕ) = 22 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 22) (pc := 6) (source := 7) (destination := 8)
    (next := 7) (value := rationalTupleFlag raw)
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    (rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues]))]
  rw [show (22 : ℕ) = 21 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 21) (pc := 7) (source := 7) (destination := 9)
    (next := 8) (value := rationalSign raw)
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    (rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues]))]
  rw [show (21 : ℕ) = 20 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 20) (pc := 8) (source := 4) (destination := 10)
    (next := 9) (value := rationalDenominatorFlag raw)
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, rationalDenominatorFlag])
    (rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues]))]
  rw [show (20 : ℕ) = 19 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 19) (pc := 9) (source := 4) (destination := 11)
    (next := 10) (value := rationalDenominatorValue raw)
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, rationalDenominatorValue])
    (rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues]))]
  rw [show (19 : ℕ) = 18 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 18) (pc := 10) (source := 6) (destination := 12)
    (next := 11) (value := rationalMagnitudeFlag raw)
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, rationalMagnitudeFlag])
    (rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues]))]
  rw [show (18 : ℕ) = 17 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 17) (pc := 11) (source := 6) (destination := 13)
    (next := 12) (value := rationalMagnitudeValue raw)
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, rationalMagnitudeValue])
    (rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues]))]
  rfl

private theorem run_rationalValidationGateFailure
    (inputLength raw extra : ℕ) (state : NPOracleState)
    (hpc : state.pc = 29)
    (hzero :
      natBitLength 0 ≤ rationalValidationGateBits inputLength raw) :
    runNPOracleProgram rationalValidationGateProgram
        (rationalValidationGateBits inputLength raw) (extra + 2) state =
      some 0 := by
  rw [show extra + 2 = (extra + 1) + 1 by omega]
  rw [run_set_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := extra + 1) (pc := 29) (register := 0) (value := 0)
    (next := 28) (by rfl) hpc hzero]
  exact run_halt_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := extra) (pc := 28) (outputRegister := 0) (value := 0)
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [NPOracleState.write]) hzero

private theorem run_rationalValidationGateSuccess
    (inputLength raw extra : ℕ) (state : NPOracleState)
    (hpc : state.pc = 24)
    (hsign : state.registers 9 = rationalSign raw)
    (hmagnitude : state.registers 13 = rationalMagnitudeValue raw)
    (hdenominator : state.registers 11 = rationalDenominatorValue raw)
    (hone :
      natBitLength 1 ≤ rationalValidationGateBits inputLength raw)
    (hmagnitudeDenominator :
      natBitLength
          (Nat.pair (rationalMagnitudeValue raw)
            (rationalDenominatorValue raw)) ≤
        rationalValidationGateBits inputLength raw)
    (hsignPayload :
      natBitLength
          (Nat.pair (rationalSign raw)
            (Nat.pair (rationalMagnitudeValue raw)
              (rationalDenominatorValue raw))) ≤
        rationalValidationGateBits inputLength raw)
    (hsuccess :
      natBitLength
          (Nat.pair 1
            (Nat.pair (rationalSign raw)
              (Nat.pair (rationalMagnitudeValue raw)
                (rationalDenominatorValue raw)))) ≤
        rationalValidationGateBits inputLength raw) :
    runNPOracleProgram rationalValidationGateProgram
        (rationalValidationGateBits inputLength raw) (extra + 5) state =
      some
        (Nat.pair 1
          (Nat.pair (rationalSign raw)
            (Nat.pair (rationalMagnitudeValue raw)
              (rationalDenominatorValue raw)))) := by
  rw [show extra + 5 = (extra + 4) + 1 by omega]
  rw [run_set_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := extra + 4) (pc := 24) (register := 15) (value := 1)
    (next := 25) (by rfl) hpc hone]
  rw [show extra + 4 = (extra + 3) + 1 by omega]
  rw [run_pair_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := extra + 3) (pc := 25) (left := 13) (right := 11)
    (destination := 16) (next := 26)
    (value := Nat.pair (rationalMagnitudeValue raw)
      (rationalDenominatorValue raw))
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump, hmagnitude,
      hdenominator])
    hmagnitudeDenominator]
  rw [show extra + 3 = (extra + 2) + 1 by omega]
  rw [run_pair_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := extra + 2) (pc := 26) (left := 9) (right := 16)
    (destination := 17) (next := 27)
    (value := Nat.pair (rationalSign raw)
      (Nat.pair (rationalMagnitudeValue raw)
        (rationalDenominatorValue raw)))
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump, hsign])
    hsignPayload]
  rw [show extra + 2 = (extra + 1) + 1 by omega]
  rw [run_pair_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := extra + 1) (pc := 27) (left := 15) (right := 17)
    (destination := 0) (next := 28)
    (value := Nat.pair 1
      (Nat.pair (rationalSign raw)
        (Nat.pair (rationalMagnitudeValue raw)
          (rationalDenominatorValue raw))))
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsuccess]
  exact run_halt_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := extra) (pc := 28) (outputRegister := 0)
    (value := Nat.pair 1
      (Nat.pair (rationalSign raw)
        (Nat.pair (rationalMagnitudeValue raw)
          (rationalDenominatorValue raw))))
    (by rfl) (by simp [NPOracleState.jump])
    (by simp [NPOracleState.write]) hsuccess

set_option maxHeartbeats 1000000 in
-- The sign split carries the fully parsed validation state through both exits.
private theorem run_rationalValidationGateSignStage
    (inputLength raw : ℕ)
    (htuple : rationalTupleFlag raw ≠ 0)
    (hmagnitudeFlag : rationalMagnitudeFlag raw ≠ 0)
    (hdenominatorFlag : rationalDenominatorFlag raw ≠ 0)
    (hdenominator : rationalDenominatorValue raw ≠ 0)
    (hgcd : rationalGcdValue raw = 1) :
    runNPOracleProgram rationalValidationGateProgram
        (rationalValidationGateBits inputLength raw) 10
        ((rationalValidationGateGcdState inputLength raw).jump 19) =
      some (rationalValidationOutput raw) := by
  have hsignBits :
      natBitLength (rationalSign raw) ≤
        rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hsignPredBits :
      natBitLength (rationalSign raw).pred ≤
        rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hmagnitudeDenominator :
      natBitLength
          (Nat.pair (rationalMagnitudeValue raw)
            (rationalDenominatorValue raw)) ≤
        rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hsignPayload :
      natBitLength
          (Nat.pair (rationalSign raw)
            (Nat.pair (rationalMagnitudeValue raw)
              (rationalDenominatorValue raw))) ≤
        rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hsuccess :
      natBitLength
          (Nat.pair 1
            (Nat.pair (rationalSign raw)
              (Nat.pair (rationalMagnitudeValue raw)
                (rationalDenominatorValue raw)))) ≤
        rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hzero :
      natBitLength 0 ≤ rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hone :
      natBitLength 1 ≤ rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_branchZero_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 9) (pc := 19) (register := 9)
    (zeroTarget := 24) (nonzeroTarget := 20)
    (by rfl) (by simp [NPOracleState.jump])]
  by_cases hsignZero : rationalSign raw = 0
  · rw [if_pos (by simp [NPOracleState.jump, hsignZero])]
    rw [show rationalValidationOutput raw =
        Nat.pair 1
          (Nat.pair (rationalSign raw)
            (Nat.pair (rationalMagnitudeValue raw)
              (rationalDenominatorValue raw))) by
      simp [rationalValidationOutput, rationalValidationAccepts,
        htuple, hmagnitudeFlag, hdenominatorFlag, hdenominator, hgcd,
        hsignZero]]
    exact
      run_rationalValidationGateSuccess inputLength raw 4
        ((rationalValidationGateGcdState inputLength raw).jump 24)
        (by rfl) (by simp) (by simp) (by simp) hone
        hmagnitudeDenominator hsignPayload hsuccess
  · rw [if_neg (by simp [NPOracleState.jump, hsignZero])]
    change
      runNPOracleProgram rationalValidationGateProgram
          (rationalValidationGateBits inputLength raw) 9
          ((rationalValidationGateGcdState inputLength raw).jump 20) =
        some (rationalValidationOutput raw)
    rw [show (9 : ℕ) = 8 + 1 by omega]
    rw [run_copy_instruction
      (program := rationalValidationGateProgram)
      (maximumBits := rationalValidationGateBits inputLength raw)
      (fuel := 8) (pc := 20) (source := 9) (destination := 14)
      (next := 21) (value := rationalSign raw)
      (by rfl) (by simp [NPOracleState.jump]) (by simp) hsignBits]
    rw [show (8 : ℕ) = 7 + 1 by omega]
    rw [run_decrement_instruction
      (program := rationalValidationGateProgram)
      (maximumBits := rationalValidationGateBits inputLength raw)
      (fuel := 7) (pc := 21) (register := 14) (next := 22)
      (value := (rationalSign raw).pred)
      (by rfl) (by simp [NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump]) hsignPredBits]
    change
      runNPOracleProgram rationalValidationGateProgram
          (rationalValidationGateBits inputLength raw) 7
          ((rationalValidationGateSignState inputLength raw).jump 22) =
        some (rationalValidationOutput raw)
    rw [show (7 : ℕ) = 6 + 1 by omega]
    rw [run_branchZero_instruction
      (program := rationalValidationGateProgram)
      (maximumBits := rationalValidationGateBits inputLength raw)
      (fuel := 6) (pc := 22) (register := 14)
      (zeroTarget := 23) (nonzeroTarget := 29)
      (by rfl) (by simp [NPOracleState.jump])]
    by_cases hsignOne : rationalSign raw = 1
    · rw [if_pos (by simp [NPOracleState.jump, hsignOne])]
      rw [show (6 : ℕ) = 5 + 1 by omega]
      rw [run_branchZero_instruction
        (program := rationalValidationGateProgram)
        (maximumBits := rationalValidationGateBits inputLength raw)
        (fuel := 5) (pc := 23) (register := 13)
        (zeroTarget := 29) (nonzeroTarget := 24)
        (by rfl) (by simp [NPOracleState.jump])]
      by_cases hmagnitudeZero : rationalMagnitudeValue raw = 0
      · rw [if_pos (by simp [NPOracleState.jump, hmagnitudeZero])]
        have hreject : ¬rationalValidationAccepts raw := by
          intro haccepts
          rcases haccepts.2.2.2.2.2 with hzero | ⟨_, hmagnitude⟩
          · exact hsignZero hzero
          · exact hmagnitude hmagnitudeZero
        rw [show rationalValidationOutput raw = 0 by
          simp [rationalValidationOutput, hreject]]
        exact run_rationalValidationGateFailure inputLength raw 3
          ((rationalValidationGateSignState inputLength raw).jump 29)
          (by rfl) hzero
      · rw [if_neg (by simp [NPOracleState.jump, hmagnitudeZero])]
        rw [show rationalValidationOutput raw =
            Nat.pair 1
              (Nat.pair (rationalSign raw)
                (Nat.pair (rationalMagnitudeValue raw)
                  (rationalDenominatorValue raw))) by
          simp [rationalValidationOutput, rationalValidationAccepts,
            htuple, hmagnitudeFlag, hdenominatorFlag, hdenominator, hgcd,
            hsignOne, hmagnitudeZero]]
        exact
          run_rationalValidationGateSuccess inputLength raw 0
            ((rationalValidationGateSignState inputLength raw).jump 24)
            (by rfl) (by simp) (by simp) (by simp) hone
            hmagnitudeDenominator hsignPayload hsuccess
    · have hsignPredNonzero : (rationalSign raw).pred ≠ 0 := by
        intro hpred
        apply hsignOne
        calc
          rationalSign raw = (rationalSign raw).pred.succ :=
            (Nat.succ_pred hsignZero).symm
          _ = 1 := by rw [hpred]
      rw [if_neg (by simpa using hsignPredNonzero)]
      rw [show rationalValidationOutput raw = 0 by
        simp [rationalValidationOutput, rationalValidationAccepts,
          hsignZero, hsignOne]]
      exact run_rationalValidationGateFailure inputLength raw 4
        ((rationalValidationGateSignState inputLength raw).jump 29)
        (by rfl) hzero

set_option maxHeartbeats 1000000 in
-- Six dependent validation branches share one exact fixed-fuel execution trace.
theorem run_rationalValidationGateProgram (inputLength raw : ℕ) :
    runNPOracleProgram rationalValidationGateProgram
        (rationalValidationGateBits inputLength raw)
        rationalValidationGateFuel
        (initialNPOracleState inputLength (rationalGcdStageOutput raw)) =
      some (rationalValidationOutput raw) := by
  have hsign :
      natBitLength (rationalSign raw) ≤
        rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hgcdPred :
      natBitLength (rationalGcdValue raw).pred ≤
        rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hsignPred :
      natBitLength (rationalSign raw).pred ≤
        rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hmagnitudeDenominator :
      natBitLength
          (Nat.pair (rationalMagnitudeValue raw)
            (rationalDenominatorValue raw)) ≤
        rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hsignPayload :
      natBitLength
          (Nat.pair (rationalSign raw)
            (Nat.pair (rationalMagnitudeValue raw)
              (rationalDenominatorValue raw))) ≤
        rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hsuccess :
      natBitLength
          (Nat.pair 1
            (Nat.pair (rationalSign raw)
              (Nat.pair (rationalMagnitudeValue raw)
                (rationalDenominatorValue raw)))) ≤
        rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hzero :
      natBitLength 0 ≤ rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  have hone :
      natBitLength 1 ≤ rationalValidationGateBits inputLength raw :=
    rationalValidationGateValue_bits inputLength raw _ (by
      simp [rationalValidationGateValues])
  rw [run_rationalValidationGatePrefix]
  rw [show (17 : ℕ) = 16 + 1 by omega]
  rw [run_branchZero_instruction
    (program := rationalValidationGateProgram)
    (maximumBits := rationalValidationGateBits inputLength raw)
    (fuel := 16) (pc := 12) (register := 8)
    (zeroTarget := 29) (nonzeroTarget := 13)
    (by rfl) (by simp)]
  by_cases htupleZero : rationalTupleFlag raw = 0
  · rw [if_pos (by simp [htupleZero])]
    rw [show rationalValidationOutput raw = 0 by
      simp [rationalValidationOutput, rationalValidationAccepts,
        htupleZero]]
    simpa only [show (16 : ℕ) = 14 + 2 by omega] using
      run_rationalValidationGateFailure inputLength raw 14 _ (by
        simp [NPOracleState.jump]) hzero
  · rw [if_neg (by simp [htupleZero])]
    rw [show (16 : ℕ) = 15 + 1 by omega]
    rw [run_branchZero_instruction
      (program := rationalValidationGateProgram)
      (maximumBits := rationalValidationGateBits inputLength raw)
      (fuel := 15) (pc := 13) (register := 12)
      (zeroTarget := 29) (nonzeroTarget := 14)
      (by rfl) (by simp [NPOracleState.jump])]
    by_cases hmagnitudeFlagZero : rationalMagnitudeFlag raw = 0
    · rw [if_pos (by simp [NPOracleState.jump, hmagnitudeFlagZero])]
      rw [show rationalValidationOutput raw = 0 by
        simp [rationalValidationOutput, rationalValidationAccepts,
          hmagnitudeFlagZero]]
      simpa only [show (15 : ℕ) = 13 + 2 by omega] using
        run_rationalValidationGateFailure inputLength raw 13 _ (by
          simp [NPOracleState.jump]) hzero
    · rw [if_neg (by simp [NPOracleState.jump, hmagnitudeFlagZero])]
      rw [show (15 : ℕ) = 14 + 1 by omega]
      rw [run_branchZero_instruction
        (program := rationalValidationGateProgram)
        (maximumBits := rationalValidationGateBits inputLength raw)
        (fuel := 14) (pc := 14) (register := 10)
        (zeroTarget := 29) (nonzeroTarget := 15)
        (by rfl) (by simp [NPOracleState.jump])]
      by_cases hdenominatorFlagZero : rationalDenominatorFlag raw = 0
      · rw [if_pos (by simp [NPOracleState.jump, hdenominatorFlagZero])]
        rw [show rationalValidationOutput raw = 0 by
          simp [rationalValidationOutput, rationalValidationAccepts,
            hdenominatorFlagZero]]
        simpa only [show (14 : ℕ) = 12 + 2 by omega] using
          run_rationalValidationGateFailure inputLength raw 12 _ (by
            simp [NPOracleState.jump]) hzero
      · rw [if_neg (by simp [NPOracleState.jump, hdenominatorFlagZero])]
        rw [show (14 : ℕ) = 13 + 1 by omega]
        rw [run_branchZero_instruction
          (program := rationalValidationGateProgram)
          (maximumBits := rationalValidationGateBits inputLength raw)
          (fuel := 13) (pc := 15) (register := 11)
          (zeroTarget := 29) (nonzeroTarget := 16)
          (by rfl) (by simp [NPOracleState.jump])]
        by_cases hdenominatorZero : rationalDenominatorValue raw = 0
        · rw [if_pos (by simp [NPOracleState.jump, hdenominatorZero])]
          rw [show rationalValidationOutput raw = 0 by
            simp [rationalValidationOutput, rationalValidationAccepts,
              hdenominatorZero]]
          simpa only [show (13 : ℕ) = 11 + 2 by omega] using
            run_rationalValidationGateFailure inputLength raw 11 _ (by
              simp [NPOracleState.jump]) hzero
        · rw [if_neg (by simp [NPOracleState.jump, hdenominatorZero])]
          rw [show (13 : ℕ) = 12 + 1 by omega]
          rw [run_branchZero_instruction
            (program := rationalValidationGateProgram)
            (maximumBits := rationalValidationGateBits inputLength raw)
            (fuel := 12) (pc := 16) (register := 2)
            (zeroTarget := 29) (nonzeroTarget := 17)
            (by rfl) (by simp [NPOracleState.jump])]
          by_cases hgcdZero : rationalGcdValue raw = 0
          · rw [if_pos (by simp [NPOracleState.jump, hgcdZero])]
            rw [show rationalValidationOutput raw = 0 by
              simp [rationalValidationOutput, rationalValidationAccepts,
                hgcdZero]]
            simpa only [show (12 : ℕ) = 10 + 2 by omega] using
              run_rationalValidationGateFailure inputLength raw 10 _ (by
                simp [NPOracleState.jump]) hzero
          · rw [if_neg (by simp [NPOracleState.jump, hgcdZero])]
            change
              runNPOracleProgram rationalValidationGateProgram
                  (rationalValidationGateBits inputLength raw) 12
                  ((rationalValidationGateParsedState inputLength raw).jump
                    17) =
                some (rationalValidationOutput raw)
            rw [show (12 : ℕ) = 11 + 1 by omega]
            rw [run_decrement_instruction
              (program := rationalValidationGateProgram)
              (maximumBits := rationalValidationGateBits inputLength raw)
              (fuel := 11) (pc := 17) (register := 2) (next := 18)
              (value := (rationalGcdValue raw).pred)
              (by rfl) (by simp [NPOracleState.jump])
              (by simp [NPOracleState.jump])
              hgcdPred]
            rw [show (11 : ℕ) = 10 + 1 by omega]
            rw [run_branchZero_instruction
              (program := rationalValidationGateProgram)
              (maximumBits := rationalValidationGateBits inputLength raw)
              (fuel := 10) (pc := 18) (register := 2)
              (zeroTarget := 19) (nonzeroTarget := 29)
              (by rfl) (by simp [NPOracleState.jump])]
            by_cases hgcdOne : rationalGcdValue raw = 1
            · rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump,
                hgcdOne])]
              change
                runNPOracleProgram rationalValidationGateProgram
                    (rationalValidationGateBits inputLength raw) 10
                    ((rationalValidationGateGcdState inputLength raw).jump 19) =
                  some (rationalValidationOutput raw)
              exact run_rationalValidationGateSignStage inputLength raw
                htupleZero hmagnitudeFlagZero hdenominatorFlagZero
                hdenominatorZero hgcdOne
            · have hgcdPredNonzero :
                  (rationalGcdValue raw).pred ≠ 0 := by
                intro hpred
                apply hgcdOne
                calc
                  rationalGcdValue raw =
                      (rationalGcdValue raw).pred.succ :=
                    (Nat.succ_pred hgcdZero).symm
                  _ = 1 := by rw [hpred]
              change
                runNPOracleProgram rationalValidationGateProgram
                    (rationalValidationGateBits inputLength raw) 10
                    (((rationalValidationGateParsedState inputLength raw).write
                      2 (rationalGcdValue raw).pred).jump
                        (if (rationalGcdValue raw).pred = 0 then 19 else 29)) =
                  some (rationalValidationOutput raw)
              rw [if_neg hgcdPredNonzero]
              rw [show rationalValidationOutput raw = 0 by
                simp [rationalValidationOutput, rationalValidationAccepts,
                  hgcdOne]]
              simpa only [show (10 : ℕ) = 8 + 2 by omega] using
                run_rationalValidationGateFailure inputLength raw 8 _ (by
                  simp [NPOracleState.jump]) hzero

/-! ## Unique total rational validator -/

def rationalValidationProgram : NPOracleProgram :=
  linkPrograms rationalTupleProgram <|
    linkPrograms rationalProjectionProgram <|
      linkPrograms rationalMagnitudeStageProgram <|
        linkPrograms rationalDenominatorLoweringProgram <|
          linkPrograms rationalDenominatorStageProgram <|
            linkPrograms rationalGcdLoweringProgram <|
              linkPrograms rationalGcdStageProgram
                rationalValidationGateProgram

@[simp] theorem rationalValidationProgram_oracleFree :
    OracleFree rationalValidationProgram := by
  exact oracleFree_linkPrograms rationalTupleProgram_oracleFree <|
    oracleFree_linkPrograms rationalProjectionProgram_oracleFree <|
      oracleFree_linkPrograms rationalMagnitudeStageProgram_oracleFree <|
        oracleFree_linkPrograms
          rationalDenominatorLoweringProgram_oracleFree <|
          oracleFree_linkPrograms rationalDenominatorStageProgram_oracleFree <|
            oracleFree_linkPrograms rationalGcdLoweringProgram_oracleFree <|
              oracleFree_linkPrograms rationalGcdStageProgram_oracleFree
                rationalValidationGateProgram_oracleFree

def rationalValidationFuel (_inputLength raw : ℕ) : ℕ :=
  linkFuel
      (linkPrograms rationalProjectionProgram <|
        linkPrograms rationalMagnitudeStageProgram <|
          linkPrograms rationalDenominatorLoweringProgram <|
            linkPrograms rationalDenominatorStageProgram <|
              linkPrograms rationalGcdLoweringProgram <|
                linkPrograms rationalGcdStageProgram
                  rationalValidationGateProgram)
      rationalTupleFuel <|
    linkFuel
        (linkPrograms rationalMagnitudeStageProgram <|
          linkPrograms rationalDenominatorLoweringProgram <|
            linkPrograms rationalDenominatorStageProgram <|
              linkPrograms rationalGcdLoweringProgram <|
                linkPrograms rationalGcdStageProgram
                  rationalValidationGateProgram)
        rationalProjectionFuel <|
      linkFuel
          (linkPrograms rationalDenominatorLoweringProgram <|
            linkPrograms rationalDenominatorStageProgram <|
              linkPrograms rationalGcdLoweringProgram <|
                linkPrograms rationalGcdStageProgram
                  rationalValidationGateProgram)
          (rationalMagnitudeStageFuel raw) <|
        linkFuel
            (linkPrograms rationalDenominatorStageProgram <|
              linkPrograms rationalGcdLoweringProgram <|
                linkPrograms rationalGcdStageProgram
                  rationalValidationGateProgram)
            rationalDenominatorLoweringFuel <|
          linkFuel
              (linkPrograms rationalGcdLoweringProgram <|
                linkPrograms rationalGcdStageProgram
                  rationalValidationGateProgram)
              (rationalDenominatorStageFuel raw) <|
            linkFuel
                (linkPrograms rationalGcdStageProgram
                  rationalValidationGateProgram)
                rationalGcdLoweringFuel <|
              linkFuel rationalValidationGateProgram
                (rationalGcdStageFuel raw) rationalValidationGateFuel

def rationalValidationBits (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (rationalTupleBits inputLength raw) <|
      max (rationalProjectionBits inputLength raw) <|
        max (rationalMagnitudeStageBits inputLength raw) <|
          max (rationalDenominatorLoweringBits inputLength raw) <|
            max (rationalDenominatorStageBits inputLength raw) <|
              max (rationalGcdLoweringBits inputLength raw) <|
                max (rationalGcdStageBits inputLength raw)
                  (rationalValidationGateBits inputLength raw)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
-- The final proof links seven nested programs and their exact resource ledgers.
theorem run_rationalValidationProgram (inputLength raw : ℕ) :
    runNPOracleProgram rationalValidationProgram
        (rationalValidationBits inputLength raw)
        (rationalValidationFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (rationalValidationOutput raw) := by
  let maximumBits := rationalValidationBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, rationalValidationBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, rationalValidationBits]
  have htupleBits :
      rationalTupleBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, rationalValidationBits]
  have hprojectionBits :
      rationalProjectionBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, rationalValidationBits]
  have hmagnitudeBits :
      rationalMagnitudeStageBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, rationalValidationBits]
  have hdenominatorLoweringBits :
      rationalDenominatorLoweringBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, rationalValidationBits]
  have hdenominatorBits :
      rationalDenominatorStageBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, rationalValidationBits]
  have hgcdLoweringBits :
      rationalGcdLoweringBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, rationalValidationBits]
  have hgcdBits :
      rationalGcdStageBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, rationalValidationBits]
  have hgateBits :
      rationalValidationGateBits inputLength raw ≤ maximumBits := by
    simp [maximumBits, rationalValidationBits]
  have htuple :=
    run_bits_mono (run_rationalTupleProgram inputLength raw) htupleBits
  have hprojection :=
    run_bits_mono (run_rationalProjectionProgram inputLength raw)
      hprojectionBits
  have hmagnitude :=
    run_bits_mono (run_rationalMagnitudeStageProgram inputLength raw)
      hmagnitudeBits
  have hdenominatorLowering :=
    run_bits_mono
      (run_rationalDenominatorLoweringProgram inputLength raw)
      hdenominatorLoweringBits
  have hdenominator :=
    run_bits_mono (run_rationalDenominatorStageProgram inputLength raw)
      hdenominatorBits
  have hgcdLowering :=
    run_bits_mono (run_rationalGcdLoweringProgram inputLength raw)
      hgcdLoweringBits
  have hgcd :=
    run_bits_mono (run_rationalGcdStageProgram inputLength raw) hgcdBits
  have hgate :=
    run_bits_mono (run_rationalValidationGateProgram inputLength raw)
      hgateBits
  have hgcdTail :=
    run_linkPrograms hpositive hlength hgcd hgate
  have hgcdLoweringTail :=
    run_linkPrograms hpositive hlength hgcdLowering hgcdTail
  have hdenominatorTail :=
    run_linkPrograms hpositive hlength hdenominator hgcdLoweringTail
  have hdenominatorLoweringTail :=
    run_linkPrograms hpositive hlength hdenominatorLowering hdenominatorTail
  have hmagnitudeTail :=
    run_linkPrograms hpositive hlength hmagnitude hdenominatorLoweringTail
  have hprojectionTail :=
    run_linkPrograms hpositive hlength hprojection hmagnitudeTail
  have hrun :=
    run_linkPrograms hpositive hlength htuple hprojectionTail
  simpa [rationalValidationProgram, rationalValidationFuel] using hrun

theorem rationalValidationAccepts_encodeCanonicalRational
    (coefficient : ℚ) :
    rationalValidationAccepts (encodeCanonicalRational coefficient) := by
  have hgcd : coefficient.num.natAbs.gcd coefficient.den = 1 :=
    coefficient.reduced.gcd_eq_one
  have htuple :
      rationalTupleOutput (encodeCanonicalRational coefficient) =
        Nat.pair 1
          (Nat.pair (Nat.pair 0 (encodeInt coefficient.num))
            (encodeNat coefficient.den)) := by
    unfold rationalTupleOutput taggedTupleOutput encodeCanonicalRational
    rw [show (2 : ℕ) =
      [encodeInt coefficient.num, encodeNat coefficient.den].length by rfl]
    rw [decodeTaggedTuple_encode]
    rfl
  by_cases hnegative : coefficient.num < 0
  · have hmagnitude : coefficient.num.natAbs ≠ 0 := by
      exact Int.natAbs_ne_zero.mpr (by omega)
    simp [rationalValidationAccepts, rationalTupleFlag, htuple,
      rationalTupleFields,
      rationalNumeratorFrame, rationalNumeratorCode, rationalDenominatorCode,
      rationalSign, rationalMagnitudeCode, rationalMagnitudeFlag,
      rationalMagnitudeValidation, rationalMagnitudeValue,
      rationalDenominatorFlag, rationalDenominatorValidation,
      rationalDenominatorValue, rationalGcdValue, encodeInt,
      hnegative, hmagnitude, coefficient.den_nz, hgcd]
  · simp [rationalValidationAccepts, rationalTupleFlag, htuple,
      rationalTupleFields,
      rationalNumeratorFrame, rationalNumeratorCode, rationalDenominatorCode,
      rationalSign, rationalMagnitudeCode, rationalMagnitudeFlag,
      rationalMagnitudeValidation, rationalMagnitudeValue,
      rationalDenominatorFlag, rationalDenominatorValidation,
      rationalDenominatorValue, rationalGcdValue, encodeInt,
      hnegative, coefficient.den_nz, hgcd]

theorem rationalValidationAccepts_iff_decodeCanonicalRational
    (raw : ℕ) :
    rationalValidationAccepts raw ↔
      ∃ coefficient, decodeCanonicalRational raw = some coefficient := by
  constructor
  · rintro ⟨htupleFlag, hmagnitudeFlag, hdenominatorFlag,
      hdenominatorNonzero, hgcd, hsign⟩
    have htupleOutput : rationalTupleOutput raw ≠ 0 := by
      intro hzero
      apply htupleFlag
      simp [rationalTupleFlag, hzero]
    obtain ⟨values, hlength, hcode⟩ :=
      (taggedTupleOutput_ne_zero_iff 2 raw).mp htupleOutput
    cases values with
    | nil => simp at hlength
    | cons numeratorCode rest =>
        cases rest with
        | nil => simp at hlength
        | cons denominatorCode rest =>
            cases rest with
            | cons extra tail => simp at hlength
            | nil =>
                have hraw :
                    raw =
                      encodeTaggedList [numeratorCode, denominatorCode] :=
                  hcode.symm
                subst raw
                have htuple :
                    rationalTupleOutput
                        (encodeTaggedList
                          [numeratorCode, denominatorCode]) =
                      Nat.pair 1
                        (Nat.pair (Nat.pair 0 numeratorCode)
                          denominatorCode) := by
                  unfold rationalTupleOutput taggedTupleOutput
                  rw [show (2 : ℕ) =
                    [numeratorCode, denominatorCode].length by rfl]
                  rw [decodeTaggedTuple_encode]
                  rfl
                have hmagnitudeFlag' :
                    (Nat.unpair
                      (canonicalNatValidationOutput
                        (Nat.unpair numeratorCode).2)).1 ≠ 0 := by
                  simpa [rationalMagnitudeFlag, rationalMagnitudeValidation,
                    rationalMagnitudeCode, rationalNumeratorCode,
                    rationalNumeratorFrame, rationalTupleFields, htuple] using
                    hmagnitudeFlag
                have hmagnitudeOutput :
                    canonicalNatValidationOutput
                        (Nat.unpair numeratorCode).2 ≠ 0 := by
                  intro hzero
                  apply hmagnitudeFlag'
                  simp [hzero]
                obtain ⟨magnitude, hmagnitudeDecode⟩ :=
                  (canonicalNatValidationOutput_ne_zero_iff
                    (Nat.unpair numeratorCode).2).mp hmagnitudeOutput
                have hdenominatorFlag' :
                    (Nat.unpair
                      (canonicalNatValidationOutput denominatorCode)).1 ≠ 0 := by
                  simpa [rationalDenominatorFlag,
                    rationalDenominatorValidation, rationalDenominatorCode,
                    rationalTupleFields, htuple] using hdenominatorFlag
                have hdenominatorOutput :
                    canonicalNatValidationOutput denominatorCode ≠ 0 := by
                  intro hzero
                  apply hdenominatorFlag'
                  simp [hzero]
                obtain ⟨denominator, hdenominatorDecode⟩ :=
                  (canonicalNatValidationOutput_ne_zero_iff
                    denominatorCode).mp hdenominatorOutput
                have hmagnitudeValidation :=
                  canonicalNatValidationOutput_of_decode hmagnitudeDecode
                have hdenominatorValidation :=
                  canonicalNatValidationOutput_of_decode hdenominatorDecode
                have hmagnitudeValue :
                    rationalMagnitudeValue
                        (encodeTaggedList
                          [numeratorCode, denominatorCode]) =
                      magnitude := by
                  simp [rationalMagnitudeValue, rationalMagnitudeValidation,
                    rationalMagnitudeCode, rationalNumeratorCode,
                    rationalNumeratorFrame, rationalTupleFields, htuple,
                    hmagnitudeValidation]
                have hdenominatorValue :
                    rationalDenominatorValue
                        (encodeTaggedList
                          [numeratorCode, denominatorCode]) =
                      denominator := by
                  simp [rationalDenominatorValue,
                    rationalDenominatorValidation, rationalDenominatorCode,
                    rationalTupleFields, htuple, hdenominatorValidation]
                have hdenominatorNonzero' : denominator ≠ 0 := by
                  simpa [hdenominatorValue] using hdenominatorNonzero
                have hgcd' : magnitude.gcd denominator = 1 := by
                  simpa [rationalGcdValue, hmagnitudeValue,
                    hdenominatorValue] using hgcd
                have hsign' :
                    (Nat.unpair numeratorCode).1 = 0 ∨
                      ((Nat.unpair numeratorCode).1 = 1 ∧ magnitude ≠ 0) := by
                  simpa [rationalSign, rationalNumeratorCode,
                    rationalNumeratorFrame, rationalTupleFields, htuple,
                    hmagnitudeValue] using hsign
                have hmagnitudeCode :
                    encodeNat magnitude = (Nat.unpair numeratorCode).2 :=
                  encodeNat_of_decode hmagnitudeDecode
                have hdenominatorCode :
                    encodeNat denominator = denominatorCode :=
                  encodeNat_of_decode hdenominatorDecode
                have hfinish (numerator : ℤ)
                    (hnatAbs : numerator.natAbs = magnitude)
                    (hnumeratorCode : encodeInt numerator = numeratorCode) :
                    ∃ coefficient,
                      decodeCanonicalRational
                          (encodeTaggedList
                            [numeratorCode, denominatorCode]) =
                        some coefficient := by
                  have hreduced : numerator.natAbs.Coprime denominator := by
                    rw [hnatAbs]
                    exact Nat.coprime_iff_gcd_eq_one.mpr hgcd'
                  let coefficient : ℚ :=
                    { num := numerator
                      den := denominator
                      den_nz := hdenominatorNonzero'
                      reduced := hreduced }
                  refine ⟨coefficient, ?_⟩
                  have hcanonical :
                      encodeCanonicalRational coefficient =
                        encodeTaggedList
                          [numeratorCode, denominatorCode] := by
                    simp only [encodeCanonicalRational, coefficient]
                    rw [hnumeratorCode, hdenominatorCode]
                  rw [← hcanonical]
                  exact decodeCanonicalRational_encode coefficient
                rcases hsign' with hsignZero |
                    ⟨hsignOne, hmagnitudeNonzero⟩
                · apply hfinish (magnitude : ℤ)
                  · simp
                  · calc
                      encodeInt (magnitude : ℤ) =
                          Nat.pair 0 (encodeNat magnitude) := by
                            simp [encodeInt]
                      _ = Nat.pair (Nat.unpair numeratorCode).1
                          (Nat.unpair numeratorCode).2 := by
                            rw [hsignZero, hmagnitudeCode]
                      _ = numeratorCode := Nat.pair_unpair numeratorCode
                · apply hfinish (-(magnitude : ℤ))
                  · simp
                  · calc
                      encodeInt (-(magnitude : ℤ)) =
                          Nat.pair 1 (encodeNat magnitude) := by
                            simp [encodeInt, hmagnitudeNonzero]
                      _ = Nat.pair (Nat.unpair numeratorCode).1
                          (Nat.unpair numeratorCode).2 := by
                            rw [hsignOne, hmagnitudeCode]
                      _ = numeratorCode := Nat.pair_unpair numeratorCode
  · rintro ⟨coefficient, hdecode⟩
    have hcode := encodeCanonicalRational_of_decode hdecode
    rw [← hcode]
    exact rationalValidationAccepts_encodeCanonicalRational coefficient

theorem rationalValidationOutput_ne_zero_iff_accepts (raw : ℕ) :
    rationalValidationOutput raw ≠ 0 ↔ rationalValidationAccepts raw := by
  unfold rationalValidationOutput
  split
  · rename_i haccepts
    exact ⟨fun _ => haccepts, fun _ => by
      have hpositive :=
        Nat.left_le_pair 1
          (Nat.pair (rationalSign raw)
            (Nat.pair (rationalMagnitudeValue raw)
              (rationalDenominatorValue raw)))
      omega⟩
  · rename_i hrejects
    simp [hrejects]

theorem rationalValidationOutput_ne_zero_iff_decodeCanonicalRational
    (raw : ℕ) :
    rationalValidationOutput raw ≠ 0 ↔
      ∃ coefficient, decodeCanonicalRational raw = some coefficient := by
  exact (rationalValidationOutput_ne_zero_iff_accepts raw).trans
    (rationalValidationAccepts_iff_decodeCanonicalRational raw)

theorem rationalValidationOutput_ne_zero_iff_isSome (raw : ℕ) :
    rationalValidationOutput raw ≠ 0 ↔
      (decodeCanonicalRational raw).isSome = true := by
  rw [rationalValidationOutput_ne_zero_iff_decodeCanonicalRational]
  exact Option.isSome_iff_exists.symm

end NearCubicWires.CanonicalRationalValidationProgram
