import Proof.MachineModel.CanonicalBalancedLookupProgram
import Proof.MachineModel.CanonicalBitSliceProgram
import Proof.MachineModel.CanonicalSignedGateEvaluationProgram
import Proof.MachineModel.GeneratedBalancedRangeProgram

namespace NearCubicWires.CanonicalSignedAtomRequestProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CanonicalSignedGateEvaluationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
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

/-! ## §1 The coordinate frame

The generated range leaves one index beside a shared context.  For an atom
list that context is the gate's weight code, the requested sign, and the mask
whose digit selects the coordinate's bit. -/

/-- The shared context of one atom list: weights, requested sign, mask. -/
def signedAtomContext (weightsCode wanted maskCode : ℕ) : ℕ :=
  Nat.pair weightsCode (Nat.pair wanted maskCode)

def signedAtomFrame (index weightsCode wanted maskCode : ℕ) : ℕ :=
  Nat.pair index (signedAtomContext weightsCode wanted maskCode)

/-- The lookup request beside the retained coordinate context. -/
def signedAtomLookupFrame
    (arity index weightsCode wanted maskCode : ℕ) : ℕ :=
  Nat.pair (Nat.pair arity (Nat.pair index weightsCode))
    (Nat.pair index (Nat.pair wanted maskCode))

/-- The one-digit slice request beside the retained weight and sign. -/
def signedAtomSliceFrame (index weightCode wanted maskCode : ℕ) : ℕ :=
  Nat.pair (bitSliceInput index 1 maskCode) (Nat.pair weightCode wanted)

/-! ## §2 The three straight-line adapters -/

/-- Frame the coordinate's balanced lookup request, retaining the index, the
requested sign, and the mask. -/
def signedAtomLookupFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 4 6 5
  , .pair 1 6 7 6
  , .pair 2 5 8 7
  , .pair 7 8 0 8
  , .halt 0
  ]

@[simp] theorem signedAtomLookupFrameProgram_oracleFree :
    OracleFree signedAtomLookupFrameProgram := by
  rfl

def signedAtomLookupFrameFuel : ℕ := 9

private def signedAtomLookupFrameValues
    (arity index weightsCode wanted maskCode : ℕ) : List ℕ :=
  [ arity
  , signedAtomFrame index weightsCode wanted maskCode
  , index
  , signedAtomContext weightsCode wanted maskCode
  , weightsCode
  , Nat.pair wanted maskCode
  , Nat.pair index weightsCode
  , Nat.pair arity (Nat.pair index weightsCode)
  , Nat.pair index (Nat.pair wanted maskCode)
  , signedAtomLookupFrame arity index weightsCode wanted maskCode
  ]

def signedAtomLookupFrameBits
    (arity index weightsCode wanted maskCode : ℕ) : ℕ :=
  natBitLength
    ((signedAtomLookupFrameValues arity index weightsCode wanted
      maskCode).foldr max 1)

private theorem signedAtomLookupFrame_value_bits
    (arity index weightsCode wanted maskCode : ℕ) {candidate : ℕ}
    (hcandidate :
      candidate ∈
        signedAtomLookupFrameValues arity index weightsCode wanted maskCode) :
    natBitLength candidate ≤
      signedAtomLookupFrameBits arity index weightsCode wanted maskCode :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

theorem run_signedAtomLookupFrameProgram
    (arity index weightsCode wanted maskCode maximumBits : ℕ)
    (hbits :
      signedAtomLookupFrameBits arity index weightsCode wanted maskCode ≤
        maximumBits) :
    runNPOracleProgram signedAtomLookupFrameProgram maximumBits
        signedAtomLookupFrameFuel
        (initialNPOracleState arity
          (signedAtomFrame index weightsCode wanted maskCode)) =
      some (signedAtomLookupFrame arity index weightsCode wanted maskCode) := by
  have hindexBits : natBitLength index ≤ maximumBits :=
    (signedAtomLookupFrame_value_bits arity index weightsCode wanted maskCode
      (by simp [signedAtomLookupFrameValues])).trans hbits
  have hcontextBits :
      natBitLength (signedAtomContext weightsCode wanted maskCode) ≤
        maximumBits :=
    (signedAtomLookupFrame_value_bits arity index weightsCode wanted maskCode
      (by simp [signedAtomLookupFrameValues])).trans hbits
  have hweightsBits : natBitLength weightsCode ≤ maximumBits :=
    (signedAtomLookupFrame_value_bits arity index weightsCode wanted maskCode
      (by simp [signedAtomLookupFrameValues])).trans hbits
  have htailBits : natBitLength (Nat.pair wanted maskCode) ≤ maximumBits :=
    (signedAtomLookupFrame_value_bits arity index weightsCode wanted maskCode
      (by simp [signedAtomLookupFrameValues])).trans hbits
  have hpairBits : natBitLength (Nat.pair index weightsCode) ≤ maximumBits :=
    (signedAtomLookupFrame_value_bits arity index weightsCode wanted maskCode
      (by simp [signedAtomLookupFrameValues])).trans hbits
  have hrequestBits :
      natBitLength (Nat.pair arity (Nat.pair index weightsCode)) ≤
        maximumBits :=
    (signedAtomLookupFrame_value_bits arity index weightsCode wanted maskCode
      (by simp [signedAtomLookupFrameValues])).trans hbits
  have hretainBits :
      natBitLength (Nat.pair index (Nat.pair wanted maskCode)) ≤ maximumBits :=
    (signedAtomLookupFrame_value_bits arity index weightsCode wanted maskCode
      (by simp [signedAtomLookupFrameValues])).trans hbits
  have houtputBits :
      natBitLength
          (signedAtomLookupFrame arity index weightsCode wanted maskCode) ≤
        maximumBits :=
    (signedAtomLookupFrame_value_bits arity index weightsCode wanted maskCode
      (by simp [signedAtomLookupFrameValues])).trans hbits
  rw [show signedAtomLookupFrameFuel = 8 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [initialNPOracleState, signedAtomFrame]) hindexBits]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := signedAtomContext weightsCode wanted maskCode) (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        signedAtomFrame])
    hcontextBits]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := weightsCode) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, signedAtomContext])
    hweightsBits]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair wanted maskCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, signedAtomContext])
    htailBits]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair index weightsCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpairBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair arity (Nat.pair index weightsCode)) (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hrequestBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair index (Nat.pair wanted maskCode)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hretainBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := signedAtomLookupFrame arity index weightsCode wanted maskCode)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, signedAtomLookupFrame])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := signedAtomLookupFrame arity index weightsCode wanted maskCode)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Frame the coordinate's one-digit mask slice, retaining the selected weight
code and the requested sign. -/
def signedAtomSliceFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .set 8 1 7
  , .pair 8 7 9 8
  , .pair 4 9 10 9
  , .pair 2 6 11 10
  , .pair 10 11 0 11
  , .halt 0
  ]

@[simp] theorem signedAtomSliceFrameProgram_oracleFree :
    OracleFree signedAtomSliceFrameProgram := by
  rfl

def signedAtomSliceFrameFuel : ℕ := 12

private def signedAtomSliceFrameValues
    (index weightCode wanted maskCode : ℕ) : List ℕ :=
  [ Nat.pair weightCode (Nat.pair index (Nat.pair wanted maskCode))
  , weightCode
  , Nat.pair index (Nat.pair wanted maskCode)
  , index
  , Nat.pair wanted maskCode
  , wanted
  , maskCode
  , 1
  , Nat.pair 1 maskCode
  , bitSliceInput index 1 maskCode
  , Nat.pair weightCode wanted
  , signedAtomSliceFrame index weightCode wanted maskCode
  ]

def signedAtomSliceFrameBits (index weightCode wanted maskCode : ℕ) : ℕ :=
  natBitLength
    ((signedAtomSliceFrameValues index weightCode wanted maskCode).foldr max 1)

private theorem signedAtomSliceFrame_value_bits
    (index weightCode wanted maskCode : ℕ) {candidate : ℕ}
    (hcandidate :
      candidate ∈ signedAtomSliceFrameValues index weightCode wanted maskCode) :
    natBitLength candidate ≤
      signedAtomSliceFrameBits index weightCode wanted maskCode :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

theorem run_signedAtomSliceFrameProgram
    (arity index weightCode wanted maskCode maximumBits : ℕ)
    (hbits :
      signedAtomSliceFrameBits index weightCode wanted maskCode ≤
        maximumBits) :
    runNPOracleProgram signedAtomSliceFrameProgram maximumBits
        signedAtomSliceFrameFuel
        (initialNPOracleState arity
          (Nat.pair weightCode (Nat.pair index (Nat.pair wanted maskCode)))) =
      some (signedAtomSliceFrame index weightCode wanted maskCode) := by
  have hweightBits : natBitLength weightCode ≤ maximumBits :=
    (signedAtomSliceFrame_value_bits index weightCode wanted maskCode
      (by simp [signedAtomSliceFrameValues])).trans hbits
  have htailBits :
      natBitLength (Nat.pair index (Nat.pair wanted maskCode)) ≤ maximumBits :=
    (signedAtomSliceFrame_value_bits index weightCode wanted maskCode
      (by simp [signedAtomSliceFrameValues])).trans hbits
  have hindexBits : natBitLength index ≤ maximumBits :=
    (signedAtomSliceFrame_value_bits index weightCode wanted maskCode
      (by simp [signedAtomSliceFrameValues])).trans hbits
  have hpairBits : natBitLength (Nat.pair wanted maskCode) ≤ maximumBits :=
    (signedAtomSliceFrame_value_bits index weightCode wanted maskCode
      (by simp [signedAtomSliceFrameValues])).trans hbits
  have hwantedBits : natBitLength wanted ≤ maximumBits :=
    (signedAtomSliceFrame_value_bits index weightCode wanted maskCode
      (by simp [signedAtomSliceFrameValues])).trans hbits
  have hmaskBits : natBitLength maskCode ≤ maximumBits :=
    (signedAtomSliceFrame_value_bits index weightCode wanted maskCode
      (by simp [signedAtomSliceFrameValues])).trans hbits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (signedAtomSliceFrame_value_bits index weightCode wanted maskCode
      (by simp [signedAtomSliceFrameValues])).trans hbits
  have hwidthBits : natBitLength (Nat.pair 1 maskCode) ≤ maximumBits :=
    (signedAtomSliceFrame_value_bits index weightCode wanted maskCode
      (by simp [signedAtomSliceFrameValues])).trans hbits
  have hsliceBits :
      natBitLength (bitSliceInput index 1 maskCode) ≤ maximumBits :=
    (signedAtomSliceFrame_value_bits index weightCode wanted maskCode
      (by simp [signedAtomSliceFrameValues])).trans hbits
  have hretainBits :
      natBitLength (Nat.pair weightCode wanted) ≤ maximumBits :=
    (signedAtomSliceFrame_value_bits index weightCode wanted maskCode
      (by simp [signedAtomSliceFrameValues])).trans hbits
  have houtputBits :
      natBitLength (signedAtomSliceFrame index weightCode wanted maskCode) ≤
        maximumBits :=
    (signedAtomSliceFrame_value_bits index weightCode wanted maskCode
      (by simp [signedAtomSliceFrameValues])).trans hbits
  rw [show signedAtomSliceFrameFuel = 11 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := weightCode) (by rfl) rfl
    (by simp [initialNPOracleState]) hweightBits]
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair index (Nat.pair wanted maskCode)) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hindexBits]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair wanted maskCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpairBits]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := wanted) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwantedBits]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := maskCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmaskBits]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_set_instruction (register := 8) (value := 1) (next := 7)
    (by rfl) rfl honeBits]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 1 maskCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := bitSliceInput index 1 maskCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSliceInput])
    hsliceBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair weightCode wanted) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hretainBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := signedAtomSliceFrame index weightCode wanted maskCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomSliceFrame])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := signedAtomSliceFrame index weightCode wanted maskCode)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Assemble the balanced-call request of one signed atom from the selected
weight code, the requested sign, and the coordinate's mask digit. -/
def signedAtomAssembleProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 5 2 6 5
  , .pair 4 6 7 6
  , .pair 1 7 0 7
  , .halt 0
  ]

@[simp] theorem signedAtomAssembleProgram_oracleFree :
    OracleFree signedAtomAssembleProgram := by
  rfl

def signedAtomAssembleFuel : ℕ := 8

private def signedAtomAssembleValues
    (arity weightCode wanted bit : ℕ) : List ℕ :=
  [ arity
  , Nat.pair bit (Nat.pair weightCode wanted)
  , bit
  , Nat.pair weightCode wanted
  , weightCode
  , wanted
  , Nat.pair wanted bit
  , Nat.pair weightCode (Nat.pair wanted bit)
  , Nat.pair arity (Nat.pair weightCode (Nat.pair wanted bit))
  ]

def signedAtomAssembleBits (arity weightCode wanted bit : ℕ) : ℕ :=
  natBitLength
    ((signedAtomAssembleValues arity weightCode wanted bit).foldr max 1)

private theorem signedAtomAssemble_value_bits
    (arity weightCode wanted bit : ℕ) {candidate : ℕ}
    (hcandidate : candidate ∈ signedAtomAssembleValues arity weightCode wanted bit) :
    natBitLength candidate ≤ signedAtomAssembleBits arity weightCode wanted bit :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

theorem run_signedAtomAssembleProgram
    (arity weightCode wanted bit maximumBits : ℕ)
    (hbits : signedAtomAssembleBits arity weightCode wanted bit ≤ maximumBits) :
    runNPOracleProgram signedAtomAssembleProgram maximumBits
        signedAtomAssembleFuel
        (initialNPOracleState arity
          (Nat.pair bit (Nat.pair weightCode wanted))) =
      some
        (Nat.pair arity (Nat.pair weightCode (Nat.pair wanted bit))) := by
  have hbitBits : natBitLength bit ≤ maximumBits :=
    (signedAtomAssemble_value_bits arity weightCode wanted bit
      (by simp [signedAtomAssembleValues])).trans hbits
  have htailBits : natBitLength (Nat.pair weightCode wanted) ≤ maximumBits :=
    (signedAtomAssemble_value_bits arity weightCode wanted bit
      (by simp [signedAtomAssembleValues])).trans hbits
  have hweightBits : natBitLength weightCode ≤ maximumBits :=
    (signedAtomAssemble_value_bits arity weightCode wanted bit
      (by simp [signedAtomAssembleValues])).trans hbits
  have hwantedBits : natBitLength wanted ≤ maximumBits :=
    (signedAtomAssemble_value_bits arity weightCode wanted bit
      (by simp [signedAtomAssembleValues])).trans hbits
  have hframeBits : natBitLength (Nat.pair wanted bit) ≤ maximumBits :=
    (signedAtomAssemble_value_bits arity weightCode wanted bit
      (by simp [signedAtomAssembleValues])).trans hbits
  have hcodeBits :
      natBitLength (Nat.pair weightCode (Nat.pair wanted bit)) ≤ maximumBits :=
    (signedAtomAssemble_value_bits arity weightCode wanted bit
      (by simp [signedAtomAssembleValues])).trans hbits
  have houtputBits :
      natBitLength
          (Nat.pair arity (Nat.pair weightCode (Nat.pair wanted bit))) ≤
        maximumBits :=
    (signedAtomAssemble_value_bits arity weightCode wanted bit
      (by simp [signedAtomAssembleValues])).trans hbits
  rw [show signedAtomAssembleFuel = 7 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := bit) (by rfl) rfl
    (by simp [initialNPOracleState]) hbitBits]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair weightCode wanted)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := weightCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hweightBits]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := wanted) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwantedBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair wanted bit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hframeBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair weightCode (Nat.pair wanted bit)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcodeBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair arity (Nat.pair weightCode (Nat.pair wanted bit)))
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := Nat.pair arity (Nat.pair weightCode (Nat.pair wanted bit)))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ## §3 The mask digit is the coordinate's bit -/

theorem bitSlice_one_eq_boolCode (offset value : ℕ) :
    bitSlice offset 1 value = boolCode (value.testBit offset) := by
  have hshift : Nat.shiftRight value offset = value / 2 ^ offset :=
    Nat.shiftRight_eq_div_pow value offset
  have htest : value.testBit offset = decide (value / 2 ^ offset % 2 = 1) :=
    Nat.testBit_eq_decide_div_mod_eq
  unfold bitSlice
  rw [hshift, htest, pow_one]
  rcases Nat.mod_two_eq_zero_or_one (value / 2 ^ offset) with hzero | hone
  · rw [hzero]
    simp [boolCode]
  · rw [hone]
    simp [boolCode]

/-! ## §4 The per-coordinate atom stage

Five stages: frame the lookup, select the weight, frame the digit, read the
digit, assemble the request.  Only the two library stages do any work; the
three adapters are pure pair plumbing. -/

/-- Read the mask digit, then assemble the request. -/
def signedAtomDigitProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitSliceProgram) signedAtomAssembleProgram

/-- Frame the mask digit, then `signedAtomDigitProgram`. -/
def signedAtomSelectedProgram : NPOracleProgram :=
  linkPrograms signedAtomSliceFrameProgram signedAtomDigitProgram

/-- Select the coordinate's weight, then `signedAtomSelectedProgram`. -/
def signedAtomWeightProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram canonicalBalancedLookupProgram)
    signedAtomSelectedProgram

/-- **The per-coordinate signed atom request machine.** -/
def signedAtomRequestProgram : NPOracleProgram :=
  linkPrograms signedAtomLookupFrameProgram signedAtomWeightProgram

theorem signedAtomDigitProgram_oracleFree : OracleFree signedAtomDigitProgram :=
  oracleFree_linkPrograms
    (preserveRightProgram_oracleFree bitSliceProgram bitSliceProgram_oracleFree)
    signedAtomAssembleProgram_oracleFree

theorem signedAtomSelectedProgram_oracleFree :
    OracleFree signedAtomSelectedProgram :=
  oracleFree_linkPrograms signedAtomSliceFrameProgram_oracleFree
    signedAtomDigitProgram_oracleFree

theorem signedAtomWeightProgram_oracleFree :
    OracleFree signedAtomWeightProgram :=
  oracleFree_linkPrograms
    (preserveRightProgram_oracleFree canonicalBalancedLookupProgram
      canonicalBalancedLookupProgram_oracleFree)
    signedAtomSelectedProgram_oracleFree

theorem signedAtomRequestProgram_oracleFree :
    OracleFree signedAtomRequestProgram :=
  oracleFree_linkPrograms signedAtomLookupFrameProgram_oracleFree
    signedAtomWeightProgram_oracleFree

def signedAtomRequestFuel (codes : List ℕ) (index : ℕ) : ℕ :=
  linkFuel signedAtomWeightProgram signedAtomLookupFrameFuel
    (linkFuel signedAtomSelectedProgram
      (preserveRightFuel (balancedLookupFuel codes index))
      (linkFuel signedAtomDigitProgram signedAtomSliceFrameFuel
        (linkFuel signedAtomAssembleProgram
          (preserveRightFuel (bitSliceFuel 1)) signedAtomAssembleFuel)))

def signedAtomRequestStageBits
    (codes : List ℕ) (index wanted maskCode weightCode : ℕ) : List ℕ :=
  [ 1
  , natBitLength codes.length
  , signedAtomLookupFrameBits codes.length index (encodeBalancedList codes)
      wanted maskCode
  , preserveRightBits (balancedLookupMaximumBits codes index)
      (balancedLookupInput codes index)
      (Nat.pair index (Nat.pair wanted maskCode)) weightCode
  , signedAtomSliceFrameBits index weightCode wanted maskCode
  , preserveRightBits (bitSliceBits codes.length index 1 maskCode)
      (bitSliceInput index 1 maskCode) (Nat.pair weightCode wanted)
      (bitSlice index 1 maskCode)
  , signedAtomAssembleBits codes.length weightCode wanted
      (bitSlice index 1 maskCode)
  ]

def signedAtomRequestBits
    (codes : List ℕ) (index wanted maskCode weightCode : ℕ) : ℕ :=
  (signedAtomRequestStageBits codes index wanted maskCode weightCode).foldr
    max 1

theorem run_signedAtomRequestProgram
    (codes : List ℕ) (index wanted maskCode weightCode maximumBits : ℕ)
    (hweight : codes[index]? = some weightCode)
    (hbits :
      signedAtomRequestBits codes index wanted maskCode weightCode ≤
        maximumBits) :
    runNPOracleProgram signedAtomRequestProgram maximumBits
        (signedAtomRequestFuel codes index)
        (initialNPOracleState codes.length
          (signedAtomFrame index (encodeBalancedList codes) wanted maskCode)) =
      some
        (Nat.pair codes.length
          (Nat.pair weightCode
            (Nat.pair wanted (boolCode (maskCode.testBit index))))) := by
  have hindex : index < codes.length := by
    have := List.getElem?_eq_some_iff.mp hweight
    exact this.choose
  have hselected : codes[index] = weightCode := by
    have hsome : codes[index]? = some codes[index] :=
      List.getElem?_eq_getElem hindex
    rw [hsome] at hweight
    exact Option.some.inj hweight
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈ signedAtomRequestStageBits codes index wanted maskCode
          weightCode) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [signedAtomRequestStageBits]
  have hlength : natBitLength codes.length ≤ maximumBits := by
    apply bits_of_member
    simp [signedAtomRequestStageBits]
  have hframe :
      runNPOracleProgram signedAtomLookupFrameProgram maximumBits
          signedAtomLookupFrameFuel
          (initialNPOracleState codes.length
            (signedAtomFrame index (encodeBalancedList codes) wanted
              maskCode)) =
        some
          (signedAtomLookupFrame codes.length index (encodeBalancedList codes)
            wanted maskCode) := by
    refine run_signedAtomLookupFrameProgram codes.length index
      (encodeBalancedList codes) wanted maskCode maximumBits ?_
    apply bits_of_member
    simp [signedAtomRequestStageBits]
  have hlookupFrame :
      signedAtomLookupFrame codes.length index (encodeBalancedList codes)
          wanted maskCode =
        Nat.pair (balancedLookupInput codes index)
          (Nat.pair index (Nat.pair wanted maskCode)) := by
    rfl
  have hweightStage :
      runNPOracleProgram (preserveRightProgram canonicalBalancedLookupProgram)
          maximumBits (preserveRightFuel (balancedLookupFuel codes index))
          (initialNPOracleState codes.length
            (Nat.pair (balancedLookupInput codes index)
              (Nat.pair index (Nat.pair wanted maskCode)))) =
        some
          (Nat.pair weightCode (Nat.pair index (Nat.pair wanted maskCode))) := by
    have hsource :
        runNPOracleProgram canonicalBalancedLookupProgram
            (balancedLookupMaximumBits codes index)
            (balancedLookupFuel codes index)
            (initialNPOracleState codes.length
              (balancedLookupInput codes index)) =
          some weightCode := by
      rw [← hselected]
      exact run_canonicalBalancedLookupProgram codes index codes.length hindex
    refine run_bits_mono
      (run_preserveRightProgram canonicalBalancedLookupProgram codes.length
        (balancedLookupMaximumBits codes index)
        (balancedLookupFuel codes index) (balancedLookupInput codes index)
        (Nat.pair index (Nat.pair wanted maskCode)) weightCode hsource) ?_
    apply bits_of_member
    simp [signedAtomRequestStageBits]
  have hsliceFrame :
      runNPOracleProgram signedAtomSliceFrameProgram maximumBits
          signedAtomSliceFrameFuel
          (initialNPOracleState codes.length
            (Nat.pair weightCode (Nat.pair index (Nat.pair wanted maskCode)))) =
        some (signedAtomSliceFrame index weightCode wanted maskCode) := by
    refine run_signedAtomSliceFrameProgram codes.length index weightCode wanted
      maskCode maximumBits ?_
    apply bits_of_member
    simp [signedAtomRequestStageBits]
  have hdigitFrame :
      signedAtomSliceFrame index weightCode wanted maskCode =
        Nat.pair (bitSliceInput index 1 maskCode)
          (Nat.pair weightCode wanted) := by
    rfl
  have hdigit :
      runNPOracleProgram (preserveRightProgram bitSliceProgram) maximumBits
          (preserveRightFuel (bitSliceFuel 1))
          (initialNPOracleState codes.length
            (Nat.pair (bitSliceInput index 1 maskCode)
              (Nat.pair weightCode wanted))) =
        some
          (Nat.pair (bitSlice index 1 maskCode)
            (Nat.pair weightCode wanted)) := by
    refine run_bits_mono
      (run_preserveRightProgram bitSliceProgram codes.length
        (bitSliceBits codes.length index 1 maskCode) (bitSliceFuel 1)
        (bitSliceInput index 1 maskCode) (Nat.pair weightCode wanted)
        (bitSlice index 1 maskCode)
        (run_bitSliceProgram codes.length index 1 maskCode)) ?_
    apply bits_of_member
    simp [signedAtomRequestStageBits]
  have hassemble :
      runNPOracleProgram signedAtomAssembleProgram maximumBits
          signedAtomAssembleFuel
          (initialNPOracleState codes.length
            (Nat.pair (bitSlice index 1 maskCode)
              (Nat.pair weightCode wanted))) =
        some
          (Nat.pair codes.length
            (Nat.pair weightCode
              (Nat.pair wanted (bitSlice index 1 maskCode)))) := by
    refine run_signedAtomAssembleProgram codes.length weightCode wanted
      (bitSlice index 1 maskCode) maximumBits ?_
    apply bits_of_member
    simp [signedAtomRequestStageBits]
  rw [bitSlice_one_eq_boolCode] at hdigit hassemble
  rw [hlookupFrame] at hframe
  rw [hdigitFrame] at hsliceFrame
  exact run_linkPrograms hpositive hlength hframe
    (run_linkPrograms hpositive hlength hweightStage
      (run_linkPrograms hpositive hlength hsliceFrame
        (run_linkPrograms hpositive hlength hdigit hassemble)))

/-! ## §5 The atom the stage names

Instantiating the code list at a gate's canonical weight syntax identifies the
stage's output with `signedAtomRequest`, the balanced-call request the signed
accumulator of `CanonicalSignedGateEvaluationProgram` §4 consumes. -/

theorem run_signedAtomRequestProgram_weights
    (weights : List ℤ) (index wanted maskCode maximumBits : ℕ)
    (weight : ℤ)
    (hweight : weights[index]? = some weight)
    (hbits :
      signedAtomRequestBits (weights.map encodeInt) index wanted maskCode
          (encodeInt weight) ≤
        maximumBits) :
    runNPOracleProgram signedAtomRequestProgram maximumBits
        (signedAtomRequestFuel (weights.map encodeInt) index)
        (initialNPOracleState weights.length
          (signedAtomFrame index (encodeIntList weights) wanted maskCode)) =
      some
        (signedAtomRequest weights.length
          (weight, wanted, maskCode.testBit index)) := by
  have hcodes : (weights.map encodeInt)[index]? = some (encodeInt weight) := by
    rw [List.getElem?_map, hweight]
    rfl
  have hlength : (weights.map encodeInt).length = weights.length := by
    simp
  have hrun :=
    run_signedAtomRequestProgram (weights.map encodeInt) index wanted maskCode
      (encodeInt weight) maximumBits hcodes hbits
  rw [hlength] at hrun
  have hframe :
      encodeBalancedList (weights.map encodeInt) = encodeIntList weights := rfl
  rw [hframe] at hrun
  exact hrun

/-! ## §6 One masked accumulator's whole request list

The coordinate stage is uniform in the index, so the whole atom list of one
masked accumulator is the generated index range mapped through it.  Nothing
between the generator and the balanced call is new: the retained context is
dropped by one projection instruction. -/

/-- Keep the left component of a canonical pair. -/
def leftProjectionProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

@[simp] theorem leftProjectionProgram_oracleFree :
    OracleFree leftProjectionProgram := by
  rfl

def leftProjectionBits (left right : ℕ) : ℕ :=
  natBitLength (Nat.pair left right)

theorem run_leftProjectionProgram (inputLength left right : ℕ) :
    runNPOracleProgram leftProjectionProgram (leftProjectionBits left right) 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some left := by
  have hinput :
      natBitLength (Nat.pair left right) ≤ leftProjectionBits left right :=
    Nat.le_refl _
  have hleft : natBitLength left ≤ leftProjectionBits left right :=
    (natBitLength_mono (Nat.left_le_pair left right)).trans hinput
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  exact run_halt_instruction (fuel := 0) (value := left) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hleft

def signedAtomFrameIndex (raw : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair raw).2).1

@[simp] theorem signedAtomFrameIndex_atom
    (arity index weightsCode wanted maskCode : ℕ) :
    signedAtomFrameIndex
        (balancedRangeRequestAtom arity index
          (signedAtomContext weightsCode wanted maskCode)) =
      index := by
  simp [signedAtomFrameIndex, balancedRangeRequestAtom]

/-- The shared context of one atom list, as the generator receives it. -/
def signedAtomRangeContext (codes : List ℕ) (wanted maskCode : ℕ) : ℕ :=
  signedAtomContext (encodeBalancedList codes) wanted maskCode

def signedAtomRangeRequests (codes : List ℕ) (wanted maskCode : ℕ) : List ℕ :=
  balancedRangeRequestAtoms codes.length
    (signedAtomRangeContext codes wanted maskCode) 0 codes.length

def signedAtomLeafOutput (codes : List ℕ) (wanted maskCode raw : ℕ) : ℕ :=
  Nat.pair codes.length
    (Nat.pair (codes.getD (signedAtomFrameIndex raw) 0)
      (Nat.pair wanted
        (boolCode (maskCode.testBit (signedAtomFrameIndex raw)))))

def signedAtomLeafFuel (codes : List ℕ) (raw : ℕ) : ℕ :=
  signedAtomRequestFuel codes (signedAtomFrameIndex raw)

/-- Drop the retained context, then map the coordinate stage. -/
def signedAtomRequestCallProgram : NPOracleProgram :=
  linkPrograms leftProjectionProgram
    (balancedCallProgram signedAtomRequestProgram)

/-- **One masked accumulator's request list.** -/
def signedAtomRequestListProgram : NPOracleProgram :=
  linkPrograms generatedBalancedRangeProgram signedAtomRequestCallProgram

theorem signedAtomRequestCallProgram_oracleFree :
    OracleFree signedAtomRequestCallProgram :=
  oracleFree_linkPrograms leftProjectionProgram_oracleFree
    (balancedCallProgram_oracleFree signedAtomRequestProgram_oracleFree)

theorem signedAtomRequestListProgram_oracleFree :
    OracleFree signedAtomRequestListProgram :=
  oracleFree_linkPrograms generatedBalancedRangeProgram_oracleFree
    signedAtomRequestCallProgram_oracleFree

def signedAtomRequestListFuel (codes : List ℕ) (wanted maskCode : ℕ) : ℕ :=
  linkFuel signedAtomRequestCallProgram
    (generatedBalancedRangeFuel codes.length codes.length
      (signedAtomRangeContext codes wanted maskCode))
    (linkFuel (balancedCallProgram signedAtomRequestProgram) 2
      (balancedCallFuel signedAtomRequestProgram (signedAtomLeafFuel codes)
        (signedAtomRangeRequests codes wanted maskCode)))

def signedAtomRequestListCalleeBits
    (codes : List ℕ) (wanted maskCode : ℕ) : ℕ :=
  ((List.range codes.length).map fun index =>
    signedAtomRequestBits codes index wanted maskCode
      (codes.getD index 0)).foldr max 1

def signedAtomRequestListStageBits
    (codes : List ℕ) (wanted maskCode : ℕ) : List ℕ :=
  [ 1
  , natBitLength codes.length
  , generatedBalancedRangeRequiredBits codes.length codes.length
      (signedAtomRangeContext codes wanted maskCode)
  , leftProjectionBits
      (encodeBalancedList (signedAtomRangeRequests codes wanted maskCode))
      (signedAtomRangeContext codes wanted maskCode)
  , balancedCallRequiredBits (signedAtomLeafOutput codes wanted maskCode)
      (signedAtomRangeRequests codes wanted maskCode)
  , signedAtomRequestListCalleeBits codes wanted maskCode
  ]

def signedAtomRequestListBits (codes : List ℕ) (wanted maskCode : ℕ) : ℕ :=
  (signedAtomRequestListStageBits codes wanted maskCode).foldr max 1

/-- **One masked accumulator's request list, executed.**  The gate's weight
code and the coordinate mask are consumed exactly once each. -/
theorem run_signedAtomRequestListProgram
    (codes : List ℕ) (wanted maskCode maximumBits : ℕ)
    (hbits : signedAtomRequestListBits codes wanted maskCode ≤ maximumBits) :
    runNPOracleProgram signedAtomRequestListProgram maximumBits
        (signedAtomRequestListFuel codes wanted maskCode)
        (initialNPOracleState codes.length
          (generatedBalancedRangeInput codes.length
            (signedAtomRangeContext codes wanted maskCode))) =
      some
        (encodeBalancedList
          ((signedAtomRangeRequests codes wanted maskCode).map
            (signedAtomLeafOutput codes wanted maskCode))) := by
  have bits_of_member {value : ℕ}
      (hvalue : value ∈ signedAtomRequestListStageBits codes wanted maskCode) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [signedAtomRequestListStageBits]
  have hlength : natBitLength codes.length ≤ maximumBits := by
    apply bits_of_member
    simp [signedAtomRequestListStageBits]
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel codes.length codes.length
            (signedAtomRangeContext codes wanted maskCode))
          (initialNPOracleState codes.length
            (generatedBalancedRangeInput codes.length
              (signedAtomRangeContext codes wanted maskCode))) =
        some
          (Nat.pair
            (encodeBalancedList (signedAtomRangeRequests codes wanted maskCode))
            (signedAtomRangeContext codes wanted maskCode)) := by
    refine run_bits_mono
      (run_generatedBalancedRangeProgram codes.length codes.length
        (signedAtomRangeContext codes wanted maskCode)) ?_
    apply bits_of_member
    simp [signedAtomRequestListStageBits]
  have hproject :
      runNPOracleProgram leftProjectionProgram maximumBits 2
          (initialNPOracleState codes.length
            (Nat.pair
              (encodeBalancedList
                (signedAtomRangeRequests codes wanted maskCode))
              (signedAtomRangeContext codes wanted maskCode))) =
        some
          (encodeBalancedList
            (signedAtomRangeRequests codes wanted maskCode)) := by
    refine run_bits_mono
      (run_leftProjectionProgram codes.length
        (encodeBalancedList (signedAtomRangeRequests codes wanted maskCode))
        (signedAtomRangeContext codes wanted maskCode)) ?_
    apply bits_of_member
    simp [signedAtomRequestListStageBits]
  have hcalleeBits :
      signedAtomRequestListCalleeBits codes wanted maskCode ≤ maximumBits := by
    apply bits_of_member
    simp [signedAtomRequestListStageBits]
  have hcallBits :
      balancedCallRequiredBits (signedAtomLeafOutput codes wanted maskCode)
          (signedAtomRangeRequests codes wanted maskCode) ≤
        maximumBits := by
    apply bits_of_member
    simp [signedAtomRequestListStageBits]
  have hexec : ∀ raw : ℕ,
      raw ∈ signedAtomRangeRequests codes wanted maskCode →
      runNPOracleProgram signedAtomRequestProgram maximumBits
          (signedAtomLeafFuel codes raw)
          (initialNPOracleState (Nat.unpair raw).1 (Nat.unpair raw).2) =
        some (signedAtomLeafOutput codes wanted maskCode raw) := by
    intro raw hraw
    have hmembers :
        signedAtomRangeRequests codes wanted maskCode =
          (List.range codes.length).map fun offset =>
            balancedRangeRequestAtom codes.length (0 + offset)
              (signedAtomRangeContext codes wanted maskCode) :=
      balancedRangeRequestAtoms_eq_map_range codes.length
        (signedAtomRangeContext codes wanted maskCode) 0 codes.length
    rw [hmembers] at hraw
    obtain ⟨offset, hoffset, hatom⟩ := List.mem_map.mp hraw
    have hindex : offset < codes.length := List.mem_range.mp hoffset
    have hgetD : codes.getD offset 0 = codes[offset] :=
      List.getD_eq_getElem codes 0 hindex
    have hweight : codes[offset]? = some (codes.getD offset 0) := by
      rw [hgetD]
      exact List.getElem?_eq_getElem hindex
    have hraw_eq :
        raw =
          balancedRangeRequestAtom codes.length offset
            (signedAtomRangeContext codes wanted maskCode) := by
      rw [← hatom]
      simp
    have hleft : (Nat.unpair raw).1 = codes.length := by
      rw [hraw_eq]
      simp [balancedRangeRequestAtom]
    have hright :
        (Nat.unpair raw).2 =
          signedAtomFrame offset (encodeBalancedList codes) wanted maskCode := by
      rw [hraw_eq]
      simp [balancedRangeRequestAtom, signedAtomFrame, signedAtomRangeContext]
    have hframeIndex : signedAtomFrameIndex raw = offset := by
      rw [hraw_eq]
      exact signedAtomFrameIndex_atom codes.length offset
        (encodeBalancedList codes) wanted maskCode
    have hstageBits :
        signedAtomRequestBits codes offset wanted maskCode
            (codes.getD offset 0) ≤
          maximumBits := by
      refine le_trans ?_ hcalleeBits
      exact le_foldr_max_of_mem
        (List.mem_map_of_mem (List.mem_range.mpr hindex))
    have hstage :=
      run_signedAtomRequestProgram codes offset wanted maskCode
        (codes.getD offset 0) maximumBits hweight hstageBits
    rw [hleft, hright, signedAtomLeafFuel, signedAtomLeafOutput, hframeIndex]
    exact hstage
  have hcall :=
    run_balancedCallProgram_from
      (callee := signedAtomRequestProgram) (maximumBits := maximumBits)
      codes.length (signedAtomRangeRequests codes wanted maskCode)
      (signedAtomLeafFuel codes) (signedAtomLeafOutput codes wanted maskCode)
      hcallBits hexec
  exact run_linkPrograms hpositive hlength hrange
    (run_linkPrograms hpositive hlength hproject hcall)

/-! ## §7 The atom list the machine names

Instantiating the code list at a gate's canonical weight syntax identifies the
executed list with `signedAtomRequests` of `gateAtoms`: exactly the balanced
request list `run_signedAtomTotalProgram` consumes. -/

private theorem signedAtomRangeRequests_eq (codes : List ℕ) (wanted maskCode : ℕ) :
    signedAtomRangeRequests codes wanted maskCode =
      (List.range codes.length).map fun index =>
        balancedRangeRequestAtom codes.length index
          (signedAtomRangeContext codes wanted maskCode) := by
  unfold signedAtomRangeRequests
  rw [balancedRangeRequestAtoms_eq_map_range]
  simp

private theorem signedAtomLeafOutput_atom
    (codes : List ℕ) (arity index wanted maskCode : ℕ) :
    signedAtomLeafOutput codes wanted maskCode
        (balancedRangeRequestAtom arity index
          (signedAtomRangeContext codes wanted maskCode)) =
      Nat.pair codes.length
        (Nat.pair (codes.getD index 0)
          (Nat.pair wanted (boolCode (maskCode.testBit index)))) := by
  unfold signedAtomLeafOutput signedAtomRangeContext
  rw [signedAtomFrameIndex_atom]

theorem map_signedAtomLeafOutput_ofFn
    {n : ℕ} (weight : Fin n → ℤ) (wanted maskCode : ℕ) :
    (signedAtomRangeRequests ((List.ofFn weight).map encodeInt) wanted
        maskCode).map
        (signedAtomLeafOutput ((List.ofFn weight).map encodeInt) wanted
          maskCode) =
      signedAtomRequests n
        (List.ofFn fun index : Fin n =>
          (weight index, wanted, maskCode.testBit index.val)) := by
  rw [signedAtomRangeRequests_eq, List.map_map]
  unfold signedAtomRequests
  refine List.ext_getElem (by simp) ?_
  intro index hleft hright
  have hindex : index < n := by
    simpa using hright
  have hlengthCodes : ((List.ofFn weight).map encodeInt).length = n := by
    simp
  have hgetD :
      ((List.ofFn weight).map encodeInt).getD index 0 =
        encodeInt (weight ⟨index, hindex⟩) := by
    rw [List.getD_eq_getElem _ _ (by simpa [hlengthCodes] using hindex)]
    simp
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn,
    Function.comp_apply]
  rw [signedAtomLeafOutput_atom, hgetD, hlengthCodes]
  simp [signedAtomRequest, nativeInputRequest, signedAtomCode]

/-- **One masked accumulator's atom list, executed from the gate's canonical
weight syntax.**  This is the balanced request list of
`run_signedAtomTotalProgram` for every accumulator whose coordinate selector is
a single mask digit. -/
theorem run_signedAtomRequestListProgram_gateAtoms
    {n : ℕ} (gate : NormalizedThresholdGate n) (wanted maskCode maximumBits : ℕ)
    (hbits :
      signedAtomRequestListBits ((List.ofFn gate.weight).map encodeInt) wanted
          maskCode ≤
        maximumBits) :
    runNPOracleProgram signedAtomRequestListProgram maximumBits
        (signedAtomRequestListFuel ((List.ofFn gate.weight).map encodeInt)
          wanted maskCode)
        (initialNPOracleState ((List.ofFn gate.weight).map encodeInt).length
          (generatedBalancedRangeInput
            ((List.ofFn gate.weight).map encodeInt).length
            (signedAtomRangeContext ((List.ofFn gate.weight).map encodeInt)
              wanted maskCode))) =
      some
        (encodeBalancedList
          (signedAtomRequests n
            (gateAtoms gate wanted fun index => maskCode.testBit index.val))) := by
  have hrun :=
    run_signedAtomRequestListProgram ((List.ofFn gate.weight).map encodeInt)
      wanted maskCode maximumBits hbits
  rw [map_signedAtomLeafOutput_ofFn gate.weight wanted maskCode] at hrun
  exact hrun

/-! ## §8 The frozen coordinate: two mask digits and one subtraction

`residualConstantLeftAtoms` and `residualConstantRightAtoms` select their
coordinates with `frozenSelector`, which is `AND NOT` of the input and live
digits.  On single bits saturating subtraction is exactly that, so the frozen
coordinate stage is the uniform stage with a second one-digit slice and one
`subtract` instruction.  Carrying the two masks as one pair leaves the lookup
frame of §2 untouched.

Taking the second mask to be zero recovers the uniform selector, so this one
machine covers every atom list of `CanonicalSignedGateEvaluationProgram`. -/

/-- The two masks of a frozen coordinate, carried as one context field. -/
def signedAtomMaskPair (inputMask liveMask : ℕ) : ℕ :=
  Nat.pair inputMask liveMask

/-- The frozen coordinate's bit: the input digit that the live mask does not
cover. -/
def frozenAtomBit (inputMask liveMask index : ℕ) : Bool :=
  inputMask.testBit index && !liveMask.testBit index

theorem boolCode_sub (left right : Bool) :
    boolCode left - boolCode right = boolCode (left && !right) := by
  cases left <;> cases right <;> simp [boolCode]

/-- Frame the input mask's digit, retaining the weight code, the requested
sign, the index, and the live mask. -/
def signedAtomFirstSliceFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .set 10 1 9
  , .pair 10 8 11 10
  , .pair 4 11 12 11
  , .pair 4 9 13 12
  , .pair 6 13 14 13
  , .pair 2 14 15 14
  , .pair 12 15 0 15
  , .halt 0
  ]

@[simp] theorem signedAtomFirstSliceFrameProgram_oracleFree :
    OracleFree signedAtomFirstSliceFrameProgram := by
  rfl

def signedAtomFirstSliceFrameFuel : ℕ := 16

/-- The first slice request beside the retained frozen context. -/
def signedAtomFirstSliceFrame
    (index weightCode wanted inputMask liveMask : ℕ) : ℕ :=
  Nat.pair (bitSliceInput index 1 inputMask)
    (Nat.pair weightCode (Nat.pair wanted (Nat.pair index liveMask)))

private def signedAtomFirstSliceFrameValues
    (index weightCode wanted inputMask liveMask : ℕ) : List ℕ :=
  [ Nat.pair weightCode
      (Nat.pair index
        (Nat.pair wanted (signedAtomMaskPair inputMask liveMask)))
  , weightCode
  , Nat.pair index (Nat.pair wanted (signedAtomMaskPair inputMask liveMask))
  , index
  , Nat.pair wanted (signedAtomMaskPair inputMask liveMask)
  , wanted
  , signedAtomMaskPair inputMask liveMask
  , inputMask
  , liveMask
  , 1
  , Nat.pair 1 inputMask
  , bitSliceInput index 1 inputMask
  , Nat.pair index liveMask
  , Nat.pair wanted (Nat.pair index liveMask)
  , Nat.pair weightCode (Nat.pair wanted (Nat.pair index liveMask))
  , signedAtomFirstSliceFrame index weightCode wanted inputMask liveMask
  ]

def signedAtomFirstSliceFrameBits
    (index weightCode wanted inputMask liveMask : ℕ) : ℕ :=
  natBitLength
    ((signedAtomFirstSliceFrameValues index weightCode wanted inputMask
      liveMask).foldr max 1)

private theorem signedAtomFirstSliceFrame_value_bits
    (index weightCode wanted inputMask liveMask : ℕ) {candidate : ℕ}
    (hcandidate :
      candidate ∈
        signedAtomFirstSliceFrameValues index weightCode wanted inputMask
          liveMask) :
    natBitLength candidate ≤
      signedAtomFirstSliceFrameBits index weightCode wanted inputMask
        liveMask :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

theorem run_signedAtomFirstSliceFrameProgram
    (arity index weightCode wanted inputMask liveMask maximumBits : ℕ)
    (hbits :
      signedAtomFirstSliceFrameBits index weightCode wanted inputMask
          liveMask ≤
        maximumBits) :
    runNPOracleProgram signedAtomFirstSliceFrameProgram maximumBits
        signedAtomFirstSliceFrameFuel
        (initialNPOracleState arity
          (Nat.pair weightCode
            (Nat.pair index
              (Nat.pair wanted (signedAtomMaskPair inputMask liveMask))))) =
      some
        (signedAtomFirstSliceFrame index weightCode wanted inputMask
          liveMask) := by
  have hweightBits : natBitLength weightCode ≤ maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have htailBits :
      natBitLength
          (Nat.pair index
            (Nat.pair wanted (signedAtomMaskPair inputMask liveMask))) ≤
        maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have hindexBits : natBitLength index ≤ maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have hsignBits :
      natBitLength
          (Nat.pair wanted (signedAtomMaskPair inputMask liveMask)) ≤
        maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have hwantedBits : natBitLength wanted ≤ maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have hmasksBits :
      natBitLength (signedAtomMaskPair inputMask liveMask) ≤ maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have hinputBits : natBitLength inputMask ≤ maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have hliveBits : natBitLength liveMask ≤ maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have hwidthBits : natBitLength (Nat.pair 1 inputMask) ≤ maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have hsliceBits :
      natBitLength (bitSliceInput index 1 inputMask) ≤ maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have hcarryBits : natBitLength (Nat.pair index liveMask) ≤ maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have hsignCarryBits :
      natBitLength (Nat.pair wanted (Nat.pair index liveMask)) ≤ maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have hretainBits :
      natBitLength
          (Nat.pair weightCode (Nat.pair wanted (Nat.pair index liveMask))) ≤
        maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  have houtputBits :
      natBitLength
          (signedAtomFirstSliceFrame index weightCode wanted inputMask
            liveMask) ≤
        maximumBits :=
    (signedAtomFirstSliceFrame_value_bits index weightCode wanted inputMask
      liveMask (by simp [signedAtomFirstSliceFrameValues])).trans hbits
  rw [show signedAtomFirstSliceFrameFuel = 15 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := weightCode) (by rfl) rfl
    (by simp [initialNPOracleState]) hweightBits]
  rw [show (15 : ℕ) = 14 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair index (Nat.pair wanted (signedAtomMaskPair inputMask liveMask)))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [show (14 : ℕ) = 13 + 1 by omega]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hindexBits]
  rw [show (13 : ℕ) = 12 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair wanted (signedAtomMaskPair inputMask liveMask))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsignBits]
  rw [show (12 : ℕ) = 11 + 1 by omega]
  rw [run_unpairLeft_instruction (value := wanted) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwantedBits]
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := signedAtomMaskPair inputMask liveMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmasksBits]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := inputMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomMaskPair])
    hinputBits]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := liveMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, signedAtomMaskPair])
    hliveBits]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_set_instruction (register := 10) (value := 1) (next := 9)
    (by rfl) rfl honeBits]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 1 inputMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_pair_instruction (value := bitSliceInput index 1 inputMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSliceInput])
    hsliceBits]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair index liveMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcarryBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair wanted (Nat.pair index liveMask)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsignCarryBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair weightCode (Nat.pair wanted (Nat.pair index liveMask)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hretainBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      signedAtomFirstSliceFrame index weightCode wanted inputMask liveMask)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        signedAtomFirstSliceFrame])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value :=
      signedAtomFirstSliceFrame index weightCode wanted inputMask liveMask)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Frame the live mask's digit, retaining the weight code, the requested
sign, and the input digit already read. -/
def signedAtomSecondSliceFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .set 10 1 9
  , .pair 10 9 11 10
  , .pair 8 11 12 11
  , .pair 6 2 13 12
  , .pair 4 13 14 13
  , .pair 12 14 0 14
  , .halt 0
  ]

@[simp] theorem signedAtomSecondSliceFrameProgram_oracleFree :
    OracleFree signedAtomSecondSliceFrameProgram := by
  rfl

def signedAtomSecondSliceFrameFuel : ℕ := 15

/-- The second slice request beside the retained weight, sign, and digit. -/
def signedAtomSecondSliceFrame
    (index weightCode wanted inputBit liveMask : ℕ) : ℕ :=
  Nat.pair (bitSliceInput index 1 liveMask)
    (Nat.pair weightCode (Nat.pair wanted inputBit))

private def signedAtomSecondSliceFrameValues
    (index weightCode wanted inputBit liveMask : ℕ) : List ℕ :=
  [ Nat.pair inputBit
      (Nat.pair weightCode (Nat.pair wanted (Nat.pair index liveMask)))
  , inputBit
  , Nat.pair weightCode (Nat.pair wanted (Nat.pair index liveMask))
  , weightCode
  , Nat.pair wanted (Nat.pair index liveMask)
  , wanted
  , Nat.pair index liveMask
  , index
  , liveMask
  , 1
  , Nat.pair 1 liveMask
  , bitSliceInput index 1 liveMask
  , Nat.pair wanted inputBit
  , Nat.pair weightCode (Nat.pair wanted inputBit)
  , signedAtomSecondSliceFrame index weightCode wanted inputBit liveMask
  ]

def signedAtomSecondSliceFrameBits
    (index weightCode wanted inputBit liveMask : ℕ) : ℕ :=
  natBitLength
    ((signedAtomSecondSliceFrameValues index weightCode wanted inputBit
      liveMask).foldr max 1)

private theorem signedAtomSecondSliceFrame_value_bits
    (index weightCode wanted inputBit liveMask : ℕ) {candidate : ℕ}
    (hcandidate :
      candidate ∈
        signedAtomSecondSliceFrameValues index weightCode wanted inputBit
          liveMask) :
    natBitLength candidate ≤
      signedAtomSecondSliceFrameBits index weightCode wanted inputBit
        liveMask :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

theorem run_signedAtomSecondSliceFrameProgram
    (arity index weightCode wanted inputBit liveMask maximumBits : ℕ)
    (hbits :
      signedAtomSecondSliceFrameBits index weightCode wanted inputBit
          liveMask ≤
        maximumBits) :
    runNPOracleProgram signedAtomSecondSliceFrameProgram maximumBits
        signedAtomSecondSliceFrameFuel
        (initialNPOracleState arity
          (Nat.pair inputBit
            (Nat.pair weightCode
              (Nat.pair wanted (Nat.pair index liveMask))))) =
      some
        (signedAtomSecondSliceFrame index weightCode wanted inputBit
          liveMask) := by
  have hbitBits : natBitLength inputBit ≤ maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have htailBits :
      natBitLength
          (Nat.pair weightCode (Nat.pair wanted (Nat.pair index liveMask))) ≤
        maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have hweightBits : natBitLength weightCode ≤ maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have hsignBits :
      natBitLength (Nat.pair wanted (Nat.pair index liveMask)) ≤ maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have hwantedBits : natBitLength wanted ≤ maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have hcarryBits : natBitLength (Nat.pair index liveMask) ≤ maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have hindexBits : natBitLength index ≤ maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have hliveBits : natBitLength liveMask ≤ maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have hwidthBits : natBitLength (Nat.pair 1 liveMask) ≤ maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have hsliceBits :
      natBitLength (bitSliceInput index 1 liveMask) ≤ maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have hframeBits : natBitLength (Nat.pair wanted inputBit) ≤ maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have hretainBits :
      natBitLength (Nat.pair weightCode (Nat.pair wanted inputBit)) ≤
        maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  have houtputBits :
      natBitLength
          (signedAtomSecondSliceFrame index weightCode wanted inputBit
            liveMask) ≤
        maximumBits :=
    (signedAtomSecondSliceFrame_value_bits index weightCode wanted inputBit
      liveMask (by simp [signedAtomSecondSliceFrameValues])).trans hbits
  rw [show signedAtomSecondSliceFrameFuel = 14 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := inputBit) (by rfl) rfl
    (by simp [initialNPOracleState]) hbitBits]
  rw [show (14 : ℕ) = 13 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair weightCode (Nat.pair wanted (Nat.pair index liveMask)))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [show (13 : ℕ) = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := weightCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hweightBits]
  rw [show (12 : ℕ) = 11 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair wanted (Nat.pair index liveMask)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsignBits]
  rw [show (11 : ℕ) = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := wanted) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwantedBits]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair index liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcarryBits]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := index) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hindexBits]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := liveMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hliveBits]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_set_instruction (register := 10) (value := 1) (next := 9)
    (by rfl) rfl honeBits]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 1 liveMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_pair_instruction (value := bitSliceInput index 1 liveMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSliceInput])
    hsliceBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair wanted inputBit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hframeBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair weightCode (Nat.pair wanted inputBit)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hretainBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      signedAtomSecondSliceFrame index weightCode wanted inputBit liveMask)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        signedAtomSecondSliceFrame])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value :=
      signedAtomSecondSliceFrame index weightCode wanted inputBit liveMask)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Subtract the live digit from the input digit and assemble the frozen
coordinate's balanced-call request. -/
def signedAtomSubtractAssembleProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .subtract 7 2 8 7
  , .pair 6 8 9 8
  , .pair 4 9 10 9
  , .pair 1 10 0 10
  , .halt 0
  ]

@[simp] theorem signedAtomSubtractAssembleProgram_oracleFree :
    OracleFree signedAtomSubtractAssembleProgram := by
  rfl

def signedAtomSubtractAssembleFuel : ℕ := 11

private def signedAtomSubtractAssembleValues
    (arity weightCode wanted inputBit liveBit : ℕ) : List ℕ :=
  [ arity
  , Nat.pair liveBit (Nat.pair weightCode (Nat.pair wanted inputBit))
  , liveBit
  , Nat.pair weightCode (Nat.pair wanted inputBit)
  , weightCode
  , Nat.pair wanted inputBit
  , wanted
  , inputBit
  , inputBit - liveBit
  , Nat.pair wanted (inputBit - liveBit)
  , Nat.pair weightCode (Nat.pair wanted (inputBit - liveBit))
  , Nat.pair arity (Nat.pair weightCode (Nat.pair wanted (inputBit - liveBit)))
  ]

def signedAtomSubtractAssembleBits
    (arity weightCode wanted inputBit liveBit : ℕ) : ℕ :=
  natBitLength
    ((signedAtomSubtractAssembleValues arity weightCode wanted inputBit
      liveBit).foldr max 1)

private theorem signedAtomSubtractAssemble_value_bits
    (arity weightCode wanted inputBit liveBit : ℕ) {candidate : ℕ}
    (hcandidate :
      candidate ∈
        signedAtomSubtractAssembleValues arity weightCode wanted inputBit
          liveBit) :
    natBitLength candidate ≤
      signedAtomSubtractAssembleBits arity weightCode wanted inputBit
        liveBit :=
  natBitLength_mono (le_foldr_max_of_mem hcandidate)

theorem run_signedAtomSubtractAssembleProgram
    (arity weightCode wanted inputBit liveBit maximumBits : ℕ)
    (hbits :
      signedAtomSubtractAssembleBits arity weightCode wanted inputBit
          liveBit ≤
        maximumBits) :
    runNPOracleProgram signedAtomSubtractAssembleProgram maximumBits
        signedAtomSubtractAssembleFuel
        (initialNPOracleState arity
          (Nat.pair liveBit
            (Nat.pair weightCode (Nat.pair wanted inputBit)))) =
      some
        (Nat.pair arity
          (Nat.pair weightCode
            (Nat.pair wanted (inputBit - liveBit)))) := by
  have hliveBits : natBitLength liveBit ≤ maximumBits :=
    (signedAtomSubtractAssemble_value_bits arity weightCode wanted inputBit
      liveBit (by simp [signedAtomSubtractAssembleValues])).trans hbits
  have htailBits :
      natBitLength (Nat.pair weightCode (Nat.pair wanted inputBit)) ≤
        maximumBits :=
    (signedAtomSubtractAssemble_value_bits arity weightCode wanted inputBit
      liveBit (by simp [signedAtomSubtractAssembleValues])).trans hbits
  have hweightBits : natBitLength weightCode ≤ maximumBits :=
    (signedAtomSubtractAssemble_value_bits arity weightCode wanted inputBit
      liveBit (by simp [signedAtomSubtractAssembleValues])).trans hbits
  have hframeBits : natBitLength (Nat.pair wanted inputBit) ≤ maximumBits :=
    (signedAtomSubtractAssemble_value_bits arity weightCode wanted inputBit
      liveBit (by simp [signedAtomSubtractAssembleValues])).trans hbits
  have hwantedBits : natBitLength wanted ≤ maximumBits :=
    (signedAtomSubtractAssemble_value_bits arity weightCode wanted inputBit
      liveBit (by simp [signedAtomSubtractAssembleValues])).trans hbits
  have hinputBits : natBitLength inputBit ≤ maximumBits :=
    (signedAtomSubtractAssemble_value_bits arity weightCode wanted inputBit
      liveBit (by simp [signedAtomSubtractAssembleValues])).trans hbits
  have hdifferenceBits : natBitLength (inputBit - liveBit) ≤ maximumBits :=
    (signedAtomSubtractAssemble_value_bits arity weightCode wanted inputBit
      liveBit (by simp [signedAtomSubtractAssembleValues])).trans hbits
  have hsignBits :
      natBitLength (Nat.pair wanted (inputBit - liveBit)) ≤ maximumBits :=
    (signedAtomSubtractAssemble_value_bits arity weightCode wanted inputBit
      liveBit (by simp [signedAtomSubtractAssembleValues])).trans hbits
  have hcodeBits :
      natBitLength
          (Nat.pair weightCode (Nat.pair wanted (inputBit - liveBit))) ≤
        maximumBits :=
    (signedAtomSubtractAssemble_value_bits arity weightCode wanted inputBit
      liveBit (by simp [signedAtomSubtractAssembleValues])).trans hbits
  have houtputBits :
      natBitLength
          (Nat.pair arity
            (Nat.pair weightCode (Nat.pair wanted (inputBit - liveBit)))) ≤
        maximumBits :=
    (signedAtomSubtractAssemble_value_bits arity weightCode wanted inputBit
      liveBit (by simp [signedAtomSubtractAssembleValues])).trans hbits
  rw [show signedAtomSubtractAssembleFuel = 10 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := liveBit) (by rfl) rfl
    (by simp [initialNPOracleState]) hliveBits]
  rw [show (10 : ℕ) = 9 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair weightCode (Nat.pair wanted inputBit)) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [show (9 : ℕ) = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := weightCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hweightBits]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair wanted inputBit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hframeBits]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := wanted) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwantedBits]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := inputBit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hinputBits]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_subtract_instruction (value := inputBit - liveBit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdifferenceBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair wanted (inputBit - liveBit))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsignBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair weightCode (Nat.pair wanted (inputBit - liveBit)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcodeBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair arity
        (Nat.pair weightCode (Nat.pair wanted (inputBit - liveBit))))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value :=
      Nat.pair arity
        (Nat.pair weightCode (Nat.pair wanted (inputBit - liveBit))))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-! ## §9 The frozen coordinate stage

Seven stages: frame the lookup, select the weight, frame and read the input
digit, frame and read the live digit, subtract and assemble.  Taking
`liveMask = 0` leaves the input digit untouched, so this machine also names the
uniform selectors of §4. -/

/-- Read the live digit, subtract, and assemble. -/
def frozenAtomDigitProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitSliceProgram)
    signedAtomSubtractAssembleProgram

/-- Frame the live digit, then `frozenAtomDigitProgram`. -/
def frozenAtomSecondProgram : NPOracleProgram :=
  linkPrograms signedAtomSecondSliceFrameProgram frozenAtomDigitProgram

/-- Read the input digit, then `frozenAtomSecondProgram`. -/
def frozenAtomFirstDigitProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitSliceProgram) frozenAtomSecondProgram

/-- Frame the input digit, then `frozenAtomFirstDigitProgram`. -/
def frozenAtomSelectedProgram : NPOracleProgram :=
  linkPrograms signedAtomFirstSliceFrameProgram frozenAtomFirstDigitProgram

/-- Select the coordinate's weight, then `frozenAtomSelectedProgram`. -/
def frozenAtomWeightProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram canonicalBalancedLookupProgram)
    frozenAtomSelectedProgram

/-- **The frozen coordinate's signed atom request machine.** -/
def frozenAtomRequestProgram : NPOracleProgram :=
  linkPrograms signedAtomLookupFrameProgram frozenAtomWeightProgram

theorem frozenAtomDigitProgram_oracleFree : OracleFree frozenAtomDigitProgram :=
  oracleFree_linkPrograms
    (preserveRightProgram_oracleFree bitSliceProgram bitSliceProgram_oracleFree)
    signedAtomSubtractAssembleProgram_oracleFree

theorem frozenAtomSecondProgram_oracleFree :
    OracleFree frozenAtomSecondProgram :=
  oracleFree_linkPrograms signedAtomSecondSliceFrameProgram_oracleFree
    frozenAtomDigitProgram_oracleFree

theorem frozenAtomFirstDigitProgram_oracleFree :
    OracleFree frozenAtomFirstDigitProgram :=
  oracleFree_linkPrograms
    (preserveRightProgram_oracleFree bitSliceProgram bitSliceProgram_oracleFree)
    frozenAtomSecondProgram_oracleFree

theorem frozenAtomSelectedProgram_oracleFree :
    OracleFree frozenAtomSelectedProgram :=
  oracleFree_linkPrograms signedAtomFirstSliceFrameProgram_oracleFree
    frozenAtomFirstDigitProgram_oracleFree

theorem frozenAtomWeightProgram_oracleFree :
    OracleFree frozenAtomWeightProgram :=
  oracleFree_linkPrograms
    (preserveRightProgram_oracleFree canonicalBalancedLookupProgram
      canonicalBalancedLookupProgram_oracleFree)
    frozenAtomSelectedProgram_oracleFree

theorem frozenAtomRequestProgram_oracleFree :
    OracleFree frozenAtomRequestProgram :=
  oracleFree_linkPrograms signedAtomLookupFrameProgram_oracleFree
    frozenAtomWeightProgram_oracleFree

def frozenAtomRequestFuel (codes : List ℕ) (index : ℕ) : ℕ :=
  linkFuel frozenAtomWeightProgram signedAtomLookupFrameFuel
    (linkFuel frozenAtomSelectedProgram
      (preserveRightFuel (balancedLookupFuel codes index))
      (linkFuel frozenAtomFirstDigitProgram signedAtomFirstSliceFrameFuel
        (linkFuel frozenAtomSecondProgram (preserveRightFuel (bitSliceFuel 1))
          (linkFuel frozenAtomDigitProgram signedAtomSecondSliceFrameFuel
            (linkFuel signedAtomSubtractAssembleProgram
              (preserveRightFuel (bitSliceFuel 1))
              signedAtomSubtractAssembleFuel)))))

def frozenAtomRequestStageBits
    (codes : List ℕ) (index wanted inputMask liveMask weightCode : ℕ) :
    List ℕ :=
  [ 1
  , natBitLength codes.length
  , signedAtomLookupFrameBits codes.length index (encodeBalancedList codes)
      wanted (signedAtomMaskPair inputMask liveMask)
  , preserveRightBits (balancedLookupMaximumBits codes index)
      (balancedLookupInput codes index)
      (Nat.pair index
        (Nat.pair wanted (signedAtomMaskPair inputMask liveMask)))
      weightCode
  , signedAtomFirstSliceFrameBits index weightCode wanted inputMask liveMask
  , preserveRightBits (bitSliceBits codes.length index 1 inputMask)
      (bitSliceInput index 1 inputMask)
      (Nat.pair weightCode (Nat.pair wanted (Nat.pair index liveMask)))
      (bitSlice index 1 inputMask)
  , signedAtomSecondSliceFrameBits index weightCode wanted
      (bitSlice index 1 inputMask) liveMask
  , preserveRightBits (bitSliceBits codes.length index 1 liveMask)
      (bitSliceInput index 1 liveMask)
      (Nat.pair weightCode (Nat.pair wanted (bitSlice index 1 inputMask)))
      (bitSlice index 1 liveMask)
  , signedAtomSubtractAssembleBits codes.length weightCode wanted
      (bitSlice index 1 inputMask) (bitSlice index 1 liveMask)
  ]

def frozenAtomRequestBits
    (codes : List ℕ) (index wanted inputMask liveMask weightCode : ℕ) : ℕ :=
  (frozenAtomRequestStageBits codes index wanted inputMask liveMask
    weightCode).foldr max 1

/-- **One frozen coordinate's signed atom request, executed.**  The two masks
are read one digit at a time and combined by the saturating subtraction that
implements `AND NOT` on single bits. -/
theorem run_frozenAtomRequestProgram
    (codes : List ℕ)
    (index wanted inputMask liveMask weightCode maximumBits : ℕ)
    (hweight : codes[index]? = some weightCode)
    (hbits :
      frozenAtomRequestBits codes index wanted inputMask liveMask weightCode ≤
        maximumBits) :
    runNPOracleProgram frozenAtomRequestProgram maximumBits
        (frozenAtomRequestFuel codes index)
        (initialNPOracleState codes.length
          (signedAtomFrame index (encodeBalancedList codes) wanted
            (signedAtomMaskPair inputMask liveMask))) =
      some
        (Nat.pair codes.length
          (Nat.pair weightCode
            (Nat.pair wanted
              (boolCode (frozenAtomBit inputMask liveMask index))))) := by
  have hindex : index < codes.length := by
    have := List.getElem?_eq_some_iff.mp hweight
    exact this.choose
  have hselected : codes[index] = weightCode := by
    have hsome : codes[index]? = some codes[index] :=
      List.getElem?_eq_getElem hindex
    rw [hsome] at hweight
    exact Option.some.inj hweight
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          frozenAtomRequestStageBits codes index wanted inputMask liveMask
            weightCode) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [frozenAtomRequestStageBits]
  have hlength : natBitLength codes.length ≤ maximumBits := by
    apply bits_of_member
    simp [frozenAtomRequestStageBits]
  have hframe :
      runNPOracleProgram signedAtomLookupFrameProgram maximumBits
          signedAtomLookupFrameFuel
          (initialNPOracleState codes.length
            (signedAtomFrame index (encodeBalancedList codes) wanted
              (signedAtomMaskPair inputMask liveMask))) =
        some
          (Nat.pair (balancedLookupInput codes index)
            (Nat.pair index
              (Nat.pair wanted (signedAtomMaskPair inputMask liveMask)))) := by
    refine run_signedAtomLookupFrameProgram codes.length index
      (encodeBalancedList codes) wanted (signedAtomMaskPair inputMask liveMask)
      maximumBits ?_
    apply bits_of_member
    simp [frozenAtomRequestStageBits]
  have hweightStage :
      runNPOracleProgram (preserveRightProgram canonicalBalancedLookupProgram)
          maximumBits (preserveRightFuel (balancedLookupFuel codes index))
          (initialNPOracleState codes.length
            (Nat.pair (balancedLookupInput codes index)
              (Nat.pair index
                (Nat.pair wanted (signedAtomMaskPair inputMask liveMask))))) =
        some
          (Nat.pair weightCode
            (Nat.pair index
              (Nat.pair wanted (signedAtomMaskPair inputMask liveMask)))) := by
    have hsource :
        runNPOracleProgram canonicalBalancedLookupProgram
            (balancedLookupMaximumBits codes index)
            (balancedLookupFuel codes index)
            (initialNPOracleState codes.length
              (balancedLookupInput codes index)) =
          some weightCode := by
      rw [← hselected]
      exact run_canonicalBalancedLookupProgram codes index codes.length hindex
    refine run_bits_mono
      (run_preserveRightProgram canonicalBalancedLookupProgram codes.length
        (balancedLookupMaximumBits codes index)
        (balancedLookupFuel codes index) (balancedLookupInput codes index)
        (Nat.pair index
          (Nat.pair wanted (signedAtomMaskPair inputMask liveMask)))
        weightCode hsource) ?_
    apply bits_of_member
    simp [frozenAtomRequestStageBits]
  have hfirstFrame :
      runNPOracleProgram signedAtomFirstSliceFrameProgram maximumBits
          signedAtomFirstSliceFrameFuel
          (initialNPOracleState codes.length
            (Nat.pair weightCode
              (Nat.pair index
                (Nat.pair wanted (signedAtomMaskPair inputMask liveMask))))) =
        some
          (Nat.pair (bitSliceInput index 1 inputMask)
            (Nat.pair weightCode
              (Nat.pair wanted (Nat.pair index liveMask)))) := by
    refine run_signedAtomFirstSliceFrameProgram codes.length index weightCode
      wanted inputMask liveMask maximumBits ?_
    apply bits_of_member
    simp [frozenAtomRequestStageBits]
  have hfirstDigit :
      runNPOracleProgram (preserveRightProgram bitSliceProgram) maximumBits
          (preserveRightFuel (bitSliceFuel 1))
          (initialNPOracleState codes.length
            (Nat.pair (bitSliceInput index 1 inputMask)
              (Nat.pair weightCode
                (Nat.pair wanted (Nat.pair index liveMask))))) =
        some
          (Nat.pair (bitSlice index 1 inputMask)
            (Nat.pair weightCode
              (Nat.pair wanted (Nat.pair index liveMask)))) := by
    refine run_bits_mono
      (run_preserveRightProgram bitSliceProgram codes.length
        (bitSliceBits codes.length index 1 inputMask) (bitSliceFuel 1)
        (bitSliceInput index 1 inputMask)
        (Nat.pair weightCode (Nat.pair wanted (Nat.pair index liveMask)))
        (bitSlice index 1 inputMask)
        (run_bitSliceProgram codes.length index 1 inputMask)) ?_
    apply bits_of_member
    simp [frozenAtomRequestStageBits]
  have hsecondFrame :
      runNPOracleProgram signedAtomSecondSliceFrameProgram maximumBits
          signedAtomSecondSliceFrameFuel
          (initialNPOracleState codes.length
            (Nat.pair (bitSlice index 1 inputMask)
              (Nat.pair weightCode
                (Nat.pair wanted (Nat.pair index liveMask))))) =
        some
          (Nat.pair (bitSliceInput index 1 liveMask)
            (Nat.pair weightCode
              (Nat.pair wanted (bitSlice index 1 inputMask)))) := by
    refine run_signedAtomSecondSliceFrameProgram codes.length index weightCode
      wanted (bitSlice index 1 inputMask) liveMask maximumBits ?_
    apply bits_of_member
    simp [frozenAtomRequestStageBits]
  have hsecondDigit :
      runNPOracleProgram (preserveRightProgram bitSliceProgram) maximumBits
          (preserveRightFuel (bitSliceFuel 1))
          (initialNPOracleState codes.length
            (Nat.pair (bitSliceInput index 1 liveMask)
              (Nat.pair weightCode
                (Nat.pair wanted (bitSlice index 1 inputMask))))) =
        some
          (Nat.pair (bitSlice index 1 liveMask)
            (Nat.pair weightCode
              (Nat.pair wanted (bitSlice index 1 inputMask)))) := by
    refine run_bits_mono
      (run_preserveRightProgram bitSliceProgram codes.length
        (bitSliceBits codes.length index 1 liveMask) (bitSliceFuel 1)
        (bitSliceInput index 1 liveMask)
        (Nat.pair weightCode (Nat.pair wanted (bitSlice index 1 inputMask)))
        (bitSlice index 1 liveMask)
        (run_bitSliceProgram codes.length index 1 liveMask)) ?_
    apply bits_of_member
    simp [frozenAtomRequestStageBits]
  have hassemble :
      runNPOracleProgram signedAtomSubtractAssembleProgram maximumBits
          signedAtomSubtractAssembleFuel
          (initialNPOracleState codes.length
            (Nat.pair (bitSlice index 1 liveMask)
              (Nat.pair weightCode
                (Nat.pair wanted (bitSlice index 1 inputMask))))) =
        some
          (Nat.pair codes.length
            (Nat.pair weightCode
              (Nat.pair wanted
                (bitSlice index 1 inputMask - bitSlice index 1 liveMask)))) := by
    refine run_signedAtomSubtractAssembleProgram codes.length weightCode wanted
      (bitSlice index 1 inputMask) (bitSlice index 1 liveMask) maximumBits ?_
    apply bits_of_member
    simp [frozenAtomRequestStageBits]
  have hfrozen :
      bitSlice index 1 inputMask - bitSlice index 1 liveMask =
        boolCode (frozenAtomBit inputMask liveMask index) := by
    rw [bitSlice_one_eq_boolCode, bitSlice_one_eq_boolCode, boolCode_sub]
    rfl
  rw [← hfrozen]
  exact run_linkPrograms hpositive hlength hframe
    (run_linkPrograms hpositive hlength hweightStage
      (run_linkPrograms hpositive hlength hfirstFrame
        (run_linkPrograms hpositive hlength hfirstDigit
          (run_linkPrograms hpositive hlength hsecondFrame
            (run_linkPrograms hpositive hlength hsecondDigit hassemble)))))

/-! ## §10 The atom list over an arbitrary coordinate stage

The generator, the projection, and the balanced call do not depend on which
coordinate stage is mapped, so the list builder takes that stage as a
link-time parameter with one contract per index.  `signedAtomRequestListProgram`
is the uniform instance of this program by definition. -/

/-- **The atom request list builder** over one coordinate stage. -/
def atomRequestListProgram (stage : NPOracleProgram) : NPOracleProgram :=
  linkPrograms generatedBalancedRangeProgram
    (linkPrograms leftProjectionProgram (balancedCallProgram stage))

theorem atomRequestListProgram_oracleFree
    (stage : NPOracleProgram) (hstage : OracleFree stage) :
    OracleFree (atomRequestListProgram stage) :=
  oracleFree_linkPrograms generatedBalancedRangeProgram_oracleFree
    (oracleFree_linkPrograms leftProjectionProgram_oracleFree
      (balancedCallProgram_oracleFree hstage))

def atomRequestListFuel
    (stage : NPOracleProgram) (codes : List ℕ) (wanted maskCode : ℕ)
    (leafFuel : ℕ → ℕ) : ℕ :=
  linkFuel (linkPrograms leftProjectionProgram (balancedCallProgram stage))
    (generatedBalancedRangeFuel codes.length codes.length
      (signedAtomRangeContext codes wanted maskCode))
    (linkFuel (balancedCallProgram stage) 2
      (balancedCallFuel stage (fun raw => leafFuel (signedAtomFrameIndex raw))
        (signedAtomRangeRequests codes wanted maskCode)))

def atomRequestListStageBits
    (codes : List ℕ) (wanted maskCode : ℕ) (leafOutput : ℕ → ℕ) : List ℕ :=
  [ 1
  , natBitLength codes.length
  , generatedBalancedRangeRequiredBits codes.length codes.length
      (signedAtomRangeContext codes wanted maskCode)
  , leftProjectionBits
      (encodeBalancedList (signedAtomRangeRequests codes wanted maskCode))
      (signedAtomRangeContext codes wanted maskCode)
  , balancedCallRequiredBits (fun raw => leafOutput (signedAtomFrameIndex raw))
      (signedAtomRangeRequests codes wanted maskCode)
  ]

def atomRequestListBits
    (codes : List ℕ) (wanted maskCode : ℕ) (leafOutput : ℕ → ℕ) : ℕ :=
  (atomRequestListStageBits codes wanted maskCode leafOutput).foldr max 1

private theorem map_signedAtomFrameIndex
    (codes : List ℕ) (wanted maskCode : ℕ) (leafOutput : ℕ → ℕ) :
    (signedAtomRangeRequests codes wanted maskCode).map
        (fun raw => leafOutput (signedAtomFrameIndex raw)) =
      (List.range codes.length).map leafOutput := by
  rw [signedAtomRangeRequests_eq, List.map_map]
  refine List.map_congr_left ?_
  intro index _
  simp only [Function.comp_apply, signedAtomRangeContext]
  rw [signedAtomFrameIndex_atom]

/-- **The atom request list, executed** over any coordinate stage meeting one
contract per index. -/
theorem run_atomRequestListProgram
    (stage : NPOracleProgram) (codes : List ℕ)
    (wanted maskCode maximumBits : ℕ) (leafFuel leafOutput : ℕ → ℕ)
    (hbits : atomRequestListBits codes wanted maskCode leafOutput ≤ maximumBits)
    (hleaf : ∀ index : ℕ, index < codes.length →
      runNPOracleProgram stage maximumBits (leafFuel index)
          (initialNPOracleState codes.length
            (signedAtomFrame index (encodeBalancedList codes) wanted
              maskCode)) =
        some (leafOutput index)) :
    runNPOracleProgram (atomRequestListProgram stage) maximumBits
        (atomRequestListFuel stage codes wanted maskCode leafFuel)
        (initialNPOracleState codes.length
          (generatedBalancedRangeInput codes.length
            (signedAtomRangeContext codes wanted maskCode))) =
      some
        (encodeBalancedList ((List.range codes.length).map leafOutput)) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈ atomRequestListStageBits codes wanted maskCode leafOutput) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [atomRequestListStageBits]
  have hlength : natBitLength codes.length ≤ maximumBits := by
    apply bits_of_member
    simp [atomRequestListStageBits]
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel codes.length codes.length
            (signedAtomRangeContext codes wanted maskCode))
          (initialNPOracleState codes.length
            (generatedBalancedRangeInput codes.length
              (signedAtomRangeContext codes wanted maskCode))) =
        some
          (Nat.pair
            (encodeBalancedList (signedAtomRangeRequests codes wanted maskCode))
            (signedAtomRangeContext codes wanted maskCode)) := by
    refine run_bits_mono
      (run_generatedBalancedRangeProgram codes.length codes.length
        (signedAtomRangeContext codes wanted maskCode)) ?_
    apply bits_of_member
    simp [atomRequestListStageBits]
  have hproject :
      runNPOracleProgram leftProjectionProgram maximumBits 2
          (initialNPOracleState codes.length
            (Nat.pair
              (encodeBalancedList
                (signedAtomRangeRequests codes wanted maskCode))
              (signedAtomRangeContext codes wanted maskCode))) =
        some
          (encodeBalancedList
            (signedAtomRangeRequests codes wanted maskCode)) := by
    refine run_bits_mono
      (run_leftProjectionProgram codes.length
        (encodeBalancedList (signedAtomRangeRequests codes wanted maskCode))
        (signedAtomRangeContext codes wanted maskCode)) ?_
    apply bits_of_member
    simp [atomRequestListStageBits]
  have hcallBits :
      balancedCallRequiredBits
          (fun raw => leafOutput (signedAtomFrameIndex raw))
          (signedAtomRangeRequests codes wanted maskCode) ≤
        maximumBits := by
    apply bits_of_member
    simp [atomRequestListStageBits]
  have hexec : ∀ raw : ℕ,
      raw ∈ signedAtomRangeRequests codes wanted maskCode →
      runNPOracleProgram stage maximumBits
          (leafFuel (signedAtomFrameIndex raw))
          (initialNPOracleState (Nat.unpair raw).1 (Nat.unpair raw).2) =
        some (leafOutput (signedAtomFrameIndex raw)) := by
    intro raw hraw
    rw [signedAtomRangeRequests_eq] at hraw
    obtain ⟨offset, hoffset, hatom⟩ := List.mem_map.mp hraw
    have hindex : offset < codes.length := List.mem_range.mp hoffset
    have hraw_eq :
        raw =
          balancedRangeRequestAtom codes.length offset
            (signedAtomRangeContext codes wanted maskCode) := hatom.symm
    have hleft : (Nat.unpair raw).1 = codes.length := by
      rw [hraw_eq]
      simp [balancedRangeRequestAtom]
    have hright :
        (Nat.unpair raw).2 =
          signedAtomFrame offset (encodeBalancedList codes) wanted maskCode := by
      rw [hraw_eq]
      simp [balancedRangeRequestAtom, signedAtomFrame, signedAtomRangeContext]
    have hframeIndex : signedAtomFrameIndex raw = offset := by
      rw [hraw_eq, signedAtomRangeContext]
      exact signedAtomFrameIndex_atom codes.length offset
        (encodeBalancedList codes) wanted maskCode
    rw [hleft, hright, hframeIndex]
    exact hleaf offset hindex
  have hcall :=
    run_balancedCallProgram_from
      (callee := stage) (maximumBits := maximumBits)
      codes.length (signedAtomRangeRequests codes wanted maskCode)
      (fun raw => leafFuel (signedAtomFrameIndex raw))
      (fun raw => leafOutput (signedAtomFrameIndex raw)) hcallBits hexec
  rw [map_signedAtomFrameIndex] at hcall
  exact run_linkPrograms hpositive hlength hrange
    (run_linkPrograms hpositive hlength hproject hcall)

/-! ## §11 The frozen atom list

The frozen instance of §10.  Its output is `signedAtomRequests` of
`gateAtoms gate wanted (frozenSelector inputMask liveMask)`: the coordinate
body of both `residualConstant` atom lists. -/

def frozenAtomLeafOutput
    (codes : List ℕ) (wanted inputMask liveMask index : ℕ) : ℕ :=
  Nat.pair codes.length
    (Nat.pair (codes.getD index 0)
      (Nat.pair wanted (boolCode (frozenAtomBit inputMask liveMask index))))

def frozenAtomListCalleeBits
    (codes : List ℕ) (wanted inputMask liveMask : ℕ) : ℕ :=
  ((List.range codes.length).map fun index =>
    frozenAtomRequestBits codes index wanted inputMask liveMask
      (codes.getD index 0)).foldr max 1

def frozenAtomListBits
    (codes : List ℕ) (wanted inputMask liveMask : ℕ) : ℕ :=
  max
    (atomRequestListBits codes wanted (signedAtomMaskPair inputMask liveMask)
      (frozenAtomLeafOutput codes wanted inputMask liveMask))
    (frozenAtomListCalleeBits codes wanted inputMask liveMask)

def frozenAtomListFuel
    (codes : List ℕ) (wanted inputMask liveMask : ℕ) : ℕ :=
  atomRequestListFuel frozenAtomRequestProgram codes wanted
    (signedAtomMaskPair inputMask liveMask) (frozenAtomRequestFuel codes)

/-- **The frozen atom list, executed.** -/
theorem run_frozenAtomListProgram
    (codes : List ℕ) (wanted inputMask liveMask maximumBits : ℕ)
    (hbits : frozenAtomListBits codes wanted inputMask liveMask ≤ maximumBits) :
    runNPOracleProgram (atomRequestListProgram frozenAtomRequestProgram)
        maximumBits (frozenAtomListFuel codes wanted inputMask liveMask)
        (initialNPOracleState codes.length
          (generatedBalancedRangeInput codes.length
            (signedAtomRangeContext codes wanted
              (signedAtomMaskPair inputMask liveMask)))) =
      some
        (encodeBalancedList
          ((List.range codes.length).map
            (frozenAtomLeafOutput codes wanted inputMask liveMask))) := by
  have hlistBits :
      atomRequestListBits codes wanted (signedAtomMaskPair inputMask liveMask)
          (frozenAtomLeafOutput codes wanted inputMask liveMask) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hcalleeBits :
      frozenAtomListCalleeBits codes wanted inputMask liveMask ≤ maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  refine run_atomRequestListProgram frozenAtomRequestProgram codes wanted
    (signedAtomMaskPair inputMask liveMask) maximumBits
    (frozenAtomRequestFuel codes)
    (frozenAtomLeafOutput codes wanted inputMask liveMask) hlistBits ?_
  intro index hindex
  have hgetD : codes.getD index 0 = codes[index] :=
    List.getD_eq_getElem codes 0 hindex
  have hweight : codes[index]? = some (codes.getD index 0) := by
    rw [hgetD]
    exact List.getElem?_eq_getElem hindex
  have hstageBits :
      frozenAtomRequestBits codes index wanted inputMask liveMask
          (codes.getD index 0) ≤
        maximumBits := by
    refine le_trans ?_ hcalleeBits
    exact le_foldr_max_of_mem
      (List.mem_map_of_mem (List.mem_range.mpr hindex))
  exact run_frozenAtomRequestProgram codes index wanted inputMask liveMask
    (codes.getD index 0) maximumBits hweight hstageBits

theorem map_frozenAtomLeafOutput_ofFn
    {n : ℕ} (weight : Fin n → ℤ) (wanted inputMask liveMask : ℕ) :
    (List.range ((List.ofFn weight).map encodeInt).length).map
        (frozenAtomLeafOutput ((List.ofFn weight).map encodeInt) wanted
          inputMask liveMask) =
      signedAtomRequests n
        (List.ofFn fun index : Fin n =>
          (weight index, wanted,
            frozenAtomBit inputMask liveMask index.val)) := by
  unfold signedAtomRequests
  refine List.ext_getElem (by simp) ?_
  intro index hleft hright
  have hindex : index < n := by
    simpa using hright
  have hlengthCodes : ((List.ofFn weight).map encodeInt).length = n := by
    simp
  have hgetD :
      ((List.ofFn weight).map encodeInt).getD index 0 =
        encodeInt (weight ⟨index, hindex⟩) := by
    rw [List.getD_eq_getElem _ _ (by simpa [hlengthCodes] using hindex)]
    simp
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [frozenAtomLeafOutput, hgetD, hlengthCodes]
  simp [signedAtomRequest, nativeInputRequest, signedAtomCode]

/-- **The frozen atom list of one gate, executed.**  This is the balanced
request list of `run_signedAtomTotalProgram` for the frozen halves of
`residualConstantLeftAtoms` and `residualConstantRightAtoms`. -/
theorem run_frozenAtomListProgram_gateAtoms
    {n : ℕ} (gate : NormalizedThresholdGate n)
    (wanted inputMask liveMask maximumBits : ℕ)
    (hbits :
      frozenAtomListBits ((List.ofFn gate.weight).map encodeInt) wanted
          inputMask liveMask ≤
        maximumBits) :
    runNPOracleProgram (atomRequestListProgram frozenAtomRequestProgram)
        maximumBits
        (frozenAtomListFuel ((List.ofFn gate.weight).map encodeInt) wanted
          inputMask liveMask)
        (initialNPOracleState ((List.ofFn gate.weight).map encodeInt).length
          (generatedBalancedRangeInput
            ((List.ofFn gate.weight).map encodeInt).length
            (signedAtomRangeContext ((List.ofFn gate.weight).map encodeInt)
              wanted (signedAtomMaskPair inputMask liveMask)))) =
      some
        (encodeBalancedList
          (signedAtomRequests n
            (gateAtoms gate wanted (frozenSelector inputMask liveMask)))) := by
  have hrun :=
    run_frozenAtomListProgram ((List.ofFn gate.weight).map encodeInt) wanted
      inputMask liveMask maximumBits hbits
  rw [map_frozenAtomLeafOutput_ofFn gate.weight wanted inputMask liveMask]
    at hrun
  exact hrun

end NearCubicWires.CanonicalSignedAtomRequestProgram
