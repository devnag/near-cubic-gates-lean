import Proof.MachineModel.CanonicalNatDecodeProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Canonical integer predecessor

The public integer syntax is `pair(sign, encodeNat magnitude)`.  This module
implements predecessor with one fixed oracle-free program: a structural
adapter places the magnitude first, the canonical natural decoder produces a
native magnitude while preserving the sign, and a fixed final stage performs
the three integer cases before restoring canonical syntax.
-/

namespace NearCubicWires.CanonicalIntPredecessorProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

def intSignCode (value : ℤ) : ℕ :=
  if value < 0 then 1 else 0

def intPredecessorPrepared (value : ℤ) : ℕ :=
  Nat.pair (encodeNat value.natAbs) (intSignCode value)

/-- Swap the canonical integer fields so the shared right-preserving adapter
can decode the magnitude without copying it into a second runtime format. -/
def intPredecessorPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 3 2 0 3
  , .halt 0
  ]

@[simp] theorem intPredecessorPrepareProgram_oracleFree :
    OracleFree intPredecessorPrepareProgram := by
  rfl

def intPredecessorPrepareFuel : ℕ := 4

private def intPredecessorPrepareWorkingValues
    (value : ℤ) : List ℕ :=
  [intSignCode value, encodeNat value.natAbs, encodeInt value,
    intPredecessorPrepared value]

private def intPredecessorPrepareWorkBound (value : ℤ) : ℕ :=
  (intPredecessorPrepareWorkingValues value).foldr max 1

def intPredecessorPrepareBits (value : ℤ) : ℕ :=
  natBitLength (intPredecessorPrepareWorkBound value)

private theorem intPredecessor_le_foldr_max_of_mem
    {candidate : ℕ} {values : List ℕ} (hmem : candidate ∈ values) :
    candidate ≤ values.foldr max 1 := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (ih hmem).trans (Nat.le_max_right _ _)

private theorem intPredecessorPrepare_value_bits
    (value : ℤ) (candidate : ℕ)
    (hmem : candidate ∈ intPredecessorPrepareWorkingValues value) :
    natBitLength candidate ≤ intPredecessorPrepareBits value := by
  unfold intPredecessorPrepareBits intPredecessorPrepareWorkBound
  exact natBitLength_mono (intPredecessor_le_foldr_max_of_mem hmem)

theorem run_intPredecessorPrepareProgram
    (inputLength : ℕ) (value : ℤ) :
    runNPOracleProgram intPredecessorPrepareProgram
        (intPredecessorPrepareBits value)
        intPredecessorPrepareFuel
        (initialNPOracleState inputLength (encodeInt value)) =
      some (intPredecessorPrepared value) := by
  let sign := intSignCode value
  let magnitudeCode := encodeNat value.natAbs
  let prepared := intPredecessorPrepared value
  let maximumBits := intPredecessorPrepareBits value
  have hsign : natBitLength sign ≤ maximumBits :=
    intPredecessorPrepare_value_bits value sign (by
      simp [intPredecessorPrepareWorkingValues, sign])
  have hmagnitudeCode : natBitLength magnitudeCode ≤ maximumBits :=
    intPredecessorPrepare_value_bits value magnitudeCode (by
      simp [intPredecessorPrepareWorkingValues, magnitudeCode])
  have hprepared : natBitLength prepared ≤ maximumBits :=
    intPredecessorPrepare_value_bits value prepared (by
      simp [intPredecessorPrepareWorkingValues, prepared])
  rw [show intPredecessorPrepareFuel = 3 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := sign)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, encodeInt, sign, intSignCode])
    hsign]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := magnitudeCode)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, encodeInt, magnitudeCode])
    hmagnitudeCode]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := prepared)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, prepared, intPredecessorPrepared,
        sign, magnitudeCode])
    hprepared]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, prepared])
    hprepared

/-! ## Native predecessor and canonical re-encoding -/

def intPredecessorFinishOutput (magnitude sign : ℕ) : ℕ :=
  if sign = 0 then
    if magnitude = 0 then
      Nat.pair 1 (encodeNat 1)
    else
      Nat.pair 0 (encodeNat magnitude.pred)
  else
    Nat.pair 1 (encodeNat (magnitude + 1))

/-- After the magnitude is native, only one branch diamond is needed.  The
zero and negative cases share the increment/re-encode tail; the positive case
decrements and rejoins immediately at the final pair. -/
def intPredecessorFinishProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .branchZero 3 3 7
  , .branchZero 2 7 4
  , .decrement 2 5
  , .encodeNat 2 4 6
  , .pair 3 4 0 10
  , .increment 2 8
  , .encodeNat 2 4 9
  , .set 3 1 6
  , .halt 0
  ]

@[simp] theorem intPredecessorFinishProgram_oracleFree :
    OracleFree intPredecessorFinishProgram := by
  rfl

def intPredecessorFinishFuel (magnitude sign : ℕ) : ℕ :=
  if sign = 0 ∧ magnitude = 0 then 9 else 8

private def intPredecessorFinishWorkingValues
    (magnitude sign : ℕ) : List ℕ :=
  [0, 1, magnitude, sign, Nat.pair magnitude sign,
    magnitude.pred, encodeNat magnitude.pred,
    Nat.pair 0 (encodeNat magnitude.pred),
    magnitude + 1, encodeNat (magnitude + 1),
    Nat.pair 1 (encodeNat (magnitude + 1)),
    intPredecessorFinishOutput magnitude sign]

private def intPredecessorFinishWorkBound
    (magnitude sign : ℕ) : ℕ :=
  (intPredecessorFinishWorkingValues magnitude sign).foldr max 1

def intPredecessorFinishBits (magnitude sign : ℕ) : ℕ :=
  natBitLength (intPredecessorFinishWorkBound magnitude sign)

private theorem intPredecessorFinish_value_bits
    (magnitude sign candidate : ℕ)
    (hmem :
      candidate ∈ intPredecessorFinishWorkingValues magnitude sign) :
    natBitLength candidate ≤
      intPredecessorFinishBits magnitude sign := by
  unfold intPredecessorFinishBits intPredecessorFinishWorkBound
  exact natBitLength_mono (intPredecessor_le_foldr_max_of_mem hmem)

theorem run_intPredecessorFinishProgram
    (inputLength magnitude sign : ℕ) :
    runNPOracleProgram intPredecessorFinishProgram
        (intPredecessorFinishBits magnitude sign)
        (intPredecessorFinishFuel magnitude sign)
        (initialNPOracleState inputLength (Nat.pair magnitude sign)) =
      some (intPredecessorFinishOutput magnitude sign) := by
  let output := intPredecessorFinishOutput magnitude sign
  let maximumBits := intPredecessorFinishBits magnitude sign
  have hbits :
      ∀ candidate,
        candidate ∈
            intPredecessorFinishWorkingValues magnitude sign →
          natBitLength candidate ≤ maximumBits :=
    intPredecessorFinish_value_bits magnitude sign
  have hmagnitude := hbits magnitude (by
    simp [intPredecessorFinishWorkingValues])
  have hsign := hbits sign (by
    simp [intPredecessorFinishWorkingValues])
  have hone := hbits 1 (by
    simp [intPredecessorFinishWorkingValues])
  have hpred := hbits magnitude.pred (by
    simp [intPredecessorFinishWorkingValues])
  have hpredCode := hbits (encodeNat magnitude.pred) (by
    simp [intPredecessorFinishWorkingValues])
  have hsucc := hbits (magnitude + 1) (by
    simp [intPredecessorFinishWorkingValues])
  have hsuccCode := hbits (encodeNat (magnitude + 1)) (by
    simp [intPredecessorFinishWorkingValues])
  have houtput := hbits output (by
    simp [intPredecessorFinishWorkingValues, output])
  let initial :=
    initialNPOracleState inputLength (Nat.pair magnitude sign)
  let state1 := (initial.write 2 magnitude).jump 1
  let state2 := (state1.write 3 sign).jump 2
  by_cases hsignZero : sign = 0
  · subst sign
    by_cases hmagnitudeZero : magnitude = 0
    · subst magnitude
      rw [show intPredecessorFinishFuel 0 0 = 8 + 1 by
        simp [intPredecessorFinishFuel]]
      rw [run_unpairLeft_instruction (value := 0)
        (by rfl) rfl
        (by rfl)
        hmagnitude]
      change
        runNPOracleProgram intPredecessorFinishProgram maximumBits
            8 state1 =
          some output
      rw [show 8 = 7 + 1 by omega]
      rw [run_unpairRight_instruction (value := 0)
        (by rfl) rfl
        (by simp [state1, initial, initialNPOracleState])
        hsign]
      change
        runNPOracleProgram intPredecessorFinishProgram maximumBits
            7 state2 =
          some output
      rw [show 7 = 6 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state2.registers 3 = 0 by simp [state2]]
      rw [if_pos rfl]
      rw [show 6 = 5 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show (state2.jump 3).registers 2 = 0 by
        simp [state2, state1]]
      rw [if_pos rfl]
      rw [show 5 = 4 + 1 by omega]
      rw [run_increment_instruction (value := 1)
        (by rfl) rfl
        (by simp [state2, state1])
        hone]
      rw [show 4 = 3 + 1 by omega]
      rw [run_encodeNat_instruction (value := 1)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        hsuccCode]
      rw [show 3 = 2 + 1 by omega]
      rw [run_set_instruction (value := 1)
        (by rfl) rfl hone]
      rw [show 2 = 1 + 1 by omega]
      rw [run_pair_instruction (value := output)
        (by rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump, output,
            intPredecessorFinishOutput])
        houtput]
      exact run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, output])
        houtput
    · rw [show intPredecessorFinishFuel magnitude 0 = 7 + 1 by
        simp [intPredecessorFinishFuel, hmagnitudeZero]]
      rw [run_unpairLeft_instruction (value := magnitude)
        (by rfl) rfl
        (by simp [initialNPOracleState])
        hmagnitude]
      change
        runNPOracleProgram intPredecessorFinishProgram maximumBits
            7 state1 =
          some output
      rw [show 7 = 6 + 1 by omega]
      rw [run_unpairRight_instruction (value := 0)
        (by rfl) rfl
        (by simp [state1, initial, initialNPOracleState])
        hsign]
      change
        runNPOracleProgram intPredecessorFinishProgram maximumBits
            6 state2 =
          some output
      rw [show 6 = 5 + 1 by omega]
      rw [run_branchZero_instruction
        (by rfl) rfl]
      rw [show state2.registers 3 = 0 by rfl]
      rw [if_pos rfl]
      rw [show 5 = 4 + 1 by omega]
      rw [run_branchZero_instruction
        (by rfl) rfl]
      rw [show (state2.jump 3).registers 2 = magnitude by
        simp [state2, state1]]
      rw [if_neg hmagnitudeZero]
      rw [show 4 = 3 + 1 by omega]
      rw [run_decrement_instruction (value := magnitude.pred)
        (by rfl) rfl
        (by simp [state2, state1])
        hpred]
      rw [show 3 = 2 + 1 by omega]
      rw [run_encodeNat_instruction (value := magnitude.pred)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        hpredCode]
      rw [show 2 = 1 + 1 by omega]
      rw [run_pair_instruction (value := output)
        (by rfl) rfl
        (by
          simp [state2, state1, initial, initialNPOracleState,
            NPOracleState.write, NPOracleState.jump, output,
            intPredecessorFinishOutput, hmagnitudeZero])
        houtput]
      exact run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, output])
        houtput
  · rw [show intPredecessorFinishFuel magnitude sign = 7 + 1 by
      simp [intPredecessorFinishFuel, hsignZero]]
    rw [run_unpairLeft_instruction (value := magnitude)
      (by rfl) rfl
      (by simp [initialNPOracleState])
      hmagnitude]
    change
      runNPOracleProgram intPredecessorFinishProgram maximumBits
          7 state1 =
        some output
    rw [show 7 = 6 + 1 by omega]
    rw [run_unpairRight_instruction (value := sign)
      (by rfl) rfl
      (by simp [state1, initial, initialNPOracleState])
      hsign]
    change
      runNPOracleProgram intPredecessorFinishProgram maximumBits
          6 state2 =
        some output
    rw [show 6 = 5 + 1 by omega]
    rw [run_branchZero_instruction (by rfl) rfl]
    rw [show state2.registers 3 = sign by simp [state2]]
    rw [if_neg hsignZero]
    rw [show 5 = 4 + 1 by omega]
    rw [run_increment_instruction (value := magnitude + 1)
      (by rfl) rfl
      (by simp [state2, state1])
      hsucc]
    rw [show 4 = 3 + 1 by omega]
    rw [run_encodeNat_instruction (value := magnitude + 1)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hsuccCode]
    rw [show 3 = 2 + 1 by omega]
    rw [run_set_instruction (value := 1)
      (by rfl) rfl hone]
    rw [show 2 = 1 + 1 by omega]
    rw [run_pair_instruction (value := output)
      (by rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, output,
          intPredecessorFinishOutput, hsignZero])
      houtput]
    exact run_halt_instruction (fuel := 0) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, output])
      houtput

theorem intPredecessorFinishOutput_eq_encodeInt_sub_one
    (value : ℤ) :
    intPredecessorFinishOutput value.natAbs (intSignCode value) =
      encodeInt (value - 1) := by
  cases value with
  | ofNat magnitude =>
      cases magnitude with
      | zero =>
          simp [intPredecessorFinishOutput, encodeInt]
      | succ magnitude =>
          have hsub :
              (Int.ofNat magnitude.succ - 1) =
                Int.ofNat magnitude := by
            simp
          change
            intPredecessorFinishOutput magnitude.succ 0 =
              encodeInt (Int.ofNat magnitude.succ - 1)
          rw [hsub]
          simp [intPredecessorFinishOutput, encodeInt]
  | negSucc magnitude =>
      simp [intPredecessorFinishOutput, intSignCode, encodeInt]

/-! ## One public linked program -/

def intPredecessorDecodeProgram : NPOracleProgram :=
  preserveRightProgram canonicalNatDecodeProgram

def intPredecessorCoreProgram : NPOracleProgram :=
  linkPrograms intPredecessorDecodeProgram
    intPredecessorFinishProgram

def canonicalIntPredecessorProgram : NPOracleProgram :=
  linkPrograms intPredecessorPrepareProgram
    intPredecessorCoreProgram

@[simp] theorem canonicalIntPredecessorProgram_oracleFree :
    OracleFree canonicalIntPredecessorProgram := by
  apply oracleFree_linkPrograms intPredecessorPrepareProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree _
      canonicalNatDecodeProgram_oracleFree
  · exact intPredecessorFinishProgram_oracleFree

def intPredecessorDecodeFuel (value : ℤ) : ℕ :=
  preserveRightFuel (canonicalNatDecodeFuel value.natAbs)

def intPredecessorCoreFuel (value : ℤ) : ℕ :=
  linkFuel intPredecessorFinishProgram
    (intPredecessorDecodeFuel value)
    (intPredecessorFinishFuel value.natAbs (intSignCode value))

def canonicalIntPredecessorFuel (value : ℤ) : ℕ :=
  linkFuel intPredecessorCoreProgram
    intPredecessorPrepareFuel
    (intPredecessorCoreFuel value)

def canonicalIntPredecessorBits
    (inputLength : ℕ) (value : ℤ) : ℕ :=
  max (natBitLength inputLength) <|
    max (intPredecessorPrepareBits value) <|
      max
        (preserveRightBits
          (canonicalNatDecodeBits inputLength value.natAbs)
          (encodeNat value.natAbs) (intSignCode value)
          value.natAbs)
        (intPredecessorFinishBits value.natAbs (intSignCode value))

/-- Exact execution of integer predecessor from and to the sole canonical
integer syntax.  Every arithmetic and codec step is checked by the fixed
interpreter; the proof uses no semantic callback or host-built terminal value.
-/
theorem run_canonicalIntPredecessorProgram
    (inputLength : ℕ) (value : ℤ) :
    runNPOracleProgram canonicalIntPredecessorProgram
        (canonicalIntPredecessorBits inputLength value)
        (canonicalIntPredecessorFuel value)
        (initialNPOracleState inputLength (encodeInt value)) =
      some (encodeInt (value - 1)) := by
  let sign := intSignCode value
  let magnitude := value.natAbs
  let magnitudeCode := encodeNat magnitude
  let prepared := Nat.pair magnitudeCode sign
  let decoded := Nat.pair magnitude sign
  let output := intPredecessorFinishOutput magnitude sign
  let maximumBits := canonicalIntPredecessorBits inputLength value
  let prepareBits := intPredecessorPrepareBits value
  let decodeBits :=
    preserveRightBits
      (canonicalNatDecodeBits inputLength magnitude)
      magnitudeCode sign magnitude
  let finishBits := intPredecessorFinishBits magnitude sign
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hprepareBits : prepareBits ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hdecodeBits : decodeBits ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hfinishBits : finishBits ≤ maximumBits := by
    exact (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlengthBits
  have hprepare :
      runNPOracleProgram intPredecessorPrepareProgram maximumBits
          intPredecessorPrepareFuel
          (initialNPOracleState inputLength (encodeInt value)) =
        some prepared := by
    have hrun :=
      run_bits_mono
        (run_intPredecessorPrepareProgram inputLength value)
        hprepareBits
    simpa only [prepared, intPredecessorPrepared, magnitudeCode,
      magnitude, sign] using hrun
  have hdecode :
      runNPOracleProgram intPredecessorDecodeProgram maximumBits
          (intPredecessorDecodeFuel value)
          (initialNPOracleState inputLength prepared) =
        some decoded := by
    have hrun :=
      run_preserveRightProgram canonicalNatDecodeProgram inputLength
        (canonicalNatDecodeBits inputLength magnitude)
        (canonicalNatDecodeFuel magnitude)
        magnitudeCode sign magnitude
        (run_canonicalNatDecodeProgram inputLength magnitude)
    exact run_bits_mono (by
      simpa only [intPredecessorDecodeProgram, decodeBits, prepared,
        decoded, intPredecessorDecodeFuel, magnitude] using hrun)
      hdecodeBits
  have hfinish :
      runNPOracleProgram intPredecessorFinishProgram maximumBits
          (intPredecessorFinishFuel magnitude sign)
          (initialNPOracleState inputLength decoded) =
        some output := by
    have hrun :=
      run_bits_mono
        (run_intPredecessorFinishProgram inputLength magnitude sign)
        hfinishBits
    simpa only [decoded, output] using hrun
  have hcore :
      runNPOracleProgram intPredecessorCoreProgram maximumBits
          (intPredecessorCoreFuel value)
          (initialNPOracleState inputLength prepared) =
        some output := by
    exact run_linkPrograms hpositive hlengthBits hdecode hfinish
  have hfull :
      runNPOracleProgram canonicalIntPredecessorProgram maximumBits
          (canonicalIntPredecessorFuel value)
          (initialNPOracleState inputLength (encodeInt value)) =
        some output := by
    exact run_linkPrograms hpositive hlengthBits hprepare hcore
  have hout : output = encodeInt (value - 1) := by
    dsimp only [output, magnitude, sign]
    exact intPredecessorFinishOutput_eq_encodeInt_sub_one value
  rw [hout] at hfull
  exact hfull

end NearCubicWires.CanonicalIntPredecessorProgram
