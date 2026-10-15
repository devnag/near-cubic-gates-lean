import Proof.Circuits.CanonicalBalancedTraversal
import Proof.Foundations.VerifiedLinker

/-!
# Canonical total Booleanization

This is the sole executable boundary from an arbitrary natural-valued stage to
a Boolean code.  Zero maps to zero and every nonzero value maps to one.  In
particular, narrow integer interpolation may be used on a certified good seed
without allowing an uncertified seed to contribute an unbounded value to a
later majority.
-/

namespace NearCubicWires.CanonicalBooleanizeProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.VerifiedLinker

def canonicalBooleanizeOutput (value : ℕ) : ℕ :=
  (decide (value ≠ 0) : Bool).toNat

def canonicalBooleanizeBits (value : ℕ) : ℕ :=
  max (natBitLength value) (natBitLength 1)

def canonicalBooleanizeProgram : NPOracleProgram :=
  [ .branchZero 0 1 2
  , .set 0 0 3
  , .set 0 1 3
  , .halt 0
  ]

def canonicalBooleanizeFinishState
    (inputLength value : ℕ) : NPOracleState :=
  (((initialNPOracleState inputLength value).jump
      (if value = 0 then 1 else 2)).write 0
        (canonicalBooleanizeOutput value)).jump 3

@[simp] theorem canonicalBooleanizeProgram_oracleFree :
    OracleFree canonicalBooleanizeProgram := by
  rfl

@[simp] theorem canonicalBooleanizeOutput_zero :
    canonicalBooleanizeOutput 0 = 0 := by
  rfl

theorem canonicalBooleanizeOutput_nonzero
    {value : ℕ} (hvalue : value ≠ 0) :
    canonicalBooleanizeOutput value = 1 := by
  simp [canonicalBooleanizeOutput, hvalue]

@[simp] theorem canonicalBooleanizeOutput_boolToNat (value : Bool) :
    canonicalBooleanizeOutput value.toNat = value.toNat := by
  cases value <;> rfl

theorem canonicalBooleanizeOutput_lt_two (value : ℕ) :
    canonicalBooleanizeOutput value < 2 := by
  by_cases hvalue : value = 0
  · simp [hvalue]
  · simp [canonicalBooleanizeOutput, hvalue]

@[simp] theorem canonicalBooleanizeOutput_encodeInt (value : ℤ) :
    canonicalBooleanizeOutput (encodeInt value) =
      (decide (value ≠ 0) : Bool).toNat := by
  by_cases hvalue : value = 0
  · simp [hvalue, encodeInt, encodeNat, encodeBits, encodeBoolList,
      encodeBalancedList, Nat.pair]
  · simp [canonicalBooleanizeOutput, hvalue]

theorem canonicalBooleanizeProgram_runsToIn
    (inputLength value : ℕ) :
    RunsToIn canonicalBooleanizeProgram
      (canonicalBooleanizeBits value) 2
      (initialNPOracleState inputLength value)
      (canonicalBooleanizeFinishState inputLength value) := by
  intro extra
  have hzeroBits :
      natBitLength 0 ≤ canonicalBooleanizeBits value := by
    exact (PolynomialClock.natBitLength_mono (Nat.zero_le value)).trans
      (Nat.le_max_left _ _)
  have honeBits :
      natBitLength 1 ≤ canonicalBooleanizeBits value :=
    Nat.le_max_right _ _
  rw [show 2 + extra = (1 + extra) + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  by_cases hvalue : value = 0
  · rw [show
      (initialNPOracleState inputLength value).registers 0 = 0 by
        simp [initialNPOracleState, hvalue]]
    rw [if_pos rfl]
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_set_instruction (fuel := extra) (pc := 1) (register := 0)
      (value := 0) (next := 3) (by rfl)
      (by simp [NPOracleState.jump]) hzeroBits]
    simp [canonicalBooleanizeFinishState, canonicalBooleanizeOutput,
      hvalue]
  · rw [show
      (initialNPOracleState inputLength value).registers 0 = value by
        simp [initialNPOracleState]]
    rw [if_neg hvalue]
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_set_instruction (fuel := extra) (pc := 2) (register := 0)
      (value := 1) (next := 3) (by rfl)
      (by simp [NPOracleState.jump]) honeBits]
    simp [canonicalBooleanizeFinishState, canonicalBooleanizeOutput,
      hvalue]

theorem canonicalBooleanizeProgram_runsWithin
    (inputLength value : ℕ) :
    RunsWithin canonicalBooleanizeProgram
      (canonicalBooleanizeBits value) 2
      (initialNPOracleState inputLength value)
      (· = canonicalBooleanizeFinishState inputLength value) :=
  (canonicalBooleanizeProgram_runsToIn inputLength value).toRunsWithin

theorem run_canonicalBooleanizeProgram
    (inputLength value : ℕ) :
    runNPOracleProgram canonicalBooleanizeProgram
        (canonicalBooleanizeBits value) 3
        (initialNPOracleState inputLength value) =
      some (canonicalBooleanizeOutput value) := by
  have hsegment :=
    canonicalBooleanizeProgram_runsToIn inputLength value 1
  rw [show 2 + 1 = 3 by omega] at hsegment
  rw [hsegment]
  apply run_halt_instruction (fuel := 0) (pc := 3)
    (outputRegister := 0) (value := canonicalBooleanizeOutput value) (by rfl)
  · simp [canonicalBooleanizeFinishState, NPOracleState.jump]
  · simp [canonicalBooleanizeFinishState, NPOracleState.write]
  · by_cases hvalue : value = 0
    · simp [canonicalBooleanizeOutput, hvalue, canonicalBooleanizeBits,
        natBitLength]
    · simp [canonicalBooleanizeOutput, hvalue, canonicalBooleanizeBits,
        natBitLength]

def booleanizedProgram (source : NPOracleProgram) : NPOracleProgram :=
  linkPrograms source canonicalBooleanizeProgram

def booleanizedFuel (sourceFuel : ℕ) : ℕ :=
  linkFuel canonicalBooleanizeProgram sourceFuel 3

theorem booleanizedProgram_oracleFree
    {source : NPOracleProgram} (hsource : OracleFree source) :
    OracleFree (booleanizedProgram source) :=
  oracleFree_linkPrograms hsource canonicalBooleanizeProgram_oracleFree

/-- Total staged execution.  The source may return any natural number; the
linked suffix always returns a code strictly below two. -/
theorem run_booleanizedProgram
    {source : NPOracleProgram}
    {maximumBits inputLength inputCode sourceFuel output : ℕ}
    (hbitsPositive : 1 ≤ maximumBits)
    (hinputLength : natBitLength inputLength ≤ maximumBits)
    (hsource :
      runNPOracleProgram source maximumBits sourceFuel
          (initialNPOracleState inputLength inputCode) =
        some output) :
    runNPOracleProgram (booleanizedProgram source) maximumBits
        (booleanizedFuel sourceFuel)
        (initialNPOracleState inputLength inputCode) =
      some (canonicalBooleanizeOutput output) := by
  apply run_linkPrograms hbitsPositive hinputLength hsource
  apply run_bits_mono
    (run_canonicalBooleanizeProgram inputLength output)
  unfold canonicalBooleanizeBits
  apply max_le
  · exact run_output_bounded hsource
  · simpa [natBitLength] using hbitsPositive

theorem run_booleanizedProgram_bool
    {source : NPOracleProgram}
    {maximumBits inputLength inputCode sourceFuel : ℕ}
    {value : Bool}
    (hbitsPositive : 1 ≤ maximumBits)
    (hinputLength : natBitLength inputLength ≤ maximumBits)
    (hsource :
      runNPOracleProgram source maximumBits sourceFuel
          (initialNPOracleState inputLength inputCode) =
        some value.toNat) :
    runNPOracleProgram (booleanizedProgram source) maximumBits
        (booleanizedFuel sourceFuel)
        (initialNPOracleState inputLength inputCode) =
      some value.toNat := by
  simpa using
    run_booleanizedProgram hbitsPositive hinputLength hsource

/-- Canonical signed rows use zero itself as the code for integer zero.
Consequently the same total suffix can safely Booleanize arbitrary signed row
values before a count or threshold stage. -/
theorem run_booleanizedProgram_encodeInt
    {source : NPOracleProgram}
    {maximumBits inputLength inputCode sourceFuel : ℕ}
    {value : ℤ}
    (hbitsPositive : 1 ≤ maximumBits)
    (hinputLength : natBitLength inputLength ≤ maximumBits)
    (hsource :
      runNPOracleProgram source maximumBits sourceFuel
          (initialNPOracleState inputLength inputCode) =
        some (encodeInt value)) :
    runNPOracleProgram (booleanizedProgram source) maximumBits
        (booleanizedFuel sourceFuel)
        (initialNPOracleState inputLength inputCode) =
      some ((decide (value ≠ 0) : Bool).toNat) := by
  simpa using
    run_booleanizedProgram hbitsPositive hinputLength hsource

end NearCubicWires.CanonicalBooleanizeProgram
