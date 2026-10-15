import Proof.Foundations.CanonicalBinaryProgram
import Proof.Amplification.RecoveryWitnessPolicy

/-!
# Canonical globally admissible weak-witness shape

The refuter contract requires a fixed executable witness width bounded by one
tenth of every input length, including small lengths.  A four-bit right shift
computes `n / 16` exactly, avoiding the capacity troughs of pairing-coordinate
projections while leaving linear room for the eventual polylogarithmic
recovery certificate.
-/

namespace NearCubicWires.RecoveryWitnessShape

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.VerifiedLinker

def recoveryWitnessWidth (inputLength : ℕ) : ℕ :=
  inputLength >>> 4

theorem recoveryWitnessWidth_eq (inputLength : ℕ) :
    recoveryWitnessWidth inputLength = inputLength / 16 := by
  simp [recoveryWitnessWidth, Nat.shiftRight_eq_div_pow]

def recoveryWitnessShapeProgram : NPOracleProgram :=
  [.shiftRight 0 4 0 1, .halt 0]

theorem recoveryWitnessShapeProgram_oracleFree :
    OracleFree recoveryWitnessShapeProgram := by
  simp [OracleFree, recoveryWitnessShapeProgram]

private theorem recoveryWitnessWidth_bits_le_budget (inputLength : ℕ) :
    natBitLength (recoveryWitnessWidth inputLength) ≤
      polynomialBudget 2 1 inputLength := by
  calc
    natBitLength (recoveryWitnessWidth inputLength) ≤
        natBitLength inputLength := by
      exact shiftRight_bits_le inputLength 4
    _ ≤ inputLength + 1 := natBitLength_le_succ inputLength
    _ ≤ polynomialBudget 2 1 inputLength := by
      simp [polynomialBudget]

theorem run_recoveryWitnessShapeProgram_two
    (inputLength maximumBits : ℕ)
    (hbits :
      natBitLength (recoveryWitnessWidth inputLength) ≤ maximumBits) :
    runNPOracleProgram recoveryWitnessShapeProgram maximumBits 2
        (initialNPOracleState inputLength inputLength) =
      some (recoveryWitnessWidth inputLength) := by
  let initial := initialNPOracleState inputLength inputLength
  let shifted :=
    (initial.write 0 (recoveryWitnessWidth inputLength)).jump 1
  calc
    runNPOracleProgram recoveryWitnessShapeProgram maximumBits 2 initial =
        runNPOracleProgram recoveryWitnessShapeProgram maximumBits 1
          shifted := by
      apply run_shiftRight_instruction
        (program := recoveryWitnessShapeProgram)
        (maximumBits := maximumBits) (fuel := 1) (pc := 0)
        (source := 0) (amount := 4) (destination := 0) (next := 1)
        (value := recoveryWitnessWidth inputLength) (state := initial)
      · simp [recoveryWitnessShapeProgram]
      · rfl
      · simp [initial, initialNPOracleState, recoveryWitnessWidth]
      · exact hbits
    _ = some (recoveryWitnessWidth inputLength) := by
      apply run_halt_instruction
        (program := recoveryWitnessShapeProgram)
        (maximumBits := maximumBits) (fuel := 0) (pc := 1)
        (outputRegister := 0) (value := recoveryWitnessWidth inputLength)
        (state := shifted)
      · simp [recoveryWitnessShapeProgram]
      · rfl
      · simp [shifted, initial, NPOracleState.write, NPOracleState.jump]
      · exact hbits

theorem run_recoveryWitnessShapeProgram (inputLength : ℕ) :
    runNPOracleProgram recoveryWitnessShapeProgram
        (polynomialBudget 2 1 inputLength)
        (polynomialBudget 2 1 inputLength)
        (initialNPOracleState inputLength inputLength) =
      some (recoveryWitnessWidth inputLength) := by
  have hminimum : 2 ≤ polynomialBudget 2 1 inputLength := by
    simp [polynomialBudget]
  obtain ⟨extra, hbudget⟩ := Nat.exists_eq_add_of_le hminimum
  have hrun := run_fuel_add
    (run_recoveryWitnessShapeProgram_two inputLength
      (polynomialBudget 2 1 inputLength)
      (recoveryWitnessWidth_bits_le_budget inputLength))
    extra
  rw [← hbudget] at hrun
  exact hrun

def recoveryWitnessShape :
    PolynomialNatProgram ℕ id id id where
  program := recoveryWitnessShapeProgram
  coefficient := 2
  coefficientPositive := by omega
  degree := 1
  initialBitsFit := by
    intro inputLength
    have hbits := natBitLength_le_succ inputLength
    simp only [id_eq, max_self, polynomialBudget, pow_one]
    omega
  halts := fun inputLength =>
    ⟨recoveryWitnessWidth inputLength,
      run_recoveryWitnessShapeProgram inputLength⟩

def recoveryWitnessShapeWitness :
    PolynomialNatProgramWitness ℕ id id id recoveryWitnessWidth where
  runner := recoveryWitnessShape
  computes := by
    intro inputLength
    simpa [PolynomialNatProgram.budget, recoveryWitnessShape] using
      run_recoveryWitnessShapeProgram inputLength

@[simp] theorem recoveryWitnessShape_execute (inputLength : ℕ) :
    recoveryWitnessShape.execute inputLength = inputLength / 16 := by
  have hrun := recoveryWitnessShapeWitness.execute_eq inputLength
  simpa [recoveryWitnessShapeWitness, recoveryWitnessWidth_eq] using hrun

theorem recoveryWitnessShape_admissible (inputLength : ℕ) :
    recoveryWitnessShape.execute inputLength ≤ inputLength / 10 := by
  rw [recoveryWitnessShape_execute]
  exact recoveryWitnessSixteenth_le_tenth inputLength

/-! ## Canonical zero extension -/

/-- A checked witness occupies the low bits of the fixed public width.  Bits
above its canonical code are zero by `Nat.testBit`; no padding is serialized as
an additional witness field. -/
def paddedRecoveryWitnessCode
    {limits : RecoveryWitnessLimits} (inputLength : ℕ)
    (witness : CheckedRecoveryWitness limits) :
    BitInput (recoveryWitnessWidth inputLength) :=
  fun bit => witness.code.testBit bit.val

theorem CheckedRecoveryWitness.bits_le_recoveryWitnessWidth
    {limits : RecoveryWitnessLimits} {inputLength : ℕ}
    (witness : CheckedRecoveryWitness limits)
    (hcapacity :
      recoveryWitnessCodeBitBound limits ≤
        recoveryWitnessWidth inputLength) :
    natBitLength witness.code ≤ recoveryWitnessWidth inputLength :=
  (NearCubicWires.RecoveryWitnessPolicy.CheckedRecoveryWitness.code_bits_le
    witness).trans hcapacity

/-- Reading the fixed-width bit vector recovers the canonical witness code
exactly whenever the public syntactic envelope fits. -/
@[simp] theorem encodeBitInput_paddedRecoveryWitnessCode
    {limits : RecoveryWitnessLimits} {inputLength : ℕ}
    (witness : CheckedRecoveryWitness limits)
    (hcapacity :
      recoveryWitnessCodeBitBound limits ≤
        recoveryWitnessWidth inputLength) :
    encodeBitInput (paddedRecoveryWitnessCode inputLength witness) =
      witness.code := by
  apply encodeBitInput_testBit
  have hcode :
      witness.code < 2 ^ natBitLength witness.code := by
    unfold natBitLength
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two witness.code
  exact hcode.trans_le
    (Nat.pow_le_pow_right (by omega)
      (NearCubicWires.RecoveryWitnessShape.CheckedRecoveryWitness.bits_le_recoveryWitnessWidth
        witness hcapacity))

end NearCubicWires.RecoveryWitnessShape
