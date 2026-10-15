import Proof.MachineModel.CanonicalPaddedAmplifierEvaluationProgram
import Proof.MachineModel.CanonicalBooleanizeProgram
import Proof.MachineModel.CanonicalTaggedParityProgram
import Proof.MachineModel.TaggedProgramChoice

/-!
# One fixed target-bit evaluator

The target language has one executable entry point.  Tag zero invokes the
published Case-1 amplifier evaluator after canonical low-bit truncation; every
nonzero tag XORs the already evaluated Case-2 seed blocks.  A single final
suffix normalizes either branch to `0` or `1`, so no caller can attach a
different Boolean convention to an imported evaluator's nonzero output.
-/

namespace NearCubicWires.CanonicalTargetBitProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanizeProgram
open NearCubicWires.CanonicalPaddedAmplifierEvaluationProgram
open NearCubicWires.CanonicalTaggedParityProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-- The only Case-1/Case-2 dispatcher.  The program depends solely on the
published amplifier implementation; all per-instance values remain data. -/
def targetBitProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm) : NPOracleProgram :=
  linkPrograms
    (taggedProgramChoice
      (paddedAmplifierEvaluationProgram algorithm)
      balancedBitParityProgram)
    canonicalBooleanizeProgram

@[simp] theorem targetBitProgram_oracleFree
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm) :
    OracleFree (targetBitProgram algorithm) := by
  apply oracleFree_linkPrograms
  · exact taggedProgramChoice_oracleFree
      (paddedAmplifierEvaluationProgram algorithm)
      balancedBitParityProgram
      (paddedAmplifierEvaluationProgram_oracleFree algorithm)
      balancedBitParityProgram_oracleFree
  · exact canonicalBooleanizeProgram_oracleFree

def targetBitCaseOneInput
    (outputArity descriptor inputCode : ℕ) : ℕ :=
  Nat.pair 0 <|
    paddedAmplifierEvaluationInput outputArity descriptor inputCode

def targetBitCaseTwoInput (bits : List Bool) : ℕ :=
  Nat.pair 1 (encodeBalancedList (bits.map Bool.toNat))

private def targetBitMaximumBits
    (inputLength tag payload sourceBits sourceOutput : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max
      (natBitLength (Nat.pair inputLength (Nat.pair tag payload))) <|
      max sourceBits (canonicalBooleanizeBits sourceOutput)

def targetBitCaseOneFuel
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (outputArity descriptor inputCode : ℕ) : ℕ :=
  linkFuel canonicalBooleanizeProgram
    (taggedProgramChoiceFuel <|
      paddedAmplifierEvaluationFuel algorithm
        outputArity descriptor inputCode)
    3

def targetBitCaseOneBits
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (inputLength outputArity descriptor inputCode : ℕ) : ℕ :=
  let request :=
    paddedAmplifierEvaluationRequest outputArity descriptor inputCode
  targetBitMaximumBits inputLength 0
    (paddedAmplifierEvaluationInput outputArity descriptor inputCode)
    (paddedAmplifierEvaluationBits algorithm inputLength
      outputArity descriptor inputCode)
    (algorithm.evaluator.execute request)

def targetBitCaseTwoFuel (bits : List Bool) : ℕ :=
  linkFuel canonicalBooleanizeProgram
    (taggedProgramChoiceFuel <|
      balancedBitParityFuel (bits.map Bool.toNat))
    3

def targetBitCaseTwoBits
    (inputLength : ℕ) (bits : List Bool) : ℕ :=
  let rawBits := bits.map Bool.toNat
  targetBitMaximumBits inputLength 1
    (encodeBalancedList rawBits)
    (balancedBitParityBits inputLength rawBits)
    (taggedParity rawBits)

theorem run_targetBitProgram_caseOne
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (inputLength outputArity descriptor inputCode : ℕ) :
    let request :=
      paddedAmplifierEvaluationRequest outputArity descriptor inputCode
    runNPOracleProgram (targetBitProgram algorithm)
        (targetBitCaseOneBits algorithm inputLength
          outputArity descriptor inputCode)
        (targetBitCaseOneFuel algorithm
          outputArity descriptor inputCode)
        (initialNPOracleState inputLength
          (targetBitCaseOneInput
            outputArity descriptor inputCode)) =
      some
        ((decide
          (algorithm.evaluator.execute request ≠ 0) : Bool).toNat) := by
  dsimp only
  let request :=
    paddedAmplifierEvaluationRequest outputArity descriptor inputCode
  let payload :=
    paddedAmplifierEvaluationInput outputArity descriptor inputCode
  let output := algorithm.evaluator.execute request
  let sourceBits :=
    paddedAmplifierEvaluationBits algorithm inputLength
      outputArity descriptor inputCode
  let maximumBits :=
    targetBitCaseOneBits algorithm inputLength
      outputArity descriptor inputCode
  have hlengthBits :
      natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (by
      unfold natBitLength
      omega : 1 ≤ natBitLength inputLength).trans hlengthBits
  have hinputBits :
      natBitLength
          (Nat.pair inputLength (Nat.pair 0 payload)) ≤
        maximumBits := by
    exact
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsourceBits : sourceBits ≤ maximumBits := by
    exact
      (Nat.le_max_left _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hbooleanBits : canonicalBooleanizeBits output ≤ maximumBits := by
    exact
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hsource :
      runNPOracleProgram
          (paddedAmplifierEvaluationProgram algorithm)
          maximumBits
          (paddedAmplifierEvaluationFuel algorithm
            outputArity descriptor inputCode)
          (initialNPOracleState inputLength payload) =
        some output := by
    exact run_bits_mono
      (run_paddedAmplifierEvaluationProgram algorithm inputLength
        outputArity descriptor inputCode)
      hsourceBits
  have hchoice :
      runNPOracleProgram
          (taggedProgramChoice
            (paddedAmplifierEvaluationProgram algorithm)
            balancedBitParityProgram)
          maximumBits
          (taggedProgramChoiceFuel <|
            paddedAmplifierEvaluationFuel algorithm
              outputArity descriptor inputCode)
          (initialNPOracleState inputLength (Nat.pair 0 payload)) =
        some output := by
    exact run_taggedProgramChoice_zero
      (paddedAmplifierEvaluationProgram algorithm)
      balancedBitParityProgram inputLength payload maximumBits
      (paddedAmplifierEvaluationFuel algorithm
        outputArity descriptor inputCode)
      output hinputBits hsource (run_output_bounded hsource)
  have hboolean :
      runNPOracleProgram canonicalBooleanizeProgram maximumBits 3
          (initialNPOracleState inputLength output) =
        some (canonicalBooleanizeOutput output) :=
    run_bits_mono
      (run_canonicalBooleanizeProgram inputLength output)
      hbooleanBits
  have hrun :=
    run_linkPrograms hpositive hlengthBits hchoice hboolean
  simpa only [targetBitProgram, targetBitCaseOneFuel,
    targetBitCaseOneInput, targetBitCaseOneBits,
    targetBitMaximumBits, payload, output, sourceBits,
    maximumBits, request, canonicalBooleanizeOutput] using hrun

theorem run_targetBitProgram_caseTwo
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (inputLength : ℕ) (bits : List Bool) :
    runNPOracleProgram (targetBitProgram algorithm)
        (targetBitCaseTwoBits inputLength bits)
        (targetBitCaseTwoFuel bits)
        (initialNPOracleState inputLength
          (targetBitCaseTwoInput bits)) =
      some (bits.foldl xor false).toNat := by
  let rawBits := bits.map Bool.toNat
  let payload := encodeBalancedList rawBits
  let output := taggedParity rawBits
  let sourceBits := balancedBitParityBits inputLength rawBits
  let maximumBits := targetBitCaseTwoBits inputLength bits
  have hlengthBits :
      natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (by
      unfold natBitLength
      omega : 1 ≤ natBitLength inputLength).trans hlengthBits
  have hinputBits :
      natBitLength
          (Nat.pair inputLength (Nat.pair 1 payload)) ≤
        maximumBits := by
    exact
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsourceBits : sourceBits ≤ maximumBits := by
    exact
      (Nat.le_max_left _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hbooleanBits : canonicalBooleanizeBits output ≤ maximumBits := by
    exact
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hsource :
      runNPOracleProgram balancedBitParityProgram maximumBits
          (balancedBitParityFuel rawBits)
          (initialNPOracleState inputLength payload) =
        some output := by
    exact run_bits_mono
      (run_balancedBitParityProgram inputLength rawBits)
      hsourceBits
  have hchoice :
      runNPOracleProgram
          (taggedProgramChoice
            (paddedAmplifierEvaluationProgram algorithm)
            balancedBitParityProgram)
          maximumBits
          (taggedProgramChoiceFuel <|
            balancedBitParityFuel rawBits)
          (initialNPOracleState inputLength (Nat.pair 1 payload)) =
        some output := by
    exact run_taggedProgramChoice_nonzero
      (paddedAmplifierEvaluationProgram algorithm)
      balancedBitParityProgram inputLength 1 payload maximumBits
      (balancedBitParityFuel rawBits) output (by omega)
      hinputBits hsource (run_output_bounded hsource)
  have hboolean :
      runNPOracleProgram canonicalBooleanizeProgram maximumBits 3
          (initialNPOracleState inputLength output) =
        some (canonicalBooleanizeOutput output) :=
    run_bits_mono
      (run_canonicalBooleanizeProgram inputLength output)
      hbooleanBits
  have hrun :=
    run_linkPrograms hpositive hlengthBits hchoice hboolean
  have hparity :
      output = (bits.foldl xor false).toNat := by
    simpa only [output, rawBits] using taggedParity_boolToNat bits
  have hnormalize :
      canonicalBooleanizeOutput output = output := by
    rw [hparity]
    cases bits.foldl xor false <;>
      simp [canonicalBooleanizeOutput]
  rw [hnormalize, hparity] at hrun
  simpa only [targetBitProgram, targetBitCaseTwoFuel,
    targetBitCaseTwoInput, targetBitCaseTwoBits,
    targetBitMaximumBits, rawBits, payload, sourceBits,
    maximumBits] using hrun

end NearCubicWires.CanonicalTargetBitProgram
