import Proof.MachineModel.BitInputPrefixProgram
import Proof.MachineModel.CanonicalNativeCallProgram

/-!
# Canonical padded amplifier evaluation

The published amplifier evaluator is defined at its exact output arity, whereas
the final language is padded to a larger public arity.  This module supplies the
single executable adapter: truncate the public input with
`bitInputPrefixProgram`, retain the descriptor, and make one native-input call
to the published evaluator.  No high input bit or host-built evaluator request
crosses the call boundary.
-/

namespace NearCubicWires.CanonicalPaddedAmplifierEvaluationProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

def paddedAmplifierEvaluationRequest
    (outputArity descriptor inputCode : ℕ) :
    AmplifierEvaluationRequest :=
  { outputArity
    descriptor
    input := bitInputPrefixView outputArity inputCode }

def paddedAmplifierEvaluationInput
    (outputArity descriptor inputCode : ℕ) : ℕ :=
  Nat.pair (bitInputPrefixInput outputArity inputCode)
    (Nat.pair outputArity descriptor)

private def paddedAmplifierEvaluationAdapterInput
    (outputArity descriptor inputCode : ℕ) : ℕ :=
  Nat.pair (bitInputPrefix outputArity inputCode)
    (Nat.pair outputArity descriptor)

private def paddedAmplifierEvaluationNativeRequest
    (outputArity descriptor inputCode : ℕ) : ℕ :=
  nativeInputRequest outputArity <|
    AmplifierEvaluationRequest.code <|
      paddedAmplifierEvaluationRequest outputArity descriptor inputCode

/-- Reframe `pair(prefix, pair(outputArity, descriptor))` as the one canonical
native call `pair(outputArity, pair(descriptor, prefix))`. -/
private def paddedAmplifierEvaluationAdapterProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 5 2 6 5
  , .pair 4 6 0 6
  , .halt 0
  ]

private def paddedAmplifierEvaluationAdapterBits
    (outputArity descriptor inputCode : ℕ) : ℕ :=
  max
    (natBitLength
      (paddedAmplifierEvaluationAdapterInput
        outputArity descriptor inputCode))
    (natBitLength
      (paddedAmplifierEvaluationNativeRequest
        outputArity descriptor inputCode))

private theorem run_paddedAmplifierEvaluationAdapterProgram
    (inputLength outputArity descriptor inputCode : ℕ) :
    runNPOracleProgram paddedAmplifierEvaluationAdapterProgram
        (paddedAmplifierEvaluationAdapterBits
          outputArity descriptor inputCode)
        7
        (initialNPOracleState inputLength
          (paddedAmplifierEvaluationAdapterInput
            outputArity descriptor inputCode)) =
      some
        (paddedAmplifierEvaluationNativeRequest
          outputArity descriptor inputCode) := by
  let prefixCode := bitInputPrefix outputArity inputCode
  let context := Nat.pair outputArity descriptor
  let request := Nat.pair descriptor prefixCode
  let nativeRequest :=
    paddedAmplifierEvaluationNativeRequest
      outputArity descriptor inputCode
  let maximumBits :=
    paddedAmplifierEvaluationAdapterBits
      outputArity descriptor inputCode
  have hnativeRequest :
      nativeRequest = Nat.pair outputArity request := by
    change
      Nat.pair outputArity
          (Nat.pair descriptor
            (encodeBitInput
              (bitInputPrefixView outputArity inputCode))) =
        Nat.pair outputArity
          (Nat.pair descriptor
            (bitInputPrefix outputArity inputCode))
    rw [← bitInputPrefix_eq_encodeView]
  have hnativeRequestDef :
      nativeRequest =
        paddedAmplifierEvaluationNativeRequest
          outputArity descriptor inputCode := by
    rfl
  have _hdefinitions :
      request = Nat.pair descriptor prefixCode := by
    rfl
  have _hnativeDefinition :
      nativeRequest =
        nativeInputRequest outputArity
          (AmplifierEvaluationRequest.code <|
            paddedAmplifierEvaluationRequest
              outputArity descriptor inputCode) := by
    simp only [nativeRequest,
      paddedAmplifierEvaluationNativeRequest,
      paddedAmplifierEvaluationRequest]
  have hinput :
      natBitLength (Nat.pair prefixCode context) ≤ maximumBits := by
    exact Nat.le_max_left _ _
  have houtput :
      natBitLength nativeRequest ≤ maximumBits := by
    dsimp only [maximumBits,
      paddedAmplifierEvaluationAdapterBits]
    exact Nat.le_max_right _ _
  have hprefix : natBitLength prefixCode ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair prefixCode context)).trans hinput
  have hcontext : natBitLength context ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair prefixCode context)).trans hinput
  have harity : natBitLength outputArity ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair outputArity descriptor)).trans hcontext
  have hdescriptor : natBitLength descriptor ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair outputArity descriptor)).trans hcontext
  have hrequest : natBitLength request ≤ maximumBits := by
    apply
      (natBitLength_mono
        (Nat.right_le_pair outputArity request)).trans
    rw [← hnativeRequest]
    exact houtput
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := prefixCode)
    (by rfl) rfl
    (by simp [initialNPOracleState,
      paddedAmplifierEvaluationAdapterInput, prefixCode])
    hprefix]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      paddedAmplifierEvaluationAdapterInput, prefixCode, context])
    hcontext]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := outputArity)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context])
    harity]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := descriptor)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context])
    hdescriptor]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := request)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, request])
    hrequest]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := nativeRequest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnativeRequest])
    houtput]
  apply run_halt_instruction (fuel := 0) (by rfl) rfl
  · simp only [NPOracleState.write, NPOracleState.jump, if_pos]
    exact hnativeRequestDef
  · simpa only [nativeRequest] using houtput

@[simp] private theorem paddedAmplifierEvaluationAdapterProgram_oracleFree :
    OracleFree paddedAmplifierEvaluationAdapterProgram := by
  rfl

/-- Fixed evaluator from a padded public input to the actual published
amplifier evaluator. -/
def paddedAmplifierEvaluationProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm) : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitInputPrefixProgram) <|
    linkPrograms paddedAmplifierEvaluationAdapterProgram <|
      nativeCallProgram algorithm.evaluator.program

def paddedAmplifierEvaluationFuel
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (outputArity descriptor inputCode : ℕ) : ℕ :=
  let request :=
    paddedAmplifierEvaluationRequest outputArity descriptor inputCode
  linkFuel
    (linkPrograms paddedAmplifierEvaluationAdapterProgram <|
      nativeCallProgram algorithm.evaluator.program)
    (preserveRightFuel (bitInputPrefixFuel outputArity inputCode)) <|
    linkFuel (nativeCallProgram algorithm.evaluator.program) 7 <|
      nativeCallFuel algorithm.evaluator.program
        (algorithm.evaluator.budget request)
        outputArity (AmplifierEvaluationRequest.code request)

def paddedAmplifierEvaluationBits
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (inputLength outputArity descriptor inputCode : ℕ) : ℕ :=
  let request :=
    paddedAmplifierEvaluationRequest outputArity descriptor inputCode
  let output := algorithm.evaluator.execute request
  max (natBitLength inputLength) <|
    max
      (preserveRightBits
        (bitInputPrefixBits outputArity inputCode)
        (bitInputPrefixInput outputArity inputCode)
        (Nat.pair outputArity descriptor)
        (bitInputPrefix outputArity inputCode)) <|
      max
        (paddedAmplifierEvaluationAdapterBits
          outputArity descriptor inputCode)
        (nativeCallBits inputLength outputArity
          (AmplifierEvaluationRequest.code request) output
          (algorithm.evaluator.budget request))

@[simp] theorem paddedAmplifierEvaluationProgram_oracleFree
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm) :
    OracleFree (paddedAmplifierEvaluationProgram algorithm) := by
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree bitInputPrefixProgram
      bitInputPrefixProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact paddedAmplifierEvaluationAdapterProgram_oracleFree
    · exact nativeCallProgram_oracleFree algorithm.evaluatorOracleFree

theorem run_paddedAmplifierEvaluationProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (inputLength outputArity descriptor inputCode : ℕ) :
    let request :=
      paddedAmplifierEvaluationRequest outputArity descriptor inputCode
    runNPOracleProgram (paddedAmplifierEvaluationProgram algorithm)
        (paddedAmplifierEvaluationBits algorithm inputLength
          outputArity descriptor inputCode)
        (paddedAmplifierEvaluationFuel algorithm
          outputArity descriptor inputCode)
        (initialNPOracleState inputLength
          (paddedAmplifierEvaluationInput
            outputArity descriptor inputCode)) =
      some (algorithm.evaluator.execute request) := by
  dsimp only
  let request :=
    paddedAmplifierEvaluationRequest outputArity descriptor inputCode
  let output := algorithm.evaluator.execute request
  let retained := Nat.pair outputArity descriptor
  let prefixInput := bitInputPrefixInput outputArity inputCode
  let prefixCode := bitInputPrefix outputArity inputCode
  let adapterInput := Nat.pair prefixCode retained
  let nativeRequest :=
    nativeInputRequest outputArity
      (AmplifierEvaluationRequest.code request)
  let maximumBits :=
    paddedAmplifierEvaluationBits algorithm inputLength
      outputArity descriptor inputCode
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (by
      unfold natBitLength
      omega : 1 ≤ natBitLength inputLength).trans hlengthBits
  have hprefixStageBits :
      preserveRightBits
          (bitInputPrefixBits outputArity inputCode)
          prefixInput retained prefixCode ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hadapterBits :
      paddedAmplifierEvaluationAdapterBits
          outputArity descriptor inputCode ≤ maximumBits := by
    exact
      (Nat.le_max_left _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hnativeBits :
      nativeCallBits inputLength outputArity
          (AmplifierEvaluationRequest.code request) output
          (algorithm.evaluator.budget request) ≤ maximumBits := by
    exact
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprefixRun :
      runNPOracleProgram
          (preserveRightProgram bitInputPrefixProgram)
          maximumBits
          (preserveRightFuel
            (bitInputPrefixFuel outputArity inputCode))
          (initialNPOracleState inputLength
            (Nat.pair prefixInput retained)) =
        some adapterInput := by
    apply run_bits_mono
      (run_preserveRightProgram bitInputPrefixProgram
        inputLength
        (bitInputPrefixBits outputArity inputCode)
        (bitInputPrefixFuel outputArity inputCode)
        prefixInput retained prefixCode ?_)
      hprefixStageBits
    exact run_bitInputPrefixProgram inputLength outputArity inputCode
      (bitInputPrefixBits outputArity inputCode) 0 (le_refl _)
  have hadapterRun :
      runNPOracleProgram paddedAmplifierEvaluationAdapterProgram
          maximumBits 7
          (initialNPOracleState inputLength adapterInput) =
        some nativeRequest := by
    apply run_bits_mono
      (run_paddedAmplifierEvaluationAdapterProgram inputLength
        outputArity descriptor inputCode)
      hadapterBits
  have hevaluator :
      runNPOracleProgram algorithm.evaluator.program
          (algorithm.evaluator.budget request)
          (algorithm.evaluator.budget request)
          (initialNPOracleState outputArity
            (AmplifierEvaluationRequest.code request)) =
        some output := by
    exact algorithm.evaluator.run_eq_execute request
  have hnativeRun :
      runNPOracleProgram
          (nativeCallProgram algorithm.evaluator.program)
          maximumBits
          (nativeCallFuel algorithm.evaluator.program
            (algorithm.evaluator.budget request)
            outputArity (AmplifierEvaluationRequest.code request))
          (initialNPOracleState inputLength nativeRequest) =
        some output := by
    exact run_bits_mono
      (run_nativeCallProgram algorithm.evaluator.program inputLength
        outputArity (AmplifierEvaluationRequest.code request) output
        (algorithm.evaluator.budget request)
        (algorithm.evaluator.budget request) hevaluator)
      hnativeBits
  have hinner :=
    run_linkPrograms hpositive hlengthBits hadapterRun hnativeRun
  have hrun :=
    run_linkPrograms hpositive hlengthBits hprefixRun hinner
  simpa only [paddedAmplifierEvaluationProgram,
    paddedAmplifierEvaluationFuel, paddedAmplifierEvaluationInput,
    request, output, retained, prefixInput, prefixCode, adapterInput,
    nativeRequest] using hrun

end NearCubicWires.CanonicalPaddedAmplifierEvaluationProgram
