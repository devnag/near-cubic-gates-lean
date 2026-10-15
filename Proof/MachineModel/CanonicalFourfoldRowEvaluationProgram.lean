import Proof.MachineModel.BitInputPrefixProgram
import Proof.MachineModel.CanonicalFourfoldRangeRequestProgram
import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.MachineModel.CanonicalSupplierEnvelopeBottomProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.Foundations.VerifiedLinker

/-!
# Canonical fourfold row evaluation

This module builds the production row evaluator only from fixed, verified
machine layers.  The first segment decodes the public five-field row request,
executes the typed circuit envelope and the imported exact-decomposition
runner, and retains the row/input coordinates beside the resulting bottom
forest.  No decoded host value or run-time compiler callback crosses this
boundary.
-/

namespace NearCubicWires.CanonicalFourfoldRowEvaluationProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalFourfoldRangeRequestProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalSupplierCircuitBatchProgram
open NearCubicWires.CanonicalSupplierCircuitBottomBatchProgram
open NearCubicWires.CanonicalSupplierEnvelopeBottomProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## Row-envelope handoff -/

def fourfoldRowEvaluationContext
    (modeCode q rowIndex inputCode : ℕ) : ℕ :=
  Nat.pair modeCode <|
    Nat.pair q <|
      Nat.pair rowIndex inputCode

/-- Information needed after destructive bottom-gate lowering.  The original
envelope is retained because residual weights and thresholds cannot be
reconstructed from an extensionally equivalent exact decomposition. -/
def fourfoldRowSourceContext
    (envelopeCode modeCode q rowIndex inputCode : ℕ) : ℕ :=
  Nat.pair envelopeCode <|
    fourfoldRowEvaluationContext modeCode q rowIndex inputCode

def fourfoldRowSourcePackage
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) : ℕ :=
  Nat.pair bottomForest <|
    fourfoldRowSourceContext
      envelopeCode modeCode q rowIndex inputCode

def fourfoldRowEnvelopeHandoffInput
    (modeCode q envelopeCode rowIndex inputCode : ℕ) : ℕ :=
  Nat.pair modeCode <|
    Nat.pair q <|
      Nat.pair envelopeCode <|
        Nat.pair rowIndex inputCode

def fourfoldRowEnvelopeHandoffOutput
    (modeCode q envelopeCode rowIndex inputCode : ℕ) : ℕ :=
  Nat.pair envelopeCode <|
    fourfoldRowSourceContext
      envelopeCode modeCode q rowIndex inputCode

/-- Isolate the typed envelope as the next request and retain the canonical
source plus its public mode, arity, row, and input fields on the right. -/
def fourfoldRowEnvelopeHandoffProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .pair 4 7 8 7
  , .pair 2 8 9 8
  , .pair 6 9 8 9
  , .pair 6 8 0 10
  , .halt 0
  ]

@[simp] theorem fourfoldRowEnvelopeHandoffProgram_oracleFree :
    OracleFree fourfoldRowEnvelopeHandoffProgram := by
  rfl

def fourfoldRowEnvelopeHandoffBits
    (modeCode q envelopeCode rowIndex inputCode : ℕ) : ℕ :=
  natBitLength <|
    max
      (fourfoldRowEnvelopeHandoffInput
        modeCode q envelopeCode rowIndex inputCode)
      (fourfoldRowEnvelopeHandoffOutput
        modeCode q envelopeCode rowIndex inputCode) + 1

theorem run_fourfoldRowEnvelopeHandoffProgram
    (modeCode q envelopeCode rowIndex inputCode : ℕ) :
    runNPOracleProgram fourfoldRowEnvelopeHandoffProgram
        (fourfoldRowEnvelopeHandoffBits
          modeCode q envelopeCode rowIndex inputCode)
        11
        (initialNPOracleState q
          (fourfoldRowEnvelopeHandoffInput
            modeCode q envelopeCode rowIndex inputCode)) =
      some
        (fourfoldRowEnvelopeHandoffOutput
          modeCode q envelopeCode rowIndex inputCode) := by
  let rowInput := Nat.pair rowIndex inputCode
  let envelopeRows := Nat.pair envelopeCode rowInput
  let qEnvelopeRows := Nat.pair q envelopeRows
  let input := Nat.pair modeCode qEnvelopeRows
  let qRows := Nat.pair q rowInput
  let context := Nat.pair modeCode qRows
  let sourceContext := Nat.pair envelopeCode context
  let output := Nat.pair envelopeCode sourceContext
  let bound := max input output + 1
  let maximumBits :=
    fourfoldRowEnvelopeHandoffBits
      modeCode q envelopeCode rowIndex inputCode
  have hmaximumBits : natBitLength bound = maximumBits := by
    rfl
  have bits_of_le {value : ℕ} (hvalue : value ≤ bound) :
      natBitLength value ≤ maximumBits := by
    rw [← hmaximumBits]
    exact natBitLength_mono hvalue
  have hinput : natBitLength input ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_left _ _).trans (Nat.le_add_right _ _)
  have houtput : natBitLength output ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)
  have hmodeCode : natBitLength modeCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair modeCode qEnvelopeRows)).trans hinput
  have hqEnvelopeRows : natBitLength qEnvelopeRows ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair modeCode qEnvelopeRows)).trans hinput
  have hq : natBitLength q ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair q envelopeRows)).trans hqEnvelopeRows
  have henvelopeRows : natBitLength envelopeRows ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair q envelopeRows)).trans hqEnvelopeRows
  have henvelopeCode : natBitLength envelopeCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair envelopeCode rowInput)).trans henvelopeRows
  have hrowInput : natBitLength rowInput ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair envelopeCode rowInput)).trans henvelopeRows
  have hsourceContext : natBitLength sourceContext ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair envelopeCode sourceContext)).trans houtput
  have hcontext : natBitLength context ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair envelopeCode context)).trans hsourceContext
  have hqRows : natBitLength qRows ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair modeCode qRows)).trans hcontext
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := modeCode)
    (by rfl) rfl
    (by
      simp [initialNPOracleState,
        fourfoldRowEnvelopeHandoffInput])
    hmodeCode]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := qEnvelopeRows)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, fourfoldRowEnvelopeHandoffInput,
        qEnvelopeRows, envelopeRows, rowInput])
    hqEnvelopeRows]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := q)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, qEnvelopeRows])
    hq]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := envelopeRows)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, qEnvelopeRows])
    henvelopeRows]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := envelopeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, envelopeRows])
    henvelopeCode]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := rowInput)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, envelopeRows])
    hrowInput]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := qRows)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, qRows])
    hqRows]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := context)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context])
    hcontext]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := sourceContext)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, sourceContext])
    hsourceContext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

/-! ## Bottom-forest context projection -/

def fourfoldRowBottomProjectionInput
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair bottomForest (supplierCircuitBatchContext modeCode q))
    (fourfoldRowSourceContext
      envelopeCode modeCode q rowIndex inputCode)

def fourfoldRowBottomProjectionOutput
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) : ℕ :=
  fourfoldRowSourcePackage
    bottomForest envelopeCode modeCode q rowIndex inputCode

/-- Drop only the duplicate `(mode,q)` emitted by the envelope-bottom stage;
the original row context remains authoritative. -/
def fourfoldRowBottomProjectionProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .pair 4 3 0 4
  , .halt 0
  ]

@[simp] theorem fourfoldRowBottomProjectionProgram_oracleFree :
    OracleFree fourfoldRowBottomProjectionProgram := by
  rfl

def fourfoldRowBottomProjectionBits
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) : ℕ :=
  natBitLength <|
    max
      (fourfoldRowBottomProjectionInput
        bottomForest envelopeCode modeCode q rowIndex inputCode)
      (fourfoldRowBottomProjectionOutput
        bottomForest envelopeCode modeCode q rowIndex inputCode) + 1

theorem run_fourfoldRowBottomProjectionProgram
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) :
    runNPOracleProgram fourfoldRowBottomProjectionProgram
        (fourfoldRowBottomProjectionBits
          bottomForest envelopeCode modeCode q rowIndex inputCode)
        5
        (initialNPOracleState q
          (fourfoldRowBottomProjectionInput
            bottomForest envelopeCode modeCode q rowIndex inputCode)) =
      some
        (fourfoldRowBottomProjectionOutput
          bottomForest envelopeCode modeCode q rowIndex inputCode) := by
  let batchContext := supplierCircuitBatchContext modeCode q
  let bottomOutput := Nat.pair bottomForest batchContext
  let context :=
    fourfoldRowSourceContext
      envelopeCode modeCode q rowIndex inputCode
  let input := Nat.pair bottomOutput context
  let output :=
    fourfoldRowSourcePackage
      bottomForest envelopeCode modeCode q rowIndex inputCode
  let bound := max input output + 1
  let maximumBits :=
    fourfoldRowBottomProjectionBits
      bottomForest envelopeCode modeCode q rowIndex inputCode
  have hmaximumBits : natBitLength bound = maximumBits := by
    rfl
  have bits_of_le {value : ℕ} (hvalue : value ≤ bound) :
      natBitLength value ≤ maximumBits := by
    rw [← hmaximumBits]
    exact natBitLength_mono hvalue
  have hinput : natBitLength input ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_left _ _).trans (Nat.le_add_right _ _)
  have houtput : natBitLength output ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)
  have hbottomOutput : natBitLength bottomOutput ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair bottomOutput context)).trans hinput
  have hcontext : natBitLength context ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair bottomOutput context)).trans hinput
  have hbottomForest : natBitLength bottomForest ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair bottomForest batchContext)).trans hbottomOutput
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := bottomOutput)
    (by rfl) rfl
    (by
      simp [initialNPOracleState,
        fourfoldRowBottomProjectionInput, bottomOutput,
        batchContext])
    hbottomOutput]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, fourfoldRowBottomProjectionInput,
        bottomOutput, batchContext, context])
    hcontext]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := bottomForest)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, bottomOutput])
    hbottomForest]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        fourfoldRowSourcePackage, context])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        fourfoldRowSourcePackage, context])
    houtput

/-! ## Closed row-code to exact-bottom lowering -/

private def fourfoldRowBottomExecutionTailProgram
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    NPOracleProgram :=
  linkPrograms
    (preserveRightProgram
      (supplierCircuitEnvelopeBottomProgram algorithm))
    fourfoldRowBottomProjectionProgram

private def fourfoldRowEnvelopeHandoffTailProgram
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    NPOracleProgram :=
  linkPrograms fourfoldRowEnvelopeHandoffProgram
    (fourfoldRowBottomExecutionTailProgram algorithm)

/-- Fixed production prefix of the row evaluator.  The imported decomposer is
selected at link time; the public request contains only canonical data. -/
def fourfoldRowBottomLoweringProgram
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    NPOracleProgram :=
  linkPrograms fourfoldRowEnvelopeProgram
    (fourfoldRowEnvelopeHandoffTailProgram algorithm)

def fourfoldRowBottomLoweringStageBits
    (raw : FourfoldRowRequest) (envelopeBits bottomForest : ℕ) :
    List ℕ :=
  let modeCode := normalizedEstimatorModeCode raw.mode
  let context :=
    fourfoldRowSourceContext raw.envelopeCode
      modeCode raw.q raw.rowIndex raw.inputCode
  let envelopeOutput :=
    Nat.pair bottomForest
      (supplierCircuitBatchContext modeCode raw.q)
  [ 1
  , natBitLength raw.q
  , fourfoldRowEnvelopeBits raw
  , fourfoldRowEnvelopeHandoffBits
      modeCode raw.q raw.envelopeCode raw.rowIndex raw.inputCode
  , preserveRightBits envelopeBits raw.envelopeCode context envelopeOutput
  , fourfoldRowBottomProjectionBits
      bottomForest raw.envelopeCode modeCode raw.q raw.rowIndex raw.inputCode
  ]

def fourfoldRowBottomLoweringBits
    (raw : FourfoldRowRequest) (envelopeBits bottomForest : ℕ) : ℕ :=
  (fourfoldRowBottomLoweringStageBits raw envelopeBits bottomForest).foldr
    max 1

def fourfoldRowBottomLoweringFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (envelopeFuel : ℕ) : ℕ :=
  linkFuel (fourfoldRowEnvelopeHandoffTailProgram algorithm) 22 <|
    linkFuel (fourfoldRowBottomExecutionTailProgram algorithm) 11 <|
      linkFuel fourfoldRowBottomProjectionProgram
        (preserveRightFuel envelopeFuel) 5

@[simp] theorem fourfoldRowBottomLoweringProgram_oracleFree
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    OracleFree (fourfoldRowBottomLoweringProgram algorithm) := by
  unfold fourfoldRowBottomLoweringProgram
  apply oracleFree_linkPrograms
  · exact fourfoldRowEnvelopeProgram_oracleFree
  unfold fourfoldRowEnvelopeHandoffTailProgram
  apply oracleFree_linkPrograms
  · exact fourfoldRowEnvelopeHandoffProgram_oracleFree
  unfold fourfoldRowBottomExecutionTailProgram
  exact oracleFree_linkPrograms
    (preserveRightProgram_oracleFree _
      (supplierCircuitEnvelopeBottomProgram_oracleFree algorithm))
    fourfoldRowBottomProjectionProgram_oracleFree

private theorem rowBottom_le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ}
    (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

private theorem run_fourfoldRowBottomLoweringProgram_of_envelope
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (raw : FourfoldRowRequest)
    (envelopeBits envelopeFuel bottomForest : ℕ)
    (henvelope :
      runNPOracleProgram
          (supplierCircuitEnvelopeBottomProgram algorithm)
          envelopeBits envelopeFuel
          (initialNPOracleState raw.q raw.envelopeCode) =
        some
          (Nat.pair bottomForest
            (supplierCircuitBatchContext
              (normalizedEstimatorModeCode raw.mode) raw.q))) :
    runNPOracleProgram (fourfoldRowBottomLoweringProgram algorithm)
        (fourfoldRowBottomLoweringBits raw envelopeBits bottomForest)
        (fourfoldRowBottomLoweringFuel algorithm envelopeFuel)
        (initialNPOracleState raw.q raw.code) =
      some
        (fourfoldRowBottomProjectionOutput bottomForest
          raw.envelopeCode (normalizedEstimatorModeCode raw.mode) raw.q
          raw.rowIndex raw.inputCode) := by
  let modeCode := normalizedEstimatorModeCode raw.mode
  let context :=
    fourfoldRowSourceContext raw.envelopeCode
      modeCode raw.q raw.rowIndex raw.inputCode
  let handoff := raw.handoffCode
  let envelopeRequest :=
    fourfoldRowEnvelopeHandoffOutput modeCode raw.q
      raw.envelopeCode raw.rowIndex raw.inputCode
  let envelopeOutput :=
    Nat.pair bottomForest
      (supplierCircuitBatchContext modeCode raw.q)
  let preservedOutput := Nat.pair envelopeOutput context
  let output :=
    fourfoldRowBottomProjectionOutput bottomForest raw.envelopeCode
      modeCode raw.q raw.rowIndex raw.inputCode
  let maximumBits :=
    fourfoldRowBottomLoweringBits raw envelopeBits bottomForest
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          fourfoldRowBottomLoweringStageBits
            raw envelopeBits bottomForest) :
      value ≤ maximumBits := by
    dsimp only [maximumBits, fourfoldRowBottomLoweringBits]
    exact rowBottom_le_foldr_max_of_mem hvalue
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRowBottomLoweringStageBits]
  have hq : natBitLength raw.q ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRowBottomLoweringStageBits]
  have hdecoderBits :
      fourfoldRowEnvelopeBits raw ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRowBottomLoweringStageBits]
  have hhandoffBits :
      fourfoldRowEnvelopeHandoffBits modeCode raw.q
          raw.envelopeCode raw.rowIndex raw.inputCode ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRowBottomLoweringStageBits, modeCode]
  have henvelopeBits :
      preserveRightBits envelopeBits raw.envelopeCode context
          envelopeOutput ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRowBottomLoweringStageBits, modeCode, context,
      envelopeOutput]
  have hprojectionBits :
      fourfoldRowBottomProjectionBits bottomForest raw.envelopeCode
          modeCode raw.q raw.rowIndex raw.inputCode ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRowBottomLoweringStageBits, modeCode]
  have hdecoder :
      runNPOracleProgram fourfoldRowEnvelopeProgram maximumBits 22
          (initialNPOracleState raw.q raw.code) =
        some handoff := by
    exact run_bits_mono
      (run_fourfoldRowEnvelopeProgram raw
        (fourfoldRowEnvelopeBits raw) (le_refl _))
      hdecoderBits
  have hhandoff :
      runNPOracleProgram fourfoldRowEnvelopeHandoffProgram maximumBits 11
          (initialNPOracleState raw.q handoff) =
        some envelopeRequest := by
    apply run_bits_mono
      (by
        simpa [handoff, envelopeRequest, modeCode,
          FourfoldRowRequest.handoffCode,
          fourfoldRowEnvelopeHandoffInput] using
          run_fourfoldRowEnvelopeHandoffProgram modeCode raw.q
            raw.envelopeCode raw.rowIndex raw.inputCode)
      hhandoffBits
  have henvelopePreserved :
      runNPOracleProgram
          (preserveRightProgram
            (supplierCircuitEnvelopeBottomProgram algorithm))
          maximumBits (preserveRightFuel envelopeFuel)
          (initialNPOracleState raw.q envelopeRequest) =
        some preservedOutput := by
    have hexact :=
      run_preserveRightProgram
        (supplierCircuitEnvelopeBottomProgram algorithm)
        raw.q envelopeBits envelopeFuel raw.envelopeCode context
        envelopeOutput henvelope
    exact run_bits_mono
      (by
        simpa [envelopeRequest, preservedOutput, envelopeOutput,
          modeCode, context, fourfoldRowEnvelopeHandoffOutput] using hexact)
      henvelopeBits
  have hprojection :
      runNPOracleProgram fourfoldRowBottomProjectionProgram
          maximumBits 5
          (initialNPOracleState raw.q preservedOutput) =
        some output := by
    apply run_bits_mono
      (by
        simpa [preservedOutput, envelopeOutput, output, modeCode,
          context, fourfoldRowBottomProjectionInput] using
          run_fourfoldRowBottomProjectionProgram bottomForest raw.envelopeCode
            modeCode raw.q raw.rowIndex raw.inputCode)
      hprojectionBits
  have hbottomTail :
      runNPOracleProgram
          (fourfoldRowBottomExecutionTailProgram algorithm)
          maximumBits
          (linkFuel fourfoldRowBottomProjectionProgram
            (preserveRightFuel envelopeFuel) 5)
          (initialNPOracleState raw.q envelopeRequest) =
        some output := by
    simpa [fourfoldRowBottomExecutionTailProgram] using
      run_linkPrograms hpositive hq henvelopePreserved hprojection
  have hhandoffTail :
      runNPOracleProgram
          (fourfoldRowEnvelopeHandoffTailProgram algorithm)
          maximumBits
          (linkFuel (fourfoldRowBottomExecutionTailProgram algorithm) 11
            (linkFuel fourfoldRowBottomProjectionProgram
              (preserveRightFuel envelopeFuel) 5))
          (initialNPOracleState raw.q handoff) =
        some output := by
    simpa [fourfoldRowEnvelopeHandoffTailProgram] using
      run_linkPrograms hpositive hq hhandoff hbottomTail
  have hrun :=
    run_linkPrograms hpositive hq hdecoder hhandoffTail
  simpa [fourfoldRowBottomLoweringProgram,
    fourfoldRowBottomLoweringFuel, output, modeCode] using hrun

/-! ## Published typed row executions -/

def symmetricFourfoldRowBottomForest
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  encodeBalancedList <|
    supplierCircuitBottomOutputs algorithm
      (symmetricCircuitBottomViews request)

def thresholdFourfoldRowBottomForest
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) : ℕ :=
  encodeBalancedList <|
    supplierCircuitBottomOutputs algorithm
      (thresholdCircuitBottomViews request)

def symmetricFourfoldRowBottomBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) : ℕ :=
  fourfoldRowBottomLoweringBits
    (symmetricFourfoldRowRequest request rowIndex input)
    (supplierCircuitEnvelopeBottomBits algorithm
      symmetricCircuitFamilyTag request.q
      (symmetricCircuitHeaderViews request)
      (symmetricCircuitBottomViews request))
    (symmetricFourfoldRowBottomForest algorithm request)

def thresholdFourfoldRowBottomBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) : ℕ :=
  fourfoldRowBottomLoweringBits
    (thresholdFourfoldRowRequest request rowIndex input)
    (supplierCircuitEnvelopeBottomBits algorithm
      thresholdCircuitFamilyTag request.q
      (thresholdCircuitHeaderViews request)
      (thresholdCircuitBottomViews request))
    (thresholdFourfoldRowBottomForest algorithm request)

def symmetricFourfoldRowBottomFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  fourfoldRowBottomLoweringFuel algorithm <|
    supplierCircuitEnvelopeBottomFuel algorithm
      (symmetricCircuitHeaderViews request)
      (symmetricCircuitBottomViews request)

def thresholdFourfoldRowBottomFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) : ℕ :=
  fourfoldRowBottomLoweringFuel algorithm <|
    supplierCircuitEnvelopeBottomFuel algorithm
      (thresholdCircuitHeaderViews request)
      (thresholdCircuitBottomViews request)

def symmetricFourfoldRowBottomOutput
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) : ℕ :=
  fourfoldRowBottomProjectionOutput
    (symmetricFourfoldRowBottomForest algorithm request)
    (symmetricFourfoldRowRequest request rowIndex input).envelopeCode
    symmetricCircuitFamilyTag request.q rowIndex (encodeBitInput input)

def thresholdFourfoldRowBottomOutput
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) : ℕ :=
  fourfoldRowBottomProjectionOutput
    (thresholdFourfoldRowBottomForest algorithm request)
    (thresholdFourfoldRowRequest request rowIndex input).envelopeCode
    thresholdCircuitFamilyTag request.q rowIndex (encodeBitInput input)

set_option maxHeartbeats 800000 in
-- Normalize the dependent circuit-family codecs through the linked VM trace.
theorem run_fourfoldRowBottomLoweringProgram_symmetric
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    runNPOracleProgram (fourfoldRowBottomLoweringProgram algorithm)
        (symmetricFourfoldRowBottomBits
          algorithm request rowIndex input)
        (symmetricFourfoldRowBottomFuel algorithm request)
        (initialNPOracleState request.q
          (symmetricFourfoldRowRequest request rowIndex input).code) =
      some
        (symmetricFourfoldRowBottomOutput
          algorithm request rowIndex input) := by
  let raw := symmetricFourfoldRowRequest request rowIndex input
  let headerViews := symmetricCircuitHeaderViews request
  let bottomViews := symmetricCircuitBottomViews request
  let envelopeBits :=
    supplierCircuitEnvelopeBottomBits algorithm
      symmetricCircuitFamilyTag request.q headerViews bottomViews
  let envelopeFuel :=
    supplierCircuitEnvelopeBottomFuel algorithm headerViews bottomViews
  let bottomForest := symmetricFourfoldRowBottomForest algorithm request
  have henvelope :
      runNPOracleProgram
          (supplierCircuitEnvelopeBottomProgram algorithm)
          envelopeBits envelopeFuel
          (initialNPOracleState raw.q raw.envelopeCode) =
        some
          (Nat.pair bottomForest
            (supplierCircuitBatchContext
              (normalizedEstimatorModeCode raw.mode) raw.q)) := by
    simpa [raw, headerViews, bottomViews, envelopeBits, envelopeFuel,
      bottomForest, symmetricFourfoldRowBottomForest,
      symmetricFourfoldRowRequest, normalizedEstimatorModeCode,
      symmetricCircuitFamilyTag,
      CanonicalWitnessCodec.symmetricCircuitCodec,
      supplierCircuitEnvelopeBottomOutput] using
      run_supplierCircuitEnvelopeBottomProgram_symmetric algorithm request
  have hrun :=
    run_fourfoldRowBottomLoweringProgram_of_envelope
      algorithm raw envelopeBits envelopeFuel bottomForest henvelope
  simpa [raw, envelopeBits, envelopeFuel, bottomForest,
    symmetricFourfoldRowBottomBits, symmetricFourfoldRowBottomFuel,
    symmetricFourfoldRowBottomOutput, symmetricFourfoldRowRequest,
    symmetricCircuitFamilyTag, normalizedEstimatorModeCode] using hrun

set_option maxHeartbeats 800000 in
-- Normalize the dependent circuit-family codecs through the linked VM trace.
theorem run_fourfoldRowBottomLoweringProgram_threshold
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    runNPOracleProgram (fourfoldRowBottomLoweringProgram algorithm)
        (thresholdFourfoldRowBottomBits
          algorithm request rowIndex input)
        (thresholdFourfoldRowBottomFuel algorithm request)
        (initialNPOracleState request.q
          (thresholdFourfoldRowRequest request rowIndex input).code) =
      some
        (thresholdFourfoldRowBottomOutput
          algorithm request rowIndex input) := by
  let raw := thresholdFourfoldRowRequest request rowIndex input
  let headerViews := thresholdCircuitHeaderViews request
  let bottomViews := thresholdCircuitBottomViews request
  let envelopeBits :=
    supplierCircuitEnvelopeBottomBits algorithm
      thresholdCircuitFamilyTag request.q headerViews bottomViews
  let envelopeFuel :=
    supplierCircuitEnvelopeBottomFuel algorithm headerViews bottomViews
  let bottomForest := thresholdFourfoldRowBottomForest algorithm request
  have henvelope :
      runNPOracleProgram
          (supplierCircuitEnvelopeBottomProgram algorithm)
          envelopeBits envelopeFuel
          (initialNPOracleState raw.q raw.envelopeCode) =
        some
          (Nat.pair bottomForest
            (supplierCircuitBatchContext
              (normalizedEstimatorModeCode raw.mode) raw.q)) := by
    simpa [raw, headerViews, bottomViews, envelopeBits, envelopeFuel,
      bottomForest, thresholdFourfoldRowBottomForest,
      thresholdFourfoldRowRequest, normalizedEstimatorModeCode,
      thresholdCircuitFamilyTag,
      CanonicalWitnessCodec.thresholdCircuitCodec,
      supplierCircuitEnvelopeBottomOutput] using
      run_supplierCircuitEnvelopeBottomProgram_threshold algorithm request
  have hrun :=
    run_fourfoldRowBottomLoweringProgram_of_envelope
      algorithm raw envelopeBits envelopeFuel bottomForest henvelope
  simpa [raw, envelopeBits, envelopeFuel, bottomForest,
    thresholdFourfoldRowBottomBits, thresholdFourfoldRowBottomFuel,
    thresholdFourfoldRowBottomOutput, thresholdFourfoldRowRequest,
    thresholdCircuitFamilyTag, normalizedEstimatorModeCode] using hrun

/-! ## Range atom to verified bottom package

This is the first paper-specific vertical slice through the aggregation ABI.
It connects the fixed range-atom lowering directly to the existing typed
bottom evaluator; no host-built `FourfoldRowRequest` crosses the boundary. -/

def fourfoldRangeBottomProgram
    (algorithm : ExecutableExactDecompositionAlgorithm) : NPOracleProgram :=
  linkPrograms fourfoldRangeRequestProgram
    (fourfoldRowBottomLoweringProgram algorithm)

@[simp] theorem fourfoldRangeBottomProgram_oracleFree
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    OracleFree (fourfoldRangeBottomProgram algorithm) := by
  exact oracleFree_linkPrograms fourfoldRangeRequestProgram_oracleFree
    (fourfoldRowBottomLoweringProgram_oracleFree algorithm)

def symmetricFourfoldRangeBottomBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (flat denominatorTail : ℕ) : ℕ :=
  max
    (fourfoldRangeRequestBits request.q flat denominatorTail
      (normalizedEstimatorModeCode .symmetric)
      (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
        encodeNormalizedSymmetricThresholdCircuit request))
    (symmetricFourfoldRowBottomBits algorithm request
      (flat >>> request.q) (bitInputPrefixView request.q flat))

def symmetricFourfoldRangeBottomFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (flat : ℕ) : ℕ :=
  linkFuel (fourfoldRowBottomLoweringProgram algorithm)
    (fourfoldRangeRequestFuel request.q flat)
    (symmetricFourfoldRowBottomFuel algorithm request)

set_option maxHeartbeats 800000 in
-- The typed circuit codecs make the linked intermediate-code normalization costly.
theorem run_fourfoldRangeBottomProgram_symmetric
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (flat denominatorTail : ℕ) :
    runNPOracleProgram (fourfoldRangeBottomProgram algorithm)
        (symmetricFourfoldRangeBottomBits
          algorithm request flat denominatorTail)
        (symmetricFourfoldRangeBottomFuel algorithm request flat)
        (initialNPOracleState request.q
          (fourfoldRangeAtomInput flat denominatorTail
            (normalizedEstimatorModeCode .symmetric)
            (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
              encodeNormalizedSymmetricThresholdCircuit request))) =
      some
        (symmetricFourfoldRowBottomOutput algorithm request
          (flat >>> request.q) (bitInputPrefixView request.q flat)) := by
  let rangeBits :=
    fourfoldRangeRequestBits request.q flat denominatorTail
      (normalizedEstimatorModeCode .symmetric)
      (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
        encodeNormalizedSymmetricThresholdCircuit request)
  let bottomBits :=
    symmetricFourfoldRowBottomBits algorithm request
      (flat >>> request.q) (bitInputPrefixView request.q flat)
  let maximumBits :=
    symmetricFourfoldRangeBottomBits algorithm request flat denominatorTail
  have hrangeBits : rangeBits ≤ maximumBits := Nat.le_max_left _ _
  have hbottomBits : bottomBits ≤ maximumBits := Nat.le_max_right _ _
  have hq : natBitLength request.q ≤ maximumBits := by
    apply le_trans ?_ hrangeBits
    simp [rangeBits, fourfoldRangeRequestBits,
      fourfoldRangeRequestStageBits]
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength request.q by
      unfold natBitLength
      omega).trans hq
  have hrange :=
    run_bits_mono
      (run_fourfoldRangeRequestProgram_mode request.q flat denominatorTail
        (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
          encodeNormalizedSymmetricThresholdCircuit request)
        .symmetric)
      hrangeBits
  have hrequest :
      FourfoldRowRequest.mk .symmetric request.q
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request)
          (flat >>> request.q) (bitInputPrefix request.q flat) =
        symmetricFourfoldRowRequest request (flat >>> request.q)
          (bitInputPrefixView request.q flat) := by
    simp [symmetricFourfoldRowRequest, bitInputPrefix_eq_encodeView,
      CanonicalWitnessCodec.symmetricCircuitCodec]
  rw [hrequest] at hrange
  have hbottom :=
    run_bits_mono
      (run_fourfoldRowBottomLoweringProgram_symmetric algorithm request
        (flat >>> request.q) (bitInputPrefixView request.q flat))
      hbottomBits
  have hrun := run_linkPrograms hpositive hq hrange hbottom
  simpa only [maximumBits, fourfoldRangeBottomProgram,
    symmetricFourfoldRangeBottomFuel] using hrun

def thresholdFourfoldRangeBottomBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (flat denominatorTail : ℕ) : ℕ :=
  max
    (fourfoldRangeRequestBits request.q flat denominatorTail
      (normalizedEstimatorModeCode .threshold)
      (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
        encodeNormalizedThresholdThresholdCircuit request))
    (thresholdFourfoldRowBottomBits algorithm request
      (flat >>> request.q) (bitInputPrefixView request.q flat))

def thresholdFourfoldRangeBottomFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (flat : ℕ) : ℕ :=
  linkFuel (fourfoldRowBottomLoweringProgram algorithm)
    (fourfoldRangeRequestFuel request.q flat)
    (thresholdFourfoldRowBottomFuel algorithm request)

set_option maxHeartbeats 800000 in
-- The typed circuit codecs make the linked intermediate-code normalization costly.
theorem run_fourfoldRangeBottomProgram_threshold
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (flat denominatorTail : ℕ) :
    runNPOracleProgram (fourfoldRangeBottomProgram algorithm)
        (thresholdFourfoldRangeBottomBits
          algorithm request flat denominatorTail)
        (thresholdFourfoldRangeBottomFuel algorithm request flat)
        (initialNPOracleState request.q
          (fourfoldRangeAtomInput flat denominatorTail
            (normalizedEstimatorModeCode .threshold)
            (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
              encodeNormalizedThresholdThresholdCircuit request))) =
      some
        (thresholdFourfoldRowBottomOutput algorithm request
          (flat >>> request.q) (bitInputPrefixView request.q flat)) := by
  let rangeBits :=
    fourfoldRangeRequestBits request.q flat denominatorTail
      (normalizedEstimatorModeCode .threshold)
      (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
        encodeNormalizedThresholdThresholdCircuit request)
  let bottomBits :=
    thresholdFourfoldRowBottomBits algorithm request
      (flat >>> request.q) (bitInputPrefixView request.q flat)
  let maximumBits :=
    thresholdFourfoldRangeBottomBits algorithm request flat denominatorTail
  have hrangeBits : rangeBits ≤ maximumBits := Nat.le_max_left _ _
  have hbottomBits : bottomBits ≤ maximumBits := Nat.le_max_right _ _
  have hq : natBitLength request.q ≤ maximumBits := by
    apply le_trans ?_ hrangeBits
    simp [rangeBits, fourfoldRangeRequestBits,
      fourfoldRangeRequestStageBits]
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength request.q by
      unfold natBitLength
      omega).trans hq
  have hrange :=
    run_bits_mono
      (run_fourfoldRangeRequestProgram_mode request.q flat denominatorTail
        (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
          encodeNormalizedThresholdThresholdCircuit request)
        .threshold)
      hrangeBits
  have hrequest :
      FourfoldRowRequest.mk .threshold request.q
          (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
            encodeNormalizedThresholdThresholdCircuit request)
          (flat >>> request.q) (bitInputPrefix request.q flat) =
        thresholdFourfoldRowRequest request (flat >>> request.q)
          (bitInputPrefixView request.q flat) := by
    simp [thresholdFourfoldRowRequest, bitInputPrefix_eq_encodeView,
      CanonicalWitnessCodec.thresholdCircuitCodec]
  rw [hrequest] at hrange
  have hbottom :=
    run_bits_mono
      (run_fourfoldRowBottomLoweringProgram_threshold algorithm request
        (flat >>> request.q) (bitInputPrefixView request.q flat))
      hbottomBits
  have hrun := run_linkPrograms hpositive hq hrange hbottom
  simpa only [maximumBits, fourfoldRangeBottomProgram,
    thresholdFourfoldRangeBottomFuel] using hrun

end NearCubicWires.CanonicalFourfoldRowEvaluationProgram
