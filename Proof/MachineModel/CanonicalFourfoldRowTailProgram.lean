import Proof.MachineModel.CanonicalNatDecodeProgram
import Proof.Supplier.FourfoldRangeAggregationComposition
import Proof.MachineModel.TaggedProgramChoice

/-!
# The executable fourfold row tail and its envelope front end

`FourfoldRangeAggregationComposition` reduces the two execution fields of
`SharedNormalizedAggregationArtifact` to one *row tail*: a machine from the
exact-bottom package produced by `fourfoldRangeBottomProgram` to the Boolean
row code.  This module supplies that tail's fixed structure and the matching
front end, so the whole chain

```text
typed envelope -> balanced range input -> all-row aggregation -> component
```

is a single linked `NPOracleProgram` with an exact run theorem in precisely
the shape `SharedNormalizedAggregationArtifact.computesSymmetric` and
`…computesThreshold` consume.

Two link-time program parameters remain, each with an exact interpreter
premise and no fuel or callback argument:

* `rowEvaluator`, on the native five-field row handoff paired with the exact
  bottom forest, computing `boolCode (evaluateCanonicalFourfoldRow …)`;
* `countProgram`, on the typed envelope, computing the row-major atom count.

Everything between them — the bottom-package repack, the family-tag decode,
the denominator tail, and the balanced range input — is executed here, with
closed width and fuel envelopes.
-/

namespace NearCubicWires.CanonicalFourfoldRowTailProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRangeRequestProgram
open NearCubicWires.CanonicalFourfoldRowEvaluationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRangeAggregationComposition
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## §1 The row-tail repack -/

/-- Row-tail ABI.  The native right-associated five-field handoff is exposed
on the left, and the exact bottom forest computed by the linked decomposition
prefix is retained on the right; no stage re-derives the forest. -/
def fourfoldRowTailHandoff
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair modeCode
      (Nat.pair q
        (Nat.pair envelopeCode (Nat.pair rowIndex inputCode))))
    bottomForest

/-- Reassociate the exact-bottom package into the row handoff.  Only pair
surgery happens here: no value is decoded, dropped, or recomputed. -/
def fourfoldRowTailRepackProgram : NPOracleProgram :=
  [ .unpairLeft 0 1 1
  , .unpairRight 0 2 2
  , .unpairLeft 2 3 3
  , .unpairRight 2 4 4
  , .unpairLeft 4 5 5
  , .unpairRight 4 6 6
  , .unpairLeft 6 7 7
  , .unpairRight 6 8 8
  , .pair 3 8 9 9
  , .pair 7 9 9 10
  , .pair 5 9 9 11
  , .pair 9 1 0 12
  , .halt 0
  ]

@[simp] theorem fourfoldRowTailRepackProgram_oracleFree :
    OracleFree fourfoldRowTailRepackProgram := by
  rfl

def fourfoldRowTailRepackBits
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) : ℕ :=
  natBitLength <|
    max
      (fourfoldRowSourcePackage
        bottomForest envelopeCode modeCode q rowIndex inputCode)
      (fourfoldRowTailHandoff
        bottomForest envelopeCode modeCode q rowIndex inputCode) + 1

theorem run_fourfoldRowTailRepackProgram
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) :
    runNPOracleProgram fourfoldRowTailRepackProgram
        (fourfoldRowTailRepackBits
          bottomForest envelopeCode modeCode q rowIndex inputCode)
        13
        (initialNPOracleState q
          (fourfoldRowSourcePackage
            bottomForest envelopeCode modeCode q rowIndex inputCode)) =
      some
        (fourfoldRowTailHandoff
          bottomForest envelopeCode modeCode q rowIndex inputCode) := by
  let rowInput := Nat.pair rowIndex inputCode
  let qRows := Nat.pair q rowInput
  let context := Nat.pair modeCode qRows
  let sourceContext := Nat.pair envelopeCode context
  let input := Nat.pair bottomForest sourceContext
  let envelopeRows := Nat.pair envelopeCode rowInput
  let qEnvelopeRows := Nat.pair q envelopeRows
  let handoff := Nat.pair modeCode qEnvelopeRows
  let output := Nat.pair handoff bottomForest
  let bound := max input output + 1
  let maximumBits :=
    fourfoldRowTailRepackBits
      bottomForest envelopeCode modeCode q rowIndex inputCode
  have hmaximumBits : natBitLength bound = maximumBits := rfl
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
  have hbottomForest : natBitLength bottomForest ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair bottomForest sourceContext)).trans hinput
  have hsourceContext : natBitLength sourceContext ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair bottomForest sourceContext)).trans hinput
  have henvelopeCode : natBitLength envelopeCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair envelopeCode context)).trans hsourceContext
  have hcontext : natBitLength context ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair envelopeCode context)).trans hsourceContext
  have hmodeCode : natBitLength modeCode ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair modeCode qRows)).trans hcontext
  have hqRows : natBitLength qRows ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair modeCode qRows)).trans hcontext
  have hq : natBitLength q ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair q rowInput)).trans hqRows
  have hrowInput : natBitLength rowInput ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair q rowInput)).trans hqRows
  have hhandoff : natBitLength handoff ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair handoff bottomForest)).trans houtput
  have hqEnvelopeRows : natBitLength qEnvelopeRows ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair modeCode qEnvelopeRows)).trans hhandoff
  have henvelopeRows : natBitLength envelopeRows ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair q envelopeRows)).trans hqEnvelopeRows
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := bottomForest)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, fourfoldRowSourcePackage])
    hbottomForest]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction (value := sourceContext)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        fourfoldRowSourcePackage, sourceContext, context, qRows, rowInput,
        fourfoldRowSourceContext, fourfoldRowEvaluationContext])
    hsourceContext]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := envelopeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, sourceContext])
    henvelopeCode]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, sourceContext])
    hcontext]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := modeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context])
    hmodeCode]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := qRows)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context])
    hqRows]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := q)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, qRows])
    hq]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := rowInput)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, qRows])
    hrowInput]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := envelopeRows)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, envelopeRows])
    henvelopeRows]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := qEnvelopeRows)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, qEnvelopeRows])
    hqEnvelopeRows]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := handoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, handoff])
    hhandoff]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        handoff, qEnvelopeRows, envelopeRows, rowInput])
    houtput

/-! ## §2 The linked row tail -/

/-- The row-tail ABI recovered from a raw exact-bottom package.  The fuel
charged for one tail call must be a function of that package alone, because
that is the shape `run_symmetricRowCalleeProgram_of_rowTail` consumes. -/
def fourfoldRowTailHandoffOfPackage (package : ℕ) : ℕ :=
  let bottomForest := (Nat.unpair package).1
  let sourceContext := (Nat.unpair package).2
  let envelopeCode := (Nat.unpair sourceContext).1
  let context := (Nat.unpair sourceContext).2
  let modeCode := (Nat.unpair context).1
  let arityRows := (Nat.unpair context).2
  let q := (Nat.unpair arityRows).1
  let rowInput := (Nat.unpair arityRows).2
  Nat.pair
    (Nat.pair modeCode (Nat.pair q (Nat.pair envelopeCode rowInput)))
    bottomForest

@[simp] theorem fourfoldRowTailHandoffOfPackage_sourcePackage
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) :
    fourfoldRowTailHandoffOfPackage
        (fourfoldRowSourcePackage
          bottomForest envelopeCode modeCode q rowIndex inputCode) =
      fourfoldRowTailHandoff
        bottomForest envelopeCode modeCode q rowIndex inputCode := by
  simp [fourfoldRowTailHandoffOfPackage, fourfoldRowTailHandoff,
    fourfoldRowSourcePackage, fourfoldRowSourceContext,
    fourfoldRowEvaluationContext]

/-- **The row tail.**  A fixed repack followed by one link-time Boolean row
evaluator on the native handoff. -/
def fourfoldRowTailProgram (rowEvaluator : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms fourfoldRowTailRepackProgram rowEvaluator

theorem fourfoldRowTailProgram_oracleFree
    (rowEvaluator : NPOracleProgram) (hevaluator : OracleFree rowEvaluator) :
    OracleFree (fourfoldRowTailProgram rowEvaluator) :=
  oracleFree_linkPrograms fourfoldRowTailRepackProgram_oracleFree hevaluator

def fourfoldRowTailFuel (rowEvaluator : NPOracleProgram)
    (evaluatorFuel : ℕ → ℕ) (package : ℕ) : ℕ :=
  linkFuel rowEvaluator 13
    (evaluatorFuel (fourfoldRowTailHandoffOfPackage package))

/-- Exact execution of the row tail on one exact-bottom package. -/
theorem run_fourfoldRowTailProgram
    (rowEvaluator : NPOracleProgram) (evaluatorFuel : ℕ → ℕ)
    (maximumBits bottomForest envelopeCode modeCode q rowIndex
      inputCode : ℕ)
    (value : Bool)
    (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength q ≤ maximumBits)
    (hrepackBits :
      fourfoldRowTailRepackBits
          bottomForest envelopeCode modeCode q rowIndex inputCode ≤
        maximumBits)
    (hevaluator :
      runNPOracleProgram rowEvaluator maximumBits
          (evaluatorFuel
            (fourfoldRowTailHandoff
              bottomForest envelopeCode modeCode q rowIndex inputCode))
          (initialNPOracleState q
            (fourfoldRowTailHandoff
              bottomForest envelopeCode modeCode q rowIndex inputCode)) =
        some (boolCode value)) :
    runNPOracleProgram (fourfoldRowTailProgram rowEvaluator) maximumBits
        (fourfoldRowTailFuel rowEvaluator evaluatorFuel
          (fourfoldRowSourcePackage
            bottomForest envelopeCode modeCode q rowIndex inputCode))
        (initialNPOracleState q
          (fourfoldRowSourcePackage
            bottomForest envelopeCode modeCode q rowIndex inputCode)) =
      some (boolCode value) := by
  have hfuel :
      fourfoldRowTailFuel rowEvaluator evaluatorFuel
          (fourfoldRowSourcePackage
            bottomForest envelopeCode modeCode q rowIndex inputCode) =
        linkFuel rowEvaluator 13
          (evaluatorFuel
            (fourfoldRowTailHandoff
              bottomForest envelopeCode modeCode q rowIndex inputCode)) := by
    unfold fourfoldRowTailFuel
    rw [fourfoldRowTailHandoffOfPackage_sourcePackage]
  rw [hfuel]
  exact run_linkPrograms hpositive hlength
    (run_bits_mono
      (run_fourfoldRowTailRepackProgram bottomForest envelopeCode modeCode q
        rowIndex inputCode)
      hrepackBits)
    hevaluator

/-! ## §3 The two published row-tail specializations

These are exactly the `htail` premises of
`run_symmetricRowCalleeProgram_of_rowTail` and
`run_thresholdRowCalleeProgram_of_rowTail`, discharged from one exact
evaluator run on the native handoff. -/

def symmetricFourfoldRowTailHandoff
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) : ℕ :=
  fourfoldRowTailHandoff
    (symmetricFourfoldRowBottomForest algorithm request)
    (symmetricFourfoldRowRequest request rowIndex input).envelopeCode
    symmetricCircuitFamilyTag request.q rowIndex (encodeBitInput input)

def symmetricFourfoldRowTailBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) : ℕ :=
  fourfoldRowTailRepackBits
    (symmetricFourfoldRowBottomForest algorithm request)
    (symmetricFourfoldRowRequest request rowIndex input).envelopeCode
    symmetricCircuitFamilyTag request.q rowIndex (encodeBitInput input)

/-- The handoff is the canonical five-field row record, right-associated as
the machine's native pairs, beside the exact bottom forest. -/
theorem symmetricFourfoldRowTailHandoff_eq
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    symmetricFourfoldRowTailHandoff algorithm request rowIndex input =
      Nat.pair
        (symmetricFourfoldRowRequest request rowIndex input).handoffCode
        (symmetricFourfoldRowBottomForest algorithm request) :=
  rfl

theorem run_symmetricFourfoldRowTailProgram
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (calleeBits : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      symmetricFourfoldRowTailBits algorithm request rowIndex input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow algorithm liveScale
              accuracyExponent
              (symmetricFourfoldRowRequest request rowIndex input))))
    (rowIndex : ℕ) (input : BitInput request.q) :
    runNPOracleProgram (fourfoldRowTailProgram rowEvaluator) calleeBits
        (fourfoldRowTailFuel rowEvaluator evaluatorFuel
          (symmetricFourfoldRowBottomOutput algorithm request rowIndex
            input))
        (initialNPOracleState request.q
          (symmetricFourfoldRowBottomOutput algorithm request rowIndex
            input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) :=
  run_fourfoldRowTailProgram rowEvaluator evaluatorFuel calleeBits
    (symmetricFourfoldRowBottomForest algorithm request)
    (symmetricFourfoldRowRequest request rowIndex input).envelopeCode
    symmetricCircuitFamilyTag request.q rowIndex (encodeBitInput input) _
    hpositive hlength (hrepackBits rowIndex input) (hevaluator rowIndex input)

/-- Pointwise symmetric row-tail execution.  Unlike the historical wrapper,
this theorem does not demand a request-local register cap for every natural
row index before the concrete index is known. -/
theorem run_symmetricFourfoldRowTailProgram_pointwise
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (calleeBits : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (rowIndex : ℕ) (input : BitInput request.q)
    (hrepackBits :
      symmetricFourfoldRowTailBits algorithm request rowIndex input ≤
        calleeBits)
    (hevaluator :
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
              (symmetricFourfoldRowRequest request rowIndex input)))) :
    runNPOracleProgram (fourfoldRowTailProgram rowEvaluator) calleeBits
        (fourfoldRowTailFuel rowEvaluator evaluatorFuel
          (symmetricFourfoldRowBottomOutput algorithm request rowIndex input))
        (initialNPOracleState request.q
          (symmetricFourfoldRowBottomOutput algorithm request rowIndex input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) :=
  run_fourfoldRowTailProgram rowEvaluator evaluatorFuel calleeBits
    (symmetricFourfoldRowBottomForest algorithm request)
    (symmetricFourfoldRowRequest request rowIndex input).envelopeCode
    symmetricCircuitFamilyTag request.q rowIndex (encodeBitInput input) _
    hpositive hlength hrepackBits hevaluator

def thresholdFourfoldRowTailHandoff
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) : ℕ :=
  fourfoldRowTailHandoff
    (thresholdFourfoldRowBottomForest algorithm request)
    (thresholdFourfoldRowRequest request rowIndex input).envelopeCode
    thresholdCircuitFamilyTag request.q rowIndex (encodeBitInput input)

def thresholdFourfoldRowTailBits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) : ℕ :=
  fourfoldRowTailRepackBits
    (thresholdFourfoldRowBottomForest algorithm request)
    (thresholdFourfoldRowRequest request rowIndex input).envelopeCode
    thresholdCircuitFamilyTag request.q rowIndex (encodeBitInput input)

theorem thresholdFourfoldRowTailHandoff_eq
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    thresholdFourfoldRowTailHandoff algorithm request rowIndex input =
      Nat.pair
        (thresholdFourfoldRowRequest request rowIndex input).handoffCode
        (thresholdFourfoldRowBottomForest algorithm request) :=
  rfl

theorem run_thresholdFourfoldRowTailProgram
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (calleeBits : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      thresholdFourfoldRowTailBits algorithm request rowIndex input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex
              input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow algorithm liveScale
              accuracyExponent
              (thresholdFourfoldRowRequest request rowIndex input))))
    (rowIndex : ℕ) (input : BitInput request.q) :
    runNPOracleProgram (fourfoldRowTailProgram rowEvaluator) calleeBits
        (fourfoldRowTailFuel rowEvaluator evaluatorFuel
          (thresholdFourfoldRowBottomOutput algorithm request rowIndex
            input))
        (initialNPOracleState request.q
          (thresholdFourfoldRowBottomOutput algorithm request rowIndex
            input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (thresholdFourfoldRowRequest request rowIndex input))) :=
  run_fourfoldRowTailProgram rowEvaluator evaluatorFuel calleeBits
    (thresholdFourfoldRowBottomForest algorithm request)
    (thresholdFourfoldRowRequest request rowIndex input).envelopeCode
    thresholdCircuitFamilyTag request.q rowIndex (encodeBitInput input) _
    hpositive hlength (hrepackBits rowIndex input) (hevaluator rowIndex input)

/-- Pointwise threshold twin of
`run_symmetricFourfoldRowTailProgram_pointwise`. -/
theorem run_thresholdFourfoldRowTailProgram_pointwise
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (calleeBits : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (rowIndex : ℕ) (input : BitInput request.q)
    (hrepackBits :
      thresholdFourfoldRowTailBits algorithm request rowIndex input ≤
        calleeBits)
    (hevaluator :
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
              (thresholdFourfoldRowRequest request rowIndex input)))) :
    runNPOracleProgram (fourfoldRowTailProgram rowEvaluator) calleeBits
        (fourfoldRowTailFuel rowEvaluator evaluatorFuel
          (thresholdFourfoldRowBottomOutput algorithm request rowIndex input))
        (initialNPOracleState request.q
          (thresholdFourfoldRowBottomOutput algorithm request rowIndex input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (thresholdFourfoldRowRequest request rowIndex input))) :=
  run_fourfoldRowTailProgram rowEvaluator evaluatorFuel calleeBits
    (thresholdFourfoldRowBottomForest algorithm request)
    (thresholdFourfoldRowRequest request rowIndex input).envelopeCode
    thresholdCircuitFamilyTag request.q rowIndex (encodeBitInput input) _
    hpositive hlength hrepackBits hevaluator

/-! ## §4 The compiled Boolean row callee

The aggregation controller charges its callee a fuel that depends only on the
generated range atom, so the tail fuel is re-expressed through the atom's own
projections. -/

/-- Exact-bottom lowering followed by the row tail: the complete Boolean row
callee consumed by the fixed range controller. -/
def sharedFourfoldRangeCalleeProgram
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (rowEvaluator : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (fourfoldRangeBottomProgram algorithm)
    (fourfoldRowTailProgram rowEvaluator)

theorem sharedFourfoldRangeCalleeProgram_oracleFree
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (rowEvaluator : NPOracleProgram) (hevaluator : OracleFree rowEvaluator) :
    OracleFree (sharedFourfoldRangeCalleeProgram algorithm rowEvaluator) :=
  oracleFree_linkPrograms (fourfoldRangeBottomProgram_oracleFree algorithm)
    (fourfoldRowTailProgram_oracleFree rowEvaluator hevaluator)

/-- The flat range coordinate carried by one generated atom. -/
def balancedRangeAtomIndex (atom : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair atom).2).1

@[simp] theorem balancedRangeAtomIndex_atom
    (inputLength index context : ℕ) :
    balancedRangeAtomIndex (balancedRangeRequestAtom inputLength index
        context) =
      index := by
  simp [balancedRangeAtomIndex, balancedRangeRequestAtom]

noncomputable def symmetricRowCalleeAtomFuel
    (contracts : PublishedContracts)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (evaluatorFuel : ℕ → ℕ)
    (atom : ℕ) : ℕ :=
  symmetricRowCalleeFuel contracts request
    (fourfoldRowTailProgram rowEvaluator)
    (fourfoldRowTailFuel rowEvaluator evaluatorFuel)
    (balancedRangeAtomIndex atom)

noncomputable def thresholdRowCalleeAtomFuel
    (contracts : PublishedContracts)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (evaluatorFuel : ℕ → ℕ)
    (atom : ℕ) : ℕ :=
  thresholdRowCalleeFuel contracts request
    (fourfoldRowTailProgram rowEvaluator)
    (fourfoldRowTailFuel rowEvaluator evaluatorFuel)
    (balancedRangeAtomIndex atom)

/-- **The discharged `hexec` premise, symmetric case.**  One exact evaluator
run per row handoff yields the exact callee run on every generated atom. -/
theorem run_symmetricRowCalleeProgram_of_rowEvaluator
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (calleeBits : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request →
      symmetricFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (fourfoldRangeDenominatorTail
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      symmetricFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (symmetricFourfoldRowRequest request rowIndex input))))
    (flat : ℕ)
    (hflat :
      flat <
        fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :
    runNPOracleProgram
        (sharedFourfoldRangeCalleeProgram
          (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
        calleeBits
        (symmetricRowCalleeAtomFuel contracts request rowEvaluator
          evaluatorFuel
          (balancedRangeRequestAtom request.q flat
            (fourfoldRangeCallContext
              (publishedSymmetricRows contracts liveScale accuracyExponent)
              request .symmetric
              (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
                encodeNormalizedSymmetricThresholdCircuit request))))
        (initialNPOracleState request.q
          (fourfoldRangeCallAtom
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request .symmetric
            (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
              encodeNormalizedSymmetricThresholdCircuit request) flat)) =
      some
        (boolCode
          (fourfoldFlatRowValue
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request flat)) := by
  have hfuel :
      symmetricRowCalleeAtomFuel contracts request rowEvaluator evaluatorFuel
          (balancedRangeRequestAtom request.q flat
            (fourfoldRangeCallContext
              (publishedSymmetricRows contracts liveScale accuracyExponent)
              request .symmetric
              (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
                encodeNormalizedSymmetricThresholdCircuit request))) =
        symmetricRowCalleeFuel contracts request
          (fourfoldRowTailProgram rowEvaluator)
          (fourfoldRowTailFuel rowEvaluator evaluatorFuel) flat := by
    unfold symmetricRowCalleeAtomFuel
    rw [balancedRangeAtomIndex_atom]
  rw [hfuel]
  exact run_symmetricRowCalleeProgram_of_rowTail contracts liveScale
    accuracyExponent request (fourfoldRowTailProgram rowEvaluator) calleeBits
    (fourfoldRowTailFuel rowEvaluator evaluatorFuel) hpositive hlength
    hbottomBits
    (run_symmetricFourfoldRowTailProgram
      (selectedExactDecompositionAlgorithm contracts) liveScale
      accuracyExponent request rowEvaluator calleeBits evaluatorFuel
      hpositive hlength hrepackBits hevaluator)
    flat hflat

/-- Symmetric exact-bottom plus row-tail closure on the controller's finite row
domain.  Both the repack width and evaluator run are requested only where the
flat controller can call them. -/
theorem run_symmetricRowCalleeProgram_of_boundedRowEvaluator
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (calleeBits : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request →
      symmetricFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (fourfoldRangeDenominatorTail
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      rowIndex <
          (publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request →
      symmetricFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      rowIndex <
          (publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request →
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (symmetricFourfoldRowRequest request rowIndex input))))
    (flat : ℕ)
    (hflat :
      flat <
        fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :
    runNPOracleProgram
        (sharedFourfoldRangeCalleeProgram
          (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
        calleeBits
        (symmetricRowCalleeAtomFuel contracts request rowEvaluator
          evaluatorFuel
          (balancedRangeRequestAtom request.q flat
            (fourfoldRangeCallContext
              (publishedSymmetricRows contracts liveScale accuracyExponent)
              request .symmetric
              (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
                encodeNormalizedSymmetricThresholdCircuit request))))
        (initialNPOracleState request.q
          (fourfoldRangeCallAtom
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request .symmetric
            (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
              encodeNormalizedSymmetricThresholdCircuit request) flat)) =
      some
        (boolCode
          (fourfoldFlatRowValue
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request flat)) := by
  have hfuel :
      symmetricRowCalleeAtomFuel contracts request rowEvaluator evaluatorFuel
          (balancedRangeRequestAtom request.q flat
            (fourfoldRangeCallContext
              (publishedSymmetricRows contracts liveScale accuracyExponent)
              request .symmetric
              (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
                encodeNormalizedSymmetricThresholdCircuit request))) =
        symmetricRowCalleeFuel contracts request
          (fourfoldRowTailProgram rowEvaluator)
          (fourfoldRowTailFuel rowEvaluator evaluatorFuel) flat := by
    unfold symmetricRowCalleeAtomFuel
    rw [balancedRangeAtomIndex_atom]
  rw [hfuel]
  exact run_symmetricRowCalleeProgram_of_boundedRowTail contracts liveScale
    accuracyExponent request (fourfoldRowTailProgram rowEvaluator) calleeBits
    (fourfoldRowTailFuel rowEvaluator evaluatorFuel) hpositive hlength
    hbottomBits
    (fun rowIndex input hrow =>
      run_symmetricFourfoldRowTailProgram_pointwise
        (selectedExactDecompositionAlgorithm contracts) liveScale
        accuracyExponent request rowEvaluator calleeBits evaluatorFuel
        hpositive hlength rowIndex input (hrepackBits rowIndex input hrow)
        (hevaluator rowIndex input hrow))
    flat hflat

/-- **The discharged `hexec` premise, threshold case.** -/
theorem run_thresholdRowCalleeProgram_of_rowEvaluator
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (calleeBits : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request →
      thresholdFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (fourfoldRangeDenominatorTail
            (publishedThresholdRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      thresholdFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (thresholdFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (thresholdFourfoldRowRequest request rowIndex input))))
    (flat : ℕ)
    (hflat :
      flat <
        fourfoldRangeAtomCount
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request) :
    runNPOracleProgram
        (sharedFourfoldRangeCalleeProgram
          (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
        calleeBits
        (thresholdRowCalleeAtomFuel contracts request rowEvaluator
          evaluatorFuel
          (balancedRangeRequestAtom request.q flat
            (fourfoldRangeCallContext
              (publishedThresholdRows contracts liveScale accuracyExponent)
              request .threshold
              (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
                encodeNormalizedThresholdThresholdCircuit request))))
        (initialNPOracleState request.q
          (fourfoldRangeCallAtom
            (publishedThresholdRows contracts liveScale accuracyExponent)
            request .threshold
            (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
              encodeNormalizedThresholdThresholdCircuit request) flat)) =
      some
        (boolCode
          (fourfoldFlatRowValue
            (publishedThresholdRows contracts liveScale accuracyExponent)
            request flat)) := by
  have hfuel :
      thresholdRowCalleeAtomFuel contracts request rowEvaluator evaluatorFuel
          (balancedRangeRequestAtom request.q flat
            (fourfoldRangeCallContext
              (publishedThresholdRows contracts liveScale accuracyExponent)
              request .threshold
              (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
                encodeNormalizedThresholdThresholdCircuit request))) =
        thresholdRowCalleeFuel contracts request
          (fourfoldRowTailProgram rowEvaluator)
          (fourfoldRowTailFuel rowEvaluator evaluatorFuel) flat := by
    unfold thresholdRowCalleeAtomFuel
    rw [balancedRangeAtomIndex_atom]
  rw [hfuel]
  exact run_thresholdRowCalleeProgram_of_rowTail contracts liveScale
    accuracyExponent request (fourfoldRowTailProgram rowEvaluator) calleeBits
    (fourfoldRowTailFuel rowEvaluator evaluatorFuel) hpositive hlength
    hbottomBits
    (run_thresholdFourfoldRowTailProgram
      (selectedExactDecompositionAlgorithm contracts) liveScale
      accuracyExponent request rowEvaluator calleeBits evaluatorFuel
      hpositive hlength hrepackBits hevaluator)
    flat hflat

/-- Threshold twin of
`run_symmetricRowCalleeProgram_of_boundedRowEvaluator`. -/
theorem run_thresholdRowCalleeProgram_of_boundedRowEvaluator
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (calleeBits : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request →
      thresholdFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (fourfoldRangeDenominatorTail
            (publishedThresholdRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      rowIndex <
          (publishedThresholdRows contracts liveScale
            accuracyExponent).rowCount request →
      thresholdFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      rowIndex <
          (publishedThresholdRows contracts liveScale
            accuracyExponent).rowCount request →
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (thresholdFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (thresholdFourfoldRowRequest request rowIndex input))))
    (flat : ℕ)
    (hflat :
      flat <
        fourfoldRangeAtomCount
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request) :
    runNPOracleProgram
        (sharedFourfoldRangeCalleeProgram
          (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
        calleeBits
        (thresholdRowCalleeAtomFuel contracts request rowEvaluator
          evaluatorFuel
          (balancedRangeRequestAtom request.q flat
            (fourfoldRangeCallContext
              (publishedThresholdRows contracts liveScale accuracyExponent)
              request .threshold
              (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
                encodeNormalizedThresholdThresholdCircuit request))))
        (initialNPOracleState request.q
          (fourfoldRangeCallAtom
            (publishedThresholdRows contracts liveScale accuracyExponent)
            request .threshold
            (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
              encodeNormalizedThresholdThresholdCircuit request) flat)) =
      some
        (boolCode
          (fourfoldFlatRowValue
            (publishedThresholdRows contracts liveScale accuracyExponent)
            request flat)) := by
  have hfuel :
      thresholdRowCalleeAtomFuel contracts request rowEvaluator evaluatorFuel
          (balancedRangeRequestAtom request.q flat
            (fourfoldRangeCallContext
              (publishedThresholdRows contracts liveScale accuracyExponent)
              request .threshold
              (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
                encodeNormalizedThresholdThresholdCircuit request))) =
        thresholdRowCalleeFuel contracts request
          (fourfoldRowTailProgram rowEvaluator)
          (fourfoldRowTailFuel rowEvaluator evaluatorFuel) flat := by
    unfold thresholdRowCalleeAtomFuel
    rw [balancedRangeAtomIndex_atom]
  rw [hfuel]
  exact run_thresholdRowCalleeProgram_of_boundedRowTail contracts liveScale
    accuracyExponent request (fourfoldRowTailProgram rowEvaluator) calleeBits
    (fourfoldRowTailFuel rowEvaluator evaluatorFuel) hpositive hlength
    hbottomBits
    (fun rowIndex input hrow =>
      run_thresholdFourfoldRowTailProgram_pointwise
        (selectedExactDecompositionAlgorithm contracts) liveScale
        accuracyExponent request rowEvaluator calleeBits evaluatorFuel
        hpositive hlength rowIndex input (hrepackBits rowIndex input hrow)
        (hevaluator rowIndex input hrow))
    flat hflat

/-! ## §5 The compiled all-row aggregation component -/

/-- Balanced all-row aggregation with the compiled Boolean row callee linked
in.  No stage of this program takes a semantic argument. -/
def sharedFourfoldRangeComponentProgram
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (rowEvaluator : NPOracleProgram) : NPOracleProgram :=
  fixedBooleanRangeComponentProgram
    (sharedFourfoldRangeCalleeProgram algorithm rowEvaluator)

theorem sharedFourfoldRangeComponentProgram_oracleFree
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (rowEvaluator : NPOracleProgram) (hevaluator : OracleFree rowEvaluator) :
    OracleFree (sharedFourfoldRangeComponentProgram algorithm rowEvaluator) :=
  fixedBooleanRangeComponentProgram_oracleFree _
    (sharedFourfoldRangeCalleeProgram_oracleFree algorithm rowEvaluator
      hevaluator)

noncomputable def symmetricFourfoldRangeComponentBits
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (calleeBits : ℕ) : ℕ :=
  fourfoldRangeComponentBits calleeBits
    (publishedSymmetricRows contracts liveScale accuracyExponent) request
    .symmetric
    (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
      encodeNormalizedSymmetricThresholdCircuit request)

noncomputable def symmetricFourfoldRangeComponentFuel
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (evaluatorFuel : ℕ → ℕ) : ℕ :=
  fourfoldRangeComponentFuel
    (sharedFourfoldRangeCalleeProgram
      (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
    (symmetricRowCalleeAtomFuel contracts request rowEvaluator evaluatorFuel)
    (publishedSymmetricRows contracts liveScale accuracyExponent) request
    .symmetric
    (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
      encodeNormalizedSymmetricThresholdCircuit request)

/-- **Symmetric all-row aggregation, executed from the row evaluator.** -/
theorem run_symmetricFourfoldRangeComponentProgram_of_rowEvaluator
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (calleeBits : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request →
      symmetricFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (fourfoldRangeDenominatorTail
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      symmetricFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (symmetricFourfoldRowRequest request rowIndex input)))) :
    runNPOracleProgram
        (sharedFourfoldRangeComponentProgram
          (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
        (symmetricFourfoldRangeComponentBits contracts liveScale
          accuracyExponent request calleeBits)
        (symmetricFourfoldRangeComponentFuel contracts liveScale
          accuracyExponent request rowEvaluator evaluatorFuel)
        (initialNPOracleState request.q
          (generatedBalancedRangeInput
            (fourfoldRangeAtomCount
              (publishedSymmetricRows contracts liveScale accuracyExponent)
              request)
            (fourfoldRangeCallContext
              (publishedSymmetricRows contracts liveScale accuracyExponent)
              request .symmetric
              (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
                encodeNormalizedSymmetricThresholdCircuit request)))) =
      some
        (symmetricRatioComponentCode
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :=
  run_symmetricFourfoldRangeComponentProgram_of_rowCallee contracts liveScale
    accuracyExponent request
    (sharedFourfoldRangeCalleeProgram
      (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
    calleeBits
    (symmetricRowCalleeAtomFuel contracts request rowEvaluator evaluatorFuel)
    (fun flat hflat =>
      run_symmetricRowCalleeProgram_of_rowEvaluator contracts liveScale
        accuracyExponent request rowEvaluator calleeBits evaluatorFuel
        hpositive hlength hbottomBits hrepackBits hevaluator flat hflat)

/-- All-row symmetric aggregation from a row evaluator whose execution and
repack ledgers are stated only on the finite published row family. -/
theorem run_symmetricFourfoldRangeComponentProgram_of_boundedRowEvaluator
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (calleeBits : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request →
      symmetricFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (fourfoldRangeDenominatorTail
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      rowIndex <
          (publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request →
      symmetricFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      rowIndex <
          (publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request →
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (symmetricFourfoldRowRequest request rowIndex input)))) :
    runNPOracleProgram
        (sharedFourfoldRangeComponentProgram
          (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
        (symmetricFourfoldRangeComponentBits contracts liveScale
          accuracyExponent request calleeBits)
        (symmetricFourfoldRangeComponentFuel contracts liveScale
          accuracyExponent request rowEvaluator evaluatorFuel)
        (initialNPOracleState request.q
          (generatedBalancedRangeInput
            (fourfoldRangeAtomCount
              (publishedSymmetricRows contracts liveScale accuracyExponent)
              request)
            (fourfoldRangeCallContext
              (publishedSymmetricRows contracts liveScale accuracyExponent)
              request .symmetric
              (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
                encodeNormalizedSymmetricThresholdCircuit request)))) =
      some
        (symmetricRatioComponentCode
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :=
  run_symmetricFourfoldRangeComponentProgram_of_rowCallee contracts liveScale
    accuracyExponent request
    (sharedFourfoldRangeCalleeProgram
      (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
    calleeBits
    (symmetricRowCalleeAtomFuel contracts request rowEvaluator evaluatorFuel)
    (fun flat hflat =>
      run_symmetricRowCalleeProgram_of_boundedRowEvaluator contracts liveScale
        accuracyExponent request rowEvaluator calleeBits evaluatorFuel
        hpositive hlength hbottomBits hrepackBits hevaluator flat hflat)

noncomputable def thresholdFourfoldRangeComponentBits
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (calleeBits : ℕ) : ℕ :=
  fourfoldRangeComponentBits calleeBits
    (publishedThresholdRows contracts liveScale accuracyExponent) request
    .threshold
    (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
      encodeNormalizedThresholdThresholdCircuit request)

noncomputable def thresholdFourfoldRangeComponentFuel
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (evaluatorFuel : ℕ → ℕ) : ℕ :=
  fourfoldRangeComponentFuel
    (sharedFourfoldRangeCalleeProgram
      (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
    (thresholdRowCalleeAtomFuel contracts request rowEvaluator evaluatorFuel)
    (publishedThresholdRows contracts liveScale accuracyExponent) request
    .threshold
    (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
      encodeNormalizedThresholdThresholdCircuit request)

/-- **Threshold all-row aggregation, executed from the row evaluator.** -/
theorem run_thresholdFourfoldRangeComponentProgram_of_rowEvaluator
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowEvaluator : NPOracleProgram) (calleeBits : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request →
      thresholdFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (fourfoldRangeDenominatorTail
            (publishedThresholdRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      thresholdFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (thresholdFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (thresholdFourfoldRowRequest request rowIndex input)))) :
    runNPOracleProgram
        (sharedFourfoldRangeComponentProgram
          (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
        (thresholdFourfoldRangeComponentBits contracts liveScale
          accuracyExponent request calleeBits)
        (thresholdFourfoldRangeComponentFuel contracts liveScale
          accuracyExponent request rowEvaluator evaluatorFuel)
        (initialNPOracleState request.q
          (generatedBalancedRangeInput
            (fourfoldRangeAtomCount
              (publishedThresholdRows contracts liveScale accuracyExponent)
              request)
            (fourfoldRangeCallContext
              (publishedThresholdRows contracts liveScale accuracyExponent)
              request .threshold
              (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
                encodeNormalizedThresholdThresholdCircuit request)))) =
      some
        (thresholdRatioComponentCode
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request) :=
  run_thresholdFourfoldRangeComponentProgram_of_rowCallee contracts liveScale
    accuracyExponent request
    (sharedFourfoldRangeCalleeProgram
      (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
    calleeBits
    (thresholdRowCalleeAtomFuel contracts request rowEvaluator evaluatorFuel)
    (fun flat hflat =>
      run_thresholdRowCalleeProgram_of_rowEvaluator contracts liveScale
        accuracyExponent request rowEvaluator calleeBits evaluatorFuel
        hpositive hlength hbottomBits hrepackBits hevaluator flat hflat)

/-! ## §6 The envelope front end

The aggregation controller starts from `generatedBalancedRangeInput`, while
the artifact's public entry point is the typed envelope.  This section
executes the missing prefix: recover the family tag as a native number, build
the opaque row context, obtain the row-major atom count from one link-time
counter, and emit the denominator tail beside it. -/

def fourfoldRangeEntryTagOutput (tagCode payload : ℕ) : ℕ :=
  Nat.pair tagCode (Nat.pair tagCode payload)

/-- Expose the encoded family tag while retaining the whole envelope. -/
def fourfoldRangeEntryTagProgram : NPOracleProgram :=
  [ .unpairLeft 0 1 1
  , .pair 1 0 0 2
  , .halt 0
  ]

@[simp] theorem fourfoldRangeEntryTagProgram_oracleFree :
    OracleFree fourfoldRangeEntryTagProgram := by
  rfl

def fourfoldRangeEntryTagBits (tagCode payload : ℕ) : ℕ :=
  natBitLength (fourfoldRangeEntryTagOutput tagCode payload)

theorem run_fourfoldRangeEntryTagProgram (q tagCode payload : ℕ) :
    runNPOracleProgram fourfoldRangeEntryTagProgram
        (fourfoldRangeEntryTagBits tagCode payload) 3
        (initialNPOracleState q (Nat.pair tagCode payload)) =
      some (fourfoldRangeEntryTagOutput tagCode payload) := by
  let envelopeCode := Nat.pair tagCode payload
  let output := Nat.pair tagCode envelopeCode
  let maximumBits := fourfoldRangeEntryTagBits tagCode payload
  have houtput : natBitLength output ≤ maximumBits := Nat.le_refl _
  have htagCode : natBitLength tagCode ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair tagCode envelopeCode)).trans houtput
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tagCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    htagCode]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        output, envelopeCode])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

def fourfoldRangeEntryContextOutput (modeCode envelopeCode : ℕ) : ℕ :=
  Nat.pair envelopeCode (Nat.pair modeCode envelopeCode)

/-- Freeze the opaque row context and expose the envelope for the counter. -/
def fourfoldRangeEntryContextProgram : NPOracleProgram :=
  [ .unpairRight 0 1 1
  , .pair 1 0 0 2
  , .halt 0
  ]

@[simp] theorem fourfoldRangeEntryContextProgram_oracleFree :
    OracleFree fourfoldRangeEntryContextProgram := by
  rfl

def fourfoldRangeEntryContextBits (modeCode envelopeCode : ℕ) : ℕ :=
  natBitLength (fourfoldRangeEntryContextOutput modeCode envelopeCode)

theorem run_fourfoldRangeEntryContextProgram
    (q modeCode envelopeCode : ℕ) :
    runNPOracleProgram fourfoldRangeEntryContextProgram
        (fourfoldRangeEntryContextBits modeCode envelopeCode) 3
        (initialNPOracleState q (Nat.pair modeCode envelopeCode)) =
      some (fourfoldRangeEntryContextOutput modeCode envelopeCode) := by
  let rowContext := Nat.pair modeCode envelopeCode
  let output := Nat.pair envelopeCode rowContext
  let maximumBits := fourfoldRangeEntryContextBits modeCode envelopeCode
  have houtput : natBitLength output ≤ maximumBits := Nat.le_refl _
  have henvelopeCode : natBitLength envelopeCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair envelopeCode rowContext)).trans houtput
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := envelopeCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    henvelopeCode]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        output, rowContext])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

def fourfoldRangeEntryPackerOutput (count rowContext : ℕ) : ℕ :=
  generatedBalancedRangeInput count
    (fixedBooleanRangeComponentContext (count - 1) rowContext)

/-- Emit the published denominator tail beside the sample count.  The tail is
one below the count, matching `fourfoldRangeDenominatorTail`. -/
def fourfoldRangeEntryPackerProgram : NPOracleProgram :=
  [ .unpairLeft 0 1 1
  , .unpairRight 0 2 2
  , .copy 1 3 3
  , .decrement 3 4
  , .pair 3 2 4 5
  , .pair 1 4 0 6
  , .halt 0
  ]

@[simp] theorem fourfoldRangeEntryPackerProgram_oracleFree :
    OracleFree fourfoldRangeEntryPackerProgram := by
  rfl

def fourfoldRangeEntryPackerBits (count rowContext : ℕ) : ℕ :=
  natBitLength <|
    max (Nat.pair count rowContext)
      (fourfoldRangeEntryPackerOutput count rowContext) + 1

theorem run_fourfoldRangeEntryPackerProgram (q count rowContext : ℕ) :
    runNPOracleProgram fourfoldRangeEntryPackerProgram
        (fourfoldRangeEntryPackerBits count rowContext) 7
        (initialNPOracleState q (Nat.pair count rowContext)) =
      some (fourfoldRangeEntryPackerOutput count rowContext) := by
  let input := Nat.pair count rowContext
  let inner := Nat.pair (count - 1) rowContext
  let output := Nat.pair count inner
  let bound := max input output + 1
  let maximumBits := fourfoldRangeEntryPackerBits count rowContext
  have hmaximumBits : natBitLength bound = maximumBits := rfl
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
  have hcount : natBitLength count ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair count rowContext)).trans hinput
  have hrowContext : natBitLength rowContext ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair count rowContext)).trans hinput
  have hpredCount : natBitLength (count - 1) ≤ maximumBits :=
    (natBitLength_mono (Nat.sub_le count 1)).trans hcount
  have hinner : natBitLength inner ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair count inner)).trans houtput
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := count)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hcount]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := rowContext)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hrowContext]
  rw [show 5 = 4 + 1 by omega]
  rw [run_copy_instruction (value := count)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcount]
  rw [show 4 = 3 + 1 by omega]
  rw [run_decrement_instruction (value := count - 1)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpredCount]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := inner)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, inner])
    hinner]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-- **The envelope front end.**  One link-time atom counter is the only
non-structural stage. -/
def fourfoldRangeEntryProgram (countProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms fourfoldRangeEntryTagProgram
    (linkPrograms (preserveRightProgram canonicalNatDecodeProgram)
      (linkPrograms fourfoldRangeEntryContextProgram
        (linkPrograms (preserveRightProgram countProgram)
          fourfoldRangeEntryPackerProgram)))

theorem fourfoldRangeEntryProgram_oracleFree
    (countProgram : NPOracleProgram) (hcount : OracleFree countProgram) :
    OracleFree (fourfoldRangeEntryProgram countProgram) :=
  oracleFree_linkPrograms fourfoldRangeEntryTagProgram_oracleFree <|
    oracleFree_linkPrograms
      (preserveRightProgram_oracleFree _ canonicalNatDecodeProgram_oracleFree)
      (oracleFree_linkPrograms fourfoldRangeEntryContextProgram_oracleFree
        (oracleFree_linkPrograms
          (preserveRightProgram_oracleFree _ hcount)
          fourfoldRangeEntryPackerProgram_oracleFree))

def fourfoldRangeEntryStageBits
    (q familyTag payload countBits count : ℕ) : List ℕ :=
  let envelopeCode := Nat.pair (encodeNat familyTag) payload
  let rowContext := Nat.pair familyTag envelopeCode
  [ 1
  , natBitLength q
  , fourfoldRangeEntryTagBits (encodeNat familyTag) payload
  , preserveRightBits (canonicalNatDecodeBits q familyTag)
      (encodeNat familyTag) envelopeCode familyTag
  , fourfoldRangeEntryContextBits familyTag envelopeCode
  , preserveRightBits countBits envelopeCode rowContext count
  , fourfoldRangeEntryPackerBits count rowContext
  ]

def fourfoldRangeEntryBits
    (q familyTag payload countBits count : ℕ) : ℕ :=
  (fourfoldRangeEntryStageBits q familyTag payload countBits count).foldr
    max 1

def fourfoldRangeEntryFuel (countProgram : NPOracleProgram)
    (familyTag countFuel : ℕ) : ℕ :=
  linkFuel
      (linkPrograms (preserveRightProgram canonicalNatDecodeProgram)
        (linkPrograms fourfoldRangeEntryContextProgram
          (linkPrograms (preserveRightProgram countProgram)
            fourfoldRangeEntryPackerProgram))) 3 <|
    linkFuel
        (linkPrograms fourfoldRangeEntryContextProgram
          (linkPrograms (preserveRightProgram countProgram)
            fourfoldRangeEntryPackerProgram))
        (preserveRightFuel (canonicalNatDecodeFuel familyTag)) <|
      linkFuel
          (linkPrograms (preserveRightProgram countProgram)
            fourfoldRangeEntryPackerProgram) 3 <|
        linkFuel fourfoldRangeEntryPackerProgram (preserveRightFuel countFuel)
          7

private theorem entry_le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ}
    (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

/-- **The envelope front end, executed.**  From one exact run of the atom
counter on the typed envelope, the front end emits precisely the balanced
range input consumed by the fixed aggregation controller. -/
theorem run_fourfoldRangeEntryProgram
    (countProgram : NPOracleProgram)
    (q familyTag payload countBits countFuel count : ℕ)
    (hcount :
      runNPOracleProgram countProgram countBits countFuel
          (initialNPOracleState q (Nat.pair (encodeNat familyTag) payload)) =
        some count) :
    runNPOracleProgram (fourfoldRangeEntryProgram countProgram)
        (fourfoldRangeEntryBits q familyTag payload countBits count)
        (fourfoldRangeEntryFuel countProgram familyTag countFuel)
        (initialNPOracleState q
          (Nat.pair (encodeNat familyTag) payload)) =
      some
        (generatedBalancedRangeInput count
          (fixedBooleanRangeComponentContext (count - 1)
            (Nat.pair familyTag
              (Nat.pair (encodeNat familyTag) payload)))) := by
  let envelopeCode := Nat.pair (encodeNat familyTag) payload
  let rowContext := Nat.pair familyTag envelopeCode
  let maximumBits :=
    fourfoldRangeEntryBits q familyTag payload countBits count
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈ fourfoldRangeEntryStageBits q familyTag payload countBits
          count) :
      value ≤ maximumBits := by
    dsimp only [maximumBits, fourfoldRangeEntryBits]
    exact entry_le_foldr_max_of_mem hvalue
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeEntryStageBits]
  have hq : natBitLength q ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeEntryStageBits]
  have htagBits :
      fourfoldRangeEntryTagBits (encodeNat familyTag) payload ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeEntryStageBits]
  have hdecodeBits :
      preserveRightBits (canonicalNatDecodeBits q familyTag)
          (encodeNat familyTag) envelopeCode familyTag ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeEntryStageBits, envelopeCode]
  have hcontextBits :
      fourfoldRangeEntryContextBits familyTag envelopeCode ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeEntryStageBits, envelopeCode]
  have hcountBits :
      preserveRightBits countBits envelopeCode rowContext count ≤
        maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeEntryStageBits, envelopeCode, rowContext]
  have hpackerBits :
      fourfoldRangeEntryPackerBits count rowContext ≤ maximumBits := by
    apply bits_of_member
    simp [fourfoldRangeEntryStageBits, envelopeCode, rowContext]
  have htag :
      runNPOracleProgram fourfoldRangeEntryTagProgram maximumBits 3
          (initialNPOracleState q envelopeCode) =
        some (Nat.pair (encodeNat familyTag) envelopeCode) :=
    run_bits_mono
      (run_fourfoldRangeEntryTagProgram q (encodeNat familyTag) payload)
      htagBits
  have hdecode :
      runNPOracleProgram (preserveRightProgram canonicalNatDecodeProgram)
          maximumBits (preserveRightFuel (canonicalNatDecodeFuel familyTag))
          (initialNPOracleState q
            (Nat.pair (encodeNat familyTag) envelopeCode)) =
        some (Nat.pair familyTag envelopeCode) :=
    run_bits_mono
      (run_preserveRightProgram canonicalNatDecodeProgram q
        (canonicalNatDecodeBits q familyTag)
        (canonicalNatDecodeFuel familyTag) (encodeNat familyTag)
        envelopeCode familyTag (run_canonicalNatDecodeProgram q familyTag))
      hdecodeBits
  have hcontext :
      runNPOracleProgram fourfoldRangeEntryContextProgram maximumBits 3
          (initialNPOracleState q rowContext) =
        some (Nat.pair envelopeCode rowContext) :=
    run_bits_mono
      (run_fourfoldRangeEntryContextProgram q familyTag envelopeCode)
      hcontextBits
  have hcountStage :
      runNPOracleProgram (preserveRightProgram countProgram) maximumBits
          (preserveRightFuel countFuel)
          (initialNPOracleState q (Nat.pair envelopeCode rowContext)) =
        some (Nat.pair count rowContext) :=
    run_bits_mono
      (run_preserveRightProgram countProgram q countBits countFuel
        envelopeCode rowContext count hcount)
      hcountBits
  have hpacker :
      runNPOracleProgram fourfoldRangeEntryPackerProgram maximumBits 7
          (initialNPOracleState q (Nat.pair count rowContext)) =
        some (fourfoldRangeEntryPackerOutput count rowContext) :=
    run_bits_mono
      (run_fourfoldRangeEntryPackerProgram q count rowContext)
      hpackerBits
  exact run_linkPrograms hpositive hq htag
    (run_linkPrograms hpositive hq hdecode
      (run_linkPrograms hpositive hq hcontext
        (run_linkPrograms hpositive hq hcountStage hpacker)))

/-! ## §7 One program from the typed envelope to the ratio component

This is the shape `SharedNormalizedAggregationArtifact.computesSymmetric` and
`…computesThreshold` consume.  The program is fixed once for both modes: the
family tag is decoded from the request, never supplied. -/

/-- Everything of the typed envelope below the encoded family tag. -/
def fourfoldRequestEnvelopePayload
    {Circuit : CircuitFamily}
    (encodeCircuit : {q : ℕ} → Circuit q → ℕ)
    (request : FourfoldRequest Circuit) : ℕ :=
  Nat.pair request.q
    (encodeBalancedList (request.circuits.map encodeCircuit))

theorem fourfoldRequestEnvelopeOutput_eq_pair
    {Circuit : CircuitFamily}
    (familyTag : ℕ)
    (encodeCircuit : {q : ℕ} → Circuit q → ℕ)
    (request : FourfoldRequest Circuit) :
    fourfoldRequestEnvelopeOutput familyTag encodeCircuit request =
      Nat.pair (encodeNat familyTag)
        (fourfoldRequestEnvelopePayload encodeCircuit request) :=
  rfl

/-- **The composed aggregation program.**  Envelope front end, balanced
all-row aggregation, and the compiled Boolean row callee, linked once. -/
def sharedFourfoldAggregationProgram
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (countProgram rowEvaluator : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (fourfoldRangeEntryProgram countProgram)
    (sharedFourfoldRangeComponentProgram algorithm rowEvaluator)

theorem sharedFourfoldAggregationProgram_oracleFree
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (countProgram rowEvaluator : NPOracleProgram)
    (hcount : OracleFree countProgram)
    (hevaluator : OracleFree rowEvaluator) :
    OracleFree
      (sharedFourfoldAggregationProgram algorithm countProgram
        rowEvaluator) :=
  oracleFree_linkPrograms
    (fourfoldRangeEntryProgram_oracleFree countProgram hcount)
    (sharedFourfoldRangeComponentProgram_oracleFree algorithm rowEvaluator
      hevaluator)

noncomputable def symmetricFourfoldEntryBits
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (countBits : ℕ) : ℕ :=
  fourfoldRangeEntryBits request.q symmetricCircuitFamilyTag
    (fourfoldRequestEnvelopePayload
      encodeNormalizedSymmetricThresholdCircuit request)
    countBits
    (fourfoldRangeAtomCount
      (publishedSymmetricRows contracts liveScale accuracyExponent) request)

noncomputable def symmetricSharedFourfoldAggregationFuel
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (countProgram rowEvaluator : NPOracleProgram)
    (countFuel : ℕ) (evaluatorFuel : ℕ → ℕ) : ℕ :=
  linkFuel
    (sharedFourfoldRangeComponentProgram
      (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
    (fourfoldRangeEntryFuel countProgram symmetricCircuitFamilyTag countFuel)
    (symmetricFourfoldRangeComponentFuel contracts liveScale accuracyExponent
      request rowEvaluator evaluatorFuel)

/-- The front end's output is literally the controller's balanced range
input; the family tag doubles as the canonical mode code. -/
private theorem symmetricEntryOutput_eq
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    generatedBalancedRangeInput
        (fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request)
        (fixedBooleanRangeComponentContext
          (fourfoldRangeAtomCount
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request - 1)
          (Nat.pair symmetricCircuitFamilyTag
            (Nat.pair (encodeNat symmetricCircuitFamilyTag)
              (fourfoldRequestEnvelopePayload
                encodeNormalizedSymmetricThresholdCircuit request)))) =
      generatedBalancedRangeInput
        (fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request)
        (fourfoldRangeCallContext
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request .symmetric
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request)) :=
  rfl

/-- **Symmetric closure of the artifact's execution field.**  Two link-time
callees with exact interpreter premises, one fixed program, one exact run. -/
theorem run_sharedFourfoldAggregationProgram_symmetric
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (countProgram rowEvaluator : NPOracleProgram)
    (maximumBits calleeBits countBits countFuel : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hentryBits :
      symmetricFourfoldEntryBits contracts liveScale accuracyExponent request
          countBits ≤
        maximumBits)
    (hcomponentBits :
      symmetricFourfoldRangeComponentBits contracts liveScale
          accuracyExponent request calleeBits ≤
        maximumBits)
    (hcalleePositive : 1 ≤ calleeBits)
    (hcalleeLength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request →
      symmetricFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (fourfoldRangeDenominatorTail
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      symmetricFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (symmetricFourfoldRowRequest request rowIndex input))))
    (hcount :
      runNPOracleProgram countProgram countBits countFuel
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
              encodeNormalizedSymmetricThresholdCircuit request)) =
        some
          (fourfoldRangeAtomCount
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request)) :
    runNPOracleProgram
        (sharedFourfoldAggregationProgram
          (selectedExactDecompositionAlgorithm contracts) countProgram
          rowEvaluator)
        maximumBits
        (symmetricSharedFourfoldAggregationFuel contracts liveScale
          accuracyExponent request countProgram rowEvaluator countFuel
          evaluatorFuel)
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request)) =
      some
        (symmetricRatioComponentCode
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) := by
  have hentry :
      runNPOracleProgram (fourfoldRangeEntryProgram countProgram) maximumBits
          (fourfoldRangeEntryFuel countProgram symmetricCircuitFamilyTag
            countFuel)
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
              encodeNormalizedSymmetricThresholdCircuit request)) =
        some
          (generatedBalancedRangeInput
            (fourfoldRangeAtomCount
              (publishedSymmetricRows contracts liveScale accuracyExponent)
              request)
            (fourfoldRangeCallContext
              (publishedSymmetricRows contracts liveScale accuracyExponent)
              request .symmetric
              (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
                encodeNormalizedSymmetricThresholdCircuit request))) := by
    rw [← symmetricEntryOutput_eq contracts liveScale accuracyExponent
      request]
    exact run_bits_mono
      (run_fourfoldRangeEntryProgram countProgram request.q
        symmetricCircuitFamilyTag
        (fourfoldRequestEnvelopePayload
          encodeNormalizedSymmetricThresholdCircuit request)
        countBits countFuel
        (fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request)
        hcount)
      hentryBits
  have hcomponent :=
    run_bits_mono
      (run_symmetricFourfoldRangeComponentProgram_of_rowEvaluator contracts
        liveScale accuracyExponent request rowEvaluator calleeBits
        evaluatorFuel hcalleePositive hcalleeLength hbottomBits hrepackBits
        hevaluator)
      hcomponentBits
  exact run_linkPrograms hpositive hlength hentry hcomponent

/-- Symmetric artifact-branch execution with all row-indexed obligations
restricted to the finite published row family actually traversed. -/
theorem run_sharedFourfoldAggregationProgram_symmetric_bounded
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (countProgram rowEvaluator : NPOracleProgram)
    (maximumBits calleeBits countBits countFuel : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hentryBits :
      symmetricFourfoldEntryBits contracts liveScale accuracyExponent request
          countBits ≤
        maximumBits)
    (hcomponentBits :
      symmetricFourfoldRangeComponentBits contracts liveScale
          accuracyExponent request calleeBits ≤
        maximumBits)
    (hcalleePositive : 1 ≤ calleeBits)
    (hcalleeLength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request →
      symmetricFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (fourfoldRangeDenominatorTail
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      rowIndex <
          (publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request →
      symmetricFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      rowIndex <
          (publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request →
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (symmetricFourfoldRowRequest request rowIndex input))))
    (hcount :
      runNPOracleProgram countProgram countBits countFuel
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
              encodeNormalizedSymmetricThresholdCircuit request)) =
        some
          (fourfoldRangeAtomCount
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request)) :
    runNPOracleProgram
        (sharedFourfoldAggregationProgram
          (selectedExactDecompositionAlgorithm contracts) countProgram
          rowEvaluator)
        maximumBits
        (symmetricSharedFourfoldAggregationFuel contracts liveScale
          accuracyExponent request countProgram rowEvaluator countFuel
          evaluatorFuel)
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request)) =
      some
        (symmetricRatioComponentCode
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) := by
  have hentry :
      runNPOracleProgram (fourfoldRangeEntryProgram countProgram) maximumBits
          (fourfoldRangeEntryFuel countProgram symmetricCircuitFamilyTag
            countFuel)
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
              encodeNormalizedSymmetricThresholdCircuit request)) =
        some
          (generatedBalancedRangeInput
            (fourfoldRangeAtomCount
              (publishedSymmetricRows contracts liveScale accuracyExponent)
              request)
            (fourfoldRangeCallContext
              (publishedSymmetricRows contracts liveScale accuracyExponent)
              request .symmetric
              (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
                encodeNormalizedSymmetricThresholdCircuit request))) := by
    rw [← symmetricEntryOutput_eq contracts liveScale accuracyExponent
      request]
    exact run_bits_mono
      (run_fourfoldRangeEntryProgram countProgram request.q
        symmetricCircuitFamilyTag
        (fourfoldRequestEnvelopePayload
          encodeNormalizedSymmetricThresholdCircuit request)
        countBits countFuel
        (fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request)
        hcount)
      hentryBits
  have hcomponent :=
    run_bits_mono
      (run_symmetricFourfoldRangeComponentProgram_of_boundedRowEvaluator
        contracts liveScale accuracyExponent request rowEvaluator calleeBits
        evaluatorFuel hcalleePositive hcalleeLength hbottomBits hrepackBits
        hevaluator)
      hcomponentBits
  exact run_linkPrograms hpositive hlength hentry hcomponent

noncomputable def thresholdFourfoldEntryBits
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (countBits : ℕ) : ℕ :=
  fourfoldRangeEntryBits request.q thresholdCircuitFamilyTag
    (fourfoldRequestEnvelopePayload
      encodeNormalizedThresholdThresholdCircuit request)
    countBits
    (fourfoldRangeAtomCount
      (publishedThresholdRows contracts liveScale accuracyExponent) request)

noncomputable def thresholdSharedFourfoldAggregationFuel
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (countProgram rowEvaluator : NPOracleProgram)
    (countFuel : ℕ) (evaluatorFuel : ℕ → ℕ) : ℕ :=
  linkFuel
    (sharedFourfoldRangeComponentProgram
      (selectedExactDecompositionAlgorithm contracts) rowEvaluator)
    (fourfoldRangeEntryFuel countProgram thresholdCircuitFamilyTag countFuel)
    (thresholdFourfoldRangeComponentFuel contracts liveScale accuracyExponent
      request rowEvaluator evaluatorFuel)

private theorem thresholdEntryOutput_eq
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    generatedBalancedRangeInput
        (fourfoldRangeAtomCount
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request)
        (fixedBooleanRangeComponentContext
          (fourfoldRangeAtomCount
            (publishedThresholdRows contracts liveScale accuracyExponent)
            request - 1)
          (Nat.pair thresholdCircuitFamilyTag
            (Nat.pair (encodeNat thresholdCircuitFamilyTag)
              (fourfoldRequestEnvelopePayload
                encodeNormalizedThresholdThresholdCircuit request)))) =
      generatedBalancedRangeInput
        (fourfoldRangeAtomCount
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request)
        (fourfoldRangeCallContext
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request .threshold
          (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
            encodeNormalizedThresholdThresholdCircuit request)) :=
  rfl

/-- **Threshold closure of the artifact's execution field.** -/
theorem run_sharedFourfoldAggregationProgram_threshold
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (countProgram rowEvaluator : NPOracleProgram)
    (maximumBits calleeBits countBits countFuel : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hentryBits :
      thresholdFourfoldEntryBits contracts liveScale accuracyExponent request
          countBits ≤
        maximumBits)
    (hcomponentBits :
      thresholdFourfoldRangeComponentBits contracts liveScale
          accuracyExponent request calleeBits ≤
        maximumBits)
    (hcalleePositive : 1 ≤ calleeBits)
    (hcalleeLength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request →
      thresholdFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (fourfoldRangeDenominatorTail
            (publishedThresholdRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      thresholdFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (thresholdFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (thresholdFourfoldRowRequest request rowIndex input))))
    (hcount :
      runNPOracleProgram countProgram countBits countFuel
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
              encodeNormalizedThresholdThresholdCircuit request)) =
        some
          (fourfoldRangeAtomCount
            (publishedThresholdRows contracts liveScale accuracyExponent)
            request)) :
    runNPOracleProgram
        (sharedFourfoldAggregationProgram
          (selectedExactDecompositionAlgorithm contracts) countProgram
          rowEvaluator)
        maximumBits
        (thresholdSharedFourfoldAggregationFuel contracts liveScale
          accuracyExponent request countProgram rowEvaluator countFuel
          evaluatorFuel)
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
            encodeNormalizedThresholdThresholdCircuit request)) =
      some
        (thresholdRatioComponentCode
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request) := by
  have hentry :
      runNPOracleProgram (fourfoldRangeEntryProgram countProgram) maximumBits
          (fourfoldRangeEntryFuel countProgram thresholdCircuitFamilyTag
            countFuel)
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
              encodeNormalizedThresholdThresholdCircuit request)) =
        some
          (generatedBalancedRangeInput
            (fourfoldRangeAtomCount
              (publishedThresholdRows contracts liveScale accuracyExponent)
              request)
            (fourfoldRangeCallContext
              (publishedThresholdRows contracts liveScale accuracyExponent)
              request .threshold
              (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
                encodeNormalizedThresholdThresholdCircuit request))) := by
    rw [← thresholdEntryOutput_eq contracts liveScale accuracyExponent
      request]
    exact run_bits_mono
      (run_fourfoldRangeEntryProgram countProgram request.q
        thresholdCircuitFamilyTag
        (fourfoldRequestEnvelopePayload
          encodeNormalizedThresholdThresholdCircuit request)
        countBits countFuel
        (fourfoldRangeAtomCount
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request)
        hcount)
      hentryBits
  have hcomponent :=
    run_bits_mono
      (run_thresholdFourfoldRangeComponentProgram_of_rowEvaluator contracts
        liveScale accuracyExponent request rowEvaluator calleeBits
        evaluatorFuel hcalleePositive hcalleeLength hbottomBits hrepackBits
        hevaluator)
      hcomponentBits
  exact run_linkPrograms hpositive hlength hentry hcomponent

/-! ## §8 Splitting the row residual by published family

The artifact holds one program for both published families, so the row
evaluator above must serve both.  This section removes that coupling: the
canonical mode code already sits at the head of the row handoff, so a fixed
hoist plus the verified tag dispatcher reduces the single residual to one
evaluator per family.  Composing `run_fourfoldRowModeDispatchProgram_*` with
the `hevaluator` premise of §5 and §7 needs no further glue. -/

/-- Copy the canonical mode code to the head of the row-tail ABI. -/
def fourfoldRowModeHoistProgram : NPOracleProgram :=
  [ .unpairLeft 0 1 1
  , .unpairLeft 1 2 2
  , .pair 2 0 0 3
  , .halt 0
  ]

@[simp] theorem fourfoldRowModeHoistProgram_oracleFree :
    OracleFree fourfoldRowModeHoistProgram := by
  rfl

def fourfoldRowModeHoistBits (modeCode handoff : ℕ) : ℕ :=
  natBitLength (Nat.pair modeCode handoff)

theorem run_fourfoldRowModeHoistProgram
    (q modeCode rowFields bottomForest : ℕ) :
    runNPOracleProgram fourfoldRowModeHoistProgram
        (fourfoldRowModeHoistBits modeCode
          (Nat.pair (Nat.pair modeCode rowFields) bottomForest))
        4
        (initialNPOracleState q
          (Nat.pair (Nat.pair modeCode rowFields) bottomForest)) =
      some
        (Nat.pair modeCode
          (Nat.pair (Nat.pair modeCode rowFields) bottomForest)) := by
  let handoff := Nat.pair modeCode rowFields
  let input := Nat.pair handoff bottomForest
  let output := Nat.pair modeCode input
  let maximumBits := fourfoldRowModeHoistBits modeCode input
  have houtput : natBitLength output ≤ maximumBits := Nat.le_refl _
  have hinput : natBitLength input ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair modeCode input)).trans houtput
  have hhandoff : natBitLength handoff ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair handoff bottomForest)).trans hinput
  have hmodeCode : natBitLength modeCode ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair modeCode rowFields)).trans hhandoff
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := handoff)
    (by rfl) rfl
    (by simp [initialNPOracleState, handoff])
    hhandoff]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := modeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, handoff])
    hmodeCode]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        output, input, handoff])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-- **The two-family row evaluator.**  One fixed program; the published family
is read from the request, never supplied. -/
def fourfoldRowModeDispatchProgram
    (symmetricEvaluator thresholdEvaluator : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms fourfoldRowModeHoistProgram
    (taggedProgramChoice symmetricEvaluator thresholdEvaluator)

theorem fourfoldRowModeDispatchProgram_oracleFree
    (symmetricEvaluator thresholdEvaluator : NPOracleProgram)
    (hsymmetric : OracleFree symmetricEvaluator)
    (hthreshold : OracleFree thresholdEvaluator) :
    OracleFree
      (fourfoldRowModeDispatchProgram symmetricEvaluator
        thresholdEvaluator) :=
  oracleFree_linkPrograms fourfoldRowModeHoistProgram_oracleFree
    (taggedProgramChoice_oracleFree symmetricEvaluator thresholdEvaluator
      hsymmetric hthreshold)

def fourfoldRowModeDispatchFuel
    (symmetricEvaluator thresholdEvaluator : NPOracleProgram)
    (branchFuel : ℕ → ℕ) (handoff : ℕ) : ℕ :=
  linkFuel (taggedProgramChoice symmetricEvaluator thresholdEvaluator) 4
    (taggedProgramChoiceFuel (branchFuel handoff))

private theorem boolCode_bits_le
    {maximumBits : ℕ} (value : Bool) (hpositive : 1 ≤ maximumBits) :
    natBitLength (boolCode value) ≤ maximumBits := by
  have hbits : natBitLength (boolCode value) = 1 := by
    cases value <;> rfl
  rw [hbits]
  exact hpositive

/-- Symmetric branch of the dispatcher, in the `hevaluator` shape of §5. -/
theorem run_fourfoldRowModeDispatchProgram_symmetric
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (symmetricEvaluator thresholdEvaluator : NPOracleProgram)
    (calleeBits : ℕ) (branchFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hhoistBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      fourfoldRowModeHoistBits symmetricCircuitFamilyTag
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex
            input) ≤
        calleeBits)
    (hdispatchBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      natBitLength
          (Nat.pair request.q
            (Nat.pair symmetricCircuitFamilyTag
              (symmetricFourfoldRowTailHandoff algorithm request rowIndex
                input))) ≤
        calleeBits)
    (hbranch : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram symmetricEvaluator calleeBits
          (branchFuel
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow algorithm liveScale
              accuracyExponent
              (symmetricFourfoldRowRequest request rowIndex input))))
    (rowIndex : ℕ) (input : BitInput request.q) :
    runNPOracleProgram
        (fourfoldRowModeDispatchProgram symmetricEvaluator
          thresholdEvaluator)
        calleeBits
        (fourfoldRowModeDispatchFuel symmetricEvaluator thresholdEvaluator
          branchFuel
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex
            input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) := by
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_fourfoldRowModeHoistProgram request.q symmetricCircuitFamilyTag
        (Nat.pair request.q
          (Nat.pair
            (symmetricFourfoldRowRequest request rowIndex input).envelopeCode
            (Nat.pair rowIndex (encodeBitInput input))))
        (symmetricFourfoldRowBottomForest algorithm request))
      (hhoistBits rowIndex input)
  · exact run_taggedProgramChoice_zero symmetricEvaluator thresholdEvaluator
      request.q
      (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)
      calleeBits
      (branchFuel
        (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
      _ (hdispatchBits rowIndex input) (hbranch rowIndex input)
      (boolCode_bits_le _ hpositive)

/-- Pointwise symmetric mode dispatch.  Every premise concerns the single row
handoff being evaluated, so bounded callers need not manufacture total
resource ledgers over all natural row indices. -/
theorem run_fourfoldRowModeDispatchProgram_symmetric_pointwise
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (symmetricEvaluator thresholdEvaluator : NPOracleProgram)
    (calleeBits : ℕ) (branchFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (rowIndex : ℕ) (input : BitInput request.q)
    (hhoistBits :
      fourfoldRowModeHoistBits symmetricCircuitFamilyTag
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input) ≤
        calleeBits)
    (hdispatchBits :
      natBitLength
          (Nat.pair request.q
            (Nat.pair symmetricCircuitFamilyTag
              (symmetricFourfoldRowTailHandoff algorithm request rowIndex
                input))) ≤
        calleeBits)
    (hbranch :
      runNPOracleProgram symmetricEvaluator calleeBits
          (branchFuel
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
              (symmetricFourfoldRowRequest request rowIndex input)))) :
    runNPOracleProgram
        (fourfoldRowModeDispatchProgram symmetricEvaluator thresholdEvaluator)
        calleeBits
        (fourfoldRowModeDispatchFuel symmetricEvaluator thresholdEvaluator
          branchFuel
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) := by
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_fourfoldRowModeHoistProgram request.q symmetricCircuitFamilyTag
        (Nat.pair request.q
          (Nat.pair
            (symmetricFourfoldRowRequest request rowIndex input).envelopeCode
            (Nat.pair rowIndex (encodeBitInput input))))
        (symmetricFourfoldRowBottomForest algorithm request))
      hhoistBits
  · exact run_taggedProgramChoice_zero symmetricEvaluator thresholdEvaluator
      request.q
      (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)
      calleeBits
      (branchFuel
        (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
      _ hdispatchBits hbranch (boolCode_bits_le _ hpositive)

/-- Threshold branch of the dispatcher, in the `hevaluator` shape of §5. -/
theorem run_fourfoldRowModeDispatchProgram_threshold
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (symmetricEvaluator thresholdEvaluator : NPOracleProgram)
    (calleeBits : ℕ) (branchFuel : ℕ → ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hhoistBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      fourfoldRowModeHoistBits thresholdCircuitFamilyTag
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex
            input) ≤
        calleeBits)
    (hdispatchBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      natBitLength
          (Nat.pair request.q
            (Nat.pair thresholdCircuitFamilyTag
              (thresholdFourfoldRowTailHandoff algorithm request rowIndex
                input))) ≤
        calleeBits)
    (hbranch : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram thresholdEvaluator calleeBits
          (branchFuel
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex
              input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (boolCode
            (evaluateCanonicalFourfoldRow algorithm liveScale
              accuracyExponent
              (thresholdFourfoldRowRequest request rowIndex input))))
    (rowIndex : ℕ) (input : BitInput request.q) :
    runNPOracleProgram
        (fourfoldRowModeDispatchProgram symmetricEvaluator
          thresholdEvaluator)
        calleeBits
        (fourfoldRowModeDispatchFuel symmetricEvaluator thresholdEvaluator
          branchFuel
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex input))
        (initialNPOracleState request.q
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex
            input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (thresholdFourfoldRowRequest request rowIndex input))) := by
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_fourfoldRowModeHoistProgram request.q thresholdCircuitFamilyTag
        (Nat.pair request.q
          (Nat.pair
            (thresholdFourfoldRowRequest request rowIndex input).envelopeCode
            (Nat.pair rowIndex (encodeBitInput input))))
        (thresholdFourfoldRowBottomForest algorithm request))
      (hhoistBits rowIndex input)
  · exact run_taggedProgramChoice_nonzero symmetricEvaluator
      thresholdEvaluator request.q thresholdCircuitFamilyTag
      (thresholdFourfoldRowTailHandoff algorithm request rowIndex input)
      calleeBits
      (branchFuel
        (thresholdFourfoldRowTailHandoff algorithm request rowIndex input))
      _ (by decide) (hdispatchBits rowIndex input) (hbranch rowIndex input)
      (boolCode_bits_le _ hpositive)

end NearCubicWires.CanonicalFourfoldRowTailProgram
