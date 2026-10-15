import Proof.MachineModel.CanonicalFourfoldListDenominatorProgram
import Proof.MachineModel.CanonicalFourfoldRowTailProgram
import Proof.MachineModel.CanonicalStructuralGF2EvaluationProgram

/-!
# Packaging the two row producers into the published row evaluator

`CanonicalStructuralGF2EvaluationProgram` compiles everything below two
link-time producers: a *table* producer emitting the residual assignment
context of one row, and a *polynomial* producer emitting the encoded
structural row polynomial.  Both read the same row-tail handoff.

`CanonicalFourfoldRowTailProgram` consumes a row evaluator whose fuel is a
function of that handoff alone, and dispatches the two published families on
the mode code already sitting at the head of the handoff.

This module is the seam between them.  It supplies

* total projections of the row-tail ABI, with exact inverses on both
  published handoffs, so no field is recomputed from the envelope;
* the total row polynomial named by one handoff, agreeing with the structural
  row on every decodable row index and with the zero polynomial elsewhere, so
  the producers' contracts are single equations quantified over *all* row
  indices;
* the branch fuel as a closed function of the handoff, obtained by inverting
  the envelope and seed encodings;
* the discharged `hbranch` premises of
  `run_fourfoldRowModeDispatchProgram_symmetric` and `…_threshold`, and
  therefore the `hevaluator` premises of
  `run_sharedFourfoldAggregationProgram_symmetric` and `…_threshold`.

After this module the whole evaluator side of the fourfold aggregation is a
single fixed program over exactly four link-time producers, each with one
exact interpreter premise and no fuel or callback argument.
-/

namespace NearCubicWires.CanonicalFourfoldRowProducerDispatchProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalFourfoldListDenominatorProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalFourfoldRowEvaluationProgram
open NearCubicWires.CanonicalFourfoldRowTailProgram
open NearCubicWires.CanonicalStructuralGF2EvaluationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.FourfoldRangeAggregationComposition
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime
open NearCubicWires.VerifiedLinker

/-! ## §1 Total projections of the row-tail ABI

The handoff is `Nat.pair (Nat.pair modeCode (Nat.pair q (Nat.pair
envelopeCode (Nat.pair rowIndex inputCode)))) bottomForest`.  Each projection
below is a fixed composition of the machine's own pair projections, so the
later fuel formulas read the handoff exactly as the machine does. -/

def rowTailHandoffFields (handoff : ℕ) : ℕ :=
  (Nat.unpair handoff).1

def rowTailHandoffBottomForest (handoff : ℕ) : ℕ :=
  (Nat.unpair handoff).2

def rowTailHandoffModeCode (handoff : ℕ) : ℕ :=
  (Nat.unpair (rowTailHandoffFields handoff)).1

def rowTailHandoffArity (handoff : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (rowTailHandoffFields handoff)).2).1

def rowTailHandoffEnvelopeCode (handoff : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair (rowTailHandoffFields handoff)).2).2).1

def rowTailHandoffRowIndex (handoff : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair
      (Nat.unpair (Nat.unpair (rowTailHandoffFields handoff)).2).2).2).1

def rowTailHandoffInputCode (handoff : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair
      (Nat.unpair (Nat.unpair (rowTailHandoffFields handoff)).2).2).2).2

@[simp] theorem rowTailHandoffBottomForest_handoff
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) :
    rowTailHandoffBottomForest
        (fourfoldRowTailHandoff bottomForest envelopeCode modeCode q rowIndex
          inputCode) =
      bottomForest := by
  simp [rowTailHandoffBottomForest, fourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffModeCode_handoff
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) :
    rowTailHandoffModeCode
        (fourfoldRowTailHandoff bottomForest envelopeCode modeCode q rowIndex
          inputCode) =
      modeCode := by
  simp [rowTailHandoffModeCode, rowTailHandoffFields, fourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffArity_handoff
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) :
    rowTailHandoffArity
        (fourfoldRowTailHandoff bottomForest envelopeCode modeCode q rowIndex
          inputCode) =
      q := by
  simp [rowTailHandoffArity, rowTailHandoffFields, fourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffEnvelopeCode_handoff
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) :
    rowTailHandoffEnvelopeCode
        (fourfoldRowTailHandoff bottomForest envelopeCode modeCode q rowIndex
          inputCode) =
      envelopeCode := by
  simp [rowTailHandoffEnvelopeCode, rowTailHandoffFields,
    fourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffRowIndex_handoff
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) :
    rowTailHandoffRowIndex
        (fourfoldRowTailHandoff bottomForest envelopeCode modeCode q rowIndex
          inputCode) =
      rowIndex := by
  simp [rowTailHandoffRowIndex, rowTailHandoffFields, fourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffInputCode_handoff
    (bottomForest envelopeCode modeCode q rowIndex inputCode : ℕ) :
    rowTailHandoffInputCode
        (fourfoldRowTailHandoff bottomForest envelopeCode modeCode q rowIndex
          inputCode) =
      inputCode := by
  simp [rowTailHandoffInputCode, rowTailHandoffFields, fourfoldRowTailHandoff]

/-! ## §2 The published handoffs read back exactly

These are the inverses used by every fuel formula below: the mode code, the
arity, the envelope, the row index, and the input code of a published row are
recovered from the handoff without touching the retained bottom forest. -/

@[simp] theorem rowTailHandoffModeCode_symmetric
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    rowTailHandoffModeCode
        (symmetricFourfoldRowTailHandoff algorithm request rowIndex input) =
      symmetricCircuitFamilyTag := by
  simp [symmetricFourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffArity_symmetric
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    rowTailHandoffArity
        (symmetricFourfoldRowTailHandoff algorithm request rowIndex input) =
      request.q := by
  simp [symmetricFourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffEnvelopeCode_symmetric
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    rowTailHandoffEnvelopeCode
        (symmetricFourfoldRowTailHandoff algorithm request rowIndex input) =
      (symmetricFourfoldRowRequest request rowIndex input).envelopeCode := by
  simp [symmetricFourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffRowIndex_symmetric
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    rowTailHandoffRowIndex
        (symmetricFourfoldRowTailHandoff algorithm request rowIndex input) =
      rowIndex := by
  simp [symmetricFourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffInputCode_symmetric
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    rowTailHandoffInputCode
        (symmetricFourfoldRowTailHandoff algorithm request rowIndex input) =
      encodeBitInput input := by
  simp [symmetricFourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffModeCode_threshold
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    rowTailHandoffModeCode
        (thresholdFourfoldRowTailHandoff algorithm request rowIndex input) =
      thresholdCircuitFamilyTag := by
  simp [thresholdFourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffArity_threshold
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    rowTailHandoffArity
        (thresholdFourfoldRowTailHandoff algorithm request rowIndex input) =
      request.q := by
  simp [thresholdFourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffEnvelopeCode_threshold
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    rowTailHandoffEnvelopeCode
        (thresholdFourfoldRowTailHandoff algorithm request rowIndex input) =
      (thresholdFourfoldRowRequest request rowIndex input).envelopeCode := by
  simp [thresholdFourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffRowIndex_threshold
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    rowTailHandoffRowIndex
        (thresholdFourfoldRowTailHandoff algorithm request rowIndex input) =
      rowIndex := by
  simp [thresholdFourfoldRowTailHandoff]

@[simp] theorem rowTailHandoffInputCode_threshold
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    rowTailHandoffInputCode
        (thresholdFourfoldRowTailHandoff algorithm request rowIndex input) =
      encodeBitInput input := by
  simp [thresholdFourfoldRowTailHandoff]

/-! ## §3 The total row polynomial of one row index

The dispatcher quantifies over every natural row index, so the producers'
contracts must too.  `symmetricRowPolynomial` is the structural row on every
decodable index and the zero polynomial elsewhere, which is exactly the
convention `evaluateCanonicalSymmetricFourfoldRow` already fixes. -/

/-- The frozen circuit offsets selected by the external column of one row. -/
def symmetricRowConstantOffset
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) (input : BitInput request.q) :
    Fin request.circuits.length → ℕ :=
  fun circuitIndex =>
    occurrenceResidualConstantCount (symmetricFourfoldOccurrences request)
      liveScale input (symmetricCircuitMask request circuitIndex)

noncomputable def symmetricRowPolynomial
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q) :
    StructuralGF2Polynomial :=
  match
      decodeNormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request)
        liveScale
        (symmetricListDenominator request
          (fixedTargetDenominator accuracyExponent request.q))
        rowIndex with
  | some sample =>
      structuralCanonicalSymmetricFourfoldRow request liveScale
        (symmetricListDenominator request
          (fixedTargetDenominator accuracyExponent request.q))
        sample (symmetricRowConstantOffset request liveScale input)
  | none => structuralGF2Zero

theorem symmetricRowPolynomial_of_sample
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale
      (symmetricListDenominator request
        (fixedTargetDenominator accuracyExponent request.q)))
    (hsample :
      decodeNormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request)
          liveScale
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q))
          rowIndex =
        some sample) :
    symmetricRowPolynomial request liveScale accuracyExponent rowIndex input =
      structuralCanonicalSymmetricFourfoldRow request liveScale
        (symmetricListDenominator request
          (fixedTargetDenominator accuracyExponent request.q))
        sample (symmetricRowConstantOffset request liveScale input) := by
  unfold symmetricRowPolynomial
  rw [hsample]

theorem symmetricRowPolynomial_of_none
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (hsample :
      decodeNormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request)
          liveScale
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q))
          rowIndex =
        none) :
    symmetricRowPolynomial request liveScale accuracyExponent rowIndex input =
      structuralGF2Zero := by
  unfold symmetricRowPolynomial
  rw [hsample]

/-- The signed equation offsets contributed by the deterministic residual
constants of one threshold row. -/
noncomputable def thresholdRowResidualOffset
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale : ℕ) (input : BitInput request.q) (prime : ℕ) :
    ThresholdChildSelection algorithm request → ℕ :=
  fun selection =>
    modularResidualOffset (thresholdFourfoldOccurrences request) liveScale
      input (thresholdSelectionEquation algorithm request selection) prime

noncomputable def thresholdRowPolynomial
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q) :
    StructuralGF2Polynomial :=
  match
      decodePrimeListSample
        (cutoff :=
          thresholdPrimeCutoff algorithm request
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q)))
        (thresholdFourfoldOccurrences request) liveScale
        (thresholdListUnionDenominator algorithm request
          (fixedTargetDenominator accuracyExponent request.q))
        rowIndex with
  | some sample =>
      structuralCanonicalThresholdFourfoldRow algorithm request liveScale
        (thresholdPrimeUnionDenominator algorithm request
          (fixedTargetDenominator accuracyExponent request.q))
        (thresholdListUnionDenominator algorithm request
          (fixedTargetDenominator accuracyExponent request.q))
        sample
        (thresholdRowResidualOffset algorithm request liveScale input
          sample.1.val)
  | none => structuralGF2Zero

theorem thresholdRowPolynomial_of_sample
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (sample :
      PrimeIndex
          (thresholdPrimeCutoff algorithm request
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))) ×
        NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences request)
          liveScale
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q)))
    (hsample :
      decodePrimeListSample
          (cutoff :=
            thresholdPrimeCutoff algorithm request
              (thresholdPrimeUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q)))
          (thresholdFourfoldOccurrences request) liveScale
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q))
          rowIndex =
        some sample) :
    thresholdRowPolynomial algorithm request liveScale accuracyExponent
        rowIndex input =
      structuralCanonicalThresholdFourfoldRow algorithm request liveScale
        (thresholdPrimeUnionDenominator algorithm request
          (fixedTargetDenominator accuracyExponent request.q))
        (thresholdListUnionDenominator algorithm request
          (fixedTargetDenominator accuracyExponent request.q))
        sample
        (thresholdRowResidualOffset algorithm request liveScale input
          sample.1.val) := by
  unfold thresholdRowPolynomial
  rw [hsample]

theorem thresholdRowPolynomial_of_none
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (hsample :
      decodePrimeListSample
          (cutoff :=
            thresholdPrimeCutoff algorithm request
              (thresholdPrimeUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q)))
          (thresholdFourfoldOccurrences request) liveScale
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q))
          rowIndex =
        none) :
    thresholdRowPolynomial algorithm request liveScale accuracyExponent
        rowIndex input =
      structuralGF2Zero := by
  unfold thresholdRowPolynomial
  rw [hsample]

/-! ## §4 The fork row evaluator on every row index

The two producers are quantified over all row indices, so the evaluator must
be too.  Below the seed boundary the malformed-index convention of
`CanonicalStructuralGF2EvaluationProgram` §15 supplies the zero polynomial and
the machine's empty parity fold; nothing else changes. -/

private theorem forkEvaluatorBits_le
    {population inputLength handoff tableBits polynomialBits maximumBits : ℕ}
    {active : Fin population → Bool} {polynomial : StructuralGF2Polynomial}
    (hbits :
      structuralForkRowEvaluatorBits inputLength handoff tableBits
          polynomialBits active polynomial ≤
        maximumBits) :
    structuralRowEvaluatorBits inputLength active polynomial ≤ maximumBits := by
  have hunfold :
      structuralForkRowEvaluatorBits inputLength handoff tableBits
          polynomialBits active polynomial =
        max (structuralRowEvaluatorBits inputLength active polynomial)
          (structuralRowDataBits inputLength handoff tableBits polynomialBits
            active polynomial) :=
    rfl
  rw [hunfold] at hbits
  omega

private theorem forkDataBits_le
    {population inputLength handoff tableBits polynomialBits maximumBits : ℕ}
    {active : Fin population → Bool} {polynomial : StructuralGF2Polynomial}
    (hbits :
      structuralForkRowEvaluatorBits inputLength handoff tableBits
          polynomialBits active polynomial ≤
        maximumBits) :
    structuralRowDataBits inputLength handoff tableBits polynomialBits active
        polynomial ≤
      maximumBits := by
  have hunfold :
      structuralForkRowEvaluatorBits inputLength handoff tableBits
          polynomialBits active polynomial =
        max (structuralRowEvaluatorBits inputLength active polynomial)
          (structuralRowDataBits inputLength handoff tableBits polynomialBits
            active polynomial) :=
    rfl
  rw [hunfold] at hbits
  omega

private theorem run_structuralForkRowEvaluatorProgram_symmetric_none
    (tableProgram polynomialProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (hsample :
      decodeNormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request)
          liveScale
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q))
          rowIndex =
        none)
    (maximumBits tableBits polynomialBits tableFuel polynomialFuel : ℕ)
    (hbits :
      structuralForkRowEvaluatorBits request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)
          tableBits polynomialBits
          (symmetricRowResidualAssignment request liveScale input)
          structuralGF2Zero ≤
        maximumBits)
    (htable :
      runNPOracleProgram tableProgram tableBits tableFuel
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (finiteAssignmentContext
            (symmetricRowResidualAssignment request liveScale input)))
    (hpolynomial :
      runNPOracleProgram polynomialProgram polynomialBits polynomialFuel
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some (encodedStructuralGF2 structuralGF2Zero)) :
    runNPOracleProgram
        (structuralForkRowEvaluatorProgram tableProgram polynomialProgram)
        maximumBits
        (structuralForkRowEvaluatorFuel tableProgram polynomialProgram
          tableFuel polynomialFuel
          (symmetricRowResidualAssignment request liveScale input)
          structuralGF2Zero)
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex
            input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) := by
  have hdata :=
    run_structuralRowDataProgram tableProgram polynomialProgram
      (symmetricRowResidualAssignment request liveScale input)
      structuralGF2Zero request.q
      (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)
      tableBits polynomialBits tableFuel polynomialFuel htable hpolynomial
  exact run_structuralRowEvaluatorProgram_symmetricFourfoldRow_none
    (structuralRowDataProgram tableProgram polynomialProgram) algorithm request
    liveScale accuracyExponent rowIndex input hsample maximumBits
    (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)
    (structuralRowDataFuel tableProgram polynomialProgram tableFuel
      polynomialFuel)
    (forkEvaluatorBits_le hbits)
    (run_bits_mono hdata (forkDataBits_le hbits))

/-- **The symmetric fork row evaluator on an arbitrary row index.**  The two
producer premises are single equations in the total row polynomial. -/
theorem run_structuralForkRowEvaluatorProgram_symmetricRow
    (tableProgram polynomialProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (maximumBits tableBits polynomialBits tableFuel polynomialFuel : ℕ)
    (hbits :
      structuralForkRowEvaluatorBits request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)
          tableBits polynomialBits
          (symmetricRowResidualAssignment request liveScale input)
          (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
            input) ≤
        maximumBits)
    (htable :
      runNPOracleProgram tableProgram tableBits tableFuel
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (finiteAssignmentContext
            (symmetricRowResidualAssignment request liveScale input)))
    (hpolynomial :
      runNPOracleProgram polynomialProgram polynomialBits polynomialFuel
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (encodedStructuralGF2
            (symmetricRowPolynomial request liveScale accuracyExponent
              rowIndex input))) :
    runNPOracleProgram
        (structuralForkRowEvaluatorProgram tableProgram polynomialProgram)
        maximumBits
        (structuralForkRowEvaluatorFuel tableProgram polynomialProgram
          tableFuel polynomialFuel
          (symmetricRowResidualAssignment request liveScale input)
          (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
            input))
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex
            input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) := by
  generalize hseed :
    decodeNormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request)
        liveScale
        (symmetricListDenominator request
          (fixedTargetDenominator accuracyExponent request.q))
        rowIndex = decoded
  match decoded, hseed with
  | none, hseed =>
      have hzero :
          symmetricRowPolynomial request liveScale accuracyExponent rowIndex
              input =
            structuralGF2Zero :=
        symmetricRowPolynomial_of_none request liveScale accuracyExponent
          rowIndex input hseed
      rw [hzero] at hbits hpolynomial ⊢
      exact run_structuralForkRowEvaluatorProgram_symmetric_none tableProgram
        polynomialProgram algorithm request liveScale accuracyExponent rowIndex
        input hseed maximumBits tableBits polynomialBits tableFuel
        polynomialFuel hbits htable hpolynomial
  | some sample, hseed =>
      have hrow :
          symmetricRowPolynomial request liveScale accuracyExponent rowIndex
              input =
            structuralCanonicalSymmetricFourfoldRow request liveScale
              (symmetricListDenominator request
                (fixedTargetDenominator accuracyExponent request.q))
              sample (symmetricRowConstantOffset request liveScale input) :=
        symmetricRowPolynomial_of_sample request liveScale accuracyExponent
          rowIndex input sample hseed
      rw [hrow] at hbits hpolynomial ⊢
      exact run_structuralForkRowEvaluatorProgram_symmetric tableProgram
        polynomialProgram algorithm request liveScale accuracyExponent rowIndex
        input sample hseed
        (symmetricRowConstantOffset request liveScale input) (fun _ => rfl)
        maximumBits
        (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)
        tableBits polynomialBits tableFuel polynomialFuel hbits htable
        hpolynomial

private theorem run_structuralForkRowEvaluatorProgram_threshold_none
    (tableProgram polynomialProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (hsample :
      decodePrimeListSample
          (cutoff :=
            thresholdPrimeCutoff algorithm request
              (thresholdPrimeUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q)))
          (thresholdFourfoldOccurrences request) liveScale
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q))
          rowIndex =
        none)
    (maximumBits tableBits polynomialBits tableFuel polynomialFuel : ℕ)
    (hbits :
      structuralForkRowEvaluatorBits request.q
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex input)
          tableBits polynomialBits
          (thresholdRowResidualAssignment request liveScale input)
          structuralGF2Zero ≤
        maximumBits)
    (htable :
      runNPOracleProgram tableProgram tableBits tableFuel
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (finiteAssignmentContext
            (thresholdRowResidualAssignment request liveScale input)))
    (hpolynomial :
      runNPOracleProgram polynomialProgram polynomialBits polynomialFuel
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some (encodedStructuralGF2 structuralGF2Zero)) :
    runNPOracleProgram
        (structuralForkRowEvaluatorProgram tableProgram polynomialProgram)
        maximumBits
        (structuralForkRowEvaluatorFuel tableProgram polynomialProgram
          tableFuel polynomialFuel
          (thresholdRowResidualAssignment request liveScale input)
          structuralGF2Zero)
        (initialNPOracleState request.q
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex
            input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (thresholdFourfoldRowRequest request rowIndex input))) := by
  have hdata :=
    run_structuralRowDataProgram tableProgram polynomialProgram
      (thresholdRowResidualAssignment request liveScale input)
      structuralGF2Zero request.q
      (thresholdFourfoldRowTailHandoff algorithm request rowIndex input)
      tableBits polynomialBits tableFuel polynomialFuel htable hpolynomial
  exact run_structuralRowEvaluatorProgram_thresholdFourfoldRow_none
    (structuralRowDataProgram tableProgram polynomialProgram) algorithm request
    liveScale accuracyExponent rowIndex input hsample maximumBits
    (thresholdFourfoldRowTailHandoff algorithm request rowIndex input)
    (structuralRowDataFuel tableProgram polynomialProgram tableFuel
      polynomialFuel)
    (forkEvaluatorBits_le hbits)
    (run_bits_mono hdata (forkDataBits_le hbits))

/-- **The threshold fork row evaluator on an arbitrary row index.** -/
theorem run_structuralForkRowEvaluatorProgram_thresholdRow
    (tableProgram polynomialProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (maximumBits tableBits polynomialBits tableFuel polynomialFuel : ℕ)
    (hbits :
      structuralForkRowEvaluatorBits request.q
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex input)
          tableBits polynomialBits
          (thresholdRowResidualAssignment request liveScale input)
          (thresholdRowPolynomial algorithm request liveScale accuracyExponent
            rowIndex input) ≤
        maximumBits)
    (htable :
      runNPOracleProgram tableProgram tableBits tableFuel
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (finiteAssignmentContext
            (thresholdRowResidualAssignment request liveScale input)))
    (hpolynomial :
      runNPOracleProgram polynomialProgram polynomialBits polynomialFuel
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (encodedStructuralGF2
            (thresholdRowPolynomial algorithm request liveScale
              accuracyExponent rowIndex input))) :
    runNPOracleProgram
        (structuralForkRowEvaluatorProgram tableProgram polynomialProgram)
        maximumBits
        (structuralForkRowEvaluatorFuel tableProgram polynomialProgram
          tableFuel polynomialFuel
          (thresholdRowResidualAssignment request liveScale input)
          (thresholdRowPolynomial algorithm request liveScale accuracyExponent
            rowIndex input))
        (initialNPOracleState request.q
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex
            input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (thresholdFourfoldRowRequest request rowIndex input))) := by
  generalize hseed :
    decodePrimeListSample
        (cutoff :=
          thresholdPrimeCutoff algorithm request
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q)))
        (thresholdFourfoldOccurrences request) liveScale
        (thresholdListUnionDenominator algorithm request
          (fixedTargetDenominator accuracyExponent request.q))
        rowIndex = decoded
  match decoded, hseed with
  | none, hseed =>
      have hzero :
          thresholdRowPolynomial algorithm request liveScale accuracyExponent
              rowIndex input =
            structuralGF2Zero :=
        thresholdRowPolynomial_of_none algorithm request liveScale
          accuracyExponent rowIndex input hseed
      rw [hzero] at hbits hpolynomial ⊢
      exact run_structuralForkRowEvaluatorProgram_threshold_none tableProgram
        polynomialProgram algorithm request liveScale accuracyExponent rowIndex
        input hseed maximumBits tableBits polynomialBits tableFuel
        polynomialFuel hbits htable hpolynomial
  | some sample, hseed =>
      have hrow :
          thresholdRowPolynomial algorithm request liveScale accuracyExponent
              rowIndex input =
            structuralCanonicalThresholdFourfoldRow algorithm request liveScale
              (thresholdPrimeUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q))
              (thresholdListUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q))
              sample
              (thresholdRowResidualOffset algorithm request liveScale input
                sample.1.val) :=
        thresholdRowPolynomial_of_sample algorithm request liveScale
          accuracyExponent rowIndex input sample hseed
      rw [hrow] at hbits hpolynomial ⊢
      exact run_structuralForkRowEvaluatorProgram_threshold tableProgram
        polynomialProgram algorithm request liveScale accuracyExponent rowIndex
        input sample hseed
        (thresholdRowResidualOffset algorithm request liveScale input
          sample.1.val)
        (fun _ => rfl) maximumBits
        (thresholdFourfoldRowTailHandoff algorithm request rowIndex input)
        tableBits polynomialBits tableFuel polynomialFuel hbits htable
        hpolynomial

/-! ## §5 The branch fuel as a closed function of the handoff

The dispatcher charges its branch a fuel that depends on the row handoff and
on nothing else.  Both encodings crossing the handoff are invertible — the
typed envelope by `decodeFourfoldEnvelope_output`, the row seed by
`decodeNormalizedOccurrenceListSeed_encode` and `decodePrimeListSample_encode`
inside the total row polynomial — so the previous module's fuel is re-expressed
through those inverses with no extra hypothesis. -/

@[simp] theorem decodeSymmetricFourfoldEnvelope_rowRequest
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    decodeSymmetricFourfoldEnvelope request.q
        (symmetricFourfoldRowRequest request rowIndex input).envelopeCode =
      some request := by
  simp [decodeSymmetricFourfoldEnvelope, symmetricFourfoldRowRequest]

@[simp] theorem decodeThresholdFourfoldEnvelope_rowRequest
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    decodeThresholdFourfoldEnvelope request.q
        (thresholdFourfoldRowRequest request rowIndex input).envelopeCode =
      some request := by
  simp [decodeThresholdFourfoldEnvelope, thresholdFourfoldRowRequest]

noncomputable def symmetricRowBranchFuel
    (tableProgram polynomialProgram : NPOracleProgram)
    (tableFuel polynomialFuel : ℕ → ℕ)
    (liveScale accuracyExponent handoff : ℕ) : ℕ :=
  match
      decodeSymmetricFourfoldEnvelope (rowTailHandoffArity handoff)
        (rowTailHandoffEnvelopeCode handoff) with
  | some request =>
      structuralForkRowEvaluatorFuel tableProgram polynomialProgram
        (tableFuel handoff) (polynomialFuel handoff)
        (symmetricRowResidualAssignment request liveScale
          (rowBitInputOfCode request.q (rowTailHandoffInputCode handoff)))
        (symmetricRowPolynomial request liveScale accuracyExponent
          (rowTailHandoffRowIndex handoff)
          (rowBitInputOfCode request.q (rowTailHandoffInputCode handoff)))
  | none => 0

noncomputable def thresholdRowBranchFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (tableProgram polynomialProgram : NPOracleProgram)
    (tableFuel polynomialFuel : ℕ → ℕ)
    (liveScale accuracyExponent handoff : ℕ) : ℕ :=
  match
      decodeThresholdFourfoldEnvelope (rowTailHandoffArity handoff)
        (rowTailHandoffEnvelopeCode handoff) with
  | some request =>
      structuralForkRowEvaluatorFuel tableProgram polynomialProgram
        (tableFuel handoff) (polynomialFuel handoff)
        (thresholdRowResidualAssignment request liveScale
          (rowBitInputOfCode request.q (rowTailHandoffInputCode handoff)))
        (thresholdRowPolynomial algorithm request liveScale accuracyExponent
          (rowTailHandoffRowIndex handoff)
          (rowBitInputOfCode request.q (rowTailHandoffInputCode handoff)))
  | none => 0

theorem symmetricRowBranchFuel_handoff
    (tableProgram polynomialProgram : NPOracleProgram)
    (tableFuel polynomialFuel : ℕ → ℕ)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q) :
    symmetricRowBranchFuel tableProgram polynomialProgram tableFuel
        polynomialFuel liveScale accuracyExponent
        (symmetricFourfoldRowTailHandoff algorithm request rowIndex input) =
      structuralForkRowEvaluatorFuel tableProgram polynomialProgram
        (tableFuel
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
        (polynomialFuel
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
        (symmetricRowResidualAssignment request liveScale input)
        (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
          input) := by
  unfold symmetricRowBranchFuel
  rw [rowTailHandoffArity_symmetric, rowTailHandoffEnvelopeCode_symmetric,
    decodeSymmetricFourfoldEnvelope_rowRequest]
  simp only [rowTailHandoffRowIndex_symmetric, rowTailHandoffInputCode_symmetric,
    rowBitInputOfCode_encode]

theorem thresholdRowBranchFuel_handoff
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (tableProgram polynomialProgram : NPOracleProgram)
    (tableFuel polynomialFuel : ℕ → ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q) :
    thresholdRowBranchFuel algorithm tableProgram polynomialProgram tableFuel
        polynomialFuel liveScale accuracyExponent
        (thresholdFourfoldRowTailHandoff algorithm request rowIndex input) =
      structuralForkRowEvaluatorFuel tableProgram polynomialProgram
        (tableFuel
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex input))
        (polynomialFuel
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex input))
        (thresholdRowResidualAssignment request liveScale input)
        (thresholdRowPolynomial algorithm request liveScale accuracyExponent
          rowIndex input) := by
  unfold thresholdRowBranchFuel
  rw [rowTailHandoffArity_threshold, rowTailHandoffEnvelopeCode_threshold,
    decodeThresholdFourfoldEnvelope_rowRequest]
  simp only [rowTailHandoffRowIndex_threshold, rowTailHandoffInputCode_threshold,
    rowBitInputOfCode_encode]

/-- **The two-family branch fuel.**  The published family is read from the
handoff's own mode code, exactly as the dispatcher's hoist reads it. -/
noncomputable def structuralFourfoldRowBranchFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (symmetricTableProgram symmetricPolynomialProgram
      thresholdTableProgram thresholdPolynomialProgram : NPOracleProgram)
    (symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
      thresholdPolynomialFuel : ℕ → ℕ)
    (liveScale accuracyExponent handoff : ℕ) : ℕ :=
  if rowTailHandoffModeCode handoff = symmetricCircuitFamilyTag then
    symmetricRowBranchFuel symmetricTableProgram symmetricPolynomialProgram
      symmetricTableFuel symmetricPolynomialFuel liveScale accuracyExponent
      handoff
  else
    thresholdRowBranchFuel algorithm thresholdTableProgram
      thresholdPolynomialProgram thresholdTableFuel thresholdPolynomialFuel
      liveScale accuracyExponent handoff

theorem structuralFourfoldRowBranchFuel_symmetric
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (symmetricTableProgram symmetricPolynomialProgram
      thresholdTableProgram thresholdPolynomialProgram : NPOracleProgram)
    (symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
      thresholdPolynomialFuel : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q) :
    structuralFourfoldRowBranchFuel algorithm symmetricTableProgram
        symmetricPolynomialProgram thresholdTableProgram
        thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
        thresholdTableFuel thresholdPolynomialFuel liveScale accuracyExponent
        (symmetricFourfoldRowTailHandoff algorithm request rowIndex input) =
      structuralForkRowEvaluatorFuel symmetricTableProgram
        symmetricPolynomialProgram
        (symmetricTableFuel
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
        (symmetricPolynomialFuel
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
        (symmetricRowResidualAssignment request liveScale input)
        (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
          input) := by
  unfold structuralFourfoldRowBranchFuel
  rw [rowTailHandoffModeCode_symmetric, if_pos rfl]
  exact symmetricRowBranchFuel_handoff symmetricTableProgram
    symmetricPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
    algorithm request liveScale accuracyExponent rowIndex input

theorem structuralFourfoldRowBranchFuel_threshold
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (symmetricTableProgram symmetricPolynomialProgram
      thresholdTableProgram thresholdPolynomialProgram : NPOracleProgram)
    (symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
      thresholdPolynomialFuel : ℕ → ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q) :
    structuralFourfoldRowBranchFuel algorithm symmetricTableProgram
        symmetricPolynomialProgram thresholdTableProgram
        thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
        thresholdTableFuel thresholdPolynomialFuel liveScale accuracyExponent
        (thresholdFourfoldRowTailHandoff algorithm request rowIndex input) =
      structuralForkRowEvaluatorFuel thresholdTableProgram
        thresholdPolynomialProgram
        (thresholdTableFuel
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex input))
        (thresholdPolynomialFuel
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex input))
        (thresholdRowResidualAssignment request liveScale input)
        (thresholdRowPolynomial algorithm request liveScale accuracyExponent
          rowIndex input) := by
  unfold structuralFourfoldRowBranchFuel
  rw [rowTailHandoffModeCode_threshold,
    if_neg (by decide : ¬ thresholdCircuitFamilyTag = symmetricCircuitFamilyTag)]
  exact thresholdRowBranchFuel_handoff algorithm thresholdTableProgram
    thresholdPolynomialProgram thresholdTableFuel thresholdPolynomialFuel
    request liveScale accuracyExponent rowIndex input

/-- **The published row evaluator over four producers.**  One fixed program;
the family, the arity, the envelope, the row index, and the input code are all
read from the handoff. -/
def structuralFourfoldRowEvaluatorProgram
    (symmetricTableProgram symmetricPolynomialProgram
      thresholdTableProgram thresholdPolynomialProgram : NPOracleProgram) :
    NPOracleProgram :=
  fourfoldRowModeDispatchProgram
    (structuralForkRowEvaluatorProgram symmetricTableProgram
      symmetricPolynomialProgram)
    (structuralForkRowEvaluatorProgram thresholdTableProgram
      thresholdPolynomialProgram)

theorem structuralFourfoldRowEvaluatorProgram_oracleFree
    (symmetricTableProgram symmetricPolynomialProgram
      thresholdTableProgram thresholdPolynomialProgram : NPOracleProgram)
    (hsymmetricTable : OracleFree symmetricTableProgram)
    (hsymmetricPolynomial : OracleFree symmetricPolynomialProgram)
    (hthresholdTable : OracleFree thresholdTableProgram)
    (hthresholdPolynomial : OracleFree thresholdPolynomialProgram) :
    OracleFree
      (structuralFourfoldRowEvaluatorProgram symmetricTableProgram
        symmetricPolynomialProgram thresholdTableProgram
        thresholdPolynomialProgram) :=
  fourfoldRowModeDispatchProgram_oracleFree
    (structuralForkRowEvaluatorProgram symmetricTableProgram
      symmetricPolynomialProgram)
    (structuralForkRowEvaluatorProgram thresholdTableProgram
      thresholdPolynomialProgram)
    (structuralForkRowEvaluatorProgram_oracleFree symmetricTableProgram
      symmetricPolynomialProgram hsymmetricTable hsymmetricPolynomial)
    (structuralForkRowEvaluatorProgram_oracleFree thresholdTableProgram
      thresholdPolynomialProgram hthresholdTable hthresholdPolynomial)

noncomputable def structuralFourfoldRowEvaluatorFuel
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (symmetricTableProgram symmetricPolynomialProgram
      thresholdTableProgram thresholdPolynomialProgram : NPOracleProgram)
    (symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
      thresholdPolynomialFuel : ℕ → ℕ)
    (liveScale accuracyExponent : ℕ) : ℕ → ℕ :=
  fourfoldRowModeDispatchFuel
    (structuralForkRowEvaluatorProgram symmetricTableProgram
      symmetricPolynomialProgram)
    (structuralForkRowEvaluatorProgram thresholdTableProgram
      thresholdPolynomialProgram)
    (structuralFourfoldRowBranchFuel algorithm symmetricTableProgram
      symmetricPolynomialProgram thresholdTableProgram
      thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
      thresholdTableFuel thresholdPolynomialFuel liveScale accuracyExponent)

/-! ## §6 The discharged `hevaluator` premises

These are verbatim the `hevaluator` premises of
`run_sharedFourfoldAggregationProgram_symmetric` and `…_threshold`, with the
row evaluator and its fuel now fixed: exactly four link-time producers remain,
each with one exact interpreter premise and no fuel or callback argument. -/

theorem run_structuralFourfoldRowEvaluatorProgram_symmetric
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (symmetricTableProgram symmetricPolynomialProgram
      thresholdTableProgram thresholdPolynomialProgram : NPOracleProgram)
    (symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
      thresholdPolynomialFuel : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent calleeBits tableBits polynomialBits : ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hhoistBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      fourfoldRowModeHoistBits symmetricCircuitFamilyTag
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input) ≤
        calleeBits)
    (hdispatchBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      natBitLength
          (Nat.pair request.q
            (Nat.pair symmetricCircuitFamilyTag
              (symmetricFourfoldRowTailHandoff algorithm request rowIndex
                input))) ≤
        calleeBits)
    (hforkBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      structuralForkRowEvaluatorBits request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)
          tableBits polynomialBits
          (symmetricRowResidualAssignment request liveScale input)
          (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
            input) ≤
        calleeBits)
    (htable : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram symmetricTableProgram tableBits
          (symmetricTableFuel
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (finiteAssignmentContext
            (symmetricRowResidualAssignment request liveScale input)))
    (hpolynomial : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram symmetricPolynomialProgram polynomialBits
          (symmetricPolynomialFuel
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (encodedStructuralGF2
            (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
              input)))
    (rowIndex : ℕ) (input : BitInput request.q) :
    runNPOracleProgram
        (structuralFourfoldRowEvaluatorProgram symmetricTableProgram
          symmetricPolynomialProgram thresholdTableProgram
          thresholdPolynomialProgram)
        calleeBits
        (structuralFourfoldRowEvaluatorFuel algorithm symmetricTableProgram
          symmetricPolynomialProgram thresholdTableProgram
          thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
          thresholdTableFuel thresholdPolynomialFuel liveScale accuracyExponent
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex
            input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) := by
  refine run_fourfoldRowModeDispatchProgram_symmetric algorithm liveScale
    accuracyExponent request
    (structuralForkRowEvaluatorProgram symmetricTableProgram
      symmetricPolynomialProgram)
    (structuralForkRowEvaluatorProgram thresholdTableProgram
      thresholdPolynomialProgram)
    calleeBits
    (structuralFourfoldRowBranchFuel algorithm symmetricTableProgram
      symmetricPolynomialProgram thresholdTableProgram
      thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
      thresholdTableFuel thresholdPolynomialFuel liveScale accuracyExponent)
    hpositive hlength hhoistBits hdispatchBits ?_ rowIndex input
  intro branchRowIndex branchInput
  rw [structuralFourfoldRowBranchFuel_symmetric algorithm symmetricTableProgram
    symmetricPolynomialProgram thresholdTableProgram thresholdPolynomialProgram
    symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
    thresholdPolynomialFuel request liveScale accuracyExponent branchRowIndex
    branchInput]
  exact run_structuralForkRowEvaluatorProgram_symmetricRow symmetricTableProgram
    symmetricPolynomialProgram algorithm request liveScale accuracyExponent
    branchRowIndex branchInput calleeBits tableBits polynomialBits
    (symmetricTableFuel
      (symmetricFourfoldRowTailHandoff algorithm request branchRowIndex
        branchInput))
    (symmetricPolynomialFuel
      (symmetricFourfoldRowTailHandoff algorithm request branchRowIndex
        branchInput))
    (hforkBits branchRowIndex branchInput) (htable branchRowIndex branchInput)
    (hpolynomial branchRowIndex branchInput)

/-- Pointwise symmetric structural evaluator.  This is the finite-row repair
socket consumed by the bounded aggregation path. -/
theorem run_structuralFourfoldRowEvaluatorProgram_symmetric_pointwise
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (symmetricTableProgram symmetricPolynomialProgram
      thresholdTableProgram thresholdPolynomialProgram : NPOracleProgram)
    (symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
      thresholdPolynomialFuel : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent calleeBits tableBits polynomialBits : ℕ)
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
    (hforkBits :
      structuralForkRowEvaluatorBits request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)
          tableBits polynomialBits
          (symmetricRowResidualAssignment request liveScale input)
          (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
            input) ≤
        calleeBits)
    (htable :
      runNPOracleProgram symmetricTableProgram tableBits
          (symmetricTableFuel
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
        some
          (finiteAssignmentContext
            (symmetricRowResidualAssignment request liveScale input)))
    (hpolynomial :
      runNPOracleProgram symmetricPolynomialProgram polynomialBits
          (symmetricPolynomialFuel
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
        some
          (encodedStructuralGF2
            (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
              input))) :
    runNPOracleProgram
        (structuralFourfoldRowEvaluatorProgram symmetricTableProgram
          symmetricPolynomialProgram thresholdTableProgram
          thresholdPolynomialProgram)
        calleeBits
        (structuralFourfoldRowEvaluatorFuel algorithm symmetricTableProgram
          symmetricPolynomialProgram thresholdTableProgram
          thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
          thresholdTableFuel thresholdPolynomialFuel liveScale accuracyExponent
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) := by
  apply run_fourfoldRowModeDispatchProgram_symmetric_pointwise algorithm
    liveScale accuracyExponent request
    (structuralForkRowEvaluatorProgram symmetricTableProgram
      symmetricPolynomialProgram)
    (structuralForkRowEvaluatorProgram thresholdTableProgram
      thresholdPolynomialProgram)
    calleeBits
    (structuralFourfoldRowBranchFuel algorithm symmetricTableProgram
      symmetricPolynomialProgram thresholdTableProgram
      thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
      thresholdTableFuel thresholdPolynomialFuel liveScale accuracyExponent)
    hpositive hlength rowIndex input hhoistBits hdispatchBits
  rw [structuralFourfoldRowBranchFuel_symmetric algorithm symmetricTableProgram
    symmetricPolynomialProgram thresholdTableProgram thresholdPolynomialProgram
    symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
    thresholdPolynomialFuel request liveScale accuracyExponent rowIndex input]
  exact run_structuralForkRowEvaluatorProgram_symmetricRow symmetricTableProgram
    symmetricPolynomialProgram algorithm request liveScale accuracyExponent
    rowIndex input calleeBits tableBits polynomialBits
    (symmetricTableFuel
      (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
    (symmetricPolynomialFuel
      (symmetricFourfoldRowTailHandoff algorithm request rowIndex input))
    hforkBits htable hpolynomial

theorem run_structuralFourfoldRowEvaluatorProgram_threshold
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (symmetricTableProgram symmetricPolynomialProgram
      thresholdTableProgram thresholdPolynomialProgram : NPOracleProgram)
    (symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
      thresholdPolynomialFuel : ℕ → ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale accuracyExponent calleeBits tableBits polynomialBits : ℕ)
    (hpositive : 1 ≤ calleeBits)
    (hlength : natBitLength request.q ≤ calleeBits)
    (hhoistBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      fourfoldRowModeHoistBits thresholdCircuitFamilyTag
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex input) ≤
        calleeBits)
    (hdispatchBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      natBitLength
          (Nat.pair request.q
            (Nat.pair thresholdCircuitFamilyTag
              (thresholdFourfoldRowTailHandoff algorithm request rowIndex
                input))) ≤
        calleeBits)
    (hforkBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      structuralForkRowEvaluatorBits request.q
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex input)
          tableBits polynomialBits
          (thresholdRowResidualAssignment request liveScale input)
          (thresholdRowPolynomial algorithm request liveScale accuracyExponent
            rowIndex input) ≤
        calleeBits)
    (htable : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram thresholdTableProgram tableBits
          (thresholdTableFuel
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (finiteAssignmentContext
            (thresholdRowResidualAssignment request liveScale input)))
    (hpolynomial : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram thresholdPolynomialProgram polynomialBits
          (thresholdPolynomialFuel
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (encodedStructuralGF2
            (thresholdRowPolynomial algorithm request liveScale
              accuracyExponent rowIndex input)))
    (rowIndex : ℕ) (input : BitInput request.q) :
    runNPOracleProgram
        (structuralFourfoldRowEvaluatorProgram symmetricTableProgram
          symmetricPolynomialProgram thresholdTableProgram
          thresholdPolynomialProgram)
        calleeBits
        (structuralFourfoldRowEvaluatorFuel algorithm symmetricTableProgram
          symmetricPolynomialProgram thresholdTableProgram
          thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
          thresholdTableFuel thresholdPolynomialFuel liveScale accuracyExponent
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex input))
        (initialNPOracleState request.q
          (thresholdFourfoldRowTailHandoff algorithm request rowIndex
            input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (thresholdFourfoldRowRequest request rowIndex input))) := by
  refine run_fourfoldRowModeDispatchProgram_threshold algorithm liveScale
    accuracyExponent request
    (structuralForkRowEvaluatorProgram symmetricTableProgram
      symmetricPolynomialProgram)
    (structuralForkRowEvaluatorProgram thresholdTableProgram
      thresholdPolynomialProgram)
    calleeBits
    (structuralFourfoldRowBranchFuel algorithm symmetricTableProgram
      symmetricPolynomialProgram thresholdTableProgram
      thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
      thresholdTableFuel thresholdPolynomialFuel liveScale accuracyExponent)
    hpositive hlength hhoistBits hdispatchBits ?_ rowIndex input
  intro branchRowIndex branchInput
  rw [structuralFourfoldRowBranchFuel_threshold algorithm symmetricTableProgram
    symmetricPolynomialProgram thresholdTableProgram thresholdPolynomialProgram
    symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
    thresholdPolynomialFuel request liveScale accuracyExponent branchRowIndex
    branchInput]
  exact run_structuralForkRowEvaluatorProgram_thresholdRow thresholdTableProgram
    thresholdPolynomialProgram algorithm request liveScale accuracyExponent
    branchRowIndex branchInput calleeBits tableBits polynomialBits
    (thresholdTableFuel
      (thresholdFourfoldRowTailHandoff algorithm request branchRowIndex
        branchInput))
    (thresholdPolynomialFuel
      (thresholdFourfoldRowTailHandoff algorithm request branchRowIndex
        branchInput))
    (hforkBits branchRowIndex branchInput) (htable branchRowIndex branchInput)
    (hpolynomial branchRowIndex branchInput)

/-! ## §7 The evaluator side of the published aggregation

Both published aggregation runs now hold with a fixed program and a fixed
fuel.  Only the counting callee `countProgram` and the four row producers
remain as link-time parameters; each has one exact interpreter premise. -/

theorem run_sharedFourfoldAggregationProgram_structuralSymmetric
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (countProgram symmetricTableProgram symmetricPolynomialProgram
      thresholdTableProgram thresholdPolynomialProgram : NPOracleProgram)
    (symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
      thresholdPolynomialFuel : ℕ → ℕ)
    (maximumBits calleeBits countBits countFuel tableBits polynomialBits : ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hentryBits :
      symmetricFourfoldEntryBits contracts liveScale accuracyExponent request
          countBits ≤
        maximumBits)
    (hcomponentBits :
      symmetricFourfoldRangeComponentBits contracts liveScale accuracyExponent
          request calleeBits ≤
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
    (hhoistBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      fourfoldRowModeHoistBits symmetricCircuitFamilyTag
          (symmetricFourfoldRowTailHandoff
            (selectedExactDecompositionAlgorithm contracts) request rowIndex
            input) ≤
        calleeBits)
    (hdispatchBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      natBitLength
          (Nat.pair request.q
            (Nat.pair symmetricCircuitFamilyTag
              (symmetricFourfoldRowTailHandoff
                (selectedExactDecompositionAlgorithm contracts) request
                rowIndex input))) ≤
        calleeBits)
    (hforkBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      structuralForkRowEvaluatorBits request.q
          (symmetricFourfoldRowTailHandoff
            (selectedExactDecompositionAlgorithm contracts) request rowIndex
            input)
          tableBits polynomialBits
          (symmetricRowResidualAssignment request liveScale input)
          (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
            input) ≤
        calleeBits)
    (htable : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram symmetricTableProgram tableBits
          (symmetricTableFuel
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request rowIndex
              input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request rowIndex
              input)) =
        some
          (finiteAssignmentContext
            (symmetricRowResidualAssignment request liveScale input)))
    (hpolynomial : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram symmetricPolynomialProgram polynomialBits
          (symmetricPolynomialFuel
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request rowIndex
              input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request rowIndex
              input)) =
        some
          (encodedStructuralGF2
            (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
              input)))
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
          (structuralFourfoldRowEvaluatorProgram symmetricTableProgram
            symmetricPolynomialProgram thresholdTableProgram
            thresholdPolynomialProgram))
        maximumBits
        (symmetricSharedFourfoldAggregationFuel contracts liveScale
          accuracyExponent request countProgram
          (structuralFourfoldRowEvaluatorProgram symmetricTableProgram
            symmetricPolynomialProgram thresholdTableProgram
            thresholdPolynomialProgram)
          countFuel
          (structuralFourfoldRowEvaluatorFuel
            (selectedExactDecompositionAlgorithm contracts)
            symmetricTableProgram symmetricPolynomialProgram
            thresholdTableProgram thresholdPolynomialProgram
            symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
            thresholdPolynomialFuel liveScale accuracyExponent))
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request)) =
      some
        (symmetricRatioComponentCode
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :=
  run_sharedFourfoldAggregationProgram_symmetric contracts liveScale
    accuracyExponent request countProgram
    (structuralFourfoldRowEvaluatorProgram symmetricTableProgram
      symmetricPolynomialProgram thresholdTableProgram
      thresholdPolynomialProgram)
    maximumBits calleeBits countBits countFuel
    (structuralFourfoldRowEvaluatorFuel
      (selectedExactDecompositionAlgorithm contracts) symmetricTableProgram
      symmetricPolynomialProgram thresholdTableProgram
      thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
      thresholdTableFuel thresholdPolynomialFuel liveScale accuracyExponent)
    hpositive hlength hentryBits hcomponentBits hcalleePositive hcalleeLength
    hbottomBits hrepackBits
    (run_structuralFourfoldRowEvaluatorProgram_symmetric
      (selectedExactDecompositionAlgorithm contracts) symmetricTableProgram
      symmetricPolynomialProgram thresholdTableProgram
      thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
      thresholdTableFuel thresholdPolynomialFuel request liveScale
      accuracyExponent calleeBits tableBits polynomialBits hcalleePositive
      hcalleeLength hhoistBits hdispatchBits hforkBits htable hpolynomial)
    hcount

theorem run_sharedFourfoldAggregationProgram_structuralThreshold
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (countProgram symmetricTableProgram symmetricPolynomialProgram
      thresholdTableProgram thresholdPolynomialProgram : NPOracleProgram)
    (symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
      thresholdPolynomialFuel : ℕ → ℕ)
    (maximumBits calleeBits countBits countFuel tableBits polynomialBits : ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hentryBits :
      thresholdFourfoldEntryBits contracts liveScale accuracyExponent request
          countBits ≤
        maximumBits)
    (hcomponentBits :
      thresholdFourfoldRangeComponentBits contracts liveScale accuracyExponent
          request calleeBits ≤
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
    (hhoistBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      fourfoldRowModeHoistBits thresholdCircuitFamilyTag
          (thresholdFourfoldRowTailHandoff
            (selectedExactDecompositionAlgorithm contracts) request rowIndex
            input) ≤
        calleeBits)
    (hdispatchBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      natBitLength
          (Nat.pair request.q
            (Nat.pair thresholdCircuitFamilyTag
              (thresholdFourfoldRowTailHandoff
                (selectedExactDecompositionAlgorithm contracts) request
                rowIndex input))) ≤
        calleeBits)
    (hforkBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      structuralForkRowEvaluatorBits request.q
          (thresholdFourfoldRowTailHandoff
            (selectedExactDecompositionAlgorithm contracts) request rowIndex
            input)
          tableBits polynomialBits
          (thresholdRowResidualAssignment request liveScale input)
          (thresholdRowPolynomial
            (selectedExactDecompositionAlgorithm contracts) request liveScale
            accuracyExponent rowIndex input) ≤
        calleeBits)
    (htable : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram thresholdTableProgram tableBits
          (thresholdTableFuel
            (thresholdFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request rowIndex
              input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request rowIndex
              input)) =
        some
          (finiteAssignmentContext
            (thresholdRowResidualAssignment request liveScale input)))
    (hpolynomial : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram thresholdPolynomialProgram polynomialBits
          (thresholdPolynomialFuel
            (thresholdFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request rowIndex
              input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request rowIndex
              input)) =
        some
          (encodedStructuralGF2
            (thresholdRowPolynomial
              (selectedExactDecompositionAlgorithm contracts) request liveScale
              accuracyExponent rowIndex input)))
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
          (structuralFourfoldRowEvaluatorProgram symmetricTableProgram
            symmetricPolynomialProgram thresholdTableProgram
            thresholdPolynomialProgram))
        maximumBits
        (thresholdSharedFourfoldAggregationFuel contracts liveScale
          accuracyExponent request countProgram
          (structuralFourfoldRowEvaluatorProgram symmetricTableProgram
            symmetricPolynomialProgram thresholdTableProgram
            thresholdPolynomialProgram)
          countFuel
          (structuralFourfoldRowEvaluatorFuel
            (selectedExactDecompositionAlgorithm contracts)
            symmetricTableProgram symmetricPolynomialProgram
            thresholdTableProgram thresholdPolynomialProgram
            symmetricTableFuel symmetricPolynomialFuel thresholdTableFuel
            thresholdPolynomialFuel liveScale accuracyExponent))
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
            encodeNormalizedThresholdThresholdCircuit request)) =
      some
        (thresholdRatioComponentCode
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request) :=
  run_sharedFourfoldAggregationProgram_threshold contracts liveScale
    accuracyExponent request countProgram
    (structuralFourfoldRowEvaluatorProgram symmetricTableProgram
      symmetricPolynomialProgram thresholdTableProgram
      thresholdPolynomialProgram)
    maximumBits calleeBits countBits countFuel
    (structuralFourfoldRowEvaluatorFuel
      (selectedExactDecompositionAlgorithm contracts) symmetricTableProgram
      symmetricPolynomialProgram thresholdTableProgram
      thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
      thresholdTableFuel thresholdPolynomialFuel liveScale accuracyExponent)
    hpositive hlength hentryBits hcomponentBits hcalleePositive hcalleeLength
    hbottomBits hrepackBits
    (run_structuralFourfoldRowEvaluatorProgram_threshold
      (selectedExactDecompositionAlgorithm contracts) symmetricTableProgram
      symmetricPolynomialProgram thresholdTableProgram
      thresholdPolynomialProgram symmetricTableFuel symmetricPolynomialFuel
      thresholdTableFuel thresholdPolynomialFuel request liveScale
      accuracyExponent calleeBits tableBits polynomialBits hcalleePositive
      hcalleeLength hhoistBits hdispatchBits hforkBits htable hpolynomial)
    hcount

/-! ## §8 The producers' shared front end

Both producers read the typed envelope out of the row-tail ABI before doing
anything else, and the retained bottom forest is left untouched by that read.
This is the fixed projection, together with the first producer stage it
carries: the list denominator at which every published symmetric row seed is
indexed. -/

def fourfoldRowHandoffEnvelopeProgram : NPOracleProgram :=
  [ .unpairLeft 0 1 1
  , .unpairRight 1 2 2
  , .unpairRight 2 3 3
  , .unpairLeft 3 0 4
  , .halt 0
  ]

@[simp] theorem fourfoldRowHandoffEnvelopeProgram_oracleFree :
    OracleFree fourfoldRowHandoffEnvelopeProgram := by
  rfl

def fourfoldRowHandoffEnvelopeBits (handoff : ℕ) : ℕ :=
  natBitLength handoff

theorem run_fourfoldRowHandoffEnvelopeProgram
    (bottomForest envelopeCode modeCode q rowIndex inputCode maximumBits : ℕ)
    (hbits :
      fourfoldRowHandoffEnvelopeBits
          (fourfoldRowTailHandoff bottomForest envelopeCode modeCode q rowIndex
            inputCode) ≤
        maximumBits) :
    runNPOracleProgram fourfoldRowHandoffEnvelopeProgram maximumBits 5
        (initialNPOracleState q
          (fourfoldRowTailHandoff bottomForest envelopeCode modeCode q rowIndex
            inputCode)) =
      some envelopeCode := by
  let rowInput := Nat.pair rowIndex inputCode
  let envelopeTail := Nat.pair envelopeCode rowInput
  let arityTail := Nat.pair q envelopeTail
  let fields := Nat.pair modeCode arityTail
  let handoff := Nat.pair fields bottomForest
  have hhandoff : natBitLength handoff ≤ maximumBits := hbits
  have hfields : natBitLength fields ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair fields bottomForest)).trans hhandoff
  have harityTail : natBitLength arityTail ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair modeCode arityTail)).trans hfields
  have henvelopeTail : natBitLength envelopeTail ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair q envelopeTail)).trans harityTail
  have henvelopeCode : natBitLength envelopeCode ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair envelopeCode rowInput)).trans
      henvelopeTail
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := fields)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, fourfoldRowTailHandoff, fields, arityTail,
        envelopeTail, rowInput])
    hfields]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := arityTail)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, fields])
    harityTail]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := envelopeTail)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, arityTail])
    henvelopeTail]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := envelopeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, envelopeTail])
    henvelopeCode]
  exact run_halt_instruction (fuel := 0) (value := envelopeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    henvelopeCode

/-- The row-tail projection followed by the fixed list-denominator machine. -/
def fourfoldRowHandoffListDenominatorProgram (accuracyExponent : ℕ) :
    NPOracleProgram :=
  linkPrograms fourfoldRowHandoffEnvelopeProgram
    (fourfoldListDenominatorProgram accuracyExponent)

theorem fourfoldRowHandoffListDenominatorProgram_oracleFree
    (accuracyExponent : ℕ) :
    OracleFree (fourfoldRowHandoffListDenominatorProgram accuracyExponent) :=
  oracleFree_linkPrograms fourfoldRowHandoffEnvelopeProgram_oracleFree
    (fourfoldListDenominatorProgram_oracleFree accuracyExponent)

def fourfoldRowHandoffListDenominatorFuel
    (accuracyExponent : ℕ) (denominatorFuel : ℕ) : ℕ :=
  linkFuel (fourfoldListDenominatorProgram accuracyExponent) 5 denominatorFuel

private theorem symmetricRowRequest_envelopeCode
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    (symmetricFourfoldRowRequest request rowIndex input).envelopeCode =
      fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
        encodeNormalizedSymmetricThresholdCircuit request := by
  simp only [symmetricFourfoldRowRequest,
    CanonicalWitnessCodec.symmetricCircuitCodec]

/-- **The symmetric list denominator, executed from the row handoff.**  This
is the first compiled stage of the symmetric polynomial producer: the seed
family of the row is selected without decoding the retained bottom forest. -/
theorem run_symmetricRowHandoffListDenominatorProgram
    (accuracyExponent : ℕ)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex maximumBits : ℕ) (input : BitInput request.q)
    (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hprojectionBits :
      fourfoldRowHandoffEnvelopeBits
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input) ≤
        maximumBits)
    (hdenominatorBits :
      symmetricListDenominatorBits accuracyExponent request ≤ maximumBits) :
    runNPOracleProgram
        (fourfoldRowHandoffListDenominatorProgram accuracyExponent) maximumBits
        (fourfoldRowHandoffListDenominatorFuel accuracyExponent
          (symmetricListDenominatorFuel accuracyExponent request))
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
      some
        (symmetricListDenominator request
          (fixedTargetDenominator accuracyExponent request.q)) := by
  unfold symmetricFourfoldRowTailHandoff at hprojectionBits ⊢
  have hdenominator :
      runNPOracleProgram (fourfoldListDenominatorProgram accuracyExponent)
          maximumBits (symmetricListDenominatorFuel accuracyExponent request)
          (initialNPOracleState request.q
            (symmetricFourfoldRowRequest request rowIndex input).envelopeCode) =
        some
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q)) := by
    rw [symmetricRowRequest_envelopeCode]
    exact run_symmetricListDenominatorProgram accuracyExponent maximumBits
      request hdenominatorBits
  exact run_linkPrograms hpositive hlength
    (run_fourfoldRowHandoffEnvelopeProgram
      (symmetricFourfoldRowBottomForest algorithm request)
      (symmetricFourfoldRowRequest request rowIndex input).envelopeCode
      symmetricCircuitFamilyTag request.q rowIndex (encodeBitInput input)
      maximumBits hprojectionBits)
    hdenominator

end NearCubicWires.CanonicalFourfoldRowProducerDispatchProgram
