import Proof.Supplier.CanonicalFourfoldRowCountFormula
import Proof.MachineModel.CanonicalFourfoldRowCountProgram
import Proof.MachineModel.CanonicalTwoPowProgram

/-!
# The symmetric counting residual, reduced to one exponent

Three facts now sit beside each other:

* `publishedSymmetricRows_rowCount_two_pow` — the published symmetric row
  count is exactly `2 ^ e` for one explicit natural exponent `e`;
* `run_binaryTwoPowProgram` — the machine computes `2 ^ e` from `e`;
* `run_symmetricFourfoldRangeAtomCountProgram_of_rowCount` — the machine
  computes the row-major atom count from the row count.

Composing them collapses the whole counting side of the artifact's execution
field to a *single* residual program: one machine that reads the typed
envelope and returns the natural number `e`.  Nothing else about the counting
path remains open, and no stage of the composition takes a semantic argument.
-/

namespace NearCubicWires.CanonicalSymmetricRowCountReduction

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalFourfoldRowCountFormula
open NearCubicWires.CanonicalFourfoldRowCountProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.FourfoldRangeAggregationComposition
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 The one remaining number -/

/-- **The symmetric counting residual, as a number.**  This is the sole
quantity a link-time counter still has to compute from the typed envelope. -/
def symmetricRowCountExponent
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  normalizedOccurrenceListSeedExponent
    (symmetricOccurrencePopulation request)
    (symmetricOccurrenceTouchingCost request liveScale)
    (symmetricListDenominator request
      (fixedTargetDenominator accuracyExponent request.q))

theorem publishedSymmetricRows_rowCount_eq_two_pow_exponent
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (publishedSymmetricRows contracts liveScale accuracyExponent).rowCount
        request =
      2 ^ symmetricRowCountExponent liveScale accuracyExponent request :=
  publishedSymmetricRows_rowCount_two_pow contracts liveScale accuracyExponent
    request

/-! ## §2 From the exponent to the published row count -/

/-- **The symmetric row counter.**  One link-time exponent program followed by
the fixed dyadic exponential. -/
def symmetricRowCountProgram (exponentProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms exponentProgram binaryTwoPowProgram

theorem symmetricRowCountProgram_oracleFree
    (exponentProgram : NPOracleProgram)
    (hexponent : OracleFree exponentProgram) :
    OracleFree (symmetricRowCountProgram exponentProgram) :=
  oracleFree_linkPrograms hexponent binaryTwoPowProgram_oracleFree

def symmetricRowCountBits (exponentBits exponent : ℕ) : ℕ :=
  max exponentBits (binaryTwoPowBits exponent)

def symmetricRowCountFuel (exponentFuel exponent : ℕ) : ℕ :=
  linkFuel binaryTwoPowProgram exponentFuel (binaryTwoPowFuel exponent)

/-- **The published symmetric row count, executed.**  Given one exact
interpreter run of the exponent program on the typed envelope, the linked
program returns the published row count itself. -/
theorem run_symmetricRowCountProgram
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (exponentProgram : NPOracleProgram)
    (exponentBits exponentFuel maximumBits : ℕ)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hbits :
      symmetricRowCountBits exponentBits
          (symmetricRowCountExponent liveScale accuracyExponent request) ≤
        maximumBits)
    (hexponent :
      runNPOracleProgram exponentProgram exponentBits exponentFuel
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
              encodeNormalizedSymmetricThresholdCircuit request)) =
        some (symmetricRowCountExponent liveScale accuracyExponent request)) :
    runNPOracleProgram (symmetricRowCountProgram exponentProgram) maximumBits
        (symmetricRowCountFuel exponentFuel
          (symmetricRowCountExponent liveScale accuracyExponent request))
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request)) =
      some
        ((publishedSymmetricRows contracts liveScale accuracyExponent).rowCount
          request) := by
  have hexponentBits : exponentBits ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hpowerBits :
      binaryTwoPowBits
          (symmetricRowCountExponent liveScale accuracyExponent request) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  have hpositive : 1 ≤ maximumBits := by
    refine le_trans ?_ hpowerBits
    unfold binaryTwoPowBits natBitLength
    omega
  rw [publishedSymmetricRows_rowCount_eq_two_pow_exponent contracts liveScale
    accuracyExponent request]
  exact run_linkPrograms hpositive hlength
    (run_bits_mono hexponent hexponentBits)
    (run_binaryTwoPowProgram request.q
      (symmetricRowCountExponent liveScale accuracyExponent request)
      maximumBits hpowerBits)

/-! ## §3 The discharged counting premise -/

/-- **The symmetric atom counter.**  Exponent program, dyadic exponential,
Boolean cube, and one bit-serial product. -/
def symmetricFourfoldAtomCountProgram (exponentProgram : NPOracleProgram) :
    NPOracleProgram :=
  fourfoldRangeAtomCountProgram (symmetricRowCountProgram exponentProgram)

theorem symmetricFourfoldAtomCountProgram_oracleFree
    (exponentProgram : NPOracleProgram)
    (hexponent : OracleFree exponentProgram) :
    OracleFree (symmetricFourfoldAtomCountProgram exponentProgram) :=
  fourfoldRangeAtomCountProgram_oracleFree _
    (symmetricRowCountProgram_oracleFree exponentProgram hexponent)

/-- **The `hcount` premise of `run_sharedFourfoldAggregationProgram_symmetric`,
discharged from one exponent program.** -/
theorem run_symmetricFourfoldAtomCountProgram_of_exponent
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (exponentProgram : NPOracleProgram)
    (exponentBits exponentFuel countBits maximumBits : ℕ)
    (hlength : natBitLength request.q ≤ countBits)
    (hrowCountBits :
      symmetricRowCountBits exponentBits
          (symmetricRowCountExponent liveScale accuracyExponent request) ≤
        countBits)
    (hbits :
      fourfoldRangeAtomCountBits countBits request.q
          ((publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request) ≤
        maximumBits)
    (hexponent :
      runNPOracleProgram exponentProgram exponentBits exponentFuel
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
              encodeNormalizedSymmetricThresholdCircuit request)) =
        some (symmetricRowCountExponent liveScale accuracyExponent request)) :
    runNPOracleProgram (symmetricFourfoldAtomCountProgram exponentProgram)
        maximumBits
        (fourfoldRangeAtomCountFuel request.q
          (symmetricRowCountFuel exponentFuel
            (symmetricRowCountExponent liveScale accuracyExponent request)))
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request)) =
      some
        (fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :=
  run_symmetricFourfoldRangeAtomCountProgram_of_rowCount contracts liveScale
    accuracyExponent request (symmetricRowCountProgram exponentProgram)
    countBits
    (symmetricRowCountFuel exponentFuel
      (symmetricRowCountExponent liveScale accuracyExponent request))
    maximumBits hbits
    (run_symmetricRowCountProgram contracts liveScale accuracyExponent request
      exponentProgram exponentBits exponentFuel countBits hlength
      hrowCountBits hexponent)

/-! ## §4 The artifact's symmetric execution field, counting side closed

`run_sharedFourfoldAggregationProgram_symmetric` had two link-time program
parameters with exact interpreter premises.  Instantiating the counter removes
one of them: the symmetric execution field now depends on a single residual
program per side — the exponent program here and the row evaluator, whose
premise is reproduced verbatim. -/

theorem run_sharedFourfoldAggregationProgram_symmetric_of_exponent
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (exponentProgram rowEvaluator : NPOracleProgram)
    (maximumBits calleeBits atomCountBits rowCountBits exponentBits
      exponentFuel : ℕ)
    (evaluatorFuel : ℕ → ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hentryBits :
      CanonicalFourfoldRowTailProgram.symmetricFourfoldEntryBits contracts
          liveScale accuracyExponent request atomCountBits ≤
        maximumBits)
    (hcomponentBits :
      CanonicalFourfoldRowTailProgram.symmetricFourfoldRangeComponentBits
          contracts liveScale accuracyExponent request calleeBits ≤
        maximumBits)
    (hcalleePositive : 1 ≤ calleeBits)
    (hcalleeLength : natBitLength request.q ≤ calleeBits)
    (hbottomBits : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request →
      CanonicalFourfoldRowEvaluationProgram.symmetricFourfoldRangeBottomBits
          (selectedExactDecompositionAlgorithm contracts) request flat
          (fourfoldRangeDenominatorTail
            (publishedSymmetricRows contracts liveScale accuracyExponent)
            request) ≤
        calleeBits)
    (hrepackBits : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      CanonicalFourfoldRowTailProgram.symmetricFourfoldRowTailBits
          (selectedExactDecompositionAlgorithm contracts) request rowIndex
          input ≤
        calleeBits)
    (hevaluator : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowEvaluator calleeBits
          (evaluatorFuel
            (CanonicalFourfoldRowTailProgram.symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (CanonicalFourfoldRowTailProgram.symmetricFourfoldRowTailHandoff
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input)) =
        some
          (boolCode
            (CanonicalFourfoldRowProgram.evaluateCanonicalFourfoldRow
              (selectedExactDecompositionAlgorithm contracts) liveScale
              accuracyExponent
              (CanonicalFourfoldRowProgram.symmetricFourfoldRowRequest request
                rowIndex input))))
    (hrowCountLength : natBitLength request.q ≤ rowCountBits)
    (hrowCountBits :
      symmetricRowCountBits exponentBits
          (symmetricRowCountExponent liveScale accuracyExponent request) ≤
        rowCountBits)
    (hatomCountBits :
      fourfoldRangeAtomCountBits rowCountBits request.q
          ((publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request) ≤
        atomCountBits)
    (hexponent :
      runNPOracleProgram exponentProgram exponentBits exponentFuel
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
              encodeNormalizedSymmetricThresholdCircuit request)) =
        some (symmetricRowCountExponent liveScale accuracyExponent request)) :
    runNPOracleProgram
        (CanonicalFourfoldRowTailProgram.sharedFourfoldAggregationProgram
          (selectedExactDecompositionAlgorithm contracts)
          (symmetricFourfoldAtomCountProgram exponentProgram) rowEvaluator)
        maximumBits
        (CanonicalFourfoldRowTailProgram.symmetricSharedFourfoldAggregationFuel
          contracts liveScale accuracyExponent request
          (symmetricFourfoldAtomCountProgram exponentProgram) rowEvaluator
          (fourfoldRangeAtomCountFuel request.q
            (symmetricRowCountFuel exponentFuel
              (symmetricRowCountExponent liveScale accuracyExponent request)))
          evaluatorFuel)
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request)) =
      some
        (symmetricRatioComponentCode
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :=
  CanonicalFourfoldRowTailProgram.run_sharedFourfoldAggregationProgram_symmetric
    contracts liveScale accuracyExponent request
    (symmetricFourfoldAtomCountProgram exponentProgram) rowEvaluator
    maximumBits calleeBits atomCountBits
    (fourfoldRangeAtomCountFuel request.q
      (symmetricRowCountFuel exponentFuel
        (symmetricRowCountExponent liveScale accuracyExponent request)))
    evaluatorFuel hpositive hlength hentryBits hcomponentBits hcalleePositive
    hcalleeLength hbottomBits hrepackBits hevaluator
    (run_symmetricFourfoldAtomCountProgram_of_exponent contracts liveScale
      accuracyExponent request exponentProgram exponentBits exponentFuel
      rowCountBits atomCountBits hrowCountLength hrowCountBits hatomCountBits
      hexponent)

end NearCubicWires.CanonicalSymmetricRowCountReduction
