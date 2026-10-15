import Proof.MachineModel.CanonicalBooleanRangeAggregationProgram
import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.Circuits.CanonicalSignedPlaneCall
import Proof.MachineModel.FixedAccuracyDenominatorProgram
import Proof.MachineModel.FourfoldRequestEnvelopeProgram
import Proof.Foundations.SourceContracts
import Proof.Supplier.SupplierEstimator
import Proof.Foundations.VerifiedLinker

/-!
# One executable normalized-estimator pipeline

Both normalized circuit families use the same raw request envelope, aggregation
program, and canonical ratio packer.  This module fixes that composition and
its complete interpreter budget.  The accuracy exponent is compile-time data,
so the request carries neither a denominator function nor a denominator
certificate.  The aggregation artifact must compute canonical
numerator/denominator components from the typed envelope; no field may provide
a final rational code or an alternate semantic estimate.
-/

namespace NearCubicWires.SharedNormalizedEstimatorProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalSignedPlaneCall
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.WilliamsPublishedForm
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker
open NearCubicWires.VerifiedPlaneRequestBuilder

/-! ## Canonical aggregation-component handoff -/

/-- Internal fixed-record handoff.  Both fields are canonical binary naturals;
the denominator is represented one below its positive semantic value. -/
def canonicalRatioComponentCode
    (numerator denominatorTail : ℕ) : ℕ :=
  encodeTaggedList [encodeNat numerator, encodeNat denominatorTail]

@[simp] theorem canonicalRatioComponentEncoderOutput_eq
    (numerator denominatorTail : ℕ) :
    canonicalRatioComponentEncoderOutput numerator denominatorTail =
      canonicalRatioComponentCode numerator denominatorTail := by
  rfl

def canonicalRatioPackerOutput
    (numerator denominatorTail : ℕ) : ℕ :=
  encodeNaturalRatio numerator denominatorTail

/-- Fixed parser/packer for the two canonical components.  It performs no
arithmetic and receives no final answer code: the pair it returns is assembled
from the two independently addressable canonical fields. -/
def canonicalRatioPackerProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 2 3 2
  , .unpairRight 2 2 3
  , .unpairRight 2 2 4
  , .unpairLeft 2 4 5
  , .pair 3 4 0 6
  , .halt 0
  ]

@[simp] theorem canonicalRatioPackerProgram_oracleFree :
    OracleFree canonicalRatioPackerProgram := by
  rfl

def canonicalRatioPackerRegisterBound
    (numerator denominatorTail : ℕ) : ℕ :=
  max (canonicalRatioComponentCode numerator denominatorTail)
    (canonicalRatioPackerOutput numerator denominatorTail) + 1

def canonicalRatioPackerBits
    (numerator denominatorTail : ℕ) : ℕ :=
  natBitLength
    (canonicalRatioPackerRegisterBound numerator denominatorTail)

private theorem boundedValueBits
    {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound)
    (hbits : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

theorem run_canonicalRatioPackerProgram
    (numerator denominatorTail inputLength maximumBits : ℕ)
    (hbits :
      canonicalRatioPackerBits numerator denominatorTail ≤ maximumBits) :
    runNPOracleProgram canonicalRatioPackerProgram maximumBits 7
        (initialNPOracleState inputLength
          (canonicalRatioComponentCode numerator denominatorTail)) =
      some (canonicalRatioPackerOutput numerator denominatorTail) := by
  let numeratorCode := encodeNat numerator
  let denominatorCode := encodeNat denominatorTail
  let tail₁ := encodeTaggedList [denominatorCode]
  let payload₀ := Nat.pair numeratorCode tail₁
  let payload₁ := Nat.pair denominatorCode 0
  let raw := canonicalRatioComponentCode numerator denominatorTail
  let output := canonicalRatioPackerOutput numerator denominatorTail
  let bound :=
    canonicalRatioPackerRegisterBound numerator denominatorTail
  have hbound : natBitLength bound ≤ maximumBits := hbits
  have hrawLe : raw ≤ bound := by
    dsimp [bound, canonicalRatioPackerRegisterBound]
    exact (le_max_left _ _).trans (Nat.le_add_right _ _)
  have houtputLe : output ≤ bound := by
    dsimp [bound, output, canonicalRatioPackerOutput]
    exact (le_max_right _ _).trans (Nat.le_add_right _ _)
  have houtput : natBitLength output ≤ maximumBits :=
    boundedValueBits houtputLe hbound
  have componentBits :
      ∀ value, value ≤ raw → natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact boundedValueBits (hvalue.trans hrawLe) hbound
  have hpayload₀Le : payload₀ ≤ raw := by
    simpa [raw, payload₀, tail₁, canonicalRatioComponentCode,
      numeratorCode, denominatorCode, encodeTaggedList] using
      (Nat.right_le_pair 1 payload₀)
  have hnumeratorLe : numeratorCode ≤ payload₀ :=
    Nat.left_le_pair numeratorCode tail₁
  have htail₁Le : tail₁ ≤ payload₀ :=
    Nat.right_le_pair numeratorCode tail₁
  have hpayload₁Le : payload₁ ≤ tail₁ := by
    simpa [tail₁, payload₁, encodeTaggedList] using
      (Nat.right_le_pair 1 payload₁)
  have hdenominatorLe : denominatorCode ≤ payload₁ :=
    Nat.left_le_pair denominatorCode 0
  have hpayload₀ : natBitLength payload₀ ≤ maximumBits :=
    componentBits payload₀ hpayload₀Le
  have hnumerator : natBitLength numeratorCode ≤ maximumBits :=
    componentBits numeratorCode (hnumeratorLe.trans hpayload₀Le)
  have htail₁ : natBitLength tail₁ ≤ maximumBits :=
    componentBits tail₁ (htail₁Le.trans hpayload₀Le)
  have hpayload₁ : natBitLength payload₁ ≤ maximumBits :=
    componentBits payload₁
      (hpayload₁Le.trans (htail₁Le.trans hpayload₀Le))
  have hdenominator : natBitLength denominatorCode ≤ maximumBits :=
    componentBits denominatorCode
      (hdenominatorLe.trans
        (hpayload₁Le.trans (htail₁Le.trans hpayload₀Le)))
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by
      simp [initialNPOracleState, payload₀, tail₁,
        canonicalRatioComponentCode, numeratorCode, denominatorCode,
        encodeTaggedList]) hpayload₀]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₀])
    hnumerator]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₀]) htail₁]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, tail₁, payload₁,
        encodeTaggedList]) hpayload₁]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload₁])
    hdenominator]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        canonicalRatioPackerOutput, encodeNaturalRatio, numeratorCode,
        denominatorCode]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        canonicalRatioPackerOutput]) houtput

/-! ## One row-major semantic bridge -/

/-- Low-to-high input codes form the exact finite enumeration used by the
fixed row ABI.  Keeping this equivalence beside the aggregation controller
prevents an unverified bit-order conversion at the final count. -/
def fourfoldInputFinEquiv (q : ℕ) : BitInput q ≃ Fin (2 ^ q) where
  toFun input := ⟨encodeBitInput input, by
    rw [encodeBitInput_eq_ofBits]
    exact Nat.ofBits_lt_two_pow input⟩
  invFun code := rowBitInputOfCode q code.val
  left_inv := rowBitInputOfCode_encode
  right_inv code := by
    apply Fin.ext
    exact encodeBitInput_testBit code.isLt

/-- The fixed flat index is row-major: each row owns one consecutive block of
all `2^q` low-to-high input codes. -/
def fourfoldFlatCoordinateEquiv
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) :
    (Fin (rows.rowCount request) × BitInput request.q) ≃
      Fin (rows.rowCount request * 2 ^ request.q) :=
  (Equiv.prodCongr (Equiv.refl _)
      (fourfoldInputFinEquiv request.q)).trans
    finProdFinEquiv

/-- Total Boolean semantics for one native flat index.  The false malformed
case is unreachable for the canonical range generated by the controller. -/
def fourfoldFlatRowValue
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) (flat : ℕ) : Bool :=
  if hflat : flat < rows.rowCount request * 2 ^ request.q then
    let coordinate :=
      (fourfoldFlatCoordinateEquiv rows request).symm ⟨flat, hflat⟩
    rows.row request coordinate.1 coordinate.2
  else false

/-- Extract the flat index from the canonical callable atom.  The preserved
right component contains denominator and row metadata and is deliberately not
interpreted by the row semantics. -/
def fourfoldFlatRangeValue
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) (atom : ℕ) : Bool :=
  fourfoldFlatRowValue rows request
    (Nat.unpair (Nat.unpair atom).2).1

/-- The sole row-major range count is definitionally the published finite-row
acceptance count.  This closes the semantic handoff from the static balanced
map/reduce controller without a second aggregation callback. -/
theorem fourfoldFlatRange_acceptanceCount
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) (context : ℕ) :
    nonzeroSupportCount
        (fixedBooleanRangeValues request.q
          (rows.rowCount request * 2 ^ request.q) context
          (fourfoldFlatRangeValue rows request)) =
      (rows.aggregation request).acceptanceCount := by
  let total := rows.rowCount request * 2 ^ request.q
  let equivalence := fourfoldFlatCoordinateEquiv rows request
  have hflatValue (flat : Fin total) :
      fourfoldFlatRowValue rows request flat.val =
        rows.row request
          (equivalence.symm flat).1
          (equivalence.symm flat).2 := by
    unfold fourfoldFlatRowValue
    rw [dif_pos flat.isLt]
  let score :
      Fin (rows.rowCount request) × BitInput request.q → ℕ :=
    fun coordinate =>
      (rows.row request coordinate.1 coordinate.2).toNat
  have hvalues :
      fixedBooleanRangeValues request.q total context
          (fourfoldFlatRangeValue rows request) =
        (List.range total).map (fourfoldFlatRowValue rows request) := by
    unfold fixedBooleanRangeValues fixedBooleanRangeRequests
    rw [balancedRangeRequestAtoms_eq_map_range]
    simp [fourfoldFlatRangeValue, balancedRangeRequestAtom,
      Function.comp_def]
  rw [show rows.rowCount request * 2 ^ request.q = total by rfl]
  rw [hvalues, nonzeroSupportCount_eq_sum_toNat, List.map_map]
  change
    ((List.range total).map
      (fun flat => (fourfoldFlatRowValue rows request flat).toNat)).sum = _
  rw [← List.sum_toFinset
    (fun flat => (fourfoldFlatRowValue rows request flat).toNat)
    (List.nodup_range : (List.range total).Nodup)]
  rw [List.toFinset_range]
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [hflatValue]
  change (∑ flat : Fin total, score (equivalence.symm flat)) = _
  rw [Equiv.sum_comp equivalence.symm score]
  unfold FourfoldRowPreprocessor.aggregation
    FiniteRowAggregation.acceptanceCount
  dsimp only [score]
  rw [Fintype.sum_prod_type]

/-! ## The one remaining concrete aggregation artifact -/

def fourfoldRangeRowContext
    (mode : NormalizedEstimatorMode) (envelopeCode : ℕ) : ℕ :=
  Nat.pair (normalizedEstimatorModeCode mode) envelopeCode

def symmetricFourfoldRangeRowContext
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  fourfoldRangeRowContext .symmetric <|
    fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
      encodeNormalizedSymmetricThresholdCircuit request

def thresholdFourfoldRangeRowContext
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) : ℕ :=
  fourfoldRangeRowContext .threshold <|
    fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
      encodeNormalizedThresholdThresholdCircuit request

def symmetricRatioComponentCode
    (rows :
      FourfoldRowPreprocessor NormalizedSymmetricThresholdCircuit
        NormalizedSymmetricThresholdCircuit.eval)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  canonicalRatioComponentCode
    (rows.aggregation request).acceptanceCount
    (rows.rowCount request * 2 ^ request.q - 1)

def thresholdRatioComponentCode
    (rows :
      FourfoldRowPreprocessor NormalizedThresholdThresholdCircuit
        NormalizedThresholdThresholdCircuit.eval)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) : ℕ :=
  canonicalRatioComponentCode
    (rows.aggregation request).acceptanceCount
    (rows.rowCount request * 2 ^ request.q - 1)

theorem fourfoldFlatRangeComponent_eq
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) (rowContext : ℕ) :
    fixedBooleanRangeComponentOutput request.q
        (rows.rowCount request * 2 ^ request.q)
        (rows.rowCount request * 2 ^ request.q - 1)
        rowContext
        (fourfoldFlatRangeValue rows request) =
      canonicalRatioComponentCode
        (rows.aggregation request).acceptanceCount
        (rows.rowCount request * 2 ^ request.q - 1) := by
  unfold fixedBooleanRangeComponentOutput
  rw [fourfoldFlatRange_acceptanceCount]
  rfl

theorem symmetric_fourfoldFlatRangeComponent_eq
    (rows :
      FourfoldRowPreprocessor NormalizedSymmetricThresholdCircuit
        NormalizedSymmetricThresholdCircuit.eval)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    fixedBooleanRangeComponentOutput request.q
        (rows.rowCount request * 2 ^ request.q)
        (rows.rowCount request * 2 ^ request.q - 1)
        (symmetricFourfoldRangeRowContext request)
        (fourfoldFlatRangeValue rows request) =
      symmetricRatioComponentCode rows request := by
  exact fourfoldFlatRangeComponent_eq rows request _

theorem threshold_fourfoldFlatRangeComponent_eq
    (rows :
      FourfoldRowPreprocessor NormalizedThresholdThresholdCircuit
        NormalizedThresholdThresholdCircuit.eval)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    fixedBooleanRangeComponentOutput request.q
        (rows.rowCount request * 2 ^ request.q)
        (rows.rowCount request * 2 ^ request.q - 1)
        (thresholdFourfoldRangeRowContext request)
        (fourfoldFlatRangeValue rows request) =
      thresholdRatioComponentCode rows request := by
  exact fourfoldFlatRangeComponent_eq rows request _

theorem symmetric_packerOutput_eq_outputCode
    (rows :
      FourfoldRowPreprocessor NormalizedSymmetricThresholdCircuit
        NormalizedSymmetricThresholdCircuit.eval)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    canonicalRatioPackerOutput
        (rows.aggregation request).acceptanceCount
        (rows.rowCount request * 2 ^ request.q - 1) =
      rows.outputCode request := by
  unfold canonicalRatioPackerOutput
  unfold FourfoldRowPreprocessor.outputCode
  unfold FiniteRowAggregation.outputCode
  congr 1
  unfold FiniteRowAggregation.sampleCount
  simp

theorem threshold_packerOutput_eq_outputCode
    (rows :
      FourfoldRowPreprocessor NormalizedThresholdThresholdCircuit
        NormalizedThresholdThresholdCircuit.eval)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    canonicalRatioPackerOutput
        (rows.aggregation request).acceptanceCount
        (rows.rowCount request * 2 ^ request.q - 1) =
      rows.outputCode request := by
  unfold canonicalRatioPackerOutput
  unfold FourfoldRowPreprocessor.outputCode
  unfold FiniteRowAggregation.outputCode
  congr 1
  unfold FiniteRowAggregation.sampleCount
  simp

/-! ## Canonical executable dependencies from the published contracts -/

/-- The decomposition algorithm selected once from the published executable
contract.  Every threshold row and the aggregation compiler use this same
algorithm; there is no independent semantic decomposition choice. -/
noncomputable def selectedExactDecompositionAlgorithm
    (contracts : PublishedContracts) :
    ExecutableExactDecompositionAlgorithm :=
  Classical.choice contracts.disjointExactDecomposition

/-- **Derived, no longer assumed.**  The published row supplies only the
algorithm; this bound comes from the fixed interpreter ABI via
`ExecutableExactDecompositionAlgorithm.children_length_le_budget`.  The
statement is unchanged, so every downstream consumer is untouched. -/
theorem selectedExactDecompositionAlgorithm_childrenBound
    (contracts : PublishedContracts) :
    ∀ request : ExactDecompositionRequest,
      ((selectedExactDecompositionAlgorithm contracts).run
        request.gate).children.length ≤
          (selectedExactDecompositionAlgorithm contracts).runner.budget
            request :=
  fun request =>
    ExecutableExactDecompositionAlgorithm.children_length_le_budget
      (selectedExactDecompositionAlgorithm contracts) request

/-- Safe semantic view of the faithful Williams source.  Unlike the retired
packed `NPOracleProgram` selector, this value is derived from the exhibited
local multitape machine's streamed receipt and does not invent a second
executable carrier or an independent cost. -/
noncomputable def selectedWilliamsSemanticAlgorithm
    (contracts : PublishedContracts) : RectangularProductAlgorithm :=
  Classical.choose contracts.booleanRectangularProductSemantic

theorem selectedWilliamsSemanticAlgorithm_spec
    (contracts : PublishedContracts) :
    ∃ onset coefficient logExponent : ℕ, 0 < coefficient ∧
      ∀ U, onset ≤ U →
        ∀ (left : BitMatrix U (rectangularInnerDimension U))
          (right : BitMatrix (rectangularInnerDimension U) U),
          (selectedWilliamsSemanticAlgorithm contracts).compute U left right =
              integerMatrixProduct left right ∧
            (selectedWilliamsSemanticAlgorithm contracts).steps U left right ≤
              coefficient * U ^ 2 * logScale U ^ logExponent :=
  Classical.choose_spec contracts.booleanRectangularProductSemantic

noncomputable def publishedSymmetricRows
    (contracts : PublishedContracts) (liveScale : ℕ)
    (accuracyExponent : ℕ) :
    FourfoldRowPreprocessor NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.eval :=
  executableSymmetricFourfoldRows contracts.expanderSpectrum
    (selectedExactDecompositionAlgorithm contracts) liveScale
    accuracyExponent

noncomputable def publishedThresholdRows
    (contracts : PublishedContracts) (liveScale : ℕ)
    (accuracyExponent : ℕ) :
    FourfoldRowPreprocessor NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.eval :=
  executableThresholdFourfoldRows contracts.expanderSpectrum
    contracts.primeThetaBound
    (selectedExactDecompositionAlgorithm contracts) liveScale
    accuracyExponent

/-- The fixed schedule pays exactly the requested inverse-polynomial accuracy;
the extra successor in the sampling denominator only improves the bound. -/
theorem publishedSymmetricRows_failure_le
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (hq : 0 < request.q) :
    (publishedSymmetricRows contracts liveScale
        accuracyExponent).failure request ≤
      inversePolynomialAdvantage request.q (accuracyExponent : ℝ) := by
  change
    (1 : ℝ) /
        (fixedTargetDenominator accuracyExponent request.q + 1 : ℕ) ≤
      inversePolynomialAdvantage request.q (accuracyExponent : ℝ)
  exact
    reciprocal_fixedTargetDenominator_succ_le accuracyExponent request.q hq

theorem publishedThresholdRows_failure_le
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (hq : 0 < request.q) :
    (publishedThresholdRows contracts liveScale
        accuracyExponent).failure request ≤
      inversePolynomialAdvantage request.q (accuracyExponent : ℝ) := by
  change
    (1 : ℝ) /
        (fixedTargetDenominator accuracyExponent request.q + 1 : ℕ) ≤
      inversePolynomialAdvantage request.q (accuracyExponent : ℝ)
  exact
    reciprocal_fixedTargetDenominator_succ_le accuracyExponent request.q hq

theorem qOneCoverage_does_not_imply_universalCoverage
    (Circuit : CircuitFamily) :
    ¬ (∀ property : FourfoldRequest Circuit → Prop,
      (∀ request, request.q = 1 → property request) →
        ∀ request, property request) := by
  intro hcoverage
  let property : FourfoldRequest Circuit → Prop :=
    fun request => request.q = 1
  have hqOne : ∀ request, request.q = 1 → property request := by
    intro request hq
    exact hq
  have hall := hcoverage property hqOne
  have htwo :=
    hall ({ q := 2, circuits := [] } : FourfoldRequest Circuit)
  simp [property] at htwo

/-- Correctness above an asymptotic onset does not, by logic alone, provide
the all-dimension correctness required by an exact row evaluator.  A single
linked program may pad or handle the finite prefix internally, but that
behavior must itself be executed and proved; it cannot be obtained by
specializing the rectangular-product contract. -/
theorem eventualCoverage_does_not_imply_universalCoverage :
    ¬ (∀ property : ℕ → Prop,
      (∃ onset, ∀ dimension, onset ≤ dimension → property dimension) →
        ∀ dimension, property dimension) := by
  intro hcoverage
  let property : ℕ → Prop := fun dimension => dimension ≠ 0
  have heventual :
      ∃ onset, ∀ dimension, onset ≤ dimension → property dimension := by
    refine ⟨1, ?_⟩
    intro dimension hdimension
    omega
  have hall := hcoverage property heventual
  exact (hall 0) rfl

/-- A concrete implementation obligation, deliberately narrower than
`SharedNormalizedEstimator`: the program starts from the already verified
typed envelope and returns the two canonical aggregation components.  Every
resource field depends only on public mode, arity, and description measure. -/
structure SharedNormalizedAggregationArtifact
    (contracts : PublishedContracts) (liveScale : ℕ)
    (accuracyExponent : ℕ) where
  /-- One fixed production program.  All imported executable dependencies are
  already selected by `contracts`; no run-time compiler callback remains. -/
  program : NPOracleProgram
  fuelByMeasure : NormalizedEstimatorMode → ℕ → ℕ → ℕ
  registerBitsByMeasure : NormalizedEstimatorMode → ℕ → ℕ → ℕ
  fuelPositive : ∀ mode q measure, 0 < fuelByMeasure mode q measure
  registerBitsPositive :
    ∀ mode q measure, 0 < registerBitsByMeasure mode q measure
  symmetricInitialBitsFit :
    ∀ request : FourfoldRequest NormalizedSymmetricThresholdCircuit,
      natBitLength
          (max request.q (symmetricFourfoldRequestCode request)) ≤
        registerBitsByMeasure .symmetric request.q
          (batchDescription
            NormalizedSymmetricThresholdCircuit.descriptionBits
            request.circuits)
  thresholdInitialBitsFit :
    ∀ request : FourfoldRequest NormalizedThresholdThresholdCircuit,
      natBitLength
          (max request.q (thresholdFourfoldRequestCode request)) ≤
        registerBitsByMeasure .threshold request.q
          (batchDescription
            NormalizedThresholdThresholdCircuit.descriptionBits
            request.circuits)
  oracleFree :
    OracleFree program
  computesSymmetric : ∀ request,
    let measure :=
      batchDescription
        NormalizedSymmetricThresholdCircuit.descriptionBits request.circuits
    runNPOracleProgram
      program
      (registerBitsByMeasure .symmetric request.q measure)
      (fuelByMeasure .symmetric request.q measure)
      (initialNPOracleState request.q
        (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
          encodeNormalizedSymmetricThresholdCircuit request)) =
      some (symmetricRatioComponentCode
        (publishedSymmetricRows contracts liveScale accuracyExponent) request)
  computesThreshold : ∀ request,
    let measure :=
      batchDescription
        NormalizedThresholdThresholdCircuit.descriptionBits request.circuits
    runNPOracleProgram
      program
      (registerBitsByMeasure .threshold request.q measure)
      (fuelByMeasure .threshold request.q measure)
      (initialNPOracleState request.q
        (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
          encodeNormalizedThresholdThresholdCircuit request)) =
      some (thresholdRatioComponentCode
        (publishedThresholdRows contracts liveScale accuracyExponent) request)
  symmetricEnvelopeFits :
    ∀ request : FourfoldRequest NormalizedSymmetricThresholdCircuit,
    fourfoldRequestEnvelopeBits symmetricCircuitFamilyTag
        encodeNormalizedSymmetricThresholdCircuit request ≤
      registerBitsByMeasure .symmetric request.q
        (batchDescription
          NormalizedSymmetricThresholdCircuit.descriptionBits
          request.circuits)
  thresholdEnvelopeFits :
    ∀ request : FourfoldRequest NormalizedThresholdThresholdCircuit,
    fourfoldRequestEnvelopeBits thresholdCircuitFamilyTag
        encodeNormalizedThresholdThresholdCircuit request ≤
      registerBitsByMeasure .threshold request.q
        (batchDescription
          NormalizedThresholdThresholdCircuit.descriptionBits
          request.circuits)
  symmetricPackerFits :
    ∀ request : FourfoldRequest NormalizedSymmetricThresholdCircuit,
    canonicalRatioPackerBits
        ((publishedSymmetricRows contracts liveScale
          accuracyExponent).aggregation request).acceptanceCount
        ((publishedSymmetricRows contracts liveScale
          accuracyExponent).rowCount request * 2 ^ request.q - 1) ≤
      registerBitsByMeasure .symmetric request.q
        (batchDescription
          NormalizedSymmetricThresholdCircuit.descriptionBits
          request.circuits)
  thresholdPackerFits :
    ∀ request : FourfoldRequest NormalizedThresholdThresholdCircuit,
    canonicalRatioPackerBits
        ((publishedThresholdRows contracts liveScale
          accuracyExponent).aggregation request).acceptanceCount
        ((publishedThresholdRows contracts liveScale
          accuracyExponent).rowCount request * 2 ^ request.q - 1) ≤
      registerBitsByMeasure .threshold request.q
        (batchDescription
          NormalizedThresholdThresholdCircuit.descriptionBits
          request.circuits)
  symmetricInputLengthFits :
    ∀ request : FourfoldRequest NormalizedSymmetricThresholdCircuit,
    natBitLength request.q ≤
      registerBitsByMeasure .symmetric request.q
        (batchDescription
          NormalizedSymmetricThresholdCircuit.descriptionBits
          request.circuits)
  thresholdInputLengthFits :
    ∀ request : FourfoldRequest NormalizedThresholdThresholdCircuit,
    natBitLength request.q ≤
      registerBitsByMeasure .threshold request.q
        (batchDescription
          NormalizedThresholdThresholdCircuit.descriptionBits
          request.circuits)

/-! ## Closed linker and `SharedNormalizedEstimator` constructor -/

variable {contracts : PublishedContracts} {liveScale accuracyExponent : ℕ}

noncomputable def SharedNormalizedAggregationArtifact.symmetricRows
    (_artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent) :
    FourfoldRowPreprocessor NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.eval :=
  publishedSymmetricRows contracts liveScale accuracyExponent

noncomputable def SharedNormalizedAggregationArtifact.thresholdRows
    (_artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent) :
    FourfoldRowPreprocessor NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.eval :=
  publishedThresholdRows contracts liveScale accuracyExponent

noncomputable def
    SharedNormalizedAggregationArtifact.aggregationPackerProgram
    (artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent) : NPOracleProgram :=
  linkPrograms artifact.program canonicalRatioPackerProgram

noncomputable def SharedNormalizedAggregationArtifact.programWithEnvelope
    (artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent) : NPOracleProgram :=
  linkPrograms fourfoldRequestEnvelopeProgram
    artifact.aggregationPackerProgram

def SharedNormalizedAggregationArtifact.aggregationPackerFuel
    (artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent)
    (mode : NormalizedEstimatorMode) (q measure : ℕ) : ℕ :=
  linkFuel canonicalRatioPackerProgram
    (artifact.fuelByMeasure mode q measure) 7

noncomputable def SharedNormalizedAggregationArtifact.totalFuel
    (artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent)
    (mode : NormalizedEstimatorMode) (q measure : ℕ) : ℕ :=
  linkFuel artifact.aggregationPackerProgram 10
    (artifact.aggregationPackerFuel mode q measure)

theorem SharedNormalizedAggregationArtifact.aggregationPacker_oracleFree
    (artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent) :
    OracleFree artifact.aggregationPackerProgram :=
  oracleFree_linkPrograms artifact.oracleFree
    canonicalRatioPackerProgram_oracleFree

theorem SharedNormalizedAggregationArtifact.programWithEnvelope_oracleFree
    (artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent) :
    OracleFree artifact.programWithEnvelope :=
  oracleFree_linkPrograms fourfoldRequestEnvelopeProgram_oracleFree
    artifact.aggregationPacker_oracleFree

theorem SharedNormalizedAggregationArtifact.runAggregationPacker_symmetric
    (artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    let measure :=
      batchDescription
        NormalizedSymmetricThresholdCircuit.descriptionBits request.circuits
    runNPOracleProgram artifact.aggregationPackerProgram
      (artifact.registerBitsByMeasure .symmetric request.q measure)
      (artifact.aggregationPackerFuel .symmetric request.q measure)
      (initialNPOracleState request.q
        (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
          encodeNormalizedSymmetricThresholdCircuit request)) =
      some (artifact.symmetricRows.outputCode request) := by
  dsimp only
  rw [← symmetric_packerOutput_eq_outputCode artifact.symmetricRows request]
  apply run_linkPrograms
  · exact artifact.registerBitsPositive .symmetric _ _
  · exact artifact.symmetricInputLengthFits request
  · exact artifact.computesSymmetric request
  · exact run_canonicalRatioPackerProgram _ _ request.q _
      (artifact.symmetricPackerFits request)

theorem SharedNormalizedAggregationArtifact.runAggregationPacker_threshold
    (artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    let measure :=
      batchDescription
        NormalizedThresholdThresholdCircuit.descriptionBits request.circuits
    runNPOracleProgram artifact.aggregationPackerProgram
      (artifact.registerBitsByMeasure .threshold request.q measure)
      (artifact.aggregationPackerFuel .threshold request.q measure)
      (initialNPOracleState request.q
        (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
          encodeNormalizedThresholdThresholdCircuit request)) =
      some (artifact.thresholdRows.outputCode request) := by
  dsimp only
  rw [← threshold_packerOutput_eq_outputCode artifact.thresholdRows request]
  apply run_linkPrograms
  · exact artifact.registerBitsPositive .threshold _ _
  · exact artifact.thresholdInputLengthFits request
  · exact artifact.computesThreshold request
  · exact run_canonicalRatioPackerProgram _ _ request.q _
      (artifact.thresholdPackerFits request)

theorem SharedNormalizedAggregationArtifact.runProgramWithEnvelope_symmetric
    (artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    let measure :=
      batchDescription
        NormalizedSymmetricThresholdCircuit.descriptionBits request.circuits
    runNPOracleProgram artifact.programWithEnvelope
      (artifact.registerBitsByMeasure .symmetric request.q measure)
      (artifact.totalFuel .symmetric request.q measure)
      (initialNPOracleState request.q
        (symmetricFourfoldRequestCode request)) =
      some (artifact.symmetricRows.outputCode request) := by
  dsimp only
  apply run_linkPrograms
  · exact artifact.registerBitsPositive .symmetric _ _
  · exact artifact.symmetricInputLengthFits request
  · exact run_fourfoldRequestEnvelopeProgram
      symmetricCircuitFamilyTag encodeNormalizedSymmetricThresholdCircuit
      request _ (artifact.symmetricEnvelopeFits request)
  · exact artifact.runAggregationPacker_symmetric request

theorem SharedNormalizedAggregationArtifact.runProgramWithEnvelope_threshold
    (artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    let measure :=
      batchDescription
        NormalizedThresholdThresholdCircuit.descriptionBits request.circuits
    runNPOracleProgram artifact.programWithEnvelope
      (artifact.registerBitsByMeasure .threshold request.q measure)
      (artifact.totalFuel .threshold request.q measure)
      (initialNPOracleState request.q
        (thresholdFourfoldRequestCode request)) =
      some (artifact.thresholdRows.outputCode request) := by
  dsimp only
  apply run_linkPrograms
  · exact artifact.registerBitsPositive .threshold _ _
  · exact artifact.thresholdInputLengthFits request
  · exact run_fourfoldRequestEnvelopeProgram
      thresholdCircuitFamilyTag encodeNormalizedThresholdThresholdCircuit
      request _ (artifact.thresholdEnvelopeFits request)
  · exact artifact.runAggregationPacker_threshold request

/-- Unique conversion from the concrete aggregation artifact to the public
shared estimator.  Fuel includes every envelope, linker, aggregation, and
packing instruction; register width is the artifact's closed common cap. -/
noncomputable def
    SharedNormalizedAggregationArtifact.toSharedNormalizedEstimator
    (artifact :
      SharedNormalizedAggregationArtifact contracts liveScale
        accuracyExponent) :
    SharedNormalizedEstimator where
  program := artifact.programWithEnvelope
  fuelByMeasure := artifact.totalFuel
  registerBitsByMeasure := artifact.registerBitsByMeasure
  fuelPositive := by
    intro mode q measure
    simp [SharedNormalizedAggregationArtifact.totalFuel,
      SharedNormalizedAggregationArtifact.aggregationPackerFuel,
      linkFuel]
  registerBitsPositive := artifact.registerBitsPositive
  symmetricInitialBitsFit := artifact.symmetricInitialBitsFit
  thresholdInitialBitsFit := artifact.thresholdInitialBitsFit
  symmetricRows := artifact.symmetricRows
  thresholdRows := artifact.thresholdRows
  oracleFree := artifact.programWithEnvelope_oracleFree
  computesSymmetric := artifact.runProgramWithEnvelope_symmetric
  computesThreshold := artifact.runProgramWithEnvelope_threshold

end NearCubicWires.SharedNormalizedEstimatorProgram
