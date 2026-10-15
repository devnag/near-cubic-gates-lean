import Proof.MachineModel.CanonicalFourfoldRowEvaluationProgram
import Proof.MachineModel.SharedNormalizedEstimatorProgram

/-!
# Executable all-row aggregation and ratio packing for fourfold requests

`SharedNormalizedAggregationArtifact` needs one fixed program that turns a
verified typed envelope into the two canonical ratio components.  Three of the
four stages already exist as verified machines: the range-atom to exact-bottom
prefix (`fourfoldRangeBottomProgram`), the balanced Boolean range aggregator
(`fixedBooleanRangeComponentProgram`), and the ratio packer
(`canonicalRatioPackerProgram`).  Only the row-evaluation tail — the machine
image of the pure `evaluateCanonicalFourfoldRow` — is missing.

This module composes the stages that do exist and proves the exact run
equalities, so the artifact's two execution fields are reduced to a *single*
named residual obligation: one Boolean row callee on the canonical range atom.
Nothing here assumes a semantic evaluator, a callback, or a fuel argument: the
callee is a link-time program parameter with an exact interpreter premise, and
every width and fuel charge is an explicit closed expression.
-/

namespace NearCubicWires.FourfoldRangeAggregationComposition

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRowEvaluationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

variable {Circuit : CircuitFamily}
  {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}

/-! ## §1 The canonical range shape of one fourfold request -/

/-- One canonical atom per `(row, input)` pair, in row-major order. -/
def fourfoldRangeAtomCount
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) : ℕ :=
  rows.rowCount request * 2 ^ request.q

/-- Published denominator component: the sample count, one below its positive
semantic value. -/
def fourfoldRangeDenominatorTail
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) : ℕ :=
  fourfoldRangeAtomCount rows request - 1

/-- Opaque metadata preserved across the aggregation and handed unchanged to
the statically linked row callee. -/
def fourfoldRangeCallContext
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit)
    (mode : NormalizedEstimatorMode) (envelopeCode : ℕ) : ℕ :=
  fixedBooleanRangeComponentContext
    (fourfoldRangeDenominatorTail rows request)
    (fourfoldRangeRowContext mode envelopeCode)

/-- Exact width of the composed aggregation, as a closed expression in the
callee width and the public request data. -/
def fourfoldRangeComponentBits (calleeBits : ℕ)
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit)
    (mode : NormalizedEstimatorMode) (envelopeCode : ℕ) : ℕ :=
  fixedBooleanRangeComponentBits calleeBits request.q
    (fourfoldRangeAtomCount rows request)
    (fourfoldRangeDenominatorTail rows request)
    (fourfoldRangeRowContext mode envelopeCode)
    (fourfoldFlatRangeValue rows request)

/-- Exact fuel of the composed aggregation. -/
def fourfoldRangeComponentFuel (callee : NPOracleProgram)
    (calleeFuel : ℕ → ℕ)
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit)
    (mode : NormalizedEstimatorMode) (envelopeCode : ℕ) : ℕ :=
  fixedBooleanRangeComponentFuel callee calleeFuel request.q
    (fourfoldRangeAtomCount rows request)
    (fourfoldRangeDenominatorTail rows request)
    (fourfoldRangeRowContext mode envelopeCode)
    (fourfoldFlatRangeValue rows request)

/-- The canonical atom the controller actually generates for flat index
`flat`, expressed in the row-request ABI consumed by
`fourfoldRangeBottomProgram`. -/
def fourfoldRangeCallAtom
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit)
    (mode : NormalizedEstimatorMode) (envelopeCode flat : ℕ) : ℕ :=
  Nat.pair flat (fourfoldRangeCallContext rows request mode envelopeCode)

/-- The atom the aggregation controller hands to the callee is literally the
row-request ABI already consumed by `fourfoldRangeBottomProgram`.  This is the
seam that lets the existing exact-bottom prefix be linked in unchanged. -/
theorem fourfoldRangeCallAtom_eq_rangeAtomInput
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit)
    (mode : NormalizedEstimatorMode) (envelopeCode flat : ℕ) :
    fourfoldRangeCallAtom rows request mode envelopeCode flat =
      CanonicalFourfoldRangeRequestProgram.fourfoldRangeAtomInput flat
        (fourfoldRangeDenominatorTail rows request)
        (normalizedEstimatorModeCode mode) envelopeCode :=
  rfl

/-! ## §2 The composed aggregation, modulo one Boolean row callee -/

/-- **Balanced all-row aggregation, executed.**  Given only an exact
interpreter run of the row callee on each canonical atom, the fixed range
controller returns precisely the published aggregation component pair. -/
theorem run_fourfoldRangeComponentProgram_of_rowCallee
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit)
    (mode : NormalizedEstimatorMode) (envelopeCode : ℕ)
    (callee : NPOracleProgram) (calleeBits : ℕ) (calleeFuel : ℕ → ℕ)
    (hexec : ∀ flat : ℕ, flat < fourfoldRangeAtomCount rows request →
      runNPOracleProgram callee calleeBits
          (calleeFuel
            (balancedRangeRequestAtom request.q flat
              (fourfoldRangeCallContext rows request mode envelopeCode)))
          (initialNPOracleState request.q
            (fourfoldRangeCallAtom rows request mode envelopeCode flat)) =
        some (boolCode (fourfoldFlatRowValue rows request flat))) :
    runNPOracleProgram (fixedBooleanRangeComponentProgram callee)
        (fourfoldRangeComponentBits calleeBits rows request mode envelopeCode)
        (fourfoldRangeComponentFuel callee calleeFuel rows request mode
          envelopeCode)
        (initialNPOracleState request.q
          (generatedBalancedRangeInput (fourfoldRangeAtomCount rows request)
            (fourfoldRangeCallContext rows request mode envelopeCode))) =
      some
        (canonicalRatioComponentCode
          (rows.aggregation request).acceptanceCount
          (fourfoldRangeDenominatorTail rows request)) := by
  have hcomponent :=
    run_fixedBooleanRangeComponentProgram callee calleeBits request.q
      (fourfoldRangeAtomCount rows request)
      (fourfoldRangeDenominatorTail rows request)
      (fourfoldRangeRowContext mode envelopeCode) calleeFuel
      (fourfoldFlatRangeValue rows request)
      (by
        intro atom hatom
        rw [fixedBooleanRangeRequests,
          balancedRangeRequestAtoms_eq_map_range] at hatom
        rcases List.mem_map.mp hatom with ⟨offset, hoffset, rfl⟩
        have hoffsetLt : offset < fourfoldRangeAtomCount rows request :=
          List.mem_range.mp hoffset
        have hrun := hexec offset hoffsetLt
        simpa [balancedRangeRequestAtom, fourfoldRangeCallContext,
          fourfoldRangeCallAtom, fourfoldFlatRangeValue] using hrun)
  rw [show
      fixedBooleanRangeComponentOutput request.q
          (fourfoldRangeAtomCount rows request)
          (fourfoldRangeDenominatorTail rows request)
          (fourfoldRangeRowContext mode envelopeCode)
          (fourfoldFlatRangeValue rows request) =
        canonicalRatioComponentCode
          (rows.aggregation request).acceptanceCount
          (fourfoldRangeDenominatorTail rows request) from
      fourfoldFlatRangeComponent_eq rows request
        (fourfoldRangeRowContext mode envelopeCode)] at hcomponent
  exact hcomponent

/-! ## §3 Ratio packing, executed -/

/-- The composed production tail: balanced aggregation followed by the fixed
canonical ratio packer. -/
def fourfoldRangePackedProgram (callee : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (fixedBooleanRangeComponentProgram callee)
    canonicalRatioPackerProgram

theorem fourfoldRangePackedProgram_oracleFree
    (callee : NPOracleProgram) (hcallee : OracleFree callee) :
    OracleFree (fourfoldRangePackedProgram callee) :=
  oracleFree_linkPrograms
    (fixedBooleanRangeComponentProgram_oracleFree callee hcallee)
    canonicalRatioPackerProgram_oracleFree

def fourfoldRangePackedFuel (callee : NPOracleProgram)
    (calleeFuel : ℕ → ℕ)
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit)
    (mode : NormalizedEstimatorMode) (envelopeCode : ℕ) : ℕ :=
  linkFuel canonicalRatioPackerProgram
    (fourfoldRangeComponentFuel callee calleeFuel rows request mode
      envelopeCode)
    7

/-- **Ratio packing, executed.**  The composed program emits the published
`FourfoldRowPreprocessor.outputCode` for the request. -/
theorem run_fourfoldRangePackedProgram_of_rowCallee
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit)
    (mode : NormalizedEstimatorMode) (envelopeCode : ℕ)
    (callee : NPOracleProgram) (calleeBits maximumBits : ℕ)
    (calleeFuel : ℕ → ℕ)
    (hbits :
      fourfoldRangeComponentBits calleeBits rows request mode envelopeCode ≤
        maximumBits)
    (hpackerBits :
      canonicalRatioPackerBits (rows.aggregation request).acceptanceCount
          (fourfoldRangeDenominatorTail rows request) ≤ maximumBits)
    (hlength : natBitLength request.q ≤ maximumBits)
    (hpositive : 1 ≤ maximumBits)
    (hexec : ∀ flat : ℕ, flat < fourfoldRangeAtomCount rows request →
      runNPOracleProgram callee calleeBits
          (calleeFuel
            (balancedRangeRequestAtom request.q flat
              (fourfoldRangeCallContext rows request mode envelopeCode)))
          (initialNPOracleState request.q
            (fourfoldRangeCallAtom rows request mode envelopeCode flat)) =
        some (boolCode (fourfoldFlatRowValue rows request flat))) :
    runNPOracleProgram (fourfoldRangePackedProgram callee) maximumBits
        (fourfoldRangePackedFuel callee calleeFuel rows request mode
          envelopeCode)
        (initialNPOracleState request.q
          (generatedBalancedRangeInput (fourfoldRangeAtomCount rows request)
            (fourfoldRangeCallContext rows request mode envelopeCode))) =
      some
        (canonicalRatioPackerOutput
          (rows.aggregation request).acceptanceCount
          (fourfoldRangeDenominatorTail rows request)) := by
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_fourfoldRangeComponentProgram_of_rowCallee rows request mode
        envelopeCode callee calleeBits calleeFuel hexec)
      hbits
  · exact run_canonicalRatioPackerProgram _ _ request.q maximumBits
      hpackerBits

/-! ## §4 The two published specializations

These are the exact statements the artifact's `computesSymmetric` and
`computesThreshold` fields consume once a row callee exists; the remaining
open obligation is entirely inside `hexec`. -/

theorem run_symmetricFourfoldRangeComponentProgram_of_rowCallee
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (callee : NPOracleProgram) (calleeBits : ℕ) (calleeFuel : ℕ → ℕ)
    (hexec : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request →
      runNPOracleProgram callee calleeBits
          (calleeFuel
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
              request flat))) :
    runNPOracleProgram (fixedBooleanRangeComponentProgram callee)
        (fourfoldRangeComponentBits calleeBits
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request .symmetric
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request))
        (fourfoldRangeComponentFuel callee calleeFuel
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request .symmetric
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request))
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
  run_fourfoldRangeComponentProgram_of_rowCallee _ request .symmetric _
    callee calleeBits calleeFuel hexec

theorem run_thresholdFourfoldRangeComponentProgram_of_rowCallee
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (callee : NPOracleProgram) (calleeBits : ℕ) (calleeFuel : ℕ → ℕ)
    (hexec : ∀ flat : ℕ,
      flat <
        fourfoldRangeAtomCount
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request →
      runNPOracleProgram callee calleeBits
          (calleeFuel
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
              request flat))) :
    runNPOracleProgram (fixedBooleanRangeComponentProgram callee)
        (fourfoldRangeComponentBits calleeBits
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request .threshold
          (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
            encodeNormalizedThresholdThresholdCircuit request))
        (fourfoldRangeComponentFuel callee calleeFuel
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request .threshold
          (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
            encodeNormalizedThresholdThresholdCircuit request))
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
  run_fourfoldRangeComponentProgram_of_rowCallee _ request .threshold _
    callee calleeBits calleeFuel hexec

/-! ## §5 Linking the existing exact-bottom prefix

The residual obligation is now localized.  `fourfoldRangeBottomProgram`
already lowers a canonical range atom to the exact bottom forest, so the only
missing machine is a *row tail*: one program from the exact bottom package to
the Boolean row code.  This section proves that such a tail is exactly what
`hexec` needs — no other seam remains between the published rows and the
aggregation controller. -/

private theorem rowBitInputOfCode_mod_two_pow (width value : ℕ) :
    rowBitInputOfCode width (value % 2 ^ width) =
      bitInputPrefixView width value := by
  funext bit
  unfold rowBitInputOfCode bitInputPrefixView
  rw [Nat.testBit_mod_two_pow]
  simp [bit.isLt]

private theorem fourfoldFlatCoordinate_fst
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit)
    (flat : Fin (rows.rowCount request * 2 ^ request.q)) :
    (((fourfoldFlatCoordinateEquiv rows request).symm flat).1 : ℕ) =
      flat.val / 2 ^ request.q :=
  rfl

private theorem fourfoldFlatCoordinate_snd
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit)
    (flat : Fin (rows.rowCount request * 2 ^ request.q)) :
    ((fourfoldFlatCoordinateEquiv rows request).symm flat).2 =
      bitInputPrefixView request.q flat.val :=
  rowBitInputOfCode_mod_two_pow request.q flat.val

/-- Every row index actually emitted by the flat range controller lies in the
finite published row family.  This is the honest domain for row-tail resource
ledgers; the raw natural index outside this range is never called. -/
theorem flat_shiftRight_lt_rowCount
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) (flat : ℕ)
    (hflat : flat < fourfoldRangeAtomCount rows request) :
    flat >>> request.q < rows.rowCount request := by
  rw [Nat.shiftRight_eq_div_pow]
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ request.q)).2
  exact hflat

set_option maxHeartbeats 1600000 in
-- Unfolding the published preprocessor through its extensional row
-- replacement is kernel-heavy; the equality itself is definitional.
/-- The published symmetric row family is the executable row evaluator; this
is the only place the identification is used. -/
private theorem publishedSymmetricRows_row
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (index :
      Fin ((publishedSymmetricRows contracts liveScale
        accuracyExponent).rowCount request))
    (input : BitInput request.q) :
    (publishedSymmetricRows contracts liveScale accuracyExponent).row request
        index input =
      evaluateCanonicalFourfoldRow
        (selectedExactDecompositionAlgorithm contracts) liveScale
        accuracyExponent
        (symmetricFourfoldRowRequest request index.val input) :=
  rfl

/-- Row-major decoding of one flat range index into the exact row-request
coordinates used by `fourfoldRangeBottomProgram`. -/
theorem publishedSymmetricRows_flatRowValue
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (flat : ℕ)
    (hflat :
      flat <
        fourfoldRangeAtomCount
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request) :
    fourfoldFlatRowValue
        (publishedSymmetricRows contracts liveScale accuracyExponent) request
        flat =
      evaluateCanonicalFourfoldRow
        (selectedExactDecompositionAlgorithm contracts) liveScale
        accuracyExponent
        (symmetricFourfoldRowRequest request (flat >>> request.q)
          (bitInputPrefixView request.q flat)) := by
  have hflatRaw :
      flat <
        (publishedSymmetricRows contracts liveScale
          accuracyExponent).rowCount request * 2 ^ request.q :=
    hflat
  unfold fourfoldFlatRowValue
  rw [dif_pos hflatRaw]
  dsimp only
  rw [publishedSymmetricRows_row contracts liveScale accuracyExponent request
    _ _]
  rw [fourfoldFlatCoordinate_fst
    (publishedSymmetricRows contracts liveScale accuracyExponent) request
    ⟨flat, hflatRaw⟩]
  rw [fourfoldFlatCoordinate_snd
    (publishedSymmetricRows contracts liveScale accuracyExponent) request
    ⟨flat, hflatRaw⟩]
  rw [Nat.shiftRight_eq_div_pow]

/-- Fuel of the linked callee at one flat index. -/
noncomputable def symmetricRowCalleeFuel
    (contracts : PublishedContracts)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowTail : NPOracleProgram) (tailFuel : ℕ → ℕ) (flat : ℕ) : ℕ :=
  linkFuel rowTail
    (symmetricFourfoldRangeBottomFuel
      (selectedExactDecompositionAlgorithm contracts) request flat)
    (tailFuel
      (symmetricFourfoldRowBottomOutput
        (selectedExactDecompositionAlgorithm contracts) request
        (flat >>> request.q) (bitInputPrefixView request.q flat)))

/-- **The residual obligation, named.**  Given one row tail with exact
semantics on the exact-bottom package, the linked callee satisfies precisely
the `hexec` premise of the aggregation composition. -/
theorem run_symmetricRowCalleeProgram_of_rowTail
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowTail : NPOracleProgram) (calleeBits : ℕ) (tailFuel : ℕ → ℕ)
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
    (htail : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowTail calleeBits
          (tailFuel
            (symmetricFourfoldRowBottomOutput
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowBottomOutput
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
        (linkPrograms
          (fourfoldRangeBottomProgram
            (selectedExactDecompositionAlgorithm contracts)) rowTail)
        calleeBits
        (symmetricRowCalleeFuel contracts request rowTail tailFuel flat)
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
  rw [publishedSymmetricRows_flatRowValue contracts liveScale accuracyExponent
    request flat hflat]
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_fourfoldRangeBottomProgram_symmetric
        (selectedExactDecompositionAlgorithm contracts) request flat
        (fourfoldRangeDenominatorTail
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request))
      (hbottomBits flat hflat)
  · exact htail (flat >>> request.q) (bitInputPrefixView request.q flat)

/-- The symmetric row-callee closure with the row-tail contract restricted to
the finite row indices that the controller can actually emit. -/
theorem run_symmetricRowCalleeProgram_of_boundedRowTail
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowTail : NPOracleProgram) (calleeBits : ℕ) (tailFuel : ℕ → ℕ)
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
    (htail : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      rowIndex <
          (publishedSymmetricRows contracts liveScale
            accuracyExponent).rowCount request →
      runNPOracleProgram rowTail calleeBits
          (tailFuel
            (symmetricFourfoldRowBottomOutput
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (symmetricFourfoldRowBottomOutput
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
        (linkPrograms
          (fourfoldRangeBottomProgram
            (selectedExactDecompositionAlgorithm contracts)) rowTail)
        calleeBits
        (symmetricRowCalleeFuel contracts request rowTail tailFuel flat)
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
  rw [publishedSymmetricRows_flatRowValue contracts liveScale accuracyExponent
    request flat hflat]
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_fourfoldRangeBottomProgram_symmetric
        (selectedExactDecompositionAlgorithm contracts) request flat
        (fourfoldRangeDenominatorTail
          (publishedSymmetricRows contracts liveScale accuracyExponent)
          request))
      (hbottomBits flat hflat)
  · exact htail (flat >>> request.q) (bitInputPrefixView request.q flat)
      (flat_shiftRight_lt_rowCount
        (publishedSymmetricRows contracts liveScale accuracyExponent) request
        flat hflat)

set_option maxHeartbeats 1600000 in
-- Same definitional unfolding as the symmetric case, through the dependent
-- prime/list replacement.
private theorem publishedThresholdRows_row
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (index :
      Fin ((publishedThresholdRows contracts liveScale
        accuracyExponent).rowCount request))
    (input : BitInput request.q) :
    (publishedThresholdRows contracts liveScale accuracyExponent).row request
        index input =
      evaluateCanonicalFourfoldRow
        (selectedExactDecompositionAlgorithm contracts) liveScale
        accuracyExponent
        (thresholdFourfoldRowRequest request index.val input) :=
  rfl

theorem publishedThresholdRows_flatRowValue
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (flat : ℕ)
    (hflat :
      flat <
        fourfoldRangeAtomCount
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request) :
    fourfoldFlatRowValue
        (publishedThresholdRows contracts liveScale accuracyExponent) request
        flat =
      evaluateCanonicalFourfoldRow
        (selectedExactDecompositionAlgorithm contracts) liveScale
        accuracyExponent
        (thresholdFourfoldRowRequest request (flat >>> request.q)
          (bitInputPrefixView request.q flat)) := by
  have hflatRaw :
      flat <
        (publishedThresholdRows contracts liveScale
          accuracyExponent).rowCount request * 2 ^ request.q :=
    hflat
  unfold fourfoldFlatRowValue
  rw [dif_pos hflatRaw]
  dsimp only
  rw [publishedThresholdRows_row contracts liveScale accuracyExponent request
    _ _]
  rw [fourfoldFlatCoordinate_fst
    (publishedThresholdRows contracts liveScale accuracyExponent) request
    ⟨flat, hflatRaw⟩]
  rw [fourfoldFlatCoordinate_snd
    (publishedThresholdRows contracts liveScale accuracyExponent) request
    ⟨flat, hflatRaw⟩]
  rw [Nat.shiftRight_eq_div_pow]

noncomputable def thresholdRowCalleeFuel
    (contracts : PublishedContracts)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowTail : NPOracleProgram) (tailFuel : ℕ → ℕ) (flat : ℕ) : ℕ :=
  linkFuel rowTail
    (thresholdFourfoldRangeBottomFuel
      (selectedExactDecompositionAlgorithm contracts) request flat)
    (tailFuel
      (thresholdFourfoldRowBottomOutput
        (selectedExactDecompositionAlgorithm contracts) request
        (flat >>> request.q) (bitInputPrefixView request.q flat)))

theorem run_thresholdRowCalleeProgram_of_rowTail
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowTail : NPOracleProgram) (calleeBits : ℕ) (tailFuel : ℕ → ℕ)
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
    (htail : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      runNPOracleProgram rowTail calleeBits
          (tailFuel
            (thresholdFourfoldRowBottomOutput
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowBottomOutput
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
        (linkPrograms
          (fourfoldRangeBottomProgram
            (selectedExactDecompositionAlgorithm contracts)) rowTail)
        calleeBits
        (thresholdRowCalleeFuel contracts request rowTail tailFuel flat)
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
  rw [publishedThresholdRows_flatRowValue contracts liveScale accuracyExponent
    request flat hflat]
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_fourfoldRangeBottomProgram_threshold
        (selectedExactDecompositionAlgorithm contracts) request flat
        (fourfoldRangeDenominatorTail
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request))
      (hbottomBits flat hflat)
  · exact htail (flat >>> request.q) (bitInputPrefixView request.q flat)

/-- Threshold twin of `run_symmetricRowCalleeProgram_of_boundedRowTail`. -/
theorem run_thresholdRowCalleeProgram_of_boundedRowTail
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowTail : NPOracleProgram) (calleeBits : ℕ) (tailFuel : ℕ → ℕ)
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
    (htail : ∀ (rowIndex : ℕ) (input : BitInput request.q),
      rowIndex <
          (publishedThresholdRows contracts liveScale
            accuracyExponent).rowCount request →
      runNPOracleProgram rowTail calleeBits
          (tailFuel
            (thresholdFourfoldRowBottomOutput
              (selectedExactDecompositionAlgorithm contracts) request
              rowIndex input))
          (initialNPOracleState request.q
            (thresholdFourfoldRowBottomOutput
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
        (linkPrograms
          (fourfoldRangeBottomProgram
            (selectedExactDecompositionAlgorithm contracts)) rowTail)
        calleeBits
        (thresholdRowCalleeFuel contracts request rowTail tailFuel flat)
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
  rw [publishedThresholdRows_flatRowValue contracts liveScale accuracyExponent
    request flat hflat]
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_fourfoldRangeBottomProgram_threshold
        (selectedExactDecompositionAlgorithm contracts) request flat
        (fourfoldRangeDenominatorTail
          (publishedThresholdRows contracts liveScale accuracyExponent)
          request))
      (hbottomBits flat hflat)
  · exact htail (flat >>> request.q) (bitInputPrefixView request.q flat)
      (flat_shiftRight_lt_rowCount
        (publishedThresholdRows contracts liveScale accuracyExponent) request
        flat hflat)

end NearCubicWires.FourfoldRangeAggregationComposition
