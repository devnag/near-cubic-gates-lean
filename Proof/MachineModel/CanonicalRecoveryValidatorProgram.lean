import Proof.MachineModel.CanonicalRecoveryProgram
import Proof.Amplification.CanonicalRecoveryInterpreter
import Proof.MachineModel.CanonicalBalancedLengthProgram
import Proof.Circuits.CanonicalBalancedTraversal
import Proof.MachineModel.CanonicalBalancedValidationMapProgram
import Proof.MachineModel.CanonicalBinaryArithmeticProgram
import Proof.MachineModel.CanonicalBooleanCircuitValidationProgram
import Proof.MachineModel.CanonicalLegalTermValidationProgram
import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.MachineModel.CanonicalNativeEqualityProgram
import Proof.MachineModel.CanonicalNatBitCapProgram
import Proof.MachineModel.CanonicalNatValidationProgram
import Proof.MachineModel.CanonicalNormalizedCircuitDescriptionProgram
import Proof.MachineModel.CanonicalNormalizedCircuitResourceProgram
import Proof.MachineModel.CanonicalNormalizedCircuitValidationProgram
import Proof.Circuits.CanonicalPairedCall
import Proof.MachineModel.CanonicalRationalMassProgram
import Proof.MachineModel.CanonicalTaggedTupleProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.Foundations.VerifiedLinker

/-!
# Canonical executable recovery-witness validator construction

The weak verifier receives an untrusted canonical witness code.  Its limits are
trusted configuration derived from the public input arity by the surrounding
schedule controller.  The internal linked stages carry that derived value
through registers so the parser has one uniform ABI; it is not an additional
field of the public weak witness.

No decoded object, validity bit, validation formula, or expected output is
present in the request.  In particular, the limits encoding below contains only
the fields of `RecoveryWitnessLimits`; all nested canonicality and resource
checks are performed by the register program.
-/

namespace NearCubicWires.CanonicalRecoveryValidatorProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalLegalTermValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalNatBitCapProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalNormalizedCircuitDescriptionProgram
open NearCubicWires.CanonicalNormalizedCircuitResourceProgram
open NearCubicWires.CanonicalNormalizedCircuitValidationProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalRationalMassProgram
open NearCubicWires.CanonicalRationalValidationProgram
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalSupportedGateRelationProgram
open NearCubicWires.CanonicalSupplierCompressedGateProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

private theorem member_le_foldr_max
    {value : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hvalue
  | cons head tail ih =>
      simp only [List.foldr]
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact le_max_left _ _
      · exact (ih htail).trans (le_max_right _ _)

/-! ## Validated-summary bridge to the wire and description programs

The staged validator's per-term circuit call emits the unique public
normalized-circuit validator output.  The compiled wire and description
programs consume that same value through their shared projection ABI, so their
hypotheses have to be discharged once, here, from validator acceptance alone.

Every statement below is conditional on the owning gate having accepted: a
rejected term never reaches a projection, so no sentinel is unpaired.  Nothing
in this section re-decodes circuit syntax or introduces a second validator
path; the typed refinements consume the existing canonical codecs. -/

private theorem supportedGateZeroOutside_forall₂
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    List.Forall₂ (fun weight bit => bit = false → weight = 0)
      (List.ofFn gate.gate.weight)
      (List.ofFn fun index : Fin inputLength =>
        decide (index ∈ gate.support)) := by
  apply List.forall₂_of_length_eq_of_get
  · simp
  · intro index hweights hmembership
    simp only [List.get_ofFn]
    intro hfalse
    apply gate.zeroOutside
    simpa using hfalse

/-- The accepted per-gate summary of a canonically encoded normalized gate,
expanded to its stored compressed payload. -/
private theorem supportedGateRelationOutput_encode_eq
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    supportedGateRelationOutput inputLength
        (encodeSupportedNormalizedGate gate) =
      Nat.pair 1
        (supportedGateCompressedPayload (encodeInt gate.gate.threshold)
          (encodeBalancedList
            (supportedWeights ((List.ofFn gate.gate.weight).map encodeInt)
              (List.ofFn fun index => decide (index ∈ gate.support))))
          (nonzeroSupportCount
            (List.ofFn fun index => decide (index ∈ gate.support)))
          (encodeBoolList
            (List.ofFn fun index => decide (index ∈ gate.support)))) :=
  supportedGateRelationOutput_eq_of_fields inputLength
    (encodeSupportedNormalizedGate gate)
    (encodeIntList (List.ofFn gate.gate.weight))
    (encodeInt gate.gate.threshold)
    (encodeBoolList
      (List.ofFn fun index => decide (index ∈ gate.support)))
    (List.ofFn gate.gate.weight) gate.gate.threshold
    (List.ofFn fun index => decide (index ∈ gate.support))
    (by simp [encodeSupportedNormalizedGate])
    (by simp) (by simp) (by simp) (by simp) (by simp)
    (supportedGateZeroOutside_forall₂ gate)

/-- The stored top-gate membership bitmap of an accepted gate summary. -/
private theorem supportedGateRelationOutput_membershipCode
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    (Nat.unpair (Nat.unpair (Nat.unpair
      (Nat.unpair
        (supportedGateRelationOutput inputLength
          (encodeSupportedNormalizedGate gate))).2).2).2).2 =
      encodeBoolList
        (List.ofFn fun index => decide (index ∈ gate.support)) := by
  rw [supportedGateRelationOutput_encode_eq gate]
  simp [supportedGateCompressedPayload]

private theorem supportedGateRelationOutput_encode_thresholdCode
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    normalizedGateDescriptionThresholdCode
        (supportedGateRelationOutput inputLength
          (encodeSupportedNormalizedGate gate)) =
      encodeInt gate.gate.threshold := by
  rw [supportedGateRelationOutput_encode_eq gate]
  simp only [normalizedGateDescriptionThresholdCode,
    supportedGateCompressedPayload, Nat.unpair_pair]

private theorem supportedGateRelationOutput_encode_selectedWeightsCode
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    normalizedGateDescriptionSelectedWeightsCode
        (supportedGateRelationOutput inputLength
          (encodeSupportedNormalizedGate gate)) =
      encodeIntList (List.ofFn (supportCompressedGate gate).weight) := by
  rw [supportedGateRelationOutput_encode_eq gate,
    supportedWeights_eq_supportCompressedGate gate]
  simp only [normalizedGateDescriptionSelectedWeightsCode,
    supportedGateCompressedPayload, Nat.unpair_pair, encodeIntList]

private theorem supportedGateRelationOutput_encode_canonical
    {inputLength : ℕ} (gate : SupportedNormalizedGate inputLength) :
    normalizedGateDescriptionThresholdCode
        (supportedGateRelationOutput inputLength
          (encodeSupportedNormalizedGate gate)) =
        encodeInt
          (normalizedGateDescriptionThreshold
            (supportedGateRelationOutput inputLength
              (encodeSupportedNormalizedGate gate))) ∧
      normalizedGateDescriptionSelectedWeightsCode
          (supportedGateRelationOutput inputLength
            (encodeSupportedNormalizedGate gate)) =
        encodeIntList
          (normalizedGateDescriptionSelectedWeights
            (supportedGateRelationOutput inputLength
              (encodeSupportedNormalizedGate gate))) := by
  constructor
  · rw [normalizedGateDescriptionThreshold,
      supportedGateRelationOutput_encode_thresholdCode gate,
      decodeInt_encode, Option.getD_some]
  · rw [normalizedGateDescriptionSelectedWeights,
      supportedGateRelationOutput_encode_selectedWeightsCode gate,
      decodeIntList_encode, Option.getD_some]

/-- Every summary retained by an accepting normalized-circuit validation is a
canonical gate description, so the compiled description program applies. -/
theorem normalizedCircuitBottomOutputs_canonical_of_headerTag
    {inputLength request : ℕ}
    (htag : normalizedCircuitHeaderTag inputLength request ≠ 0) :
    NormalizedGateDescriptionSummariesCanonical
      (normalizedCircuitBottomOutputs inputLength request) := by
  rw [NormalizedGateDescriptionSummariesCanonical]
  refine fun summary hsummary => ?_
  obtain ⟨gate, hgate⟩ :=
    normalizedCircuitBottomOutputs_mem_of_headerTag htag hsummary
  rw [hgate]
  exact supportedGateRelationOutput_encode_canonical gate

/-- The resource ABI is a pure projection of the validator's paired output, so
its four accessors are computed once on the abstract shape. -/
private theorem normalizedCircuitResourceProjections_pair
    (familyTag topSummary summariesCode bottomLength bottomTree raw : ℕ) :
    normalizedCircuitResourceFamilyTag
        (Nat.pair familyTag
          (Nat.pair topSummary
            (Nat.pair
              (Nat.pair summariesCode (Nat.pair bottomLength bottomTree))
              raw))) = familyTag ∧
      normalizedCircuitResourceTopSummary
          (Nat.pair familyTag
            (Nat.pair topSummary
              (Nat.pair
                (Nat.pair summariesCode (Nat.pair bottomLength bottomTree))
                raw))) = topSummary ∧
      normalizedCircuitResourceBottomSummariesCode
          (Nat.pair familyTag
            (Nat.pair topSummary
              (Nat.pair
                (Nat.pair summariesCode (Nat.pair bottomLength bottomTree))
                raw))) = summariesCode ∧
      normalizedCircuitResourceBottomLength
          (Nat.pair familyTag
            (Nat.pair topSummary
              (Nat.pair
                (Nat.pair summariesCode (Nat.pair bottomLength bottomTree))
                raw))) = bottomLength := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [normalizedCircuitResourceFamilyTag,
      normalizedCircuitResourcePayload,
      normalizedCircuitResourceTopSummary,
      normalizedCircuitResourceBottomAndRaw,
      normalizedCircuitResourceBottomSummaryData,
      normalizedCircuitResourceBottomSummariesCode,
      normalizedCircuitResourceBottomMetadata,
      normalizedCircuitResourceBottomLength, Nat.unpair_pair]

private theorem normalizedCircuitResourceMembership_pair
    (familyTag topSummary payload : ℕ) :
    normalizedCircuitResourceThresholdMembershipCode
        (Nat.pair familyTag (Nat.pair topSummary payload)) =
      (Nat.unpair
        (Nat.unpair (Nat.unpair (Nat.unpair topSummary).2).2).2).2 := by
  simp only [normalizedCircuitResourceThresholdMembershipCode,
    normalizedCircuitResourceThresholdCountMembership,
    normalizedCircuitResourceThresholdSelectedTail,
    normalizedCircuitResourceTopPayload,
    normalizedCircuitResourceTopSummary,
    normalizedCircuitResourcePayload, Nat.unpair_pair]

private theorem normalizedCircuitHeaderTag_ne_zero_of_ne_zero
    {inputLength request : ℕ}
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0) :
    normalizedCircuitHeaderTag inputLength request ≠ 0 := by
  rcases
      (normalizedCircuitValidationOutput_ne_zero_iff_branches
        inputLength request).1 hvalid with
    ⟨htag, _⟩ | ⟨htag, _⟩
  · rw [htag]; exact Nat.one_ne_zero
  · rw [htag]; exact Nat.succ_ne_zero 1

private theorem normalizedSymmetricValidationOutput_ne_zero_of_tag
    {inputLength request : ℕ}
    (htag : normalizedCircuitHeaderTag inputLength request = 1)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0) :
    normalizedSymmetricValidationOutput inputLength request ≠ 0 := by
  rcases
      (normalizedCircuitValidationOutput_ne_zero_iff_branches
        inputLength request).1 hvalid with
    ⟨_, hsymmetric⟩ | ⟨htwo, _⟩
  · exact hsymmetric
  · rw [htag] at htwo
    exact absurd htwo (by decide)

private theorem normalizedThresholdValidationOutput_ne_zero_of_tag
    {inputLength request : ℕ}
    (htag : normalizedCircuitHeaderTag inputLength request = 2)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0) :
    normalizedThresholdValidationOutput inputLength request ≠ 0 := by
  rcases
      (normalizedCircuitValidationOutput_ne_zero_iff_branches
        inputLength request).1 hvalid with
    ⟨hone, _⟩ | ⟨_, hthreshold⟩
  · rw [htag] at hone
    exact absurd hone (by decide)
  · exact hthreshold

private theorem normalizedCircuitValidationOutput_shape
    {inputLength request : ℕ}
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0) :
    ∃ topSummary,
      normalizedCircuitValidationOutput inputLength request =
        Nat.pair (normalizedCircuitHeaderTag inputLength request)
          (Nat.pair topSummary
            (Nat.pair
              (Nat.pair
                (encodeBalancedList
                  (normalizedCircuitBottomOutputs inputLength request))
                (Nat.pair
                  (normalizedCircuitBottomOutputs inputLength request).length
                  (normalizedCircuitBottomCode request)))
              (normalizedCircuitRawCode request))) := by
  have hdata :=
    normalizedCircuitBottomSummaryData_eq_of_headerTag
      (normalizedCircuitHeaderTag_ne_zero_of_ne_zero hvalid)
  rcases
      (normalizedCircuitValidationOutput_ne_zero_iff_branches
        inputLength request).1 hvalid with
    ⟨htag, hbranch⟩ | ⟨htag, hbranch⟩
  · refine ⟨normalizedSymmetricTopSummaryOutput inputLength request, ?_⟩
    rw [normalizedCircuitValidationOutput_eq_symmetric htag hbranch, htag,
      hdata]
  · refine ⟨normalizedThresholdTopResult request, ?_⟩
    rw [normalizedCircuitValidationOutput_eq_threshold htag hbranch, htag,
      hdata]

private theorem normalizedCircuitValidationOutput_resourceProjections
    {inputLength request : ℕ}
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0) :
    normalizedCircuitResourceFamilyTag
        (normalizedCircuitValidationOutput inputLength request) =
      normalizedCircuitHeaderTag inputLength request ∧
    normalizedCircuitResourceBottomSummariesCode
        (normalizedCircuitValidationOutput inputLength request) =
      encodeBalancedList
        (normalizedCircuitBottomOutputs inputLength request) ∧
    normalizedCircuitResourceBottomLength
        (normalizedCircuitValidationOutput inputLength request) =
      (normalizedCircuitBottomOutputs inputLength request).length := by
  obtain ⟨topSummary, hshape⟩ :=
    normalizedCircuitValidationOutput_shape hvalid
  obtain ⟨hfamily, _, hcode, hlength⟩ :=
    normalizedCircuitResourceProjections_pair
      (normalizedCircuitHeaderTag inputLength request) topSummary
      (encodeBalancedList
        (normalizedCircuitBottomOutputs inputLength request))
      (normalizedCircuitBottomOutputs inputLength request).length
      (normalizedCircuitBottomCode request)
      (normalizedCircuitRawCode request)
  rw [hshape]
  exact ⟨hfamily, hcode, hlength⟩

/-- The unique validator output already carries a decodable, exactly measured,
canonical bottom-summary list.  This is the single hypothesis bundle the
compiled wire and description programs require. -/
theorem normalizedCircuitValidationOutput_summaries_of_ne_zero
    (inputLength request : ℕ)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0) :
    ∃ summaries,
      decodeBalancedList
          (normalizedCircuitResourceBottomSummariesCode
            (normalizedCircuitValidationOutput inputLength request)) =
        some summaries ∧
      normalizedCircuitResourceBottomLength
          (normalizedCircuitValidationOutput inputLength request) =
        summaries.length ∧
      NormalizedGateDescriptionSummariesCanonical summaries := by
  obtain ⟨_, hcode, hlength⟩ :=
    normalizedCircuitValidationOutput_resourceProjections hvalid
  exact
    ⟨normalizedCircuitBottomOutputs inputLength request,
      by rw [hcode, decodeBalancedList_encode], hlength,
      normalizedCircuitBottomOutputs_canonical_of_headerTag
        (normalizedCircuitHeaderTag_ne_zero_of_ne_zero hvalid)⟩

/-- Threshold companion: the accepted top gate's support bitmap is retained in
the same ABI, and its width matches the retained bottom-summary count. -/
theorem normalizedCircuitValidationOutput_thresholdSummaries_of_ne_zero
    (inputLength request : ℕ)
    (htag : normalizedCircuitHeaderTag inputLength request = 2)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0) :
    ∃ summaries membership,
      decodeBalancedList
          (normalizedCircuitResourceBottomSummariesCode
            (normalizedCircuitValidationOutput inputLength request)) =
        some summaries ∧
      decodeBoolList
          (normalizedCircuitResourceThresholdMembershipCode
            (normalizedCircuitValidationOutput inputLength request)) =
        some membership ∧
      normalizedCircuitResourceBottomLength
          (normalizedCircuitValidationOutput inputLength request) =
        summaries.length ∧
      summaries.length = membership.length ∧
      NormalizedGateDescriptionSummariesCanonical summaries := by
  have hnonzero : normalizedCircuitHeaderTag inputLength request ≠ 0 :=
    normalizedCircuitHeaderTag_ne_zero_of_ne_zero hvalid
  obtain ⟨_, hcode, hlength⟩ :=
    normalizedCircuitValidationOutput_resourceProjections hvalid
  have hbranch :=
    normalizedThresholdValidationOutput_ne_zero_of_tag htag hvalid
  obtain ⟨gate, hgate⟩ :=
    Option.isSome_iff_exists.mp
      ((normalizedThresholdValidationOutput_ne_zero_iff
        inputLength request).1 hbranch)
  have hencode : encodeSupportedNormalizedGate gate =
      normalizedCircuitTopCode request :=
    encodeSupportedNormalizedGate_of_decode hgate
  have hmembershipCode :
      normalizedCircuitResourceThresholdMembershipCode
          (normalizedCircuitValidationOutput inputLength request) =
        encodeBoolList
          (List.ofFn fun index => decide (index ∈ gate.support)) := by
    rw [normalizedCircuitValidationOutput_eq_threshold htag hbranch,
      normalizedCircuitResourceMembership_pair,
      normalizedThresholdTopResult, ← hencode]
    exact supportedGateRelationOutput_membershipCode gate
  refine
    ⟨normalizedCircuitBottomOutputs inputLength request,
      List.ofFn fun index => decide (index ∈ gate.support),
      by rw [hcode, decodeBalancedList_encode],
      by rw [hmembershipCode, decodeBoolList_encode], hlength, ?_,
      normalizedCircuitBottomOutputs_canonical_of_headerTag hnonzero⟩
  rw [← normalizedCircuitCountValue_eq_bottomOutputs_length_of_headerTag
    hnonzero, List.length_ofFn]

/-! ### Exact wire and description semantics of one validated term

These are the two resource coordinates the staged validator still had to reach.
For an accepted term the compiled wire program returns the selected circuit's
exact physical wire count and the compiled description program returns its exact
encoding length, both computed from the retained summary ABI alone. -/

private theorem normalizedCircuitBottomOutputs_eq_validatedSummaries_symmetric
    {inputLength request : ℕ}
    {circuit : NormalizedSymmetricThresholdCircuit inputLength}
    (hdecode :
      decodeNormalizedSymmetricThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitBottomOutputs inputLength request =
      normalizedBottomValidatedSummaries circuit.bottom := by
  rw [normalizedCircuitBottomOutputs_eq_of_symmetric_decode hdecode]
  simp only [normalizedBottomValidatedSummaries,
    normalizedGateValidatedSummary]

private theorem normalizedCircuitBottomOutputs_eq_validatedSummaries_threshold
    {inputLength request : ℕ}
    {circuit : NormalizedThresholdThresholdCircuit inputLength}
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitBottomOutputs inputLength request =
      normalizedBottomValidatedSummaries circuit.bottom := by
  rw [normalizedCircuitBottomOutputs_eq_of_threshold_decode hdecode]
  simp only [normalizedBottomValidatedSummaries,
    normalizedGateValidatedSummary]

private theorem normalizedCircuitValidationOutput_topSummary_threshold
    {inputLength request : ℕ}
    {circuit : NormalizedThresholdThresholdCircuit inputLength}
    (htag : normalizedCircuitHeaderTag inputLength request = 2)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0)
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitResourceTopSummary
        (normalizedCircuitValidationOutput inputLength request) =
      normalizedGateValidatedSummary circuit.top := by
  have hbranch :=
    normalizedThresholdValidationOutput_ne_zero_of_tag htag hvalid
  rw [normalizedCircuitValidationOutput_eq_threshold htag hbranch]
  simp only [normalizedCircuitResourceTopSummary,
    normalizedCircuitResourcePayload, Nat.unpair_pair]
  rw [normalizedThresholdTopResult,
    (normalizedCircuitFields_of_threshold_decode hdecode).2.2,
    normalizedCircuitCountValue_eq_of_threshold_decode hdecode,
    normalizedGateValidatedSummary]

/-- The unique validator output refines to the selected symmetric circuit's
exact physical wire count. -/
theorem normalizedCircuitValidationOutput_resourceMetric_eq_symmetricWireCount
    {inputLength request : ℕ}
    {circuit : NormalizedSymmetricThresholdCircuit inputLength}
    (htag : normalizedCircuitHeaderTag inputLength request = 1)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0)
    (hdecode :
      decodeNormalizedSymmetricThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitResourceMetric
        (normalizedCircuitValidationOutput inputLength request) =
      circuit.wireCount := by
  obtain ⟨hfamily, hcode, _⟩ :=
    normalizedCircuitValidationOutput_resourceProjections hvalid
  exact normalizedCircuitResourceMetric_eq_symmetricWireCount
    (normalizedCircuitValidationOutput inputLength request) circuit
    (by rw [hfamily, htag])
    (by
      rw [hcode, normalizedCircuitBottomOutputs_eq_of_symmetric_decode hdecode,
        decodeBalancedList_encode])

/-- The unique validator output refines to the selected threshold circuit's
exact support-selected physical wire count. -/
theorem normalizedCircuitValidationOutput_resourceMetric_eq_thresholdWireCount
    {inputLength request : ℕ}
    {circuit : NormalizedThresholdThresholdCircuit inputLength}
    (htag : normalizedCircuitHeaderTag inputLength request = 2)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0)
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitResourceMetric
        (normalizedCircuitValidationOutput inputLength request) =
      circuit.wireCount := by
  obtain ⟨hfamily, hcode, _⟩ :=
    normalizedCircuitValidationOutput_resourceProjections hvalid
  have hbranch :=
    normalizedThresholdValidationOutput_ne_zero_of_tag htag hvalid
  have hmembership :
      normalizedCircuitResourceThresholdMembershipCode
          (normalizedCircuitValidationOutput inputLength request) =
        encodeBoolList
          (List.ofFn fun index => decide (index ∈ circuit.top.support)) := by
    rw [normalizedCircuitValidationOutput_eq_threshold htag hbranch,
      normalizedCircuitResourceMembership_pair, normalizedThresholdTopResult,
      (normalizedCircuitFields_of_threshold_decode hdecode).2.2,
      normalizedCircuitCountValue_eq_of_threshold_decode hdecode]
    exact supportedGateRelationOutput_membershipCode circuit.top
  exact normalizedCircuitResourceMetric_eq_thresholdWireCount
    (normalizedCircuitValidationOutput inputLength request) circuit
    (by rw [hfamily, htag])
    (by
      rw [hcode, normalizedCircuitBottomOutputs_eq_of_threshold_decode hdecode,
        decodeBalancedList_encode])
    (by rw [hmembership, decodeBoolList_encode])

/-- The unique validator output refines to the selected symmetric circuit's
exact description length, including every omitted zero coefficient. -/
theorem normalizedCircuitValidationOutput_descriptionMetric_eq_symmetric
    {inputLength request : ℕ}
    {circuit : NormalizedSymmetricThresholdCircuit inputLength}
    (htag : normalizedCircuitHeaderTag inputLength request = 1)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0)
    (hdecode :
      decodeNormalizedSymmetricThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitDescriptionMetric inputLength
        (normalizedCircuitValidationOutput inputLength request) =
      circuit.descriptionBits := by
  obtain ⟨hfamily, hcode, hlength⟩ :=
    normalizedCircuitValidationOutput_resourceProjections hvalid
  refine normalizedCircuitDescriptionMetric_refines_symmetric
    (normalizedCircuitValidationOutput inputLength request) circuit
    (by rw [hfamily, htag]) ?_ ?_
  · rw [hcode,
      normalizedCircuitBottomOutputs_eq_validatedSummaries_symmetric hdecode]
  · rw [hlength,
      normalizedCircuitBottomOutputs_eq_of_symmetric_decode hdecode,
      List.length_ofFn]

/-- The unique validator output refines to the selected threshold circuit's
exact description length, top gate included. -/
theorem normalizedCircuitValidationOutput_descriptionMetric_eq_threshold
    {inputLength request : ℕ}
    {circuit : NormalizedThresholdThresholdCircuit inputLength}
    (htag : normalizedCircuitHeaderTag inputLength request = 2)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0)
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitDescriptionMetric inputLength
        (normalizedCircuitValidationOutput inputLength request) =
      circuit.descriptionBits := by
  obtain ⟨hfamily, hcode, _⟩ :=
    normalizedCircuitValidationOutput_resourceProjections hvalid
  refine normalizedCircuitDescriptionMetric_refines_threshold
    (normalizedCircuitValidationOutput inputLength request) circuit
    (by rw [hfamily, htag])
    (normalizedCircuitValidationOutput_topSummary_threshold htag hvalid
      hdecode) ?_
  rw [hcode,
    normalizedCircuitBottomOutputs_eq_validatedSummaries_threshold hdecode]

/-! ### Executable wire and description results for one validated term -/

/-- The compiled wire program executes on any accepted validator output, in
either family, and returns that output's exact summary metric.  This is the
single unconditional contract a per-term wire stage needs. -/
theorem run_normalizedCircuitResourceProgram_of_validation
    (inputLength request : ℕ)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0) :
    runNPOracleProgram normalizedCircuitResourceProgram
        (normalizedCircuitResourceBits inputLength
          (normalizedCircuitValidationOutput inputLength request))
        (normalizedCircuitResourceFuel inputLength
          (normalizedCircuitValidationOutput inputLength request))
        (initialNPOracleState inputLength
          (normalizedCircuitValidationOutput inputLength request)) =
      some
        (normalizedCircuitResourceMetric
          (normalizedCircuitValidationOutput inputLength request)) := by
  obtain ⟨hfamily, hcode, _⟩ :=
    normalizedCircuitValidationOutput_resourceProjections hvalid
  rcases
      (normalizedCircuitValidationOutput_ne_zero_iff_branches
        inputLength request).1 hvalid with
    ⟨htag, _⟩ | ⟨htag, _⟩
  · exact run_normalizedCircuitResourceProgram_symmetric inputLength
      (normalizedCircuitValidationOutput inputLength request)
      (normalizedCircuitBottomOutputs inputLength request)
      (by rw [hfamily, htag])
      (by rw [hcode, decodeBalancedList_encode])
  · obtain ⟨summaries, membership, hsummaries, hmembership, hstored,
        hlengths, _⟩ :=
      normalizedCircuitValidationOutput_thresholdSummaries_of_ne_zero
        inputLength request htag hvalid
    exact run_normalizedCircuitResourceProgram_threshold inputLength
      (normalizedCircuitValidationOutput inputLength request) summaries
      membership (by rw [hfamily, htag]) hsummaries hmembership hstored
      hlengths

/-- The compiled description program executes on any accepted validator output,
in either family, and returns that output's exact description metric. -/
theorem run_normalizedCircuitDescriptionProgram_of_validation
    (inputLength request : ℕ)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0) :
    runNPOracleProgram normalizedCircuitDescriptionProgram
        (normalizedCircuitDescriptionBits inputLength
          (normalizedCircuitValidationOutput inputLength request))
        (normalizedCircuitDescriptionFuel inputLength
          (normalizedCircuitValidationOutput inputLength request))
        (initialNPOracleState inputLength
          (normalizedCircuitValidationOutput inputLength request)) =
      some
        (normalizedCircuitDescriptionMetric inputLength
          (normalizedCircuitValidationOutput inputLength request)) := by
  obtain ⟨summaries, hsummaries, hstored, hcanonical⟩ :=
    normalizedCircuitValidationOutput_summaries_of_ne_zero inputLength request
      hvalid
  obtain ⟨hfamily, _, _⟩ :=
    normalizedCircuitValidationOutput_resourceProjections hvalid
  rcases
      (normalizedCircuitValidationOutput_ne_zero_iff_branches
        inputLength request).1 hvalid with
    ⟨htag, _⟩ | ⟨htag, hbranch⟩
  · exact run_normalizedCircuitDescriptionProgram_symmetric inputLength
      (normalizedCircuitValidationOutput inputLength request) summaries
      (by rw [hfamily, htag]) hsummaries hcanonical
  · obtain ⟨gate, hgate⟩ :=
      Option.isSome_iff_exists.mp
        ((normalizedThresholdValidationOutput_ne_zero_iff
          inputLength request).1 hbranch)
    have hencode : encodeSupportedNormalizedGate gate =
        normalizedCircuitTopCode request :=
      encodeSupportedNormalizedGate_of_decode hgate
    have htop :
        normalizedCircuitResourceTopSummary
            (normalizedCircuitValidationOutput inputLength request) =
          supportedGateRelationOutput (normalizedCircuitCountValue request)
            (encodeSupportedNormalizedGate gate) := by
      rw [normalizedCircuitValidationOutput_eq_threshold htag hbranch]
      simp only [normalizedCircuitResourceTopSummary,
        normalizedCircuitResourcePayload, Nat.unpair_pair]
      rw [normalizedThresholdTopResult, ← hencode]
    exact run_normalizedCircuitDescriptionProgram_threshold inputLength
      (normalizedCircuitValidationOutput inputLength request) summaries
      gate.gate.threshold
      (List.ofFn (supportCompressedGate gate).weight)
      (by rw [hfamily, htag]) hsummaries hstored hcanonical
      (by
        rw [htop]
        exact supportedGateRelationOutput_encode_thresholdCode gate)
      (by
        rw [htop]
        exact supportedGateRelationOutput_encode_selectedWeightsCode gate)

theorem run_normalizedCircuitResourceProgram_of_validation_symmetric
    {inputLength request : ℕ}
    {circuit : NormalizedSymmetricThresholdCircuit inputLength}
    (htag : normalizedCircuitHeaderTag inputLength request = 1)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0)
    (hdecode :
      decodeNormalizedSymmetricThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    runNPOracleProgram normalizedCircuitResourceProgram
        (normalizedCircuitResourceBits inputLength
          (normalizedCircuitValidationOutput inputLength request))
        (normalizedCircuitResourceFuel inputLength
          (normalizedCircuitValidationOutput inputLength request))
        (initialNPOracleState inputLength
          (normalizedCircuitValidationOutput inputLength request)) =
      some circuit.wireCount := by
  obtain ⟨hfamily, hcode, _⟩ :=
    normalizedCircuitValidationOutput_resourceProjections hvalid
  have hrun := run_normalizedCircuitResourceProgram_symmetric inputLength
    (normalizedCircuitValidationOutput inputLength request)
    (normalizedCircuitBottomOutputs inputLength request)
    (by rw [hfamily, htag])
    (by rw [hcode, decodeBalancedList_encode])
  rw [normalizedCircuitValidationOutput_resourceMetric_eq_symmetricWireCount
    htag hvalid hdecode] at hrun
  exact hrun

theorem run_normalizedCircuitResourceProgram_of_validation_threshold
    {inputLength request : ℕ}
    {circuit : NormalizedThresholdThresholdCircuit inputLength}
    (htag : normalizedCircuitHeaderTag inputLength request = 2)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0)
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    runNPOracleProgram normalizedCircuitResourceProgram
        (normalizedCircuitResourceBits inputLength
          (normalizedCircuitValidationOutput inputLength request))
        (normalizedCircuitResourceFuel inputLength
          (normalizedCircuitValidationOutput inputLength request))
        (initialNPOracleState inputLength
          (normalizedCircuitValidationOutput inputLength request)) =
      some circuit.wireCount := by
  obtain ⟨summaries, membership, hsummaries, hmembership, hstored, hlengths,
      _⟩ :=
    normalizedCircuitValidationOutput_thresholdSummaries_of_ne_zero
      inputLength request htag hvalid
  obtain ⟨hfamily, _, _⟩ :=
    normalizedCircuitValidationOutput_resourceProjections hvalid
  have hrun := run_normalizedCircuitResourceProgram_threshold inputLength
    (normalizedCircuitValidationOutput inputLength request) summaries
    membership (by rw [hfamily, htag]) hsummaries hmembership hstored hlengths
  rw [normalizedCircuitValidationOutput_resourceMetric_eq_thresholdWireCount
    htag hvalid hdecode] at hrun
  exact hrun

theorem run_normalizedCircuitDescriptionProgram_of_validation_symmetric
    {inputLength request : ℕ}
    {circuit : NormalizedSymmetricThresholdCircuit inputLength}
    (htag : normalizedCircuitHeaderTag inputLength request = 1)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0)
    (hdecode :
      decodeNormalizedSymmetricThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    runNPOracleProgram normalizedCircuitDescriptionProgram
        (normalizedCircuitDescriptionBits inputLength
          (normalizedCircuitValidationOutput inputLength request))
        (normalizedCircuitDescriptionFuel inputLength
          (normalizedCircuitValidationOutput inputLength request))
        (initialNPOracleState inputLength
          (normalizedCircuitValidationOutput inputLength request)) =
      some circuit.descriptionBits := by
  obtain ⟨summaries, hsummaries, _, hcanonical⟩ :=
    normalizedCircuitValidationOutput_summaries_of_ne_zero inputLength request
      hvalid
  obtain ⟨hfamily, _, _⟩ :=
    normalizedCircuitValidationOutput_resourceProjections hvalid
  have hrun := run_normalizedCircuitDescriptionProgram_symmetric inputLength
    (normalizedCircuitValidationOutput inputLength request) summaries
    (by rw [hfamily, htag]) hsummaries hcanonical
  rw [normalizedCircuitValidationOutput_descriptionMetric_eq_symmetric
    htag hvalid hdecode] at hrun
  exact hrun

theorem run_normalizedCircuitDescriptionProgram_of_validation_threshold
    {inputLength request : ℕ}
    {circuit : NormalizedThresholdThresholdCircuit inputLength}
    (htag : normalizedCircuitHeaderTag inputLength request = 2)
    (hvalid : normalizedCircuitValidationOutput inputLength request ≠ 0)
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit inputLength
        (normalizedCircuitRawCode request) = some circuit) :
    runNPOracleProgram normalizedCircuitDescriptionProgram
        (normalizedCircuitDescriptionBits inputLength
          (normalizedCircuitValidationOutput inputLength request))
        (normalizedCircuitDescriptionFuel inputLength
          (normalizedCircuitValidationOutput inputLength request))
        (initialNPOracleState inputLength
          (normalizedCircuitValidationOutput inputLength request)) =
      some circuit.descriptionBits := by
  obtain ⟨summaries, hsummaries, hstored, hcanonical⟩ :=
    normalizedCircuitValidationOutput_summaries_of_ne_zero inputLength request
      hvalid
  obtain ⟨hfamily, _, _⟩ :=
    normalizedCircuitValidationOutput_resourceProjections hvalid
  have htop :=
    normalizedCircuitValidationOutput_topSummary_threshold htag hvalid hdecode
  have hrun := run_normalizedCircuitDescriptionProgram_threshold inputLength
    (normalizedCircuitValidationOutput inputLength request) summaries
    circuit.top.gate.threshold
    (List.ofFn (supportCompressedGate circuit.top).weight)
    (by rw [hfamily, htag]) hsummaries hstored hcanonical
    (by rw [htop]; exact normalizedGateValidatedSummary_thresholdCode circuit.top)
    (by
      rw [htop]
      exact normalizedGateValidatedSummary_selectedWeightsCode circuit.top)
  rw [normalizedCircuitValidationOutput_descriptionMetric_eq_threshold
    htag hvalid hdecode] at hrun
  exact hrun

private theorem recoveryNatLeOutput_ne_zero_iff (left right : ℕ) :
    nativeNatLeOutput left right ≠ 0 ↔ left ≤ right := by
  simp [nativeNatLeOutput_eq]

def recoveryLegalTermResourceArity (context : ℕ) : ℕ :=
  (Nat.unpair context).1

def recoveryLegalTermResourceCap (context : ℕ) : ℕ :=
  (Nat.unpair context).2

def recoveryLegalTermResourceLoweringOutput
    (context summary : ℕ) : ℕ :=
  Nat.pair
    (nativeInputRequest (recoveryLegalTermResourceArity context) summary)
    (recoveryLegalTermResourceCap context)

def recoveryLegalTermResourceLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 1 2 1
  , .unpairRight 1 3 2
  , .pair 2 0 4 3
  , .pair 4 3 0 4
  , .halt 0
  ]

@[simp] theorem recoveryLegalTermResourceLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermResourceLoweringProgram := by
  rfl

def recoveryLegalTermResourceLoweringValues
    (context summary : ℕ) : List ℕ :=
  [ context
  , summary
  , recoveryLegalTermResourceArity context
  , recoveryLegalTermResourceCap context
  , nativeInputRequest (recoveryLegalTermResourceArity context) summary
  , recoveryLegalTermResourceLoweringOutput context summary
  ]

def recoveryLegalTermResourceLoweringBits
    (context summary : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermResourceLoweringValues context summary).foldr max 0

theorem recoveryLegalTermResourceLoweringValue_bits
    {context summary value : ℕ}
    (hvalue :
      value ∈ recoveryLegalTermResourceLoweringValues context summary) :
    natBitLength value ≤
      recoveryLegalTermResourceLoweringBits context summary := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

private theorem run_recoveryLegalTermResourceLoweringProgram
    (context summary : ℕ) :
    runNPOracleProgram recoveryLegalTermResourceLoweringProgram
        (recoveryLegalTermResourceLoweringBits context summary) 5
        (initialNPOracleState context summary) =
      some (recoveryLegalTermResourceLoweringOutput context summary) := by
  have hbits :
      ∀ value ∈ recoveryLegalTermResourceLoweringValues context summary,
        natBitLength value ≤
          recoveryLegalTermResourceLoweringBits context summary := by
    intro value hvalue
    exact recoveryLegalTermResourceLoweringValue_bits hvalue
  simp [recoveryLegalTermResourceLoweringProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    recoveryLegalTermResourceLoweringValues,
    recoveryLegalTermResourceLoweringOutput,
    recoveryLegalTermResourceArity, recoveryLegalTermResourceCap,
    nativeInputRequest]

/-- One term accepts exactly when its exact wire count is within the cap. -/
def recoveryLegalTermWireCallOutput (context summary : ℕ) : ℕ :=
  nativeNatLeOutput (normalizedCircuitResourceMetric summary)
    (recoveryLegalTermResourceCap context)

def recoveryLegalTermWireCallProgram : NPOracleProgram :=
  linkPrograms recoveryLegalTermResourceLoweringProgram <|
    linkPrograms
      (preserveRightProgram
        (nativeCallProgram normalizedCircuitResourceProgram))
      nativeNatLeProgram

@[simp] theorem recoveryLegalTermWireCallProgram_oracleFree :
    OracleFree recoveryLegalTermWireCallProgram :=
  oracleFree_linkPrograms
    recoveryLegalTermResourceLoweringProgram_oracleFree <|
      oracleFree_linkPrograms
        (preserveRightProgram_oracleFree
          (nativeCallProgram normalizedCircuitResourceProgram)
          (nativeCallProgram_oracleFree
            normalizedCircuitResourceProgram_oracleFree))
        nativeNatLeProgram_oracleFree

def recoveryLegalTermWireInnerBits (context summary : ℕ) : ℕ :=
  nativeCallBits context (recoveryLegalTermResourceArity context) summary
    (normalizedCircuitResourceMetric summary)
    (normalizedCircuitResourceBits
      (recoveryLegalTermResourceArity context) summary)

def recoveryLegalTermWireInnerFuel (context summary : ℕ) : ℕ :=
  nativeCallFuel normalizedCircuitResourceProgram
    (normalizedCircuitResourceFuel
      (recoveryLegalTermResourceArity context) summary)
    (recoveryLegalTermResourceArity context) summary

def recoveryLegalTermWireCallBits (context summary : ℕ) : ℕ :=
  max (natBitLength context) <|
    max (recoveryLegalTermResourceLoweringBits context summary) <|
      max
        (preserveRightBits
          (recoveryLegalTermWireInnerBits context summary)
          (nativeInputRequest
            (recoveryLegalTermResourceArity context) summary)
          (recoveryLegalTermResourceCap context)
          (normalizedCircuitResourceMetric summary))
        (nativeNatLeBits (normalizedCircuitResourceMetric summary)
          (recoveryLegalTermResourceCap context))

def recoveryLegalTermWireCallFuel (context summary : ℕ) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram
        (nativeCallProgram normalizedCircuitResourceProgram))
      nativeNatLeProgram)
    5 <|
    linkFuel nativeNatLeProgram
      (preserveRightFuel (recoveryLegalTermWireInnerFuel context summary))
      (nativeNatLeFuel (normalizedCircuitResourceMetric summary)
        (recoveryLegalTermResourceCap context))

theorem run_recoveryLegalTermWireCallProgram
    (context summary : ℕ)
    (hresource :
      runNPOracleProgram normalizedCircuitResourceProgram
          (normalizedCircuitResourceBits
            (recoveryLegalTermResourceArity context) summary)
          (normalizedCircuitResourceFuel
            (recoveryLegalTermResourceArity context) summary)
          (initialNPOracleState
            (recoveryLegalTermResourceArity context) summary) =
        some (normalizedCircuitResourceMetric summary)) :
    runNPOracleProgram recoveryLegalTermWireCallProgram
        (recoveryLegalTermWireCallBits context summary)
        (recoveryLegalTermWireCallFuel context summary)
        (initialNPOracleState context summary) =
      some (recoveryLegalTermWireCallOutput context summary) := by
  have hlength :
      natBitLength context ≤ recoveryLegalTermWireCallBits context summary :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ recoveryLegalTermWireCallBits context summary :=
    (show 1 ≤ natBitLength context by
      unfold natBitLength
      omega).trans hlength
  have hloweringBits :
      recoveryLegalTermResourceLoweringBits context summary ≤
        recoveryLegalTermWireCallBits context summary :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpreserveBits :
      preserveRightBits (recoveryLegalTermWireInnerBits context summary)
          (nativeInputRequest
            (recoveryLegalTermResourceArity context) summary)
          (recoveryLegalTermResourceCap context)
          (normalizedCircuitResourceMetric summary) ≤
        recoveryLegalTermWireCallBits context summary :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hleBits :
      nativeNatLeBits (normalizedCircuitResourceMetric summary)
          (recoveryLegalTermResourceCap context) ≤
        recoveryLegalTermWireCallBits context summary :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hlowering :=
    run_bits_mono
      (run_recoveryLegalTermResourceLoweringProgram context summary)
      hloweringBits
  have hcall :=
    run_nativeCallProgram normalizedCircuitResourceProgram context
      (recoveryLegalTermResourceArity context) summary
      (normalizedCircuitResourceMetric summary)
      (normalizedCircuitResourceBits
        (recoveryLegalTermResourceArity context) summary)
      (normalizedCircuitResourceFuel
        (recoveryLegalTermResourceArity context) summary)
      hresource
  have hpreserve :=
    run_bits_mono
      (run_preserveRightProgram
        (nativeCallProgram normalizedCircuitResourceProgram) context
        (recoveryLegalTermWireInnerBits context summary)
        (recoveryLegalTermWireInnerFuel context summary)
        (nativeInputRequest (recoveryLegalTermResourceArity context) summary)
        (recoveryLegalTermResourceCap context)
        (normalizedCircuitResourceMetric summary) hcall)
      hpreserveBits
  have hle :=
    run_bits_mono
      (run_nativeNatLeProgram context
        (normalizedCircuitResourceMetric summary)
        (recoveryLegalTermResourceCap context))
      hleBits
  have htail := run_linkPrograms hpositive hlength hpreserve hle
  have hrun := run_linkPrograms hpositive hlength hlowering htail
  simpa only [recoveryLegalTermWireCallProgram,
    recoveryLegalTermWireCallFuel, recoveryLegalTermWireCallOutput,
    recoveryLegalTermResourceLoweringOutput] using hrun

theorem recoveryLegalTermWireCallOutput_ne_zero_iff
    (context summary : ℕ) :
    recoveryLegalTermWireCallOutput context summary ≠ 0 ↔
      normalizedCircuitResourceMetric summary ≤
        recoveryLegalTermResourceCap context :=
  recoveryNatLeOutput_ne_zero_iff _ _

def recoveryLegalTermWireRequestBits (request : ℕ) : ℕ :=
  recoveryLegalTermWireCallBits (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermWireRequestFuel (request : ℕ) : ℕ :=
  recoveryLegalTermWireCallFuel (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermWireRequestOutput (request : ℕ) : ℕ :=
  recoveryLegalTermWireCallOutput
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermWireListProgram : NPOracleProgram :=
  balancedValidationSummaryProgram recoveryLegalTermWireCallProgram

@[simp] theorem recoveryLegalTermWireListProgram_oracleFree :
    OracleFree recoveryLegalTermWireListProgram :=
  balancedValidationSummaryProgram_oracleFree
    recoveryLegalTermWireCallProgram
    recoveryLegalTermWireCallProgram_oracleFree

def recoveryLegalTermWireListOutput (context raw : ℕ) : ℕ :=
  balancedValidationSummaryOutput context raw
    recoveryLegalTermWireRequestOutput

def recoveryLegalTermWireListBits (context raw : ℕ) : ℕ :=
  balancedValidationSummaryBits recoveryLegalTermWireRequestBits
    recoveryLegalTermWireRequestOutput context raw

def recoveryLegalTermWireListFuel (context raw : ℕ) : ℕ :=
  balancedValidationSummaryFuel recoveryLegalTermWireCallProgram
    recoveryLegalTermWireRequestFuel context raw
    recoveryLegalTermWireRequestOutput

theorem run_recoveryLegalTermWireListProgram
    (context raw : ℕ)
    (hresource :
      ∀ summary ∈ balancedValidationMapCodes raw,
        runNPOracleProgram normalizedCircuitResourceProgram
            (normalizedCircuitResourceBits
              (recoveryLegalTermResourceArity context) summary)
            (normalizedCircuitResourceFuel
              (recoveryLegalTermResourceArity context) summary)
            (initialNPOracleState
              (recoveryLegalTermResourceArity context) summary) =
          some (normalizedCircuitResourceMetric summary)) :
    runNPOracleProgram recoveryLegalTermWireListProgram
        (recoveryLegalTermWireListBits context raw)
        (recoveryLegalTermWireListFuel context raw)
        (initialNPOracleState context raw) =
      some (recoveryLegalTermWireListOutput context raw) := by
  apply run_balancedValidationSummaryProgram
  intro request hrequest
  simp only [balancedValidationMapRequests, List.mem_map] at hrequest
  obtain ⟨summary, hsummary, hrequestEq⟩ := hrequest
  rw [← hrequestEq, recoveryLegalTermWireRequestBits,
    recoveryLegalTermWireRequestFuel, recoveryLegalTermWireRequestOutput,
    nativeInputRequest, Nat.unpair_pair]
  exact run_recoveryLegalTermWireCallProgram context summary
    (hresource summary hsummary)

/-- Fail-closed wire semantics: the mapped summary is nonzero exactly when the
tree decodes and every validated term's exact wire count is within the cap. -/
theorem recoveryLegalTermWireListOutput_ne_zero_iff
    (context raw : ℕ) :
    recoveryLegalTermWireListOutput context raw ≠ 0 ↔
      ∃ summaries,
        decodeBalancedList raw = some summaries ∧
          ∀ summary ∈ summaries,
            normalizedCircuitResourceMetric summary ≤
              recoveryLegalTermResourceCap context := by
  have hrequest : ∀ code : ℕ,
      recoveryLegalTermWireRequestOutput
          (nativeInputRequest context code) ≠ 0 ↔
        normalizedCircuitResourceMetric code ≤
          recoveryLegalTermResourceCap context := by
    intro code
    rw [recoveryLegalTermWireRequestOutput, nativeInputRequest,
      Nat.unpair_pair]
    exact recoveryLegalTermWireCallOutput_ne_zero_iff context code
  rw [recoveryLegalTermWireListOutput,
    balancedValidationSummaryOutput_ne_zero_iff]
  constructor
  · rintro ⟨summaries, hdecode, hall⟩
    exact ⟨summaries, hdecode, fun summary hsummary =>
      (hrequest summary).1 (hall summary hsummary)⟩
  · rintro ⟨summaries, hdecode, hall⟩
    exact ⟨summaries, hdecode, fun summary hsummary =>
      (hrequest summary).2 (hall summary hsummary)⟩

/-- One term accepts exactly when its exact description length is within the
cap.  This charge is not the wire charge: it includes the top gate and every
bottom gate's omitted zero coefficients. -/
def recoveryLegalTermDescriptionCallOutput (context summary : ℕ) : ℕ :=
  nativeNatLeOutput
    (normalizedCircuitDescriptionMetric
      (recoveryLegalTermResourceArity context) summary)
    (recoveryLegalTermResourceCap context)

def recoveryLegalTermDescriptionCallProgram : NPOracleProgram :=
  linkPrograms recoveryLegalTermResourceLoweringProgram <|
    linkPrograms
      (preserveRightProgram
        (nativeCallProgram normalizedCircuitDescriptionProgram))
      nativeNatLeProgram

@[simp] theorem recoveryLegalTermDescriptionCallProgram_oracleFree :
    OracleFree recoveryLegalTermDescriptionCallProgram :=
  oracleFree_linkPrograms
    recoveryLegalTermResourceLoweringProgram_oracleFree <|
      oracleFree_linkPrograms
        (preserveRightProgram_oracleFree
          (nativeCallProgram normalizedCircuitDescriptionProgram)
          (nativeCallProgram_oracleFree
            normalizedCircuitDescriptionProgram_oracleFree))
        nativeNatLeProgram_oracleFree

def recoveryLegalTermDescriptionInnerBits (context summary : ℕ) : ℕ :=
  nativeCallBits context (recoveryLegalTermResourceArity context) summary
    (normalizedCircuitDescriptionMetric
      (recoveryLegalTermResourceArity context) summary)
    (normalizedCircuitDescriptionBits
      (recoveryLegalTermResourceArity context) summary)

def recoveryLegalTermDescriptionInnerFuel (context summary : ℕ) : ℕ :=
  nativeCallFuel normalizedCircuitDescriptionProgram
    (normalizedCircuitDescriptionFuel
      (recoveryLegalTermResourceArity context) summary)
    (recoveryLegalTermResourceArity context) summary

def recoveryLegalTermDescriptionCallBits (context summary : ℕ) : ℕ :=
  max (natBitLength context) <|
    max (recoveryLegalTermResourceLoweringBits context summary) <|
      max
        (preserveRightBits
          (recoveryLegalTermDescriptionInnerBits context summary)
          (nativeInputRequest
            (recoveryLegalTermResourceArity context) summary)
          (recoveryLegalTermResourceCap context)
          (normalizedCircuitDescriptionMetric
            (recoveryLegalTermResourceArity context) summary))
        (nativeNatLeBits
          (normalizedCircuitDescriptionMetric
            (recoveryLegalTermResourceArity context) summary)
          (recoveryLegalTermResourceCap context))

def recoveryLegalTermDescriptionCallFuel (context summary : ℕ) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram
        (nativeCallProgram normalizedCircuitDescriptionProgram))
      nativeNatLeProgram)
    5 <|
    linkFuel nativeNatLeProgram
      (preserveRightFuel
        (recoveryLegalTermDescriptionInnerFuel context summary))
      (nativeNatLeFuel
        (normalizedCircuitDescriptionMetric
          (recoveryLegalTermResourceArity context) summary)
        (recoveryLegalTermResourceCap context))

theorem run_recoveryLegalTermDescriptionCallProgram
    (context summary : ℕ)
    (hdescription :
      runNPOracleProgram normalizedCircuitDescriptionProgram
          (normalizedCircuitDescriptionBits
            (recoveryLegalTermResourceArity context) summary)
          (normalizedCircuitDescriptionFuel
            (recoveryLegalTermResourceArity context) summary)
          (initialNPOracleState
            (recoveryLegalTermResourceArity context) summary) =
        some
          (normalizedCircuitDescriptionMetric
            (recoveryLegalTermResourceArity context) summary)) :
    runNPOracleProgram recoveryLegalTermDescriptionCallProgram
        (recoveryLegalTermDescriptionCallBits context summary)
        (recoveryLegalTermDescriptionCallFuel context summary)
        (initialNPOracleState context summary) =
      some (recoveryLegalTermDescriptionCallOutput context summary) := by
  have hlength :
      natBitLength context ≤
        recoveryLegalTermDescriptionCallBits context summary :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤ recoveryLegalTermDescriptionCallBits context summary :=
    (show 1 ≤ natBitLength context by
      unfold natBitLength
      omega).trans hlength
  have hloweringBits :
      recoveryLegalTermResourceLoweringBits context summary ≤
        recoveryLegalTermDescriptionCallBits context summary :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpreserveBits :
      preserveRightBits
          (recoveryLegalTermDescriptionInnerBits context summary)
          (nativeInputRequest
            (recoveryLegalTermResourceArity context) summary)
          (recoveryLegalTermResourceCap context)
          (normalizedCircuitDescriptionMetric
            (recoveryLegalTermResourceArity context) summary) ≤
        recoveryLegalTermDescriptionCallBits context summary :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hleBits :
      nativeNatLeBits
          (normalizedCircuitDescriptionMetric
            (recoveryLegalTermResourceArity context) summary)
          (recoveryLegalTermResourceCap context) ≤
        recoveryLegalTermDescriptionCallBits context summary :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hlowering :=
    run_bits_mono
      (run_recoveryLegalTermResourceLoweringProgram context summary)
      hloweringBits
  have hcall :=
    run_nativeCallProgram normalizedCircuitDescriptionProgram context
      (recoveryLegalTermResourceArity context) summary
      (normalizedCircuitDescriptionMetric
        (recoveryLegalTermResourceArity context) summary)
      (normalizedCircuitDescriptionBits
        (recoveryLegalTermResourceArity context) summary)
      (normalizedCircuitDescriptionFuel
        (recoveryLegalTermResourceArity context) summary)
      hdescription
  have hpreserve :=
    run_bits_mono
      (run_preserveRightProgram
        (nativeCallProgram normalizedCircuitDescriptionProgram) context
        (recoveryLegalTermDescriptionInnerBits context summary)
        (recoveryLegalTermDescriptionInnerFuel context summary)
        (nativeInputRequest (recoveryLegalTermResourceArity context) summary)
        (recoveryLegalTermResourceCap context)
        (normalizedCircuitDescriptionMetric
          (recoveryLegalTermResourceArity context) summary) hcall)
      hpreserveBits
  have hle :=
    run_bits_mono
      (run_nativeNatLeProgram context
        (normalizedCircuitDescriptionMetric
          (recoveryLegalTermResourceArity context) summary)
        (recoveryLegalTermResourceCap context))
      hleBits
  have htail := run_linkPrograms hpositive hlength hpreserve hle
  have hrun := run_linkPrograms hpositive hlength hlowering htail
  simpa only [recoveryLegalTermDescriptionCallProgram,
    recoveryLegalTermDescriptionCallFuel,
    recoveryLegalTermDescriptionCallOutput,
    recoveryLegalTermResourceLoweringOutput] using hrun

theorem recoveryLegalTermDescriptionCallOutput_ne_zero_iff
    (context summary : ℕ) :
    recoveryLegalTermDescriptionCallOutput context summary ≠ 0 ↔
      normalizedCircuitDescriptionMetric
          (recoveryLegalTermResourceArity context) summary ≤
        recoveryLegalTermResourceCap context :=
  recoveryNatLeOutput_ne_zero_iff _ _

def recoveryLegalTermDescriptionRequestBits (request : ℕ) : ℕ :=
  recoveryLegalTermDescriptionCallBits
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermDescriptionRequestFuel (request : ℕ) : ℕ :=
  recoveryLegalTermDescriptionCallFuel
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermDescriptionRequestOutput (request : ℕ) : ℕ :=
  recoveryLegalTermDescriptionCallOutput
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermDescriptionListProgram : NPOracleProgram :=
  balancedValidationSummaryProgram recoveryLegalTermDescriptionCallProgram

@[simp] theorem recoveryLegalTermDescriptionListProgram_oracleFree :
    OracleFree recoveryLegalTermDescriptionListProgram :=
  balancedValidationSummaryProgram_oracleFree
    recoveryLegalTermDescriptionCallProgram
    recoveryLegalTermDescriptionCallProgram_oracleFree

def recoveryLegalTermDescriptionListOutput (context raw : ℕ) : ℕ :=
  balancedValidationSummaryOutput context raw
    recoveryLegalTermDescriptionRequestOutput

def recoveryLegalTermDescriptionListBits (context raw : ℕ) : ℕ :=
  balancedValidationSummaryBits recoveryLegalTermDescriptionRequestBits
    recoveryLegalTermDescriptionRequestOutput context raw

def recoveryLegalTermDescriptionListFuel (context raw : ℕ) : ℕ :=
  balancedValidationSummaryFuel recoveryLegalTermDescriptionCallProgram
    recoveryLegalTermDescriptionRequestFuel context raw
    recoveryLegalTermDescriptionRequestOutput

theorem run_recoveryLegalTermDescriptionListProgram
    (context raw : ℕ)
    (hdescription :
      ∀ summary ∈ balancedValidationMapCodes raw,
        runNPOracleProgram normalizedCircuitDescriptionProgram
            (normalizedCircuitDescriptionBits
              (recoveryLegalTermResourceArity context) summary)
            (normalizedCircuitDescriptionFuel
              (recoveryLegalTermResourceArity context) summary)
            (initialNPOracleState
              (recoveryLegalTermResourceArity context) summary) =
          some
            (normalizedCircuitDescriptionMetric
              (recoveryLegalTermResourceArity context) summary)) :
    runNPOracleProgram recoveryLegalTermDescriptionListProgram
        (recoveryLegalTermDescriptionListBits context raw)
        (recoveryLegalTermDescriptionListFuel context raw)
        (initialNPOracleState context raw) =
      some (recoveryLegalTermDescriptionListOutput context raw) := by
  apply run_balancedValidationSummaryProgram
  intro request hrequest
  simp only [balancedValidationMapRequests, List.mem_map] at hrequest
  obtain ⟨summary, hsummary, hrequestEq⟩ := hrequest
  rw [← hrequestEq, recoveryLegalTermDescriptionRequestBits,
    recoveryLegalTermDescriptionRequestFuel,
    recoveryLegalTermDescriptionRequestOutput,
    nativeInputRequest, Nat.unpair_pair]
  exact run_recoveryLegalTermDescriptionCallProgram context summary
    (hdescription summary hsummary)

/-- Fail-closed description semantics: the mapped summary is nonzero exactly
when the tree decodes and every validated term's exact description length is
within the cap. -/
theorem recoveryLegalTermDescriptionListOutput_ne_zero_iff
    (context raw : ℕ) :
    recoveryLegalTermDescriptionListOutput context raw ≠ 0 ↔
      ∃ summaries,
        decodeBalancedList raw = some summaries ∧
          ∀ summary ∈ summaries,
            normalizedCircuitDescriptionMetric
                (recoveryLegalTermResourceArity context) summary ≤
              recoveryLegalTermResourceCap context := by
  have hrequest : ∀ code : ℕ,
      recoveryLegalTermDescriptionRequestOutput
          (nativeInputRequest context code) ≠ 0 ↔
        normalizedCircuitDescriptionMetric
            (recoveryLegalTermResourceArity context) code ≤
          recoveryLegalTermResourceCap context := by
    intro code
    rw [recoveryLegalTermDescriptionRequestOutput, nativeInputRequest,
      Nat.unpair_pair]
    exact recoveryLegalTermDescriptionCallOutput_ne_zero_iff context code
  rw [recoveryLegalTermDescriptionListOutput,
    balancedValidationSummaryOutput_ne_zero_iff]
  constructor
  · rintro ⟨summaries, hdecode, hall⟩
    exact ⟨summaries, hdecode, fun summary hsummary =>
      (hrequest summary).1 (hall summary hsummary)⟩
  · rintro ⟨summaries, hdecode, hall⟩
    exact ⟨summaries, hdecode, fun summary hsummary =>
      (hrequest summary).2 (hall summary hsummary)⟩

/-! ### Hostile boundary classes for the two new resource coordinates

Each entry is a kernel-checked minimal counterexample: one validated term whose
exact resource value is exactly one unit past the schedule-selected cap
collapses the whole mapped stage summary to zero. -/

/-- Wire overflow at the smallest boundary value. -/
theorem recoveryLegalTermWireListOutput_eq_zero_of_wireOverflow
    (context raw : ℕ) {summaries : List ℕ} {summary : ℕ}
    (hdecode : decodeBalancedList raw = some summaries)
    (hsummary : summary ∈ summaries)
    (hoverflow :
      normalizedCircuitResourceMetric summary =
        recoveryLegalTermResourceCap context + 1) :
    recoveryLegalTermWireListOutput context raw = 0 := by
  by_contra hnonzero
  obtain ⟨decoded, hdecoded, hall⟩ :=
    (recoveryLegalTermWireListOutput_ne_zero_iff context raw).1 hnonzero
  rw [hdecode] at hdecoded
  obtain rfl : summaries = decoded := Option.some.inj hdecoded
  have hbound := hall summary hsummary
  omega

/-- Description overflow at the smallest boundary value. -/
theorem recoveryLegalTermDescriptionListOutput_eq_zero_of_descriptionOverflow
    (context raw : ℕ) {summaries : List ℕ} {summary : ℕ}
    (hdecode : decodeBalancedList raw = some summaries)
    (hsummary : summary ∈ summaries)
    (hoverflow :
      normalizedCircuitDescriptionMetric
          (recoveryLegalTermResourceArity context) summary =
        recoveryLegalTermResourceCap context + 1) :
    recoveryLegalTermDescriptionListOutput context raw = 0 := by
  by_contra hnonzero
  obtain ⟨decoded, hdecoded, hall⟩ :=
    (recoveryLegalTermDescriptionListOutput_ne_zero_iff context raw).1 hnonzero
  rw [hdecode] at hdecoded
  obtain rfl : summaries = decoded := Option.some.inj hdecoded
  have hbound := hall summary hsummary
  omega

/-! ## Internal trusted-configuration syntax -/

/-- Proof fields in `LegalSumLimits` are absent, so its public serialization is
exactly the six numeric/rational resource fields in declaration order.  The
record has fixed arity, hence nested pairing is both canonical and materially
smaller than a tagged variable-length envelope. -/
def encodeLegalSumLimits (limits : LegalSumLimits) : ℕ :=
  Nat.pair limits.expectedArity <|
    Nat.pair limits.termCap <|
      Nat.pair limits.coefficientBitCap <|
        Nat.pair (encodeCanonicalRational limits.coefficientMassCap) <|
          Nat.pair limits.wireCap limits.descriptionCap

/-- The arity equalities in `RecoveryWitnessLimits` are configuration proofs,
not runtime data.  Both branch records remain explicit because their remaining
resource bounds are genuinely different. -/
def encodeRecoveryWitnessLimits (limits : RecoveryWitnessLimits) : ℕ :=
  Nat.pair limits.oracleArity <|
    Nat.pair limits.oracleSizeCap <|
      Nat.pair limits.sumArity <|
        Nat.pair (encodeLegalSumLimits limits.symmetric)
          (encodeLegalSumLimits limits.threshold)

/-- Internal raw-validator ABI:
`pair(encoded schedule-derived limits, untrusted witness)`.  The final public
wrapper must build or freeze the left component from register-one input arity;
the nondeterministic branch supplies only `raw`. -/
def recoveryWitnessValidatorInput
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  Nat.pair (encodeRecoveryWitnessLimits limits) raw

@[simp] theorem recoveryWitnessValidatorInput_limits
    (limits : RecoveryWitnessLimits) (raw : ℕ) :
    (Nat.unpair (recoveryWitnessValidatorInput limits raw)).1 =
      encodeRecoveryWitnessLimits limits := by
  simp [recoveryWitnessValidatorInput]

@[simp] theorem recoveryWitnessValidatorInput_raw
    (limits : RecoveryWitnessLimits) (raw : ℕ) :
    (Nat.unpair (recoveryWitnessValidatorInput limits raw)).2 = raw := by
  simp [recoveryWitnessValidatorInput]

/-!
The parser uses a compact failure convention: every validation subroutine
returns zero on failure and a nonzero structural payload on success.  The
top-level output is nevertheless the unique existing
`recoveryWitnessValidatorOutput`; these internal payloads never become a second
semantic result.
-/

private def acceptedModeOutput (mode raw : ℕ) : ℕ :=
  Nat.pair mode raw

private theorem acceptedModeOutput_ne_zero
    {mode raw : ℕ} (hmode : 0 < mode) :
    acceptedModeOutput mode raw ≠ 0 := by
  unfold acceptedModeOutput
  have hleft := Nat.left_le_pair mode raw
  omega

/-! ## Fixed outer handoff -/

/-- Swap the public configuration and untrusted witness so generic
left-transform/preserve-right linkers can run validators without duplicating
the configuration in scratch registers. -/
def recoveryValidatorSwapProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 3 2 0 3
  , .halt 0
  ]

@[simp] theorem recoveryValidatorSwapProgram_oracleFree :
    OracleFree recoveryValidatorSwapProgram := by
  rfl

def recoveryValidatorSwapBits
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max
    (natBitLength (recoveryWitnessValidatorInput limits raw))
    (natBitLength
      (Nat.pair raw (encodeRecoveryWitnessLimits limits)))

theorem run_recoveryValidatorSwapProgram
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryValidatorSwapProgram
        (recoveryValidatorSwapBits limits raw) 4
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits raw)) =
      some (Nat.pair raw (encodeRecoveryWitnessLimits limits)) := by
  let limitsCode := encodeRecoveryWitnessLimits limits
  let inputCode := recoveryWitnessValidatorInput limits raw
  let outputCode := Nat.pair raw limitsCode
  let maximumBits := recoveryValidatorSwapBits limits raw
  have hinput : natBitLength inputCode ≤ maximumBits := by
    exact Nat.le_max_left _ _
  have houtput : natBitLength outputCode ≤ maximumBits := by
    exact Nat.le_max_right _ _
  have hlimits : natBitLength limitsCode ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair limitsCode raw)).trans hinput
  have hraw : natBitLength raw ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair limitsCode raw)).trans hinput
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := recoveryValidatorSwapProgram)
    (maximumBits := maximumBits) (fuel := 3)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := limitsCode)
    (by rfl) rfl
    (by simp [recoveryWitnessValidatorInput,
      initialNPOracleState, limitsCode])
    hlimits]
  let state1 :=
    ((initialNPOracleState inputLength inputCode).write 2 limitsCode).jump 1
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := recoveryValidatorSwapProgram)
    (maximumBits := maximumBits) (fuel := 2)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := raw)
    (by rfl) rfl
    (by simp [recoveryWitnessValidatorInput,
      initialNPOracleState, limitsCode])
    hraw]
  let state2 := (state1.write 3 raw).jump 2
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := recoveryValidatorSwapProgram)
    (maximumBits := maximumBits) (fuel := 1)
    (pc := 2) (left := 3) (right := 2) (destination := 0)
    (next := 3) (value := outputCode)
    (by rfl) rfl
    (by simp [outputCode])
    houtput]
  apply run_halt_instruction
    (program := recoveryValidatorSwapProgram)
    (maximumBits := maximumBits) (fuel := 0)
    (pc := 3) (outputRegister := 0) (value := outputCode)
  · rfl
  · rfl
  · simp [outputCode]
  · exact houtput

def recoveryValidatorEnvelopeProgram : NPOracleProgram :=
  linkPrograms recoveryValidatorSwapProgram <|
    preserveRightProgram recoveryEnvelopeProgram

@[simp] theorem recoveryValidatorEnvelopeProgram_oracleFree :
    OracleFree recoveryValidatorEnvelopeProgram := by
  exact oracleFree_linkPrograms recoveryValidatorSwapProgram_oracleFree <|
    preserveRightProgram_oracleFree recoveryEnvelopeProgram
      recoveryEnvelopeProgram_oracleFree

def recoveryValidatorEnvelopeFuel : ℕ :=
  linkFuel (preserveRightProgram recoveryEnvelopeProgram) 4
    (preserveRightFuel recoveryEnvelopeFuel)

def recoveryValidatorEnvelopeBits
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryValidatorSwapBits limits raw) <|
      preserveRightBits (recoveryEnvelopeBits raw) raw
        (encodeRecoveryWitnessLimits limits) (recoveryEnvelopeOutput raw)

theorem run_recoveryValidatorEnvelopeProgram
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryValidatorEnvelopeProgram
        (recoveryValidatorEnvelopeBits inputLength limits raw)
        recoveryValidatorEnvelopeFuel
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits raw)) =
      some
        (Nat.pair (recoveryEnvelopeOutput raw)
          (encodeRecoveryWitnessLimits limits)) := by
  let limitsCode := encodeRecoveryWitnessLimits limits
  let swapped := Nat.pair raw limitsCode
  let output := Nat.pair (recoveryEnvelopeOutput raw) limitsCode
  let maximumBits := recoveryValidatorEnvelopeBits inputLength limits raw
  have hfirstBits :
      recoveryValidatorSwapBits limits raw ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsecondBits :
      preserveRightBits (recoveryEnvelopeBits raw) raw limitsCode
          (recoveryEnvelopeOutput raw) ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _)
  have hlengthBits : natBitLength inputLength ≤ maximumBits := by
    exact Nat.le_max_left _ _
  apply run_linkPrograms
  · unfold recoveryValidatorEnvelopeBits
    have hpositive :
        1 ≤ recoveryValidatorSwapBits limits raw := by
      unfold recoveryValidatorSwapBits natBitLength
      omega
    exact hpositive.trans hfirstBits
  · exact hlengthBits
  · exact run_bits_mono
      (run_recoveryValidatorSwapProgram inputLength limits raw)
      hfirstBits
  · have hrun :=
      run_preserveRightProgram recoveryEnvelopeProgram inputLength
        (recoveryEnvelopeBits raw) recoveryEnvelopeFuel raw limitsCode
        (recoveryEnvelopeOutput raw)
        (run_recoveryEnvelopeProgram raw inputLength
          (recoveryEnvelopeBits raw) (le_refl _))
    exact run_bits_mono hrun hsecondBits

/-! ## Canonical nested handoff

The envelope proof deliberately returns the original bytes.  The following
fixed stage projects the two nested component codes only after that proof has
accepted the exact three-cell outer syntax.  This avoids maintaining a second
outer decoder while giving later validators a compact, stable register ABI.
-/

private def taggedHeadCode (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair code).2).1

private def taggedTailCode (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair code).2).2

private def recoveryEnvelopeOracleCode (raw : ℕ) : ℕ :=
  taggedHeadCode (taggedTailCode raw)

private def recoveryEnvelopeSumCode (raw : ℕ) : ℕ :=
  taggedHeadCode (taggedTailCode (taggedTailCode raw))

/-- Internal deep-validator ABI:
`pair mode (pair raw (pair oracleCode (pair sumCode limitsCode)))`.
The original raw code is retained so final acceptance can return the unique
public output without re-encoding any decoded object. -/
def recoveryValidatorHandoffOutput
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  let envelopeOutput := recoveryEnvelopeOutput raw
  if envelopeOutput = 0 then
    0
  else
    Nat.pair (Nat.unpair envelopeOutput).1 <|
      Nat.pair raw <|
        Nat.pair (recoveryEnvelopeOracleCode raw) <|
          Nat.pair (recoveryEnvelopeSumCode raw)
            (encodeRecoveryWitnessLimits limits)

/-- Project the accepted envelope into the nested-validator ABI.  The
rejection block is shared by every failed outer parse. -/
def recoveryValidatorHandoffProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 16 2
  , .unpairRight 0 8 3
  , .unpairLeft 2 3 4
  , .unpairRight 2 4 5
  , .unpairRight 4 5 6
  , .unpairRight 5 6 7
  , .unpairRight 6 7 8
  , .unpairLeft 7 9 9
  , .unpairRight 7 6 10
  , .unpairRight 6 7 11
  , .unpairLeft 7 10 12
  , .pair 10 8 11 13
  , .pair 9 11 11 14
  , .pair 4 11 11 15
  , .pair 3 11 0 17
  , .set 0 0 17
  , .halt 0
  ]

@[simp] theorem recoveryValidatorHandoffProgram_oracleFree :
    OracleFree recoveryValidatorHandoffProgram := by
  rfl

def recoveryValidatorHandoffFuel : ℕ := 18

/-- Every value materialized by the handoff program.  Centralizing this list
keeps the exact interpreter proof and the later polynomial width proof on the
same ledger. -/
def recoveryValidatorHandoffRegisters
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  let limitsCode := encodeRecoveryWitnessLimits limits
  let envelopeOutput := recoveryEnvelopeOutput raw
  let oracleCode := recoveryEnvelopeOracleCode raw
  let sumCode := recoveryEnvelopeSumCode raw
  let sumAndLimits := Nat.pair sumCode limitsCode
  let oracleAndRest := Nat.pair oracleCode sumAndLimits
  let rawAndRest := Nat.pair raw oracleAndRest
  let accepted :=
    Nat.pair (Nat.unpair envelopeOutput).1 rawAndRest
  [ Nat.pair envelopeOutput limitsCode
  , envelopeOutput
  , limitsCode
  , (Nat.unpair envelopeOutput).1
  , raw
  , (Nat.unpair raw).2
  , taggedTailCode raw
  , (Nat.unpair (taggedTailCode raw)).2
  , oracleCode
  , taggedTailCode (taggedTailCode raw)
  , (Nat.unpair (taggedTailCode (taggedTailCode raw))).2
  , sumCode
  , sumAndLimits
  , oracleAndRest
  , rawAndRest
  , accepted
  ].foldr max 0

/-- Exact register width of the handoff trace. -/
def recoveryValidatorHandoffBits
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  natBitLength (recoveryValidatorHandoffRegisters limits raw)

private theorem recoveryValidatorHandoffRegister_bits
    (limits : RecoveryWitnessLimits) (raw value : ℕ)
    (hvalue :
      value ∈
        [Nat.pair (recoveryEnvelopeOutput raw)
            (encodeRecoveryWitnessLimits limits),
          recoveryEnvelopeOutput raw,
          encodeRecoveryWitnessLimits limits,
          (Nat.unpair (recoveryEnvelopeOutput raw)).1,
          raw,
          (Nat.unpair raw).2,
          taggedTailCode raw,
          (Nat.unpair (taggedTailCode raw)).2,
          recoveryEnvelopeOracleCode raw,
          taggedTailCode (taggedTailCode raw),
          (Nat.unpair (taggedTailCode (taggedTailCode raw))).2,
          recoveryEnvelopeSumCode raw,
          Nat.pair (recoveryEnvelopeSumCode raw)
            (encodeRecoveryWitnessLimits limits),
          Nat.pair (recoveryEnvelopeOracleCode raw)
            (Nat.pair (recoveryEnvelopeSumCode raw)
              (encodeRecoveryWitnessLimits limits)),
          Nat.pair raw
            (Nat.pair (recoveryEnvelopeOracleCode raw)
              (Nat.pair (recoveryEnvelopeSumCode raw)
                (encodeRecoveryWitnessLimits limits))),
          Nat.pair (Nat.unpair (recoveryEnvelopeOutput raw)).1
            (Nat.pair raw
              (Nat.pair (recoveryEnvelopeOracleCode raw)
                (Nat.pair (recoveryEnvelopeSumCode raw)
                  (encodeRecoveryWitnessLimits limits))))]) :
    natBitLength value ≤ recoveryValidatorHandoffBits limits raw := by
  unfold recoveryValidatorHandoffBits
  apply natBitLength_mono
  simpa [recoveryValidatorHandoffRegisters] using
    (member_le_foldr_max hvalue)

set_option maxHeartbeats 1000000 in
-- The exact 18-step trace expands a nested register ledger at each write.
theorem run_recoveryValidatorHandoffProgram
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryValidatorHandoffProgram
        (recoveryValidatorHandoffBits limits raw)
        recoveryValidatorHandoffFuel
        (initialNPOracleState inputLength
          (Nat.pair (recoveryEnvelopeOutput raw)
            (encodeRecoveryWitnessLimits limits))) =
      some (recoveryValidatorHandoffOutput limits raw) := by
  let limitsCode := encodeRecoveryWitnessLimits limits
  let envelopeOutput := recoveryEnvelopeOutput raw
  let outerPayload := (Nat.unpair raw).2
  let tail₁ := taggedTailCode raw
  let cell₁Payload := (Nat.unpair tail₁).2
  let oracleCode := recoveryEnvelopeOracleCode raw
  let tail₂ := taggedTailCode tail₁
  let cell₂Payload := (Nat.unpair tail₂).2
  let sumCode := recoveryEnvelopeSumCode raw
  let sumAndLimits := Nat.pair sumCode limitsCode
  let oracleAndRest := Nat.pair oracleCode sumAndLimits
  let rawAndRest := Nat.pair raw oracleAndRest
  let accepted :=
    Nat.pair (Nat.unpair envelopeOutput).1 rawAndRest
  let maximumBits := recoveryValidatorHandoffBits limits raw
  have hinput :
      natBitLength (Nat.pair envelopeOutput limitsCode) ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [envelopeOutput, limitsCode]
  have henvelope : natBitLength envelopeOutput ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [envelopeOutput]
  have hlimits : natBitLength limitsCode ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [limitsCode]
  have hmode :
      natBitLength (Nat.unpair envelopeOutput).1 ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [envelopeOutput]
  have hraw : natBitLength raw ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp
  have houterPayload : natBitLength outerPayload ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [outerPayload]
  have htail₁ : natBitLength tail₁ ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [tail₁]
  have hcell₁Payload :
      natBitLength cell₁Payload ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [cell₁Payload, tail₁]
  have horacle : natBitLength oracleCode ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [oracleCode]
  have htail₂ : natBitLength tail₂ ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [tail₂, tail₁]
  have hcell₂Payload :
      natBitLength cell₂Payload ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [cell₂Payload, tail₂, tail₁]
  have hsum : natBitLength sumCode ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [sumCode]
  have hsumAndLimits :
      natBitLength sumAndLimits ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [sumAndLimits, sumCode, limitsCode]
  have horacleAndRest :
      natBitLength oracleAndRest ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [oracleAndRest, oracleCode, sumAndLimits, sumCode, limitsCode]
  have hrawAndRest :
      natBitLength rawAndRest ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [rawAndRest, oracleAndRest, oracleCode, sumAndLimits, sumCode,
      limitsCode]
  have haccepted : natBitLength accepted ≤ maximumBits := by
    apply recoveryValidatorHandoffRegister_bits
    simp [accepted, envelopeOutput, rawAndRest, oracleAndRest,
      oracleCode, sumAndLimits, sumCode, limitsCode]
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength
      (Nat.pair envelopeOutput limitsCode) by
        unfold natBitLength
        omega).trans hinput
  by_cases hrejected : envelopeOutput = 0
  · simp only [recoveryValidatorHandoffFuel]
    rw [show (18 : ℕ) = 17 + 1 by omega]
    rw [run_unpairLeft_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 17)
      (pc := 0) (source := 0) (destination := 2) (next := 1)
      (value := envelopeOutput)
      (by rfl) rfl
      (by simp [initialNPOracleState, envelopeOutput])
      henvelope]
    rw [show (17 : ℕ) = 16 + 1 by omega]
    rw [run_branchZero_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 16)
      (pc := 1) (register := 2) (zeroTarget := 16)
      (nonzeroTarget := 2)
      (by rfl) (by simp)]
    rw [if_pos (by simp [hrejected])]
    rw [show (16 : ℕ) = 15 + 1 by omega]
    rw [run_set_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 15)
      (pc := 16) (register := 0) (value := 0) (next := 17)
      (by rfl) (by norm_num) (by simpa [natBitLength] using hpositive)]
    rw [show recoveryValidatorHandoffOutput limits raw = 0 by
      simp [recoveryValidatorHandoffOutput, envelopeOutput, hrejected]]
    rw [show (15 : ℕ) = 14 + 1 by omega]
    apply run_halt_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 14)
      (pc := 17) (outputRegister := 0) (value := 0)
    · rfl
    · norm_num
    · simp
    · exact hpositive
  · have hbranch : envelopeOutput ≠ 0 := hrejected
    have henvelopeRaw : (Nat.unpair envelopeOutput).2 = raw := by
      cases hdecode : decodeRecoveryEnvelope raw with
      | none =>
          exact False.elim <| hbranch <| by
            simp [envelopeOutput, recoveryEnvelopeOutput, hdecode]
      | some envelope =>
          simp [envelopeOutput, recoveryEnvelopeOutput, hdecode]
    simp only [recoveryValidatorHandoffFuel]
    rw [show (18 : ℕ) = 17 + 1 by omega]
    rw [run_unpairLeft_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 17)
      (pc := 0) (source := 0) (destination := 2) (next := 1)
      (value := envelopeOutput)
      (by rfl) rfl
      (by simp [initialNPOracleState, envelopeOutput])
      henvelope]
    let state₁ :=
      ((initialNPOracleState inputLength
        (Nat.pair envelopeOutput limitsCode)).write
          2 envelopeOutput).jump 1
    rw [show (17 : ℕ) = 16 + 1 by omega]
    rw [run_branchZero_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 16)
      (pc := 1) (register := 2) (zeroTarget := 16)
      (nonzeroTarget := 2)
      (by rfl) (by rfl)]
    rw [if_neg (by simpa [state₁] using hbranch)]
    let state₂ := state₁.jump 2
    rw [show (16 : ℕ) = 15 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 15)
      (pc := 2) (source := 0) (destination := 8) (next := 3)
      (value := limitsCode)
      (by rfl) (by rfl)
      (by simp [initialNPOracleState, limitsCode])
      hlimits]
    let state₃ := (state₂.write 8 limitsCode).jump 3
    rw [show (15 : ℕ) = 14 + 1 by omega]
    rw [run_unpairLeft_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 14)
      (pc := 3) (source := 2) (destination := 3) (next := 4)
      (value := (Nat.unpair envelopeOutput).1)
      (by rfl) (by rfl)
      (by simp)
      hmode]
    let state₄ :=
      (state₃.write 3 (Nat.unpair envelopeOutput).1).jump 4
    rw [show (14 : ℕ) = 13 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 13)
      (pc := 4) (source := 2) (destination := 4) (next := 5)
      (value := raw)
      (by rfl) (by rfl)
      (by simp [henvelopeRaw])
      hraw]
    let state₅ := (state₄.write 4 raw).jump 5
    rw [show (13 : ℕ) = 12 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 12)
      (pc := 5) (source := 4) (destination := 5) (next := 6)
      (value := outerPayload)
      (by rfl) (by rfl)
      (by simp [outerPayload])
      houterPayload]
    let state₆ := (state₅.write 5 outerPayload).jump 6
    rw [show (12 : ℕ) = 11 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 11)
      (pc := 6) (source := 5) (destination := 6) (next := 7)
      (value := tail₁)
      (by rfl) (by rfl)
      (by simp [outerPayload, tail₁,
        taggedTailCode])
      htail₁]
    let state₇ := (state₆.write 6 tail₁).jump 7
    rw [show (11 : ℕ) = 10 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 10)
      (pc := 7) (source := 6) (destination := 7) (next := 8)
      (value := cell₁Payload)
      (by rfl) (by rfl)
      (by simp [cell₁Payload])
      hcell₁Payload]
    let state₈ := (state₇.write 7 cell₁Payload).jump 8
    rw [show (10 : ℕ) = 9 + 1 by omega]
    rw [run_unpairLeft_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 9)
      (pc := 8) (source := 7) (destination := 9) (next := 9)
      (value := oracleCode)
      (by rfl) (by rfl)
      (by simp [cell₁Payload, oracleCode,
        recoveryEnvelopeOracleCode, taggedHeadCode, tail₁])
      horacle]
    let state₉ := (state₈.write 9 oracleCode).jump 9
    rw [show (9 : ℕ) = 8 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 8)
      (pc := 9) (source := 7) (destination := 6) (next := 10)
      (value := tail₂)
      (by rfl) (by rfl)
      (by simp [cell₁Payload, tail₂, tail₁,
        taggedTailCode])
      htail₂]
    let state₁₀ := (state₉.write 6 tail₂).jump 10
    rw [show (8 : ℕ) = 7 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 7)
      (pc := 10) (source := 6) (destination := 7) (next := 11)
      (value := cell₂Payload)
      (by rfl) (by rfl)
      (by simp [cell₂Payload])
      hcell₂Payload]
    let state₁₁ := (state₁₀.write 7 cell₂Payload).jump 11
    rw [show (7 : ℕ) = 6 + 1 by omega]
    rw [run_unpairLeft_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 6)
      (pc := 11) (source := 7) (destination := 10) (next := 12)
      (value := sumCode)
      (by rfl) (by rfl)
      (by simp [cell₂Payload, sumCode,
        recoveryEnvelopeSumCode, taggedHeadCode, tail₂, tail₁])
      hsum]
    let state₁₂ := (state₁₁.write 10 sumCode).jump 12
    rw [show (6 : ℕ) = 5 + 1 by omega]
    rw [run_pair_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 5)
      (pc := 12) (left := 10) (right := 8) (destination := 11)
      (next := 13) (value := sumAndLimits)
      (by rfl) (by rfl)
      (by simp [sumAndLimits])
      hsumAndLimits]
    let state₁₃ := (state₁₂.write 11 sumAndLimits).jump 13
    rw [show (5 : ℕ) = 4 + 1 by omega]
    rw [run_pair_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 4)
      (pc := 13) (left := 9) (right := 11) (destination := 11)
      (next := 14) (value := oracleAndRest)
      (by rfl) (by rfl)
      (by simp [oracleAndRest])
      horacleAndRest]
    let state₁₄ := (state₁₃.write 11 oracleAndRest).jump 14
    rw [show (4 : ℕ) = 3 + 1 by omega]
    rw [run_pair_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 3)
      (pc := 14) (left := 4) (right := 11) (destination := 11)
      (next := 15) (value := rawAndRest)
      (by rfl) (by rfl)
      (by simp [rawAndRest])
      hrawAndRest]
    let state₁₅ := (state₁₄.write 11 rawAndRest).jump 15
    rw [show (3 : ℕ) = 2 + 1 by omega]
    rw [run_pair_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 2)
      (pc := 15) (left := 3) (right := 11) (destination := 0)
      (next := 17) (value := accepted)
      (by rfl) (by rfl)
      (by simp [accepted])
      haccepted]
    rw [show recoveryValidatorHandoffOutput limits raw = accepted by
      simp [recoveryValidatorHandoffOutput, envelopeOutput, hbranch,
        accepted, rawAndRest, oracleAndRest, sumAndLimits, oracleCode,
        sumCode, limitsCode]]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    apply run_halt_instruction
      (program := recoveryValidatorHandoffProgram)
      (maximumBits := maximumBits) (fuel := 1)
      (pc := 17) (outputRegister := 0) (value := accepted)
    · rfl
    · rfl
    · simp
    · exact haccepted

/-! ## End-to-end outer/nested projection -/

/-- The single composition of public-limit ABI handling, exact outer
validation, and nested-code projection.  Later deep validators extend this
program; they never parse the recovery envelope through another path. -/
def recoveryValidatorNestedHandoffProgram : NPOracleProgram :=
  linkPrograms recoveryValidatorEnvelopeProgram
    recoveryValidatorHandoffProgram

@[simp] theorem recoveryValidatorNestedHandoffProgram_oracleFree :
    OracleFree recoveryValidatorNestedHandoffProgram := by
  exact oracleFree_linkPrograms
    recoveryValidatorEnvelopeProgram_oracleFree
    recoveryValidatorHandoffProgram_oracleFree

def recoveryValidatorNestedHandoffFuel : ℕ :=
  linkFuel recoveryValidatorHandoffProgram
    recoveryValidatorEnvelopeFuel recoveryValidatorHandoffFuel

def recoveryValidatorNestedHandoffBits
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryValidatorEnvelopeBits inputLength limits raw)
      (recoveryValidatorHandoffBits limits raw)

theorem run_recoveryValidatorNestedHandoffProgram
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryValidatorNestedHandoffProgram
        (recoveryValidatorNestedHandoffBits inputLength limits raw)
        recoveryValidatorNestedHandoffFuel
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits raw)) =
      some (recoveryValidatorHandoffOutput limits raw) := by
  let maximumBits :=
    recoveryValidatorNestedHandoffBits inputLength limits raw
  have hlength : natBitLength inputLength ≤ maximumBits := by
    exact Nat.le_max_left _ _
  have henvelope :
      recoveryValidatorEnvelopeBits inputLength limits raw ≤
        maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hhandoff :
      recoveryValidatorHandoffBits limits raw ≤ maximumBits := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_recoveryValidatorEnvelopeProgram inputLength limits raw)
      henvelope
  · exact run_bits_mono
      (run_recoveryValidatorHandoffProgram inputLength limits raw)
      hhandoff

/-! ## Mandatory nested-presence check -/

def handoffOracleCode (handoff : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).1

def handoffSumCode (handoff : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2).1

def handoffLimitsCode (handoff : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2).2

def handoffOracleArity (handoff : ℕ) : ℕ :=
  (Nat.unpair (handoffLimitsCode handoff)).1

def handoffOracleSizeCap (handoff : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (handoffLimitsCode handoff)).2).1

/-- Reject a failed envelope and the two empty nested encodings before any
family-specific traversal.  This is a necessary check, not a replacement for
the complete circuit/sum validators. -/
def recoveryNestedPresenceOutput (handoff : ℕ) : ℕ :=
  if handoff = 0 then
    0
  else if handoffOracleCode handoff = 0 then
    0
  else if handoffSumCode handoff = 0 then
    0
  else
    handoff

def recoveryNestedPresenceProgram : NPOracleProgram :=
  [ .branchZero 0 10 1
  , .unpairRight 0 2 2
  , .unpairRight 2 3 3
  , .unpairLeft 3 4 4
  , .branchZero 4 10 5
  , .unpairRight 3 5 6
  , .unpairLeft 5 6 7
  , .branchZero 6 10 8
  , .halt 0
  , .branchZero 0 10 10
  , .set 0 0 11
  , .halt 0
  ]

@[simp] theorem recoveryNestedPresenceProgram_oracleFree :
    OracleFree recoveryNestedPresenceProgram := by
  rfl

def recoveryNestedPresenceFuel : ℕ := 12

theorem run_recoveryNestedPresenceProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryNestedPresenceProgram
        (natBitLength handoff) recoveryNestedPresenceFuel
        (initialNPOracleState inputLength handoff) =
      some (recoveryNestedPresenceOutput handoff) := by
  let tail₀ := (Nat.unpair handoff).2
  let tail₁ := (Nat.unpair tail₀).2
  let oracleCode := (Nat.unpair tail₁).1
  let tail₂ := (Nat.unpair tail₁).2
  let sumCode := (Nat.unpair tail₂).1
  have hpositive : 1 ≤ natBitLength handoff := by
    unfold natBitLength
    omega
  have htail₀ : natBitLength tail₀ ≤ natBitLength handoff := by
    exact natBitLength_mono (Nat.unpair_right_le handoff)
  have htail₁ : natBitLength tail₁ ≤ natBitLength handoff := by
    exact
      (natBitLength_mono (Nat.unpair_right_le tail₀)).trans htail₀
  have horacle : natBitLength oracleCode ≤ natBitLength handoff := by
    exact
      (natBitLength_mono (Nat.unpair_left_le tail₁)).trans htail₁
  have htail₂ : natBitLength tail₂ ≤ natBitLength handoff := by
    exact
      (natBitLength_mono (Nat.unpair_right_le tail₁)).trans htail₁
  have hsum : natBitLength sumCode ≤ natBitLength handoff := by
    exact
      (natBitLength_mono (Nat.unpair_left_le tail₂)).trans htail₂
  by_cases hzero : handoff = 0
  · subst handoff
    norm_num [recoveryNestedPresenceFuel, recoveryNestedPresenceProgram,
      recoveryNestedPresenceOutput, runNPOracleProgram,
      initialNPOracleState, NPOracleState.boundedWrite,
      NPOracleState.write, NPOracleState.jump, natBitLength]
  · rw [show recoveryNestedPresenceFuel = 11 + 1 by rfl]
    rw [run_branchZero_instruction
      (program := recoveryNestedPresenceProgram)
      (maximumBits := natBitLength handoff) (fuel := 11)
      (pc := 0) (register := 0) (zeroTarget := 10)
      (nonzeroTarget := 1) (by rfl) rfl]
    rw [if_neg (by simpa [initialNPOracleState] using hzero)]
    rw [show (11 : ℕ) = 10 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := recoveryNestedPresenceProgram)
      (maximumBits := natBitLength handoff) (fuel := 10)
      (pc := 1) (source := 0) (destination := 2) (next := 2)
      (value := tail₀) (by rfl) rfl
      (by simp [initialNPOracleState, tail₀]) htail₀]
    let state₁ :=
      ((initialNPOracleState inputLength handoff).write 2 tail₀).jump 2
    rw [show (10 : ℕ) = 9 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := recoveryNestedPresenceProgram)
      (maximumBits := natBitLength handoff) (fuel := 9)
      (pc := 2) (source := 2) (destination := 3) (next := 3)
      (value := tail₁) (by rfl) (by rfl)
      (by simp [tail₁]) htail₁]
    let state₂ := (state₁.write 3 tail₁).jump 3
    rw [show (9 : ℕ) = 8 + 1 by omega]
    rw [run_unpairLeft_instruction
      (program := recoveryNestedPresenceProgram)
      (maximumBits := natBitLength handoff) (fuel := 8)
      (pc := 3) (source := 3) (destination := 4) (next := 4)
      (value := oracleCode) (by rfl) (by rfl)
      (by simp [oracleCode]) horacle]
    let state₃ := (state₂.write 4 oracleCode).jump 4
    rw [show (8 : ℕ) = 7 + 1 by omega]
    rw [run_branchZero_instruction
      (program := recoveryNestedPresenceProgram)
      (maximumBits := natBitLength handoff) (fuel := 7)
      (pc := 4) (register := 4) (zeroTarget := 10)
      (nonzeroTarget := 5) (by rfl) (by rfl)]
    by_cases horacleZero : oracleCode = 0
    · rw [if_pos (by simpa [state₃] using horacleZero)]
      rw [show (7 : ℕ) = 6 + 1 by omega]
      rw [run_set_instruction
        (program := recoveryNestedPresenceProgram)
        (maximumBits := natBitLength handoff) (fuel := 6)
        (pc := 10) (register := 0) (value := 0) (next := 11)
        (by rfl) (by norm_num)
        (by
          convert hpositive using 1
          simp [natBitLength])]
      rw [show recoveryNestedPresenceOutput handoff = 0 by
        simp [recoveryNestedPresenceOutput, hzero, horacleZero,
          handoffOracleCode, oracleCode, tail₁, tail₀]]
      rw [show (6 : ℕ) = 5 + 1 by omega]
      exact run_halt_instruction
        (program := recoveryNestedPresenceProgram)
        (maximumBits := natBitLength handoff) (fuel := 5)
        (pc := 11) (outputRegister := 0) (value := 0)
        (by rfl) (by norm_num) (by simp) hpositive
    · rw [if_neg (by simpa [state₃] using horacleZero)]
      let state₄ := state₃.jump 5
      rw [show (7 : ℕ) = 6 + 1 by omega]
      rw [run_unpairRight_instruction
        (program := recoveryNestedPresenceProgram)
        (maximumBits := natBitLength handoff) (fuel := 6)
        (pc := 5) (source := 3) (destination := 5) (next := 6)
        (value := tail₂) (by rfl) (by rfl)
        (by simp [tail₂]) htail₂]
      let state₅ := (state₄.write 5 tail₂).jump 6
      rw [show (6 : ℕ) = 5 + 1 by omega]
      rw [run_unpairLeft_instruction
        (program := recoveryNestedPresenceProgram)
        (maximumBits := natBitLength handoff) (fuel := 5)
        (pc := 6) (source := 5) (destination := 6) (next := 7)
        (value := sumCode) (by rfl) (by rfl)
        (by simp [sumCode]) hsum]
      let state₆ := (state₅.write 6 sumCode).jump 7
      rw [show (5 : ℕ) = 4 + 1 by omega]
      rw [run_branchZero_instruction
        (program := recoveryNestedPresenceProgram)
        (maximumBits := natBitLength handoff) (fuel := 4)
        (pc := 7) (register := 6) (zeroTarget := 10)
        (nonzeroTarget := 8) (by rfl) (by rfl)]
      by_cases hsumZero : sumCode = 0
      · rw [if_pos (by simpa [state₆] using hsumZero)]
        rw [show (4 : ℕ) = 3 + 1 by omega]
        rw [run_set_instruction
          (program := recoveryNestedPresenceProgram)
          (maximumBits := natBitLength handoff) (fuel := 3)
          (pc := 10) (register := 0) (value := 0) (next := 11)
          (by rfl) (by norm_num)
          (by
            convert hpositive using 1
            simp [natBitLength])]
        rw [show recoveryNestedPresenceOutput handoff = 0 by
          simp [recoveryNestedPresenceOutput, hzero, horacleZero,
            hsumZero, handoffOracleCode, handoffSumCode, oracleCode,
            sumCode, tail₂, tail₁, tail₀]]
        rw [show (3 : ℕ) = 2 + 1 by omega]
        exact run_halt_instruction
          (program := recoveryNestedPresenceProgram)
          (maximumBits := natBitLength handoff) (fuel := 2)
          (pc := 11) (outputRegister := 0) (value := 0)
          (by rfl) (by norm_num) (by simp) hpositive
      · rw [if_neg (by simpa [state₆] using hsumZero)]
        rw [show recoveryNestedPresenceOutput handoff = handoff by
          simp [recoveryNestedPresenceOutput, hzero, horacleZero,
            hsumZero, handoffOracleCode, handoffSumCode, oracleCode,
            sumCode, tail₂, tail₁, tail₀]]
        rw [show (4 : ℕ) = 3 + 1 by omega]
        exact run_halt_instruction
          (program := recoveryNestedPresenceProgram)
          (maximumBits := natBitLength handoff) (fuel := 3)
          (pc := 8) (outputRegister := 0) (value := handoff)
          (by rfl) (by norm_num)
          (by simp [initialNPOracleState])
          (le_refl _)

/-! ## Canonical structural prefix -/

/-- The unique structural prefix for the eventual full validator.  It accepts
no empty nested component and preserves the complete handoff for the deeper
Boolean-DAG and legal-sum stages. -/
def recoveryValidatorStructuralPrefixProgram : NPOracleProgram :=
  linkPrograms recoveryValidatorNestedHandoffProgram
    recoveryNestedPresenceProgram

@[simp] theorem recoveryValidatorStructuralPrefixProgram_oracleFree :
    OracleFree recoveryValidatorStructuralPrefixProgram := by
  exact oracleFree_linkPrograms
    recoveryValidatorNestedHandoffProgram_oracleFree
    recoveryNestedPresenceProgram_oracleFree

def recoveryValidatorStructuralPrefixFuel : ℕ :=
  linkFuel recoveryNestedPresenceProgram
    recoveryValidatorNestedHandoffFuel recoveryNestedPresenceFuel

def recoveryValidatorStructuralPrefixBits
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max
      (recoveryValidatorNestedHandoffBits inputLength limits raw)
      (natBitLength (recoveryValidatorHandoffOutput limits raw))

def recoveryValidatorStructuralPrefixOutput
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  recoveryNestedPresenceOutput
    (recoveryValidatorHandoffOutput limits raw)

theorem run_recoveryValidatorStructuralPrefixProgram
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryValidatorStructuralPrefixProgram
        (recoveryValidatorStructuralPrefixBits inputLength limits raw)
        recoveryValidatorStructuralPrefixFuel
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits raw)) =
      some (recoveryValidatorStructuralPrefixOutput limits raw) := by
  let maximumBits :=
    recoveryValidatorStructuralPrefixBits inputLength limits raw
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hprefix :
      recoveryValidatorNestedHandoffBits inputLength limits raw ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpresence :
      natBitLength (recoveryValidatorHandoffOutput limits raw) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_recoveryValidatorNestedHandoffProgram inputLength limits raw)
      hprefix
  · exact run_bits_mono
      (run_recoveryNestedPresenceProgram inputLength
        (recoveryValidatorHandoffOutput limits raw))
      hpresence

theorem recoveryValidatorStructuralPrefix_rejects_malformedNested
    (limits : RecoveryWitnessLimits) :
    recoveryValidatorStructuralPrefixOutput limits
        malformedNestedRecoveryCode = 0 := by
  have horacle :
      recoveryEnvelopeOracleCode malformedNestedRecoveryCode = 0 := by
    norm_num [recoveryEnvelopeOracleCode, taggedHeadCode, taggedTailCode,
      malformedNestedRecoveryCode, encodeNat, encodeBits, encodeBoolList,
      encodeBalancedList, encodeTaggedList]
  have hsum :
      recoveryEnvelopeSumCode malformedNestedRecoveryCode = 0 := by
    norm_num [recoveryEnvelopeSumCode, taggedHeadCode, taggedTailCode,
      malformedNestedRecoveryCode, encodeNat, encodeBits, encodeBoolList,
      encodeBalancedList, encodeTaggedList]
  have henvelopeNonzero :
      Nat.pair 1 malformedNestedRecoveryCode ≠ 0 := by
    have hleft := Nat.left_le_pair 1 malformedNestedRecoveryCode
    omega
  let limitsCode := encodeRecoveryWitnessLimits limits
  have hhandoffNonzero :
      Nat.pair 1
          (Nat.pair malformedNestedRecoveryCode
            (Nat.pair 0 (Nat.pair 0 limitsCode))) ≠ 0 := by
    have hleft :=
      Nat.left_le_pair 1
        (Nat.pair malformedNestedRecoveryCode
          (Nat.pair 0 (Nat.pair 0 limitsCode)))
    omega
  unfold recoveryValidatorStructuralPrefixOutput
  unfold recoveryValidatorHandoffOutput
  rw [recoveryEnvelope_accepts_malformedNestedRecoveryCode]
  rw [if_neg henvelopeNonzero]
  unfold recoveryNestedPresenceOutput
  simp only [Nat.unpair_pair, horacle, hsum]
  rw [if_neg hhandoffNonzero]
  simp [handoffOracleCode]

theorem run_recoveryValidatorStructuralPrefixProgram_malformedNested
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) :
    runNPOracleProgram recoveryValidatorStructuralPrefixProgram
        (recoveryValidatorStructuralPrefixBits inputLength limits
          malformedNestedRecoveryCode)
        recoveryValidatorStructuralPrefixFuel
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits
            malformedNestedRecoveryCode)) =
      some 0 := by
  rw [run_recoveryValidatorStructuralPrefixProgram]
  exact congrArg some
    (recoveryValidatorStructuralPrefix_rejects_malformedNested limits)

def recoveryBoundedContextInput
    (value cap context : ℕ) : ℕ :=
  Nat.pair (nativeNatLeInput value cap) context

def recoveryBoundedContextOutput
    (value cap context : ℕ) : ℕ :=
  if value ≤ cap then context else 0

def recoveryBoundedContextGateOutput
    (flag context : ℕ) : ℕ :=
  if flag = 0 then 0 else context

def recoveryBoundedContextGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 3 2
  , .unpairRight 0 0 4
  , .set 0 0 4
  , .halt 0
  ]

theorem recoveryBoundedContextGateProgram_oracleFree :
    OracleFree recoveryBoundedContextGateProgram := by
  rfl

def recoveryBoundedContextGateBits
    (flag context : ℕ) : ℕ :=
  natBitLength (Nat.pair flag context)

private theorem run_recoveryBoundedContextGateProgram
    (inputLength flag context : ℕ) :
    runNPOracleProgram recoveryBoundedContextGateProgram
        (recoveryBoundedContextGateBits flag context) 4
        (initialNPOracleState inputLength (Nat.pair flag context)) =
      some (recoveryBoundedContextGateOutput flag context) := by
  have hflag :
      natBitLength flag ≤ recoveryBoundedContextGateBits flag context := by
    exact natBitLength_mono (Nat.left_le_pair flag context)
  have hcontext :
      natBitLength context ≤
        recoveryBoundedContextGateBits flag context := by
    exact natBitLength_mono (Nat.right_le_pair flag context)
  have hpositive :
      1 ≤ recoveryBoundedContextGateBits flag context := by
    unfold recoveryBoundedContextGateBits natBitLength
    omega
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := recoveryBoundedContextGateProgram)
    (maximumBits := recoveryBoundedContextGateBits flag context)
    (fuel := 3) (pc := 0) (source := 0) (destination := 2)
    (next := 1) (value := flag)
    (by rfl) (by rfl)
    (by simp [initialNPOracleState])
    hflag]
  let state₁ :=
    ((initialNPOracleState inputLength (Nat.pair flag context)).write
      2 flag).jump 1
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_branchZero_instruction
    (program := recoveryBoundedContextGateProgram)
    (maximumBits := recoveryBoundedContextGateBits flag context)
    (fuel := 2) (pc := 1) (register := 2)
    (zeroTarget := 3) (nonzeroTarget := 2)
    (by rfl) (by rfl)]
  by_cases hflagZero : flag = 0
  · rw [if_pos (by simpa [state₁] using hflagZero)]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_set_instruction
      (program := recoveryBoundedContextGateProgram)
      (maximumBits := recoveryBoundedContextGateBits flag context)
      (fuel := 1) (pc := 3) (register := 0) (value := 0)
      (next := 4) (by rfl) (by rfl)
      (by simpa [natBitLength] using hpositive)]
    rw [show recoveryBoundedContextGateOutput flag context = 0 by
      simp [recoveryBoundedContextGateOutput, hflagZero]]
    exact run_halt_instruction
      (program := recoveryBoundedContextGateProgram)
      (maximumBits := recoveryBoundedContextGateBits flag context)
      (fuel := 0) (pc := 4) (outputRegister := 0) (value := 0)
      (by rfl) (by rfl) (by simp) hpositive
  · rw [if_neg (by simpa [state₁] using hflagZero)]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := recoveryBoundedContextGateProgram)
      (maximumBits := recoveryBoundedContextGateBits flag context)
      (fuel := 1) (pc := 2) (source := 0) (destination := 0)
      (next := 4) (value := context)
      (by rfl) (by rfl)
      (by simp [initialNPOracleState])
      hcontext]
    rw [show recoveryBoundedContextGateOutput flag context = context by
      simp [recoveryBoundedContextGateOutput, hflagZero]]
    exact run_halt_instruction
      (program := recoveryBoundedContextGateProgram)
      (maximumBits := recoveryBoundedContextGateBits flag context)
      (fuel := 0) (pc := 4) (outputRegister := 0) (value := context)
      (by rfl) (by rfl) (by simp) hcontext

def recoveryBoundedContextCompareProgram : NPOracleProgram :=
  preserveRightProgram nativeNatLeProgram

theorem recoveryBoundedContextCompareProgram_oracleFree :
    OracleFree recoveryBoundedContextCompareProgram := by
  exact preserveRightProgram_oracleFree nativeNatLeProgram
    nativeNatLeProgram_oracleFree

def recoveryBoundedContextCompareFuel
    (value cap : ℕ) : ℕ :=
  preserveRightFuel (nativeNatLeFuel value cap)

def recoveryBoundedContextCompareBits
    (value cap context : ℕ) : ℕ :=
  preserveRightBits (nativeNatLeBits value cap)
    (nativeNatLeInput value cap) context (nativeNatLeOutput value cap)

private theorem run_recoveryBoundedContextCompareProgram
    (inputLength value cap context : ℕ) :
    runNPOracleProgram recoveryBoundedContextCompareProgram
        (recoveryBoundedContextCompareBits value cap context)
        (recoveryBoundedContextCompareFuel value cap)
        (initialNPOracleState inputLength
          (recoveryBoundedContextInput value cap context)) =
      some (Nat.pair (nativeNatLeOutput value cap) context) := by
  exact run_preserveRightProgram nativeNatLeProgram inputLength
    (nativeNatLeBits value cap) (nativeNatLeFuel value cap)
    (nativeNatLeInput value cap) context (nativeNatLeOutput value cap)
    (run_nativeNatLeProgram inputLength value cap)

/-- The one fixed compare-and-continue program used by all recovery resource
checks. -/
def recoveryBoundedContextCheckProgram : NPOracleProgram :=
  linkPrograms recoveryBoundedContextCompareProgram
    recoveryBoundedContextGateProgram

@[simp] theorem recoveryBoundedContextCheckProgram_oracleFree :
    OracleFree recoveryBoundedContextCheckProgram := by
  exact oracleFree_linkPrograms
    recoveryBoundedContextCompareProgram_oracleFree
    recoveryBoundedContextGateProgram_oracleFree

def recoveryBoundedContextCheckFuel
    (value cap : ℕ) : ℕ :=
  linkFuel recoveryBoundedContextGateProgram
    (recoveryBoundedContextCompareFuel value cap) 4

theorem recoveryBoundedContextCheckFuel_le
    (value cap : ℕ) :
    recoveryBoundedContextCheckFuel value cap ≤
      18 * nativeNatLeBits value cap + 24 := by
  have hnative := nativeNatLeFuel_le value cap
  simp [recoveryBoundedContextCheckFuel,
    recoveryBoundedContextCompareFuel, preserveRightFuel, linkFuel,
    recoveryBoundedContextGateProgram, programRegisterSpan,
    instructionRegisterSpan, instructionRegisters]
  omega

def recoveryBoundedContextCheckBits
    (inputLength value cap context : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryBoundedContextCompareBits value cap context)
      (recoveryBoundedContextGateBits
        (nativeNatLeOutput value cap) context)

theorem run_recoveryBoundedContextCheckProgram
    (inputLength value cap context : ℕ) :
    runNPOracleProgram recoveryBoundedContextCheckProgram
        (recoveryBoundedContextCheckBits inputLength value cap context)
        (recoveryBoundedContextCheckFuel value cap)
        (initialNPOracleState inputLength
          (recoveryBoundedContextInput value cap context)) =
      some (recoveryBoundedContextOutput value cap context) := by
  let maximumBits :=
    recoveryBoundedContextCheckBits inputLength value cap context
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hcompare :
      recoveryBoundedContextCompareBits value cap context ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hgate :
      recoveryBoundedContextGateBits
          (nativeNatLeOutput value cap) context ≤ maximumBits :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_recoveryBoundedContextCompareProgram
        inputLength value cap context)
      hcompare
  · have hrun :=
      run_bits_mono
        (run_recoveryBoundedContextGateProgram inputLength
          (nativeNatLeOutput value cap) context)
        hgate
    rw [show recoveryBoundedContextOutput value cap context =
        recoveryBoundedContextGateOutput
          (nativeNatLeOutput value cap) context by
      rw [nativeNatLeOutput_eq]
      by_cases hle : value ≤ cap
      · simp [recoveryBoundedContextOutput,
          recoveryBoundedContextGateOutput, hle]
      · simp [recoveryBoundedContextOutput,
          recoveryBoundedContextGateOutput, hle]]
    exact hrun

/-! ## Canonical nested-oracle validation -/

/-- The structural handoff is reframed for the one canonical dynamic-input
call.  The callee arity is read from the trusted limits bytes already carried
by the handoff; it is never supplied by the witness or the caller. -/
def recoveryOracleCallInput (handoff : ℕ) : ℕ :=
  Nat.pair (handoffOracleCode handoff)
    (Nat.pair (handoffOracleArity handoff) handoff)

def recoveryOracleCallLoweringProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairRight 2 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairRight 5 6 5
  , .unpairLeft 6 7 6
  , .pair 7 0 8 7
  , .pair 4 8 0 8
  , .halt 0
  ]

@[simp] theorem recoveryOracleCallLoweringProgram_oracleFree :
    OracleFree recoveryOracleCallLoweringProgram := by
  rfl

def recoveryOracleCallLoweringFuel : ℕ := 9

private def recoveryOracleCallLoweringValues
    (handoff : ℕ) : List ℕ :=
  let tail₀ := (Nat.unpair handoff).2
  let tail₁ := (Nat.unpair tail₀).2
  let oracleCode := (Nat.unpair tail₁).1
  let tail₂ := (Nat.unpair tail₁).2
  let limitsCode := (Nat.unpair tail₂).2
  let oracleArity := (Nat.unpair limitsCode).1
  [ handoff
  , tail₀
  , tail₁
  , oracleCode
  , tail₂
  , limitsCode
  , oracleArity
  , Nat.pair oracleArity handoff
  , recoveryOracleCallInput handoff
  ]

def recoveryOracleCallLoweringBits (handoff : ℕ) : ℕ :=
  natBitLength
    ((recoveryOracleCallLoweringValues handoff).foldr max 0)

private theorem recoveryOracleCallLoweringValue_bits
    (handoff value : ℕ)
    (hvalue : value ∈ recoveryOracleCallLoweringValues handoff) :
    natBitLength value ≤ recoveryOracleCallLoweringBits handoff := by
  unfold recoveryOracleCallLoweringBits
  exact natBitLength_mono (member_le_foldr_max hvalue)

theorem run_recoveryOracleCallLoweringProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryOracleCallLoweringProgram
        (recoveryOracleCallLoweringBits handoff)
        recoveryOracleCallLoweringFuel
        (initialNPOracleState inputLength handoff) =
      some (recoveryOracleCallInput handoff) := by
  let tail₀ := (Nat.unpair handoff).2
  let tail₁ := (Nat.unpair tail₀).2
  let oracleCode := (Nat.unpair tail₁).1
  let tail₂ := (Nat.unpair tail₁).2
  let limitsCode := (Nat.unpair tail₂).2
  let oracleArity := (Nat.unpair limitsCode).1
  have htail₀ :
      natBitLength tail₀ ≤ recoveryOracleCallLoweringBits handoff := by
    apply recoveryOracleCallLoweringValue_bits
    simp [recoveryOracleCallLoweringValues, tail₀]
  have htail₁ :
      natBitLength tail₁ ≤ recoveryOracleCallLoweringBits handoff := by
    apply recoveryOracleCallLoweringValue_bits
    simp [recoveryOracleCallLoweringValues, tail₁, tail₀]
  have horacle :
      natBitLength oracleCode ≤
        recoveryOracleCallLoweringBits handoff := by
    apply recoveryOracleCallLoweringValue_bits
    simp [recoveryOracleCallLoweringValues, oracleCode, tail₁, tail₀]
  have htail₂ :
      natBitLength tail₂ ≤ recoveryOracleCallLoweringBits handoff := by
    apply recoveryOracleCallLoweringValue_bits
    simp [recoveryOracleCallLoweringValues, tail₂, tail₁, tail₀]
  have hlimits :
      natBitLength limitsCode ≤
        recoveryOracleCallLoweringBits handoff := by
    apply recoveryOracleCallLoweringValue_bits
    simp [recoveryOracleCallLoweringValues, limitsCode, tail₂, tail₁,
      tail₀]
  have harity :
      natBitLength oracleArity ≤
        recoveryOracleCallLoweringBits handoff := by
    apply recoveryOracleCallLoweringValue_bits
    simp [recoveryOracleCallLoweringValues, oracleArity, limitsCode,
      tail₂, tail₁, tail₀]
  have hretained :
      natBitLength (Nat.pair oracleArity handoff) ≤
        recoveryOracleCallLoweringBits handoff := by
    apply recoveryOracleCallLoweringValue_bits
    simp [recoveryOracleCallLoweringValues, oracleArity, limitsCode,
      tail₂, tail₁, tail₀]
  have houtput :
      natBitLength (recoveryOracleCallInput handoff) ≤
        recoveryOracleCallLoweringBits handoff := by
    apply recoveryOracleCallLoweringValue_bits
    simp [recoveryOracleCallLoweringValues]
  have houtput' :
      natBitLength
          (Nat.pair
            (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).1
            (Nat.pair
              (Nat.unpair
                (Nat.unpair
                  (Nat.unpair
                    (Nat.unpair (Nat.unpair handoff).2).2).2).2).1
              handoff)) ≤
        recoveryOracleCallLoweringBits handoff := by
    simpa [recoveryOracleCallInput, handoffOracleCode,
      handoffOracleArity, handoffLimitsCode] using houtput
  simp [recoveryOracleCallLoweringProgram,
    recoveryOracleCallLoweringFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    recoveryOracleCallInput, handoffOracleCode, handoffOracleArity,
    handoffLimitsCode, tail₀, tail₁, oracleCode, tail₂, limitsCode,
    oracleArity, htail₀, htail₁, horacle, htail₂, hlimits, harity,
    hretained, houtput']

def recoveryOracleValidationResult (handoff : ℕ) : ℕ :=
  booleanCircuitValidationOutput (handoffOracleArity handoff)
    (handoffOracleCode handoff)

def recoveryOracleCallOutput (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryOracleValidationResult handoff)
    (Nat.pair (handoffOracleArity handoff) handoff)

def recoveryOracleCallProgram : NPOracleProgram :=
  nativeContextCallProgram booleanCircuitValidationProgram

@[simp] theorem recoveryOracleCallProgram_oracleFree :
    OracleFree recoveryOracleCallProgram := by
  exact nativeContextCallProgram_oracleFree
    booleanCircuitValidationProgram_oracleFree

def recoveryOracleCallFuel (handoff : ℕ) : ℕ :=
  nativeContextCallFuel booleanCircuitValidationProgram
    (booleanCircuitValidationFuel
      (handoffOracleArity handoff) (handoffOracleCode handoff))
    (handoffOracleArity handoff) (handoffOracleCode handoff)

def recoveryOracleCallBits
    (inputLength handoff : ℕ) : ℕ :=
  nativeContextCallBits inputLength
    (handoffOracleArity handoff) (handoffOracleCode handoff) handoff
    (recoveryOracleValidationResult handoff)
    (booleanCircuitValidationBits
      (handoffOracleArity handoff) (handoffOracleCode handoff))

theorem run_recoveryOracleCallProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryOracleCallProgram
        (recoveryOracleCallBits inputLength handoff)
        (recoveryOracleCallFuel handoff)
        (initialNPOracleState inputLength
          (recoveryOracleCallInput handoff)) =
      some (recoveryOracleCallOutput handoff) := by
  exact
    run_nativeContextCallProgram booleanCircuitValidationProgram
      inputLength (handoffOracleArity handoff)
      (handoffOracleCode handoff) handoff
      (recoveryOracleValidationResult handoff)
      (booleanCircuitValidationBits
        (handoffOracleArity handoff) (handoffOracleCode handoff))
      (booleanCircuitValidationFuel
        (handoffOracleArity handoff) (handoffOracleCode handoff))
      (run_booleanCircuitValidationProgram
        (handoffOracleArity handoff) (handoffOracleCode handoff))

theorem recoveryOracleValidationResult_ne_zero_iff
    (handoff : ℕ) :
    recoveryOracleValidationResult handoff ≠ 0 ↔
      ∃ circuit : BooleanCircuit (handoffOracleArity handoff),
        decodeBooleanCircuit (handoffOracleArity handoff)
          (handoffOracleCode handoff) = some circuit := by
  exact
    booleanCircuitValidationOutput_ne_zero_iff_decodeBooleanCircuit
      (handoffOracleArity handoff) (handoffOracleCode handoff)

theorem recoveryOracleValidationResult_eq_pair_iff
    (handoff count : ℕ) :
    recoveryOracleValidationResult handoff = Nat.pair 1 count ↔
      ∃ circuit : BooleanCircuit (handoffOracleArity handoff),
        decodeBooleanCircuit (handoffOracleArity handoff)
            (handoffOracleCode handoff) = some circuit ∧
          circuit.size = count := by
  exact
    booleanCircuitValidationOutput_eq_pair_iff
      (handoffOracleArity handoff) (handoffOracleCode handoff) count

def recoveryOracleNodeCount (handoff : ℕ) : ℕ :=
  (Nat.unpair (recoveryOracleValidationResult handoff)).2

/-- Reject a failed circuit validation before applying the shared size-bound
continuation.  This ordering is essential: the right projection of zero is
zero, which by itself would satisfy every nonnegative size cap. -/
def recoveryOracleBoundInput (handoff : ℕ) : ℕ :=
  if recoveryOracleValidationResult handoff = 0 then
    0
  else
    recoveryBoundedContextInput
      (recoveryOracleNodeCount handoff)
      (handoffOracleSizeCap handoff)
      handoff

def recoveryOracleBoundValue (handoff : ℕ) : ℕ :=
  if recoveryOracleValidationResult handoff = 0 then
    0
  else
    recoveryOracleNodeCount handoff

def recoveryOracleBoundCap (handoff : ℕ) : ℕ :=
  if recoveryOracleValidationResult handoff = 0 then
    0
  else
    handoffOracleSizeCap handoff

def recoveryOracleBoundContext (handoff : ℕ) : ℕ :=
  if recoveryOracleValidationResult handoff = 0 then
    0
  else
    handoff

theorem recoveryOracleBoundInput_eq_boundedContextInput
    (handoff : ℕ) :
    recoveryOracleBoundInput handoff =
      recoveryBoundedContextInput
        (recoveryOracleBoundValue handoff)
        (recoveryOracleBoundCap handoff)
        (recoveryOracleBoundContext handoff) := by
  by_cases hzero : recoveryOracleValidationResult handoff = 0
  · simp [recoveryOracleBoundInput, recoveryOracleBoundValue,
      recoveryOracleBoundCap, recoveryOracleBoundContext,
      recoveryBoundedContextInput, nativeNatLeInput, hzero]
    norm_num [Nat.pair]
  · simp [recoveryOracleBoundInput, recoveryOracleBoundValue,
      recoveryOracleBoundCap, recoveryOracleBoundContext, hzero]

def recoveryOracleBoundLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 14 2
  , .unpairRight 0 3 3
  , .unpairRight 3 4 4
  , .unpairRight 2 5 5
  , .unpairRight 4 6 6
  , .unpairRight 6 7 7
  , .unpairRight 7 8 8
  , .unpairRight 8 9 9
  , .unpairRight 9 10 10
  , .unpairLeft 10 11 11
  , .pair 5 11 12 12
  , .pair 12 4 0 13
  , .halt 0
  , .set 0 0 13
  ]

@[simp] theorem recoveryOracleBoundLoweringProgram_oracleFree :
    OracleFree recoveryOracleBoundLoweringProgram := by
  rfl

def recoveryOracleBoundLoweringFuel : ℕ := 14

private def recoveryOracleBoundLoweringValues
    (handoff : ℕ) : List ℕ :=
  let result := recoveryOracleValidationResult handoff
  let retained := Nat.pair (handoffOracleArity handoff) handoff
  let count := (Nat.unpair result).2
  let tail₀ := (Nat.unpair handoff).2
  let tail₁ := (Nat.unpair tail₀).2
  let tail₂ := (Nat.unpair tail₁).2
  let limitsCode := (Nat.unpair tail₂).2
  let limitsTail := (Nat.unpair limitsCode).2
  let sizeCap := (Nat.unpair limitsTail).1
  let request := nativeNatLeInput count sizeCap
  [ recoveryOracleCallOutput handoff
  , result
  , retained
  , handoff
  , count
  , tail₀
  , tail₁
  , tail₂
  , limitsCode
  , limitsTail
  , sizeCap
  , request
  , Nat.pair request handoff
  , 0
  ]

def recoveryOracleBoundLoweringBits (handoff : ℕ) : ℕ :=
  natBitLength
    ((recoveryOracleBoundLoweringValues handoff).foldr max 0)

private theorem recoveryOracleBoundLoweringValue_bits
    (handoff value : ℕ)
    (hvalue : value ∈ recoveryOracleBoundLoweringValues handoff) :
    natBitLength value ≤ recoveryOracleBoundLoweringBits handoff := by
  unfold recoveryOracleBoundLoweringBits
  exact natBitLength_mono (member_le_foldr_max hvalue)

theorem run_recoveryOracleBoundLoweringProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryOracleBoundLoweringProgram
        (recoveryOracleBoundLoweringBits handoff)
        recoveryOracleBoundLoweringFuel
        (initialNPOracleState inputLength
          (recoveryOracleCallOutput handoff)) =
      some (recoveryOracleBoundInput handoff) := by
  let result := recoveryOracleValidationResult handoff
  let retained := Nat.pair (handoffOracleArity handoff) handoff
  let count := (Nat.unpair result).2
  let tail₀ := (Nat.unpair handoff).2
  let tail₁ := (Nat.unpair tail₀).2
  let tail₂ := (Nat.unpair tail₁).2
  let limitsCode := (Nat.unpair tail₂).2
  let limitsTail := (Nat.unpair limitsCode).2
  let sizeCap := (Nat.unpair limitsTail).1
  let request := nativeNatLeInput count sizeCap
  have hbits :
      ∀ value ∈ recoveryOracleBoundLoweringValues handoff,
        natBitLength value ≤
          recoveryOracleBoundLoweringBits handoff := by
    intro value hvalue
    exact recoveryOracleBoundLoweringValue_bits handoff value hvalue
  have hresult :
      natBitLength result ≤ recoveryOracleBoundLoweringBits handoff :=
    hbits result (by
      simp [recoveryOracleBoundLoweringValues, result])
  have hretained :
      natBitLength retained ≤ recoveryOracleBoundLoweringBits handoff :=
    hbits retained (by
      simp [recoveryOracleBoundLoweringValues, retained])
  have hhandoff :
      natBitLength handoff ≤ recoveryOracleBoundLoweringBits handoff :=
    hbits handoff (by
      simp [recoveryOracleBoundLoweringValues])
  have hcount :
      natBitLength count ≤ recoveryOracleBoundLoweringBits handoff :=
    hbits count (by
      simp [recoveryOracleBoundLoweringValues, count, result])
  have htail₀ :
      natBitLength tail₀ ≤ recoveryOracleBoundLoweringBits handoff :=
    hbits tail₀ (by
      simp [recoveryOracleBoundLoweringValues, tail₀])
  have htail₁ :
      natBitLength tail₁ ≤ recoveryOracleBoundLoweringBits handoff :=
    hbits tail₁ (by
      simp [recoveryOracleBoundLoweringValues, tail₁, tail₀])
  have htail₂ :
      natBitLength tail₂ ≤ recoveryOracleBoundLoweringBits handoff :=
    hbits tail₂ (by
      simp [recoveryOracleBoundLoweringValues, tail₂, tail₁, tail₀])
  have hlimits :
      natBitLength limitsCode ≤ recoveryOracleBoundLoweringBits handoff :=
    hbits limitsCode (by
      simp [recoveryOracleBoundLoweringValues, limitsCode, tail₂, tail₁,
        tail₀])
  have hlimitsTail :
      natBitLength limitsTail ≤ recoveryOracleBoundLoweringBits handoff :=
    hbits limitsTail (by
      simp [recoveryOracleBoundLoweringValues, limitsTail, limitsCode,
        tail₂, tail₁, tail₀])
  have hsizeCap :
      natBitLength sizeCap ≤ recoveryOracleBoundLoweringBits handoff :=
    hbits sizeCap (by
      simp [recoveryOracleBoundLoweringValues, sizeCap, limitsTail,
        limitsCode, tail₂, tail₁, tail₀])
  have hrequest :
      natBitLength request ≤ recoveryOracleBoundLoweringBits handoff :=
    hbits request (by
      simp [recoveryOracleBoundLoweringValues, request, count, result,
        sizeCap, limitsTail, limitsCode, tail₂, tail₁, tail₀])
  have houtput :
      natBitLength (Nat.pair request handoff) ≤
        recoveryOracleBoundLoweringBits handoff :=
    hbits (Nat.pair request handoff) (by
      simp [recoveryOracleBoundLoweringValues, request, count, result,
        sizeCap, limitsTail, limitsCode, tail₂, tail₁, tail₀])
  have hrequest' :
      natBitLength
          (Nat.pair
            (Nat.unpair (recoveryOracleValidationResult handoff)).2
            (Nat.unpair
              (Nat.unpair
                (Nat.unpair
                  (Nat.unpair
                    (Nat.unpair (Nat.unpair handoff).2).2).2).2).2).1) ≤
        recoveryOracleBoundLoweringBits handoff := by
    simpa [request, count, result, sizeCap, limitsTail, limitsCode,
      tail₂, tail₁, tail₀, nativeNatLeInput] using hrequest
  have houtput' :
      natBitLength
          (Nat.pair
            (Nat.pair
              (Nat.unpair (recoveryOracleValidationResult handoff)).2
              (Nat.unpair
                (Nat.unpair
                  (Nat.unpair
                    (Nat.unpair
                      (Nat.unpair (Nat.unpair handoff).2).2).2).2).2).1)
            handoff) ≤
        recoveryOracleBoundLoweringBits handoff := by
    simpa [request, count, result, sizeCap, limitsTail, limitsCode,
      tail₂, tail₁, tail₀, nativeNatLeInput] using houtput
  have hzero :
      natBitLength 0 ≤ recoveryOracleBoundLoweringBits handoff :=
    hbits 0 (by simp [recoveryOracleBoundLoweringValues])
  by_cases hrejected : result = 0
  · simp [recoveryOracleBoundLoweringProgram,
      recoveryOracleBoundLoweringFuel, runNPOracleProgram,
      initialNPOracleState, NPOracleState.boundedWrite,
      recoveryOracleCallOutput, recoveryOracleBoundInput,
      result, hrejected, hzero]
  · simp [recoveryOracleBoundLoweringProgram,
      recoveryOracleBoundLoweringFuel, runNPOracleProgram,
      initialNPOracleState, NPOracleState.boundedWrite,
      recoveryOracleCallOutput, recoveryOracleBoundInput,
      recoveryBoundedContextInput, nativeNatLeInput,
      recoveryOracleNodeCount, handoffOracleSizeCap, handoffLimitsCode,
      result, retained, count, tail₀, tail₁, tail₂, limitsCode,
      limitsTail, sizeCap, hrejected, hresult, hretained,
      hhandoff, hcount, htail₀, htail₁, htail₂, hlimits, hlimitsTail,
      hsizeCap, hrequest', houtput']

def recoveryOracleValidationOutput (handoff : ℕ) : ℕ :=
  recoveryBoundedContextOutput
    (recoveryOracleBoundValue handoff)
    (recoveryOracleBoundCap handoff)
    (recoveryOracleBoundContext handoff)

def recoveryOracleValidationProgram : NPOracleProgram :=
  linkPrograms recoveryOracleCallLoweringProgram <|
    linkPrograms recoveryOracleCallProgram <|
      linkPrograms recoveryOracleBoundLoweringProgram
        recoveryBoundedContextCheckProgram

@[simp] theorem recoveryOracleValidationProgram_oracleFree :
    OracleFree recoveryOracleValidationProgram := by
  exact oracleFree_linkPrograms
    recoveryOracleCallLoweringProgram_oracleFree <|
      oracleFree_linkPrograms recoveryOracleCallProgram_oracleFree <|
        oracleFree_linkPrograms
          recoveryOracleBoundLoweringProgram_oracleFree
          recoveryBoundedContextCheckProgram_oracleFree

def recoveryOracleValidationTailFuel (handoff : ℕ) : ℕ :=
  linkFuel recoveryBoundedContextCheckProgram
    recoveryOracleBoundLoweringFuel <|
      recoveryBoundedContextCheckFuel
        (recoveryOracleBoundValue handoff)
        (recoveryOracleBoundCap handoff)

def recoveryOracleValidationCallTailFuel (handoff : ℕ) : ℕ :=
  linkFuel
    (linkPrograms recoveryOracleBoundLoweringProgram
      recoveryBoundedContextCheckProgram)
    (recoveryOracleCallFuel handoff)
    (recoveryOracleValidationTailFuel handoff)

def recoveryOracleValidationFuel (handoff : ℕ) : ℕ :=
  linkFuel
    (linkPrograms recoveryOracleCallProgram <|
      linkPrograms recoveryOracleBoundLoweringProgram
        recoveryBoundedContextCheckProgram)
    recoveryOracleCallLoweringFuel
    (recoveryOracleValidationCallTailFuel handoff)

def recoveryOracleValidationBits
    (inputLength handoff : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryOracleCallLoweringBits handoff) <|
      max (recoveryOracleCallBits inputLength handoff) <|
        max (recoveryOracleBoundLoweringBits handoff)
          (recoveryBoundedContextCheckBits inputLength
            (recoveryOracleBoundValue handoff)
            (recoveryOracleBoundCap handoff)
            (recoveryOracleBoundContext handoff))

theorem run_recoveryOracleValidationProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryOracleValidationProgram
        (recoveryOracleValidationBits inputLength handoff)
        (recoveryOracleValidationFuel handoff)
        (initialNPOracleState inputLength handoff) =
      some (recoveryOracleValidationOutput handoff) := by
  let maximumBits := recoveryOracleValidationBits inputLength handoff
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hloweringBits :
      recoveryOracleCallLoweringBits handoff ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      recoveryOracleCallBits inputLength handoff ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hboundLoweringBits :
      recoveryOracleBoundLoweringBits handoff ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hboundBits :
      recoveryBoundedContextCheckBits inputLength
          (recoveryOracleBoundValue handoff)
          (recoveryOracleBoundCap handoff)
          (recoveryOracleBoundContext handoff) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlowering :=
    run_bits_mono
      (run_recoveryOracleCallLoweringProgram inputLength handoff)
      hloweringBits
  have hcall :=
    run_bits_mono
      (run_recoveryOracleCallProgram inputLength handoff) hcallBits
  have hboundLowering :=
    run_bits_mono
      (run_recoveryOracleBoundLoweringProgram inputLength handoff)
      hboundLoweringBits
  have hbound :
      runNPOracleProgram recoveryBoundedContextCheckProgram maximumBits
          (recoveryBoundedContextCheckFuel
            (recoveryOracleBoundValue handoff)
            (recoveryOracleBoundCap handoff))
          (initialNPOracleState inputLength
            (recoveryOracleBoundInput handoff)) =
        some (recoveryOracleValidationOutput handoff) := by
    rw [recoveryOracleBoundInput_eq_boundedContextInput]
    exact run_bits_mono
      (run_recoveryBoundedContextCheckProgram inputLength
        (recoveryOracleBoundValue handoff)
        (recoveryOracleBoundCap handoff)
        (recoveryOracleBoundContext handoff))
      hboundBits
  have hboundTail :=
    run_linkPrograms hpositive hlength hboundLowering hbound
  have hcallTail :=
    run_linkPrograms hpositive hlength hcall hboundTail
  have hrun :=
    run_linkPrograms hpositive hlength hlowering hcallTail
  simpa only [recoveryOracleValidationProgram,
    recoveryOracleValidationFuel, recoveryOracleValidationCallTailFuel,
    recoveryOracleValidationTailFuel] using hrun

theorem recoveryOracleValidationOutput_ne_zero_iff
    (handoff : ℕ) :
    recoveryOracleValidationOutput handoff ≠ 0 ↔
      ∃ circuit : BooleanCircuit (handoffOracleArity handoff),
        decodeBooleanCircuit (handoffOracleArity handoff)
            (handoffOracleCode handoff) = some circuit ∧
          circuit.size ≤ handoffOracleSizeCap handoff := by
  constructor
  · intro houtput
    have hresultNonzero :
        recoveryOracleValidationResult handoff ≠ 0 := by
      intro hresultZero
      have houtputZero :
          recoveryOracleValidationOutput handoff = 0 := by
        simp [recoveryOracleValidationOutput, recoveryOracleBoundValue,
          recoveryOracleBoundCap, recoveryOracleBoundContext,
          recoveryBoundedContextOutput, hresultZero]
      exact houtput houtputZero
    obtain ⟨circuit, hdecode⟩ :=
      (recoveryOracleValidationResult_ne_zero_iff handoff).1
        hresultNonzero
    have hresult :
        recoveryOracleValidationResult handoff =
          Nat.pair 1 circuit.size :=
      (recoveryOracleValidationResult_eq_pair_iff
        handoff circuit.size).2 ⟨circuit, hdecode, rfl⟩
    have hcount :
        recoveryOracleNodeCount handoff = circuit.size := by
      simp [recoveryOracleNodeCount, hresult]
    have hsize :
        circuit.size ≤ handoffOracleSizeCap handoff := by
      by_contra hnotle
      have houtputZero :
          recoveryOracleValidationOutput handoff = 0 := by
        simp [recoveryOracleValidationOutput, recoveryOracleBoundValue,
          recoveryOracleBoundCap, recoveryOracleBoundContext,
          recoveryBoundedContextOutput, hresultNonzero, hcount,
          Nat.not_le.mp hnotle]
      exact houtput houtputZero
    exact ⟨circuit, hdecode, hsize⟩
  · rintro ⟨circuit, hdecode, hsize⟩
    have hresultNonzero :
        recoveryOracleValidationResult handoff ≠ 0 :=
      (recoveryOracleValidationResult_ne_zero_iff handoff).2
        ⟨circuit, hdecode⟩
    have hresult :
        recoveryOracleValidationResult handoff =
          Nat.pair 1 circuit.size :=
      (recoveryOracleValidationResult_eq_pair_iff
        handoff circuit.size).2 ⟨circuit, hdecode, rfl⟩
    have hcount :
        recoveryOracleNodeCount handoff = circuit.size := by
      simp [recoveryOracleNodeCount, hresult]
    have hhandoff : handoff ≠ 0 := by
      intro hzero
      subst handoff
      simp [handoffOracleCode] at hdecode
    have houtput :
        recoveryOracleValidationOutput handoff = handoff := by
      simp [recoveryOracleValidationOutput, recoveryOracleBoundValue,
        recoveryOracleBoundCap, recoveryOracleBoundContext,
        recoveryBoundedContextOutput, hresultNonzero, hcount, hsize]
    rw [houtput]
    exact hhandoff

/-! ## Structural prefix with mandatory oracle validation -/

def recoveryValidatorOraclePrefixProgram : NPOracleProgram :=
  linkPrograms recoveryValidatorStructuralPrefixProgram
    recoveryOracleValidationProgram

@[simp] theorem recoveryValidatorOraclePrefixProgram_oracleFree :
    OracleFree recoveryValidatorOraclePrefixProgram := by
  exact oracleFree_linkPrograms
    recoveryValidatorStructuralPrefixProgram_oracleFree
    recoveryOracleValidationProgram_oracleFree

def recoveryValidatorOraclePrefixFuel
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  linkFuel recoveryOracleValidationProgram
    recoveryValidatorStructuralPrefixFuel <|
      recoveryOracleValidationFuel
        (recoveryValidatorStructuralPrefixOutput limits raw)

def recoveryValidatorOraclePrefixBits
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryValidatorStructuralPrefixBits inputLength limits raw)
      (recoveryOracleValidationBits inputLength
        (recoveryValidatorStructuralPrefixOutput limits raw))

def recoveryValidatorOraclePrefixOutput
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  recoveryOracleValidationOutput
    (recoveryValidatorStructuralPrefixOutput limits raw)

theorem run_recoveryValidatorOraclePrefixProgram
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryValidatorOraclePrefixProgram
        (recoveryValidatorOraclePrefixBits inputLength limits raw)
        (recoveryValidatorOraclePrefixFuel limits raw)
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits raw)) =
      some (recoveryValidatorOraclePrefixOutput limits raw) := by
  let maximumBits :=
    recoveryValidatorOraclePrefixBits inputLength limits raw
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hstructuralBits :
      recoveryValidatorStructuralPrefixBits inputLength limits raw ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have horacleBits :
      recoveryOracleValidationBits inputLength
          (recoveryValidatorStructuralPrefixOutput limits raw) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hstructural :=
    run_bits_mono
      (run_recoveryValidatorStructuralPrefixProgram
        inputLength limits raw)
      hstructuralBits
  have horacle :=
    run_bits_mono
      (run_recoveryOracleValidationProgram inputLength
        (recoveryValidatorStructuralPrefixOutput limits raw))
      horacleBits
  have hrun :=
    run_linkPrograms hpositive hlength hstructural horacle
  simpa only [recoveryValidatorOraclePrefixProgram,
    recoveryValidatorOraclePrefixFuel,
    recoveryValidatorOraclePrefixOutput] using hrun

/-! ## Fail-closed legal-sum envelope

This stage validates the selected sum end to end: common envelope syntax,
mode-specific limits, coefficient payloads, and normalized circuit families.
It keeps the existing handoff as the sole success value, so every later caller
has one fail-closed production path and no decoded side channel. -/

def handoffMode (handoff : ℕ) : ℕ :=
  (Nat.unpair handoff).1

def handoffSumArity (handoff : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair (Nat.unpair (handoffLimitsCode handoff)).2).2).1

def handoffLegalLimitsPair (handoff : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair (Nat.unpair (handoffLimitsCode handoff)).2).2).2

def handoffSelectedLegalLimits (handoff : ℕ) : ℕ :=
  if handoffMode handoff = 1 then
    (Nat.unpair (handoffLegalLimitsPair handoff)).1
  else if handoffMode handoff = 2 then
    (Nat.unpair (handoffLegalLimitsPair handoff)).2
  else
    0

def handoffLegalSumModeFlag (handoff : ℕ) : ℕ :=
  if handoffMode handoff = 1 ∨ handoffMode handoff = 2 then 1 else 0

def handoffSelectedExpectedArity (handoff : ℕ) : ℕ :=
  (Nat.unpair (handoffSelectedLegalLimits handoff)).1

def handoffSelectedTermCap (handoff : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (handoffSelectedLegalLimits handoff)).2).1

def handoffSelectedCoefficientBitCap (handoff : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair
      (Nat.unpair (handoffSelectedLegalLimits handoff)).2).2).1

/-- The canonical rational mass cap is the field immediately after the
coefficient-width cap in the selected, mode-specific limits. -/
def handoffSelectedCoefficientMassCapCode (handoff : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair
      (Nat.unpair
        (Nat.unpair (handoffSelectedLegalLimits handoff)).2).2).2).1

/-- The physical wire cap is the fifth field of the selected, mode-specific
limits, immediately after the canonical rational mass cap. -/
def handoffSelectedWireCap (handoff : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair
      (Nat.unpair
        (Nat.unpair
          (Nat.unpair (handoffSelectedLegalLimits handoff)).2).2).2).2).1

/-- The exact circuit-description cap is the last field of the selected,
mode-specific limits.  It is deliberately not interchangeable with the wire
cap: a threshold description charges the top gate and every bottom gate. -/
def handoffSelectedDescriptionCap (handoff : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair
      (Nat.unpair
        (Nat.unpair
          (Nat.unpair (handoffSelectedLegalLimits handoff)).2).2).2).2).2

def recoveryLegalSumTupleOutput (handoff : ℕ) : ℕ :=
  taggedTupleOutput 2 (handoffSumCode handoff)

def recoveryLegalSumTupleFlag (handoff : ℕ) : ℕ :=
  (Nat.unpair (recoveryLegalSumTupleOutput handoff)).1

def recoveryLegalSumTupleFields (handoff : ℕ) : ℕ :=
  (Nat.unpair (recoveryLegalSumTupleOutput handoff)).2

def recoveryLegalSumQCode (handoff : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair
    (recoveryLegalSumTupleFields handoff)).1).2

def recoveryLegalSumTermsCode (handoff : ℕ) : ℕ :=
  (Nat.unpair (recoveryLegalSumTupleFields handoff)).2

def recoveryLegalSumContext (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalSumTupleFlag handoff) <|
    Nat.pair (handoffLegalSumModeFlag handoff) <|
      Nat.pair (recoveryLegalSumTermsCode handoff) <|
        Nat.pair (handoffSelectedExpectedArity handoff) <|
          Nat.pair (handoffSelectedTermCap handoff) handoff

def recoveryLegalSumTupleLoweringOutput (handoff : ℕ) : ℕ :=
  Nat.pair (handoffSumCode handoff) handoff

def recoveryLegalSumTupleLoweringProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairRight 2 3 2
  , .unpairRight 3 4 3
  , .unpairLeft 4 5 4
  , .pair 5 0 0 5
  , .halt 0
  ]

@[simp] theorem recoveryLegalSumTupleLoweringProgram_oracleFree :
    OracleFree recoveryLegalSumTupleLoweringProgram := by
  rfl

def recoveryLegalSumTupleLoweringFuel : ℕ := 6

def recoveryLegalSumTupleLoweringValues
    (inputLength handoff : ℕ) : List ℕ :=
  [ inputLength
  , handoff
  , (Nat.unpair handoff).2
  , (Nat.unpair (Nat.unpair handoff).2).2
  , (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2
  , handoffSumCode handoff
  , recoveryLegalSumTupleLoweringOutput handoff
  ]

def recoveryLegalSumTupleLoweringBits
    (inputLength handoff : ℕ) : ℕ :=
  natBitLength
    (recoveryLegalSumTupleLoweringValues inputLength handoff
      |>.foldr max 0)

theorem recoveryLegalSumTupleLoweringValue_bits
    {inputLength handoff value : ℕ}
    (hvalue :
      value ∈
        recoveryLegalSumTupleLoweringValues inputLength handoff) :
    natBitLength value ≤
      recoveryLegalSumTupleLoweringBits inputLength handoff := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

theorem run_recoveryLegalSumTupleLoweringProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumTupleLoweringProgram
        (recoveryLegalSumTupleLoweringBits inputLength handoff)
        recoveryLegalSumTupleLoweringFuel
        (initialNPOracleState inputLength handoff) =
      some (recoveryLegalSumTupleLoweringOutput handoff) := by
  let tail₀ := (Nat.unpair handoff).2
  let tail₁ := (Nat.unpair tail₀).2
  let tail₂ := (Nat.unpair tail₁).2
  let sumCode := (Nat.unpair tail₂).1
  let output := Nat.pair sumCode handoff
  let maximumBits :=
    recoveryLegalSumTupleLoweringBits inputLength handoff
  have htail₀ : natBitLength tail₀ ≤ maximumBits := by
    apply recoveryLegalSumTupleLoweringValue_bits
    simp [recoveryLegalSumTupleLoweringValues, tail₀]
  have htail₁ : natBitLength tail₁ ≤ maximumBits := by
    apply recoveryLegalSumTupleLoweringValue_bits
    simp [recoveryLegalSumTupleLoweringValues, tail₀, tail₁]
  have htail₂ : natBitLength tail₂ ≤ maximumBits := by
    apply recoveryLegalSumTupleLoweringValue_bits
    simp [recoveryLegalSumTupleLoweringValues, tail₀, tail₁, tail₂]
  have hsum : natBitLength sumCode ≤ maximumBits := by
    apply recoveryLegalSumTupleLoweringValue_bits
    simp [recoveryLegalSumTupleLoweringValues, handoffSumCode,
      tail₀, tail₁, tail₂, sumCode]
  have houtput : natBitLength output ≤ maximumBits := by
    apply recoveryLegalSumTupleLoweringValue_bits
    simp [recoveryLegalSumTupleLoweringValues,
      recoveryLegalSumTupleLoweringOutput, handoffSumCode,
      tail₀, tail₁, tail₂, sumCode, output]
  rw [show recoveryLegalSumTupleLoweringFuel = 5 + 1 by rfl]
  rw [run_unpairRight_instruction (value := tail₀)
    (by rfl) rfl
    (by simp [initialNPOracleState, tail₀]) htail₀]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := tail₁)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tail₁, tail₀])
    htail₁]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := tail₂)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tail₂, tail₁])
    htail₂]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := sumCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, sumCode, tail₂])
    hsum]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, output])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

def recoveryLegalSumProjectionInput (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalSumTupleOutput handoff) handoff

def recoveryLegalSumProjectionOutput (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalSumQCode handoff)
    (recoveryLegalSumContext handoff)

/-- Project the two sum fields and select the exact family-specific limit
record.  Modes other than the already published tags 1 and 2 carry a zero
mode flag and can never survive the final gate. -/
def recoveryLegalSumProjectionProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 6 7 6
  , .unpairRight 5 8 7
  , .unpairLeft 3 9 8
  , .unpairRight 3 10 9
  , .unpairRight 10 10 10
  , .unpairRight 10 10 11
  , .unpairRight 10 11 12
  , .unpairRight 11 11 13
  , .unpairRight 11 11 14
  , .unpairRight 11 11 15
  , .branchZero 9 33 16
  , .decrement 9 17
  , .branchZero 9 20 18
  , .decrement 9 19
  , .branchZero 9 21 33
  , .unpairLeft 11 12 22
  , .unpairRight 11 12 22
  , .set 13 1 23
  , .unpairLeft 12 14 24
  , .unpairRight 12 12 25
  , .unpairLeft 12 15 26
  , .pair 15 3 16 27
  , .pair 14 16 16 28
  , .pair 8 16 16 29
  , .pair 13 16 16 30
  , .pair 4 16 16 31
  , .pair 7 16 0 32
  , .halt 0
  , .set 12 0 34
  , .set 13 0 23
  ]

@[simp] theorem recoveryLegalSumProjectionProgram_oracleFree :
    OracleFree recoveryLegalSumProjectionProgram := by
  rfl

theorem recoveryLegalSumProjectionProgram_at0 :
    recoveryLegalSumProjectionProgram[0]? =
      some (.unpairLeft 0 2 1) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at1 :
    recoveryLegalSumProjectionProgram[1]? =
      some (.unpairRight 0 3 2) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at2 :
    recoveryLegalSumProjectionProgram[2]? =
      some (.unpairLeft 2 4 3) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at3 :
    recoveryLegalSumProjectionProgram[3]? =
      some (.unpairRight 2 5 4) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at4 :
    recoveryLegalSumProjectionProgram[4]? =
      some (.unpairLeft 5 6 5) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at5 :
    recoveryLegalSumProjectionProgram[5]? =
      some (.unpairRight 6 7 6) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at6 :
    recoveryLegalSumProjectionProgram[6]? =
      some (.unpairRight 5 8 7) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at7 :
    recoveryLegalSumProjectionProgram[7]? =
      some (.unpairLeft 3 9 8) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at8 :
    recoveryLegalSumProjectionProgram[8]? =
      some (.unpairRight 3 10 9) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at9 :
    recoveryLegalSumProjectionProgram[9]? =
      some (.unpairRight 10 10 10) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at10 :
    recoveryLegalSumProjectionProgram[10]? =
      some (.unpairRight 10 10 11) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at11 :
    recoveryLegalSumProjectionProgram[11]? =
      some (.unpairRight 10 11 12) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at12 :
    recoveryLegalSumProjectionProgram[12]? =
      some (.unpairRight 11 11 13) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at13 :
    recoveryLegalSumProjectionProgram[13]? =
      some (.unpairRight 11 11 14) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at14 :
    recoveryLegalSumProjectionProgram[14]? =
      some (.unpairRight 11 11 15) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at15 :
    recoveryLegalSumProjectionProgram[15]? =
      some (.branchZero 9 33 16) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at16 :
    recoveryLegalSumProjectionProgram[16]? =
      some (.decrement 9 17) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at17 :
    recoveryLegalSumProjectionProgram[17]? =
      some (.branchZero 9 20 18) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at18 :
    recoveryLegalSumProjectionProgram[18]? =
      some (.decrement 9 19) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at19 :
    recoveryLegalSumProjectionProgram[19]? =
      some (.branchZero 9 21 33) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at20 :
    recoveryLegalSumProjectionProgram[20]? =
      some (.unpairLeft 11 12 22) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at21 :
    recoveryLegalSumProjectionProgram[21]? =
      some (.unpairRight 11 12 22) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at22 :
    recoveryLegalSumProjectionProgram[22]? =
      some (.set 13 1 23) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at23 :
    recoveryLegalSumProjectionProgram[23]? =
      some (.unpairLeft 12 14 24) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at24 :
    recoveryLegalSumProjectionProgram[24]? =
      some (.unpairRight 12 12 25) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at25 :
    recoveryLegalSumProjectionProgram[25]? =
      some (.unpairLeft 12 15 26) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at26 :
    recoveryLegalSumProjectionProgram[26]? =
      some (.pair 15 3 16 27) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at27 :
    recoveryLegalSumProjectionProgram[27]? =
      some (.pair 14 16 16 28) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at28 :
    recoveryLegalSumProjectionProgram[28]? =
      some (.pair 8 16 16 29) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at29 :
    recoveryLegalSumProjectionProgram[29]? =
      some (.pair 13 16 16 30) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at30 :
    recoveryLegalSumProjectionProgram[30]? =
      some (.pair 4 16 16 31) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at31 :
    recoveryLegalSumProjectionProgram[31]? =
      some (.pair 7 16 0 32) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at32 :
    recoveryLegalSumProjectionProgram[32]? =
      some (.halt 0) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at33 :
    recoveryLegalSumProjectionProgram[33]? =
      some (.set 12 0 34) := by
  rfl

theorem recoveryLegalSumProjectionProgram_at34 :
    recoveryLegalSumProjectionProgram[34]? =
      some (.set 13 0 23) := by
  rfl

def recoveryLegalSumProjectionFuel : ℕ := 32

def recoveryLegalSumProjectionValues
    (inputLength handoff : ℕ) : List ℕ :=
  let tuple := recoveryLegalSumTupleOutput handoff
  let fields := recoveryLegalSumTupleFields handoff
  let selected := handoffSelectedLegalLimits handoff
  let selectedTail := (Nat.unpair selected).2
  let termCap := handoffSelectedTermCap handoff
  let capHandoff := Nat.pair termCap handoff
  let expectedRest :=
    Nat.pair (handoffSelectedExpectedArity handoff) capHandoff
  let termsRest :=
    Nat.pair (recoveryLegalSumTermsCode handoff) expectedRest
  let modeRest :=
    Nat.pair (handoffLegalSumModeFlag handoff) termsRest
  let context :=
    Nat.pair (recoveryLegalSumTupleFlag handoff) modeRest
  [ 0
  , 1
  , inputLength
  , recoveryLegalSumProjectionInput handoff
  , tuple
  , handoff
  , recoveryLegalSumTupleFlag handoff
  , fields
  , (Nat.unpair fields).1
  , recoveryLegalSumQCode handoff
  , recoveryLegalSumTermsCode handoff
  , handoffMode handoff
  , (Nat.unpair handoff).2
  , (Nat.unpair (Nat.unpair handoff).2).2
  , (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2
  , handoffLimitsCode handoff
  , (Nat.unpair (handoffLimitsCode handoff)).2
  , (Nat.unpair (Nat.unpair (handoffLimitsCode handoff)).2).2
  , handoffLegalLimitsPair handoff
  , (Nat.unpair (handoffLegalLimitsPair handoff)).1
  , (Nat.unpair (handoffLegalLimitsPair handoff)).2
  , selected
  , handoffLegalSumModeFlag handoff
  , handoffSelectedExpectedArity handoff
  , selectedTail
  , termCap
  , capHandoff
  , expectedRest
  , termsRest
  , modeRest
  , context
  , recoveryLegalSumProjectionOutput handoff
  ]

def recoveryLegalSumProjectionBits
    (inputLength handoff : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalSumProjectionValues inputLength handoff).foldr max 0

theorem recoveryLegalSumProjectionValue_bits
    {inputLength handoff value : ℕ}
    (hvalue :
      value ∈ recoveryLegalSumProjectionValues inputLength handoff) :
    natBitLength value ≤
      recoveryLegalSumProjectionBits inputLength handoff := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

def recoveryLegalSumProjectionPrefixState
    (inputLength handoff : ℕ) : NPOracleState :=
  let tuple := recoveryLegalSumTupleOutput handoff
  let tupleFlag := recoveryLegalSumTupleFlag handoff
  let fields := recoveryLegalSumTupleFields handoff
  let qFrame := (Nat.unpair fields).1
  let qCode := recoveryLegalSumQCode handoff
  let termsCode := recoveryLegalSumTermsCode handoff
  let mode := handoffMode handoff
  let tail₀ := (Nat.unpair handoff).2
  let tail₁ := (Nat.unpair tail₀).2
  let tail₂ := (Nat.unpair tail₁).2
  let limitsCode := (Nat.unpair tail₂).2
  let limitsTail₀ := (Nat.unpair limitsCode).2
  let limitsTail₁ := (Nat.unpair limitsTail₀).2
  let legalPair := (Nat.unpair limitsTail₁).2
  let state₀ :=
    initialNPOracleState inputLength
      (recoveryLegalSumProjectionInput handoff)
  let state₁ := (state₀.write 2 tuple).jump 1
  let state₂ := (state₁.write 3 handoff).jump 2
  let state₃ := (state₂.write 4 tupleFlag).jump 3
  let state₄ := (state₃.write 5 fields).jump 4
  let state₅ := (state₄.write 6 qFrame).jump 5
  let state₆ := (state₅.write 7 qCode).jump 6
  let state₇ := (state₆.write 8 termsCode).jump 7
  let state₈ := (state₇.write 9 mode).jump 8
  let state₉ := (state₈.write 10 tail₀).jump 9
  let state₁₀ := (state₉.write 10 tail₁).jump 10
  let state₁₁ := (state₁₀.write 10 tail₂).jump 11
  let state₁₂ := (state₁₁.write 11 limitsCode).jump 12
  let state₁₃ := (state₁₂.write 11 limitsTail₀).jump 13
  let state₁₄ := (state₁₃.write 11 limitsTail₁).jump 14
  (state₁₄.write 11 legalPair).jump 15

def recoveryLegalSumProjectionCoreState
    (inputLength handoff : ℕ) : NPOracleState :=
  let tuple := recoveryLegalSumTupleOutput handoff
  let tupleFlag := recoveryLegalSumTupleFlag handoff
  let fields := recoveryLegalSumTupleFields handoff
  let qFrame := (Nat.unpair fields).1
  let qCode := recoveryLegalSumQCode handoff
  let termsCode := recoveryLegalSumTermsCode handoff
  let mode := handoffMode handoff
  let state₀ :=
    initialNPOracleState inputLength
      (recoveryLegalSumProjectionInput handoff)
  let state₁ := (state₀.write 2 tuple).jump 1
  let state₂ := (state₁.write 3 handoff).jump 2
  let state₃ := (state₂.write 4 tupleFlag).jump 3
  let state₄ := (state₃.write 5 fields).jump 4
  let state₅ := (state₄.write 6 qFrame).jump 5
  let state₆ := (state₅.write 7 qCode).jump 6
  let state₇ := (state₆.write 8 termsCode).jump 7
  (state₇.write 9 mode).jump 8

set_option maxHeartbeats 600000 in
-- Keep each trace command short enough for deterministic clean replay.
private theorem run_recoveryLegalSumProjectionCorePrefix
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumProjectionProgram
        (recoveryLegalSumProjectionBits inputLength handoff) 32
        (initialNPOracleState inputLength
          (recoveryLegalSumProjectionInput handoff)) =
      runNPOracleProgram recoveryLegalSumProjectionProgram
        (recoveryLegalSumProjectionBits inputLength handoff) 24
        (recoveryLegalSumProjectionCoreState inputLength handoff) := by
  let tuple := recoveryLegalSumTupleOutput handoff
  let tupleFlag := recoveryLegalSumTupleFlag handoff
  let fields := recoveryLegalSumTupleFields handoff
  let qFrame := (Nat.unpair fields).1
  let qCode := recoveryLegalSumQCode handoff
  let termsCode := recoveryLegalSumTermsCode handoff
  let mode := handoffMode handoff
  let input := Nat.pair tuple handoff
  let output := recoveryLegalSumProjectionOutput handoff
  let maximumBits := recoveryLegalSumProjectionBits inputLength handoff
  let state₀ := initialNPOracleState inputLength input
  let state₁ := (state₀.write 2 tuple).jump 1
  let state₂ := (state₁.write 3 handoff).jump 2
  let state₃ := (state₂.write 4 tupleFlag).jump 3
  let state₄ := (state₃.write 5 fields).jump 4
  let state₅ := (state₄.write 6 qFrame).jump 5
  let state₆ := (state₅.write 7 qCode).jump 6
  let state₇ := (state₆.write 8 termsCode).jump 7
  let state₈ := (state₇.write 9 mode).jump 8
  have hinput : natBitLength input ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, input, tuple,
      recoveryLegalSumProjectionInput]
  have htuple : natBitLength tuple ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, tuple]
  have hhandoff : natBitLength handoff ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues]
  have htupleFlag : natBitLength tupleFlag ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, tupleFlag]
  have hfields : natBitLength fields ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, fields]
  have hqFrame : natBitLength qFrame ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, qFrame, fields]
  have hqCode : natBitLength qCode ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, qCode]
  have htermsCode : natBitLength termsCode ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, termsCode]
  have hmode : natBitLength mode ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, mode]
  rw [show 32 = 31 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tuple)
    recoveryLegalSumProjectionProgram_at0 rfl
    (by
      simp [initialNPOracleState, tuple,
        recoveryLegalSumProjectionInput])
    htuple]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 31
        state₁ =
      _
  rw [show 31 = 30 + 1 by omega]
  rw [run_unpairRight_instruction (value := handoff)
    recoveryLegalSumProjectionProgram_at1 rfl
    (by simp [state₁, state₀, initialNPOracleState,
      NPOracleState.write, NPOracleState.jump, input]) hhandoff]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 30
        state₂ =
      _
  rw [show 30 = 29 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tupleFlag)
    recoveryLegalSumProjectionProgram_at2 rfl
    (by simp [state₂, state₁, state₀, initialNPOracleState,
      NPOracleState.write, NPOracleState.jump, tupleFlag, tuple, input,
      recoveryLegalSumTupleFlag])
    htupleFlag]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 29
        state₃ =
      _
  rw [show 29 = 28 + 1 by omega]
  rw [run_unpairRight_instruction (value := fields)
    recoveryLegalSumProjectionProgram_at3 rfl
    (by simp [state₃, state₂, state₁, state₀, initialNPOracleState,
      NPOracleState.write, NPOracleState.jump, fields, tuple, input,
      recoveryLegalSumTupleFields])
    hfields]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 28
        state₄ =
      _
  rw [show 28 = 27 + 1 by omega]
  rw [run_unpairLeft_instruction (value := qFrame)
    recoveryLegalSumProjectionProgram_at4 rfl
    (by simp [state₄, state₃, state₂, state₁, state₀,
      initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      qFrame, input])
    hqFrame]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 27
        state₅ =
      _
  rw [show 27 = 26 + 1 by omega]
  rw [run_unpairRight_instruction (value := qCode)
    recoveryLegalSumProjectionProgram_at5 rfl
    (by simp [state₅, state₄, state₃, state₂, state₁, state₀,
      initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      qCode, qFrame, fields, recoveryLegalSumQCode, input]) hqCode]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 26
        state₆ =
      _
  rw [show 26 = 25 + 1 by omega]
  rw [run_unpairRight_instruction (value := termsCode)
    recoveryLegalSumProjectionProgram_at6 rfl
    (by simp [state₆, state₅, state₄, state₃, state₂, state₁, state₀,
      initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      termsCode, fields, recoveryLegalSumTermsCode, input])
    htermsCode]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 25
        state₇ =
      _
  rw [show 25 = 24 + 1 by omega]
  rw [run_unpairLeft_instruction (value := mode)
    recoveryLegalSumProjectionProgram_at7 rfl
    (by simp [state₇, state₆, state₅, state₄, state₃, state₂, state₁,
      state₀, initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, mode, input, handoffMode]) hmode]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 24
        state₈ =
      runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 24
        (recoveryLegalSumProjectionCoreState inputLength handoff)
  congr 1

set_option maxHeartbeats 600000 in
-- Parse the trusted limit record separately from the untrusted sum tuple.
private theorem run_recoveryLegalSumProjectionLimitPrefix
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumProjectionProgram
        (recoveryLegalSumProjectionBits inputLength handoff) 24
        (recoveryLegalSumProjectionCoreState inputLength handoff) =
      runNPOracleProgram recoveryLegalSumProjectionProgram
        (recoveryLegalSumProjectionBits inputLength handoff) 17
        (recoveryLegalSumProjectionPrefixState inputLength handoff) := by
  let tail₀ := (Nat.unpair handoff).2
  let tail₁ := (Nat.unpair tail₀).2
  let tail₂ := (Nat.unpair tail₁).2
  let limitsCode := (Nat.unpair tail₂).2
  let limitsTail₀ := (Nat.unpair limitsCode).2
  let limitsTail₁ := (Nat.unpair limitsTail₀).2
  let legalPair := (Nat.unpair limitsTail₁).2
  let maximumBits := recoveryLegalSumProjectionBits inputLength handoff
  let state₈ := recoveryLegalSumProjectionCoreState inputLength handoff
  let state₉ := (state₈.write 10 tail₀).jump 9
  let state₁₀ := (state₉.write 10 tail₁).jump 10
  let state₁₁ := (state₁₀.write 10 tail₂).jump 11
  let state₁₂ := (state₁₁.write 11 limitsCode).jump 12
  let state₁₃ := (state₁₂.write 11 limitsTail₀).jump 13
  let state₁₄ := (state₁₃.write 11 limitsTail₁).jump 14
  let state₁₅ := (state₁₄.write 11 legalPair).jump 15
  have htail₀ : natBitLength tail₀ ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, tail₀]
  have htail₁ : natBitLength tail₁ ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, tail₀, tail₁]
  have htail₂ : natBitLength tail₂ ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, tail₀, tail₁, tail₂]
  have hlimitsCode : natBitLength limitsCode ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, handoffLimitsCode,
      tail₀, tail₁, tail₂, limitsCode]
  have hlimitsTail₀ : natBitLength limitsTail₀ ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, handoffLimitsCode,
      tail₀, tail₁, tail₂, limitsCode, limitsTail₀]
  have hlimitsTail₁ : natBitLength limitsTail₁ ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, handoffLimitsCode,
      tail₀, tail₁, tail₂, limitsCode, limitsTail₀, limitsTail₁]
  have hlegalPair : natBitLength legalPair ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, handoffLimitsCode,
      handoffLegalLimitsPair, tail₀, tail₁, tail₂, limitsCode,
      limitsTail₀, limitsTail₁, legalPair]
  rw [show 24 = 23 + 1 by omega]
  rw [run_unpairRight_instruction (value := tail₀)
    recoveryLegalSumProjectionProgram_at8 rfl
    (by
      simp [recoveryLegalSumProjectionCoreState,
        initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        tail₀])
    htail₀]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 23
        state₉ =
      _
  rw [show 23 = 22 + 1 by omega]
  rw [run_unpairRight_instruction (value := tail₁)
    recoveryLegalSumProjectionProgram_at9 rfl
    (by simp [state₉, NPOracleState.write, NPOracleState.jump, tail₁])
    htail₁]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 22
        state₁₀ =
      _
  rw [show 22 = 21 + 1 by omega]
  rw [run_unpairRight_instruction (value := tail₂)
    recoveryLegalSumProjectionProgram_at10 rfl
    (by simp [state₁₀, NPOracleState.write, NPOracleState.jump, tail₂])
    htail₂]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 21
        state₁₁ =
      _
  rw [show 21 = 20 + 1 by omega]
  rw [run_unpairRight_instruction (value := limitsCode)
    recoveryLegalSumProjectionProgram_at11 rfl
    (by
      simp [state₁₁, NPOracleState.write, NPOracleState.jump,
        limitsCode])
    hlimitsCode]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 20
        state₁₂ =
      _
  rw [show 20 = 19 + 1 by omega]
  rw [run_unpairRight_instruction (value := limitsTail₀)
    recoveryLegalSumProjectionProgram_at12 rfl
    (by
      simp [state₁₂, NPOracleState.write, NPOracleState.jump,
        limitsTail₀])
    hlimitsTail₀]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 19
        state₁₃ =
      _
  rw [show 19 = 18 + 1 by omega]
  rw [run_unpairRight_instruction (value := limitsTail₁)
    recoveryLegalSumProjectionProgram_at13 rfl
    (by
      simp [state₁₃, NPOracleState.write, NPOracleState.jump,
        limitsTail₁])
    hlimitsTail₁]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 18
        state₁₄ =
      _
  rw [show 18 = 17 + 1 by omega]
  rw [run_unpairRight_instruction (value := legalPair)
    recoveryLegalSumProjectionProgram_at14 rfl
    (by
      simp [state₁₄, NPOracleState.write, NPOracleState.jump, legalPair])
    hlegalPair]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 17
        state₁₅ =
      runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 17
        (recoveryLegalSumProjectionPrefixState inputLength handoff)
  congr 1

set_option maxHeartbeats 600000 in
-- The common assembly is independent of which validated mode was selected.
private theorem run_recoveryLegalSumProjectionAssembly
    (inputLength handoff extra : ℕ) (state : NPOracleState)
    (hpc : state.pc = 23)
    (hselected :
      state.registers 12 = handoffSelectedLegalLimits handoff)
    (hmodeFlag :
      state.registers 13 = handoffLegalSumModeFlag handoff)
    (htupleFlag :
      state.registers 4 = recoveryLegalSumTupleFlag handoff)
    (hterms :
      state.registers 8 = recoveryLegalSumTermsCode handoff)
    (hq : state.registers 7 = recoveryLegalSumQCode handoff)
    (hhandoff : state.registers 3 = handoff) :
    runNPOracleProgram recoveryLegalSumProjectionProgram
        (recoveryLegalSumProjectionBits inputLength handoff)
        (extra + 10) state =
      some (recoveryLegalSumProjectionOutput handoff) := by
  let selected := handoffSelectedLegalLimits handoff
  let selectedTail := (Nat.unpair selected).2
  let expected := handoffSelectedExpectedArity handoff
  let termCap := handoffSelectedTermCap handoff
  let capHandoff := Nat.pair termCap handoff
  let expectedRest := Nat.pair expected capHandoff
  let termsRest :=
    Nat.pair (recoveryLegalSumTermsCode handoff) expectedRest
  let modeRest :=
    Nat.pair (handoffLegalSumModeFlag handoff) termsRest
  let context :=
    Nat.pair (recoveryLegalSumTupleFlag handoff) modeRest
  let output := Nat.pair (recoveryLegalSumQCode handoff) context
  let maximumBits := recoveryLegalSumProjectionBits inputLength handoff
  let state₂₄ := (state.write 14 expected).jump 24
  let state₂₅ := (state₂₄.write 12 selectedTail).jump 25
  let state₂₆ := (state₂₅.write 15 termCap).jump 26
  let state₂₇ := (state₂₆.write 16 capHandoff).jump 27
  let state₂₈ := (state₂₇.write 16 expectedRest).jump 28
  let state₂₉ := (state₂₈.write 16 termsRest).jump 29
  let state₃₀ := (state₂₉.write 16 modeRest).jump 30
  let state₃₁ := (state₃₀.write 16 context).jump 31
  let state₃₂ := (state₃₁.write 0 output).jump 32
  have hexpected : natBitLength expected ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, expected]
  have hselectedTail : natBitLength selectedTail ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, selected, selectedTail]
  have htermCap : natBitLength termCap ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, termCap]
  have hcapHandoff : natBitLength capHandoff ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, termCap, capHandoff]
  have hexpectedRest : natBitLength expectedRest ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, expected, termCap,
      capHandoff, expectedRest]
  have htermsRest : natBitLength termsRest ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, expected, termCap,
      capHandoff, expectedRest, termsRest]
  have hmodeRest : natBitLength modeRest ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, expected, termCap,
      capHandoff, expectedRest, termsRest, modeRest]
  have hcontext : natBitLength context ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, expected, termCap,
      capHandoff, expectedRest, termsRest, modeRest, context]
  have houtput : natBitLength output ≤ maximumBits := by
    have hmember :
        recoveryLegalSumProjectionOutput handoff ∈
          recoveryLegalSumProjectionValues inputLength handoff := by
      simp [recoveryLegalSumProjectionValues]
    simpa [output, context, modeRest, termsRest, expectedRest,
      capHandoff, expected, termCap, recoveryLegalSumProjectionOutput,
      recoveryLegalSumContext] using
      (recoveryLegalSumProjectionValue_bits hmember)
  rw [show extra + 10 = (extra + 9) + 1 by omega]
  rw [run_unpairLeft_instruction (value := expected)
    recoveryLegalSumProjectionProgram_at23 hpc
    (by
      simp [hselected, expected, handoffSelectedExpectedArity])
    hexpected]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits
        (extra + 9) state₂₄ =
      _
  rw [show extra + 9 = (extra + 8) + 1 by omega]
  rw [run_unpairRight_instruction (value := selectedTail)
    recoveryLegalSumProjectionProgram_at24 rfl
    (by simp [state₂₄, hselected, selectedTail, selected])
    hselectedTail]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits
        (extra + 8) state₂₅ =
      _
  rw [show extra + 8 = (extra + 7) + 1 by omega]
  rw [run_unpairLeft_instruction (value := termCap)
    recoveryLegalSumProjectionProgram_at25 rfl
    (by
      simp [state₂₅, state₂₄, termCap, handoffSelectedTermCap,
        selectedTail, selected])
    htermCap]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits
        (extra + 7) state₂₆ =
      _
  rw [show extra + 7 = (extra + 6) + 1 by omega]
  rw [run_pair_instruction (value := capHandoff)
    recoveryLegalSumProjectionProgram_at26 rfl
    (by
      simp [state₂₆, state₂₅, state₂₄, capHandoff, hhandoff])
    hcapHandoff]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits
        (extra + 6) state₂₇ =
      _
  rw [show extra + 6 = (extra + 5) + 1 by omega]
  rw [run_pair_instruction (value := expectedRest)
    recoveryLegalSumProjectionProgram_at27 rfl
    (by
      simp [state₂₇, state₂₆, state₂₅, state₂₄, expectedRest])
    hexpectedRest]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits
        (extra + 5) state₂₈ =
      _
  rw [show extra + 5 = (extra + 4) + 1 by omega]
  rw [run_pair_instruction (value := termsRest)
    recoveryLegalSumProjectionProgram_at28 rfl
    (by
      simp [state₂₈, state₂₇, state₂₆, state₂₅, state₂₄,
        termsRest, hterms])
    htermsRest]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits
        (extra + 4) state₂₉ =
      _
  rw [show extra + 4 = (extra + 3) + 1 by omega]
  rw [run_pair_instruction (value := modeRest)
    recoveryLegalSumProjectionProgram_at29 rfl
    (by
      simp [state₂₉, state₂₈, state₂₇, state₂₆, state₂₅, state₂₄,
        modeRest, hmodeFlag])
    hmodeRest]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits
        (extra + 3) state₃₀ =
      _
  rw [show extra + 3 = (extra + 2) + 1 by omega]
  rw [run_pair_instruction (value := context)
    recoveryLegalSumProjectionProgram_at30 rfl
    (by
      simp [state₃₀, state₂₉, state₂₈, state₂₇, state₂₆, state₂₅,
        state₂₄, context, htupleFlag])
    hcontext]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits
        (extra + 2) state₃₁ =
      _
  rw [show extra + 2 = (extra + 1) + 1 by omega]
  rw [run_pair_instruction (value := output)
    recoveryLegalSumProjectionProgram_at31 rfl
    (by
      simp [state₃₁, state₃₀, state₂₉, state₂₈, state₂₇, state₂₆,
        state₂₅, state₂₄, output, hq])
    houtput]
  change
    runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits
        (extra + 1) state₃₂ =
      _
  exact run_halt_instruction (fuel := extra) (value := output)
    recoveryLegalSumProjectionProgram_at32 rfl
    (by simp [state₃₂]) houtput

set_option maxHeartbeats 600000 in
-- Reject every non-published mode while sharing one exact assembly path.
private theorem run_recoveryLegalSumProjectionSuffix
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumProjectionProgram
        (recoveryLegalSumProjectionBits inputLength handoff) 17
        (recoveryLegalSumProjectionPrefixState inputLength handoff) =
      some (recoveryLegalSumProjectionOutput handoff) := by
  let mode := handoffMode handoff
  let legalPair := handoffLegalLimitsPair handoff
  let maximumBits := recoveryLegalSumProjectionBits inputLength handoff
  let state₁₅ := recoveryLegalSumProjectionPrefixState inputLength handoff
  have hmode : state₁₅.registers 9 = mode := by
    simp [state₁₅, recoveryLegalSumProjectionPrefixState,
      initialNPOracleState, NPOracleState.write, NPOracleState.jump, mode]
  have hlegalPair : state₁₅.registers 11 = legalPair := by
    simp [state₁₅, recoveryLegalSumProjectionPrefixState,
      initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      legalPair, handoffLegalLimitsPair, handoffLimitsCode]
  have htupleFlag :
      state₁₅.registers 4 = recoveryLegalSumTupleFlag handoff := by
    simp [state₁₅, recoveryLegalSumProjectionPrefixState,
      initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  have hterms :
      state₁₅.registers 8 = recoveryLegalSumTermsCode handoff := by
    simp [state₁₅, recoveryLegalSumProjectionPrefixState,
      initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  have hq :
      state₁₅.registers 7 = recoveryLegalSumQCode handoff := by
    simp [state₁₅, recoveryLegalSumProjectionPrefixState,
      initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  have hhandoff : state₁₅.registers 3 = handoff := by
    simp [state₁₅, recoveryLegalSumProjectionPrefixState,
      initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  have hzero : natBitLength 0 ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues]
  have hone : natBitLength 1 ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues]
  have hmodeBits : natBitLength mode ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, mode]
  have hleftBits :
      natBitLength (Nat.unpair legalPair).1 ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, legalPair]
  have hrightBits :
      natBitLength (Nat.unpair legalPair).2 ≤ maximumBits := by
    apply recoveryLegalSumProjectionValue_bits
    simp [recoveryLegalSumProjectionValues, legalPair]
  rw [show 17 = 16 + 1 by omega]
  rw [run_branchZero_instruction
    recoveryLegalSumProjectionProgram_at15 rfl]
  by_cases hmodeZero : mode = 0
  · rw [show state₁₅.registers 9 = 0 by simpa [hmodeZero] using hmode]
    rw [if_pos rfl]
    let state₃₃ := state₁₅.jump 33
    rw [show 16 = 15 + 1 by omega]
    rw [run_set_instruction (value := 0)
      recoveryLegalSumProjectionProgram_at33 rfl hzero]
    let state₃₄ := (state₃₃.write 12 0).jump 34
    change
      runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 15
          state₃₄ =
        _
    rw [show 15 = 14 + 1 by omega]
    rw [run_set_instruction (value := 0)
      recoveryLegalSumProjectionProgram_at34 rfl hzero]
    let state₂₃ := (state₃₄.write 13 0).jump 23
    change
      runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 14
          state₂₃ =
        _
    apply run_recoveryLegalSumProjectionAssembly
        (extra := 4) (state := state₂₃)
    · rfl
    · simp [state₂₃, state₃₄, state₃₃,
        handoffSelectedLegalLimits, mode, hmodeZero]
    · simp [state₂₃, handoffLegalSumModeFlag, mode,
        hmodeZero]
    · simp [state₂₃, state₃₄, state₃₃, htupleFlag]
    · simp [state₂₃, state₃₄, state₃₃, hterms]
    · simp [state₂₃, state₃₄, state₃₃, hq]
    · simp [state₂₃, state₃₄, state₃₃, hhandoff]
  · rw [show state₁₅.registers 9 = mode by exact hmode]
    rw [if_neg hmodeZero]
    let state₁₆ := state₁₅.jump 16
    rw [show 16 = 15 + 1 by omega]
    rw [run_decrement_instruction (value := mode.pred)
      recoveryLegalSumProjectionProgram_at16 rfl
      (by
        simp only [NPOracleState.jump]
        rw [hmode])
      ((decrement_bits_le mode).trans hmodeBits)]
    let state₁₇ := (state₁₆.write 9 mode.pred).jump 17
    change
      runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 15
          state₁₇ =
        _
    rw [show 15 = 14 + 1 by omega]
    rw [run_branchZero_instruction
      recoveryLegalSumProjectionProgram_at17 rfl]
    by_cases hmodeOne : mode = 1
    · rw [show state₁₇.registers 9 = 0 by
        simp [state₁₇, hmodeOne]]
      rw [if_pos rfl]
      let state₂₀ := state₁₇.jump 20
      rw [show 14 = 13 + 1 by omega]
      rw [run_unpairLeft_instruction
        (value := (Nat.unpair legalPair).1)
        recoveryLegalSumProjectionProgram_at20 rfl
        (by
          simp only [state₁₇, state₁₆, NPOracleState.jump,
            NPOracleState.write, if_neg (by omega : 11 ≠ 9)]
          rw [hlegalPair])
        hleftBits]
      let state₂₂ :=
        (state₂₀.write 12 (Nat.unpair legalPair).1).jump 22
      change
        runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 13
            state₂₂ =
          _
      rw [show 13 = 12 + 1 by omega]
      rw [run_set_instruction (value := 1)
        recoveryLegalSumProjectionProgram_at22 rfl hone]
      let state₂₃ := (state₂₂.write 13 1).jump 23
      change
        runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 12
            state₂₃ =
          _
      apply run_recoveryLegalSumProjectionAssembly
          (extra := 2) (state := state₂₃)
      · rfl
      · simp [state₂₃, state₂₂, state₂₀,
          handoffSelectedLegalLimits, mode, legalPair, hmodeOne]
      · simp [state₂₃, handoffLegalSumModeFlag, mode,
          hmodeOne]
      · simp [state₂₃, state₂₂, state₂₀, state₁₇, state₁₆,
          htupleFlag]
      · simp [state₂₃, state₂₂, state₂₀, state₁₇, state₁₆, hterms]
      · simp [state₂₃, state₂₂, state₂₀, state₁₇, state₁₆, hq]
      · simp [state₂₃, state₂₂, state₂₀, state₁₇, state₁₆, hhandoff]
    · rw [show state₁₇.registers 9 = mode.pred by
        simp [state₁₇]]
      have hmodePred : mode.pred ≠ 0 := by
        simp only [Nat.pred_eq_sub_one]
        omega
      rw [if_neg hmodePred]
      let state₁₈ := state₁₇.jump 18
      rw [show 14 = 13 + 1 by omega]
      rw [run_decrement_instruction (value := mode.pred.pred)
        recoveryLegalSumProjectionProgram_at18 rfl
        (by
          simp [state₁₇, NPOracleState.jump, NPOracleState.write])
        ((decrement_bits_le mode.pred).trans <|
          (decrement_bits_le mode).trans hmodeBits)]
      let state₁₉ := (state₁₈.write 9 mode.pred.pred).jump 19
      change
        runNPOracleProgram recoveryLegalSumProjectionProgram maximumBits 13
            state₁₉ =
          _
      rw [show 13 = 12 + 1 by omega]
      rw [run_branchZero_instruction
        recoveryLegalSumProjectionProgram_at19 rfl]
      by_cases hmodeTwo : mode = 2
      · rw [show state₁₉.registers 9 = 0 by
          simp [state₁₉, hmodeTwo]]
        rw [if_pos rfl]
        let state₂₁ := state₁₉.jump 21
        rw [show 12 = 11 + 1 by omega]
        rw [run_unpairRight_instruction
          (value := (Nat.unpair legalPair).2)
          recoveryLegalSumProjectionProgram_at21 rfl
          (by
            simp only [state₁₉, state₁₈, state₁₇, state₁₆,
              NPOracleState.jump, NPOracleState.write,
              if_neg (by omega : 11 ≠ 9)]
            rw [hlegalPair])
          hrightBits]
        let state₂₂ :=
          (state₂₁.write 12 (Nat.unpair legalPair).2).jump 22
        change
          runNPOracleProgram recoveryLegalSumProjectionProgram
              maximumBits 11 state₂₂ =
            _
        rw [show 11 = 10 + 1 by omega]
        rw [run_set_instruction (value := 1)
          recoveryLegalSumProjectionProgram_at22 rfl hone]
        let state₂₃ := (state₂₂.write 13 1).jump 23
        change
          runNPOracleProgram recoveryLegalSumProjectionProgram
              maximumBits 10 state₂₃ =
            _
        apply run_recoveryLegalSumProjectionAssembly
            (extra := 0) (state := state₂₃)
        · rfl
        · simp [state₂₃, state₂₂, state₂₁,
            handoffSelectedLegalLimits, mode, legalPair, hmodeTwo]
        · simp [state₂₃, handoffLegalSumModeFlag, mode,
            hmodeTwo]
        · simp [state₂₃, state₂₂, state₂₁, state₁₉, state₁₈,
            state₁₇, state₁₆, htupleFlag]
        · simp [state₂₃, state₂₂, state₂₁, state₁₉, state₁₈,
            state₁₇, state₁₆, hterms]
        · simp [state₂₃, state₂₂, state₂₁, state₁₉, state₁₈,
            state₁₇, state₁₆, hq]
        · simp [state₂₃, state₂₂, state₂₁, state₁₉, state₁₈,
            state₁₇, state₁₆, hhandoff]
      · rw [show state₁₉.registers 9 = mode.pred.pred by
          simp [state₁₉]]
        have hmodePredPred : mode.pred.pred ≠ 0 := by
          simp only [Nat.pred_eq_sub_one]
          omega
        rw [if_neg hmodePredPred]
        let state₃₃ := state₁₉.jump 33
        rw [show 12 = 11 + 1 by omega]
        rw [run_set_instruction (value := 0)
          recoveryLegalSumProjectionProgram_at33 rfl hzero]
        let state₃₄ := (state₃₃.write 12 0).jump 34
        change
          runNPOracleProgram recoveryLegalSumProjectionProgram
              maximumBits 11 state₃₄ =
            _
        rw [show 11 = 10 + 1 by omega]
        rw [run_set_instruction (value := 0)
          recoveryLegalSumProjectionProgram_at34 rfl hzero]
        let state₂₃ := (state₃₄.write 13 0).jump 23
        change
          runNPOracleProgram recoveryLegalSumProjectionProgram
              maximumBits 10 state₂₃ =
            _
        apply run_recoveryLegalSumProjectionAssembly
            (extra := 0) (state := state₂₃)
        · rfl
        · simp [state₂₃, state₃₄, state₃₃,
            handoffSelectedLegalLimits, mode, hmodeOne, hmodeTwo]
        · simp [state₂₃, handoffLegalSumModeFlag, mode,
            hmodeOne, hmodeTwo]
        · simp [state₂₃, state₃₄, state₃₃, state₁₉, state₁₈,
            state₁₇, state₁₆, htupleFlag]
        · simp [state₂₃, state₃₄, state₃₃, state₁₉, state₁₈,
            state₁₇, state₁₆, hterms]
        · simp [state₂₃, state₃₄, state₃₃, state₁₉, state₁₈,
            state₁₇, state₁₆, hq]
        · simp [state₂₃, state₃₄, state₃₃, state₁₉, state₁₈,
            state₁₇, state₁₆, hhandoff]

theorem run_recoveryLegalSumProjectionProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumProjectionProgram
        (recoveryLegalSumProjectionBits inputLength handoff)
        recoveryLegalSumProjectionFuel
        (initialNPOracleState inputLength
          (recoveryLegalSumProjectionInput handoff)) =
      some (recoveryLegalSumProjectionOutput handoff) := by
  rw [show recoveryLegalSumProjectionFuel = 32 by rfl]
  rw [run_recoveryLegalSumProjectionCorePrefix inputLength handoff]
  rw [run_recoveryLegalSumProjectionLimitPrefix inputLength handoff]
  exact run_recoveryLegalSumProjectionSuffix inputLength handoff

def recoveryLegalSumTupleStageOutput (handoff : ℕ) : ℕ :=
  recoveryLegalSumProjectionInput handoff

def recoveryLegalSumTupleStageProgram : NPOracleProgram :=
  preserveRightProgram (taggedTupleProgram 2)

@[simp] theorem recoveryLegalSumTupleStageProgram_oracleFree :
    OracleFree recoveryLegalSumTupleStageProgram :=
  preserveRightProgram_oracleFree (taggedTupleProgram 2)
    (taggedTupleProgram_oracleFree 2)

def recoveryLegalSumTupleStageFuel : ℕ :=
  preserveRightFuel (taggedTupleFuel 2)

def recoveryLegalSumTupleStageBits
    (inputLength handoff : ℕ) : ℕ :=
  preserveRightBits
    (taggedTupleBits inputLength 2 (handoffSumCode handoff))
    (handoffSumCode handoff) handoff
    (recoveryLegalSumTupleOutput handoff)

theorem run_recoveryLegalSumTupleStageProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumTupleStageProgram
        (recoveryLegalSumTupleStageBits inputLength handoff)
        recoveryLegalSumTupleStageFuel
        (initialNPOracleState inputLength
          (recoveryLegalSumTupleLoweringOutput handoff)) =
      some (recoveryLegalSumTupleStageOutput handoff) := by
  exact run_preserveRightProgram (taggedTupleProgram 2) inputLength
    (taggedTupleBits inputLength 2 (handoffSumCode handoff))
    (taggedTupleFuel 2) (handoffSumCode handoff) handoff
    (recoveryLegalSumTupleOutput handoff)
    (run_taggedTupleProgram inputLength 2 (handoffSumCode handoff))

def recoveryLegalSumQValidation (handoff : ℕ) : ℕ :=
  canonicalNatValidationOutput (recoveryLegalSumQCode handoff)

def recoveryLegalSumQStageOutput (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalSumQValidation handoff)
    (recoveryLegalSumContext handoff)

def recoveryLegalSumQStageProgram : NPOracleProgram :=
  preserveRightProgram canonicalNatValidationProgram

@[simp] theorem recoveryLegalSumQStageProgram_oracleFree :
    OracleFree recoveryLegalSumQStageProgram :=
  preserveRightProgram_oracleFree canonicalNatValidationProgram
    canonicalNatValidationProgram_oracleFree

def recoveryLegalSumQStageFuel (handoff : ℕ) : ℕ :=
  preserveRightFuel <|
    canonicalNatValidationFuel (recoveryLegalSumQCode handoff)

def recoveryLegalSumQStageBits
    (inputLength handoff : ℕ) : ℕ :=
  preserveRightBits
    (canonicalNatValidationBits inputLength (recoveryLegalSumQCode handoff))
    (recoveryLegalSumQCode handoff)
    (recoveryLegalSumContext handoff)
    (recoveryLegalSumQValidation handoff)

theorem run_recoveryLegalSumQStageProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumQStageProgram
        (recoveryLegalSumQStageBits inputLength handoff)
        (recoveryLegalSumQStageFuel handoff)
        (initialNPOracleState inputLength
          (recoveryLegalSumProjectionOutput handoff)) =
      some (recoveryLegalSumQStageOutput handoff) := by
  exact run_preserveRightProgram canonicalNatValidationProgram inputLength
    (canonicalNatValidationBits inputLength (recoveryLegalSumQCode handoff))
    (canonicalNatValidationFuel (recoveryLegalSumQCode handoff))
    (recoveryLegalSumQCode handoff) (recoveryLegalSumContext handoff)
    (recoveryLegalSumQValidation handoff)
    (run_canonicalNatValidationProgram inputLength
      (recoveryLegalSumQCode handoff))

def recoveryLegalSumArityValue (handoff : ℕ) : ℕ :=
  (Nat.unpair (recoveryLegalSumQValidation handoff)).2

def recoveryLegalSumQFlag (handoff : ℕ) : ℕ :=
  (Nat.unpair (recoveryLegalSumQValidation handoff)).1

def recoveryLegalSumArityRequest (handoff : ℕ) : ℕ :=
  nativeNatEqInput (recoveryLegalSumArityValue handoff)
    (handoffSelectedExpectedArity handoff)

def recoveryLegalSumArityContext (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalSumQFlag handoff)
    (recoveryLegalSumContext handoff)

def recoveryLegalSumArityLoweringOutput (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalSumArityRequest handoff)
    (recoveryLegalSumArityContext handoff)

def recoveryLegalSumArityLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairRight 3 6 5
  , .unpairRight 6 6 6
  , .unpairRight 6 6 7
  , .unpairLeft 6 7 8
  , .pair 5 7 8 9
  , .pair 4 3 9 10
  , .pair 8 9 0 11
  , .halt 0
  ]

@[simp] theorem recoveryLegalSumArityLoweringProgram_oracleFree :
    OracleFree recoveryLegalSumArityLoweringProgram := by
  rfl

def recoveryLegalSumArityLoweringFuel : ℕ := 12

def recoveryLegalSumArityLoweringValues
    (inputLength handoff : ℕ) : List ℕ :=
  let qValidation := recoveryLegalSumQValidation handoff
  let context := recoveryLegalSumContext handoff
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  [ inputLength
  , recoveryLegalSumQStageOutput handoff
  , qValidation
  , context
  , recoveryLegalSumQFlag handoff
  , recoveryLegalSumArityValue handoff
  , modeRest
  , termsRest
  , expectedRest
  , handoffSelectedExpectedArity handoff
  , recoveryLegalSumArityRequest handoff
  , recoveryLegalSumArityContext handoff
  , recoveryLegalSumArityLoweringOutput handoff
  ]

def recoveryLegalSumArityLoweringBits
    (inputLength handoff : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalSumArityLoweringValues inputLength handoff).foldr max 0

theorem recoveryLegalSumArityLoweringValue_bits
    {inputLength handoff value : ℕ}
    (hvalue :
      value ∈ recoveryLegalSumArityLoweringValues inputLength handoff) :
    natBitLength value ≤
      recoveryLegalSumArityLoweringBits inputLength handoff := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

theorem run_recoveryLegalSumArityLoweringProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumArityLoweringProgram
        (recoveryLegalSumArityLoweringBits inputLength handoff)
        recoveryLegalSumArityLoweringFuel
        (initialNPOracleState inputLength
          (recoveryLegalSumQStageOutput handoff)) =
      some (recoveryLegalSumArityLoweringOutput handoff) := by
  let qValidation := recoveryLegalSumQValidation handoff
  let context := recoveryLegalSumContext handoff
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  have hbits :
      ∀ value ∈ recoveryLegalSumArityLoweringValues inputLength handoff,
        natBitLength value ≤
          recoveryLegalSumArityLoweringBits inputLength handoff := by
    intro value hvalue
    exact recoveryLegalSumArityLoweringValue_bits hvalue
  have hqValidation := hbits qValidation (by
    simp [recoveryLegalSumArityLoweringValues, qValidation])
  have hcontext := hbits context (by
    simp [recoveryLegalSumArityLoweringValues, context])
  have hqFlag := hbits (recoveryLegalSumQFlag handoff) (by
    simp [recoveryLegalSumArityLoweringValues])
  have hqValue := hbits (recoveryLegalSumArityValue handoff) (by
    simp [recoveryLegalSumArityLoweringValues])
  have hmodeRest := hbits modeRest (by
    simp [recoveryLegalSumArityLoweringValues, modeRest, context])
  have htermsRest := hbits termsRest (by
    simp [recoveryLegalSumArityLoweringValues, termsRest, modeRest,
      context])
  have hexpectedRest := hbits expectedRest (by
    simp [recoveryLegalSumArityLoweringValues, expectedRest, termsRest,
      modeRest, context])
  have hexpected := hbits (handoffSelectedExpectedArity handoff) (by
    simp [recoveryLegalSumArityLoweringValues])
  have hrequest := hbits (recoveryLegalSumArityRequest handoff) (by
    simp [recoveryLegalSumArityLoweringValues])
  have harityContext := hbits (recoveryLegalSumArityContext handoff) (by
    simp [recoveryLegalSumArityLoweringValues])
  have houtput := hbits (recoveryLegalSumArityLoweringOutput handoff) (by
    simp [recoveryLegalSumArityLoweringValues])
  rw [show recoveryLegalSumArityLoweringFuel = 11 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := qValidation)
    (by rfl) rfl
    (by simp [initialNPOracleState, recoveryLegalSumQStageOutput,
      qValidation])
    hqValidation]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, recoveryLegalSumQStageOutput,
      qValidation, context])
    hcontext]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := recoveryLegalSumQFlag handoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, qValidation,
      recoveryLegalSumQFlag])
    hqFlag]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := recoveryLegalSumArityValue handoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, qValidation,
      recoveryLegalSumArityValue])
    hqValue]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := modeRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context, modeRest])
    hmodeRest]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := termsRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, modeRest,
      termsRest])
    htermsRest]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := expectedRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, termsRest,
      expectedRest])
    hexpectedRest]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := handoffSelectedExpectedArity handoff)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, expectedRest,
        termsRest, modeRest, context, recoveryLegalSumContext])
    hexpected]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := recoveryLegalSumArityRequest handoff)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        recoveryLegalSumArityRequest, nativeNatEqInput])
    hrequest]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := recoveryLegalSumArityContext handoff)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        recoveryLegalSumArityContext, qValidation, context,
        recoveryLegalSumQFlag])
    harityContext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := recoveryLegalSumArityLoweringOutput handoff)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        recoveryLegalSumArityLoweringOutput])
    houtput]
  exact run_halt_instruction (fuel := 0)
    (value := recoveryLegalSumArityLoweringOutput handoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

def recoveryLegalSumArityFlag (handoff : ℕ) : ℕ :=
  nativeNatEqOutput (recoveryLegalSumArityValue handoff)
    (handoffSelectedExpectedArity handoff)

def recoveryLegalSumArityStageOutput (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalSumArityFlag handoff)
    (recoveryLegalSumArityContext handoff)

def recoveryLegalSumArityStageProgram : NPOracleProgram :=
  preserveRightProgram nativeNatEqProgram

@[simp] theorem recoveryLegalSumArityStageProgram_oracleFree :
    OracleFree recoveryLegalSumArityStageProgram :=
  preserveRightProgram_oracleFree nativeNatEqProgram
    nativeNatEqProgram_oracleFree

def recoveryLegalSumArityStageFuel (handoff : ℕ) : ℕ :=
  preserveRightFuel <|
    nativeNatEqFuel (recoveryLegalSumArityValue handoff)
      (handoffSelectedExpectedArity handoff)

def recoveryLegalSumArityStageBits
    (inputLength handoff : ℕ) : ℕ :=
  preserveRightBits
    (nativeNatEqBits inputLength (recoveryLegalSumArityValue handoff)
      (handoffSelectedExpectedArity handoff))
    (recoveryLegalSumArityRequest handoff)
    (recoveryLegalSumArityContext handoff)
    (recoveryLegalSumArityFlag handoff)

theorem run_recoveryLegalSumArityStageProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumArityStageProgram
        (recoveryLegalSumArityStageBits inputLength handoff)
        (recoveryLegalSumArityStageFuel handoff)
        (initialNPOracleState inputLength
          (recoveryLegalSumArityLoweringOutput handoff)) =
      some (recoveryLegalSumArityStageOutput handoff) := by
  exact run_preserveRightProgram nativeNatEqProgram inputLength
    (nativeNatEqBits inputLength (recoveryLegalSumArityValue handoff)
      (handoffSelectedExpectedArity handoff))
    (nativeNatEqFuel (recoveryLegalSumArityValue handoff)
      (handoffSelectedExpectedArity handoff))
    (recoveryLegalSumArityRequest handoff)
    (recoveryLegalSumArityContext handoff)
    (recoveryLegalSumArityFlag handoff)
    (run_nativeNatEqProgram inputLength
      (recoveryLegalSumArityValue handoff)
      (handoffSelectedExpectedArity handoff))

def recoveryLegalSumTermsLoweringOutput (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalSumTermsCode handoff)
    (recoveryLegalSumArityStageOutput handoff)

def recoveryLegalSumTermsLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 5 3
  , .unpairRight 5 6 4
  , .unpairRight 6 7 5
  , .unpairLeft 7 8 6
  , .pair 2 3 9 7
  , .pair 8 9 0 8
  , .halt 0
  ]

@[simp] theorem recoveryLegalSumTermsLoweringProgram_oracleFree :
    OracleFree recoveryLegalSumTermsLoweringProgram := by
  rfl

def recoveryLegalSumTermsLoweringFuel : ℕ := 9

def recoveryLegalSumTermsLoweringValues
    (inputLength handoff : ℕ) : List ℕ :=
  let arityContext := recoveryLegalSumArityContext handoff
  let context := recoveryLegalSumContext handoff
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  [ inputLength
  , recoveryLegalSumArityStageOutput handoff
  , recoveryLegalSumArityFlag handoff
  , arityContext
  , context
  , modeRest
  , termsRest
  , recoveryLegalSumTermsCode handoff
  , recoveryLegalSumTermsLoweringOutput handoff
  ]

def recoveryLegalSumTermsLoweringBits
    (inputLength handoff : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalSumTermsLoweringValues inputLength handoff).foldr max 0

theorem recoveryLegalSumTermsLoweringValue_bits
    {inputLength handoff value : ℕ}
    (hvalue :
      value ∈ recoveryLegalSumTermsLoweringValues inputLength handoff) :
    natBitLength value ≤
      recoveryLegalSumTermsLoweringBits inputLength handoff := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

theorem run_recoveryLegalSumTermsLoweringProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumTermsLoweringProgram
        (recoveryLegalSumTermsLoweringBits inputLength handoff)
        recoveryLegalSumTermsLoweringFuel
        (initialNPOracleState inputLength
          (recoveryLegalSumArityStageOutput handoff)) =
      some (recoveryLegalSumTermsLoweringOutput handoff) := by
  let arityContext := recoveryLegalSumArityContext handoff
  let context := recoveryLegalSumContext handoff
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  have hbits :
      ∀ value ∈ recoveryLegalSumTermsLoweringValues inputLength handoff,
        natBitLength value ≤
          recoveryLegalSumTermsLoweringBits inputLength handoff := by
    intro value hvalue
    exact recoveryLegalSumTermsLoweringValue_bits hvalue
  have harityFlag := hbits (recoveryLegalSumArityFlag handoff) (by
    simp [recoveryLegalSumTermsLoweringValues])
  have harityContext := hbits arityContext (by
    simp [recoveryLegalSumTermsLoweringValues, arityContext])
  have hcontext := hbits context (by
    simp [recoveryLegalSumTermsLoweringValues, context])
  have hmodeRest := hbits modeRest (by
    simp [recoveryLegalSumTermsLoweringValues, modeRest, context])
  have htermsRest := hbits termsRest (by
    simp [recoveryLegalSumTermsLoweringValues, termsRest, modeRest,
      context])
  have hterms := hbits (recoveryLegalSumTermsCode handoff) (by
    simp [recoveryLegalSumTermsLoweringValues])
  have harityOutput := hbits (recoveryLegalSumArityStageOutput handoff) (by
    simp [recoveryLegalSumTermsLoweringValues])
  have houtput := hbits (recoveryLegalSumTermsLoweringOutput handoff) (by
    simp [recoveryLegalSumTermsLoweringValues])
  rw [show recoveryLegalSumTermsLoweringFuel = 8 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := recoveryLegalSumArityFlag handoff)
    (by rfl) rfl
    (by simp [initialNPOracleState, recoveryLegalSumArityStageOutput])
    harityFlag]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := arityContext)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, recoveryLegalSumArityStageOutput,
      arityContext])
    harityContext]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, arityContext,
      recoveryLegalSumArityContext, context])
    hcontext]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := modeRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context, modeRest])
    hmodeRest]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := termsRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, modeRest,
      termsRest])
    htermsRest]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := recoveryLegalSumTermsCode handoff)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, termsRest,
        modeRest, context, recoveryLegalSumContext])
    hterms]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := recoveryLegalSumArityStageOutput handoff)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        recoveryLegalSumArityStageOutput, arityContext])
    harityOutput]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := recoveryLegalSumTermsLoweringOutput handoff)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        recoveryLegalSumTermsLoweringOutput])
    houtput]
  exact run_halt_instruction (fuel := 0)
    (value := recoveryLegalSumTermsLoweringOutput handoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

def recoveryLegalSumTermsValidation (handoff : ℕ) : ℕ :=
  balancedValidationMapGuardOutput (recoveryLegalSumTermsCode handoff)

def recoveryLegalSumTermsStageOutput (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalSumTermsValidation handoff)
    (recoveryLegalSumArityStageOutput handoff)

def recoveryLegalSumTermsStageProgram : NPOracleProgram :=
  preserveRightProgram balancedValidationMapGuardProgram

@[simp] theorem recoveryLegalSumTermsStageProgram_oracleFree :
    OracleFree recoveryLegalSumTermsStageProgram :=
  preserveRightProgram_oracleFree balancedValidationMapGuardProgram
    balancedValidationMapGuardProgram_oracleFree

def recoveryLegalSumTermsStageFuel (handoff : ℕ) : ℕ :=
  preserveRightFuel <|
    balancedValidationMapGuardFuel (recoveryLegalSumTermsCode handoff)

def recoveryLegalSumTermsStageBits
    (inputLength handoff : ℕ) : ℕ :=
  preserveRightBits
    (balancedValidationMapGuardBits inputLength
      (recoveryLegalSumTermsCode handoff))
    (recoveryLegalSumTermsCode handoff)
    (recoveryLegalSumArityStageOutput handoff)
    (recoveryLegalSumTermsValidation handoff)

theorem run_recoveryLegalSumTermsStageProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumTermsStageProgram
        (recoveryLegalSumTermsStageBits inputLength handoff)
        (recoveryLegalSumTermsStageFuel handoff)
        (initialNPOracleState inputLength
          (recoveryLegalSumTermsLoweringOutput handoff)) =
      some (recoveryLegalSumTermsStageOutput handoff) := by
  exact
    run_preserveRightProgram balancedValidationMapGuardProgram inputLength
      (balancedValidationMapGuardBits inputLength
        (recoveryLegalSumTermsCode handoff))
      (balancedValidationMapGuardFuel (recoveryLegalSumTermsCode handoff))
      (recoveryLegalSumTermsCode handoff)
      (recoveryLegalSumArityStageOutput handoff)
      (recoveryLegalSumTermsValidation handoff)
      (run_balancedValidationMapGuardProgram inputLength
        (recoveryLegalSumTermsCode handoff))

def recoveryLegalSumTermsGuardedCode (handoff : ℕ) : ℕ :=
  balancedValidationMapGuardedCode (recoveryLegalSumTermsCode handoff)

def recoveryLegalSumTermsFlag (handoff : ℕ) : ℕ :=
  balancedValidationMapFlag (recoveryLegalSumTermsCode handoff)

def recoveryLegalSumLengthContext (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalSumTermsFlag handoff)
    (recoveryLegalSumArityStageOutput handoff)

def recoveryLegalSumLengthLoweringOutput (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalSumTermsGuardedCode handoff)
    (recoveryLegalSumLengthContext handoff)

def recoveryLegalSumLengthLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairLeft 5 6 5
  , .pair 6 3 7 6
  , .pair 4 7 0 7
  , .halt 0
  ]

@[simp] theorem recoveryLegalSumLengthLoweringProgram_oracleFree :
    OracleFree recoveryLegalSumLengthLoweringProgram := by
  rfl

def recoveryLegalSumLengthLoweringFuel : ℕ := 8

def recoveryLegalSumLengthLoweringValues
    (inputLength handoff : ℕ) : List ℕ :=
  let termsValidation := recoveryLegalSumTermsValidation handoff
  let flagTerms := (Nat.unpair termsValidation).2
  [ inputLength
  , recoveryLegalSumTermsStageOutput handoff
  , termsValidation
  , recoveryLegalSumArityStageOutput handoff
  , recoveryLegalSumTermsGuardedCode handoff
  , flagTerms
  , recoveryLegalSumTermsFlag handoff
  , recoveryLegalSumLengthContext handoff
  , recoveryLegalSumLengthLoweringOutput handoff
  ]

def recoveryLegalSumLengthLoweringBits
    (inputLength handoff : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalSumLengthLoweringValues inputLength handoff).foldr max 0

theorem recoveryLegalSumLengthLoweringValue_bits
    {inputLength handoff value : ℕ}
    (hvalue :
      value ∈ recoveryLegalSumLengthLoweringValues inputLength handoff) :
    natBitLength value ≤
      recoveryLegalSumLengthLoweringBits inputLength handoff := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

theorem run_recoveryLegalSumLengthLoweringProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumLengthLoweringProgram
        (recoveryLegalSumLengthLoweringBits inputLength handoff)
        recoveryLegalSumLengthLoweringFuel
        (initialNPOracleState inputLength
          (recoveryLegalSumTermsStageOutput handoff)) =
      some (recoveryLegalSumLengthLoweringOutput handoff) := by
  let termsValidation := recoveryLegalSumTermsValidation handoff
  let flagTerms := (Nat.unpair termsValidation).2
  have hvalidationShape :
      termsValidation =
        Nat.pair (recoveryLegalSumTermsGuardedCode handoff)
          (Nat.pair (recoveryLegalSumTermsFlag handoff)
            (recoveryLegalSumTermsCode handoff)) := by
    rfl
  have hflagTermsShape :
      flagTerms =
        Nat.pair (recoveryLegalSumTermsFlag handoff)
          (recoveryLegalSumTermsCode handoff) := by
    simp only [flagTerms, hvalidationShape, Nat.unpair_pair]
  have hbits :
      ∀ value ∈ recoveryLegalSumLengthLoweringValues inputLength handoff,
        natBitLength value ≤
          recoveryLegalSumLengthLoweringBits inputLength handoff := by
    intro value hvalue
    exact recoveryLegalSumLengthLoweringValue_bits hvalue
  have hvalidation := hbits termsValidation (by
    simp [recoveryLegalSumLengthLoweringValues, termsValidation])
  have harityOutput := hbits (recoveryLegalSumArityStageOutput handoff) (by
    simp [recoveryLegalSumLengthLoweringValues])
  have hguarded := hbits (recoveryLegalSumTermsGuardedCode handoff) (by
    simp [recoveryLegalSumLengthLoweringValues])
  have hflagTerms := hbits flagTerms (by
    simp [recoveryLegalSumLengthLoweringValues, flagTerms,
      termsValidation])
  have htermsFlag := hbits (recoveryLegalSumTermsFlag handoff) (by
    simp [recoveryLegalSumLengthLoweringValues])
  have hcontext := hbits (recoveryLegalSumLengthContext handoff) (by
    simp [recoveryLegalSumLengthLoweringValues])
  have houtput := hbits (recoveryLegalSumLengthLoweringOutput handoff) (by
    simp [recoveryLegalSumLengthLoweringValues])
  rw [show recoveryLegalSumLengthLoweringFuel = 7 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := termsValidation)
    (by rfl) rfl
    (by simp [initialNPOracleState, recoveryLegalSumTermsStageOutput,
      termsValidation])
    hvalidation]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := recoveryLegalSumArityStageOutput handoff)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, recoveryLegalSumTermsStageOutput,
      termsValidation])
    harityOutput]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := recoveryLegalSumTermsGuardedCode handoff)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hvalidationShape])
    hguarded]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := flagTerms)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, termsValidation,
      flagTerms])
    hflagTerms]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := recoveryLegalSumTermsFlag handoff)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hflagTermsShape])
    htermsFlag]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := recoveryLegalSumLengthContext handoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      recoveryLegalSumLengthContext])
    hcontext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := recoveryLegalSumLengthLoweringOutput handoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      recoveryLegalSumLengthLoweringOutput])
    houtput]
  exact run_halt_instruction (fuel := 0)
    (value := recoveryLegalSumLengthLoweringOutput handoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

def recoveryLegalSumTermCodes (handoff : ℕ) : List ℕ :=
  balancedValidationMapCodes (recoveryLegalSumTermsCode handoff)

def recoveryLegalSumTermCount (handoff : ℕ) : ℕ :=
  (recoveryLegalSumTermCodes handoff).length

def recoveryLegalSumLengthStageOutput (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalSumTermCount handoff)
    (recoveryLegalSumLengthContext handoff)

def recoveryLegalSumLengthStageProgram : NPOracleProgram :=
  preserveRightProgram balancedLengthProgram

@[simp] theorem recoveryLegalSumLengthStageProgram_oracleFree :
    OracleFree recoveryLegalSumLengthStageProgram :=
  preserveRightProgram_oracleFree balancedLengthProgram
    balancedLengthProgram_oracleFree

def recoveryLegalSumLengthStageFuel (handoff : ℕ) : ℕ :=
  preserveRightFuel <|
    balancedLengthFuel (recoveryLegalSumTermCodes handoff)

def recoveryLegalSumLengthStageBits
    (inputLength handoff : ℕ) : ℕ :=
  preserveRightBits
    (balancedLengthBits inputLength (recoveryLegalSumTermCodes handoff))
    (recoveryLegalSumTermsGuardedCode handoff)
    (recoveryLegalSumLengthContext handoff)
    (recoveryLegalSumTermCount handoff)

theorem run_recoveryLegalSumLengthStageProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumLengthStageProgram
        (recoveryLegalSumLengthStageBits inputLength handoff)
        (recoveryLegalSumLengthStageFuel handoff)
        (initialNPOracleState inputLength
          (recoveryLegalSumLengthLoweringOutput handoff)) =
      some (recoveryLegalSumLengthStageOutput handoff) := by
  have hguarded :
      recoveryLegalSumTermsGuardedCode handoff =
        encodeBalancedList (recoveryLegalSumTermCodes handoff) := by
    exact balancedValidationMapGuardedCode_eq
      (recoveryLegalSumTermsCode handoff)
  rw [recoveryLegalSumLengthStageProgram,
    recoveryLegalSumLengthStageBits,
    recoveryLegalSumLengthStageFuel,
    recoveryLegalSumLengthLoweringOutput,
    recoveryLegalSumLengthStageOutput, hguarded]
  exact run_preserveRightProgram balancedLengthProgram inputLength
    (balancedLengthBits inputLength (recoveryLegalSumTermCodes handoff))
    (balancedLengthFuel (recoveryLegalSumTermCodes handoff))
    (encodeBalancedList (recoveryLegalSumTermCodes handoff))
    (recoveryLegalSumLengthContext handoff)
    (recoveryLegalSumTermCount handoff)
    (run_balancedLengthProgram inputLength
      (recoveryLegalSumTermCodes handoff))

def recoveryLegalSumBoundInput (handoff : ℕ) : ℕ :=
  recoveryBoundedContextInput
    (recoveryLegalSumTermCount handoff)
    (handoffSelectedTermCap handoff)
    (recoveryLegalSumLengthContext handoff)

def recoveryLegalSumBoundLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .unpairRight 4 5 4
  , .unpairRight 5 6 5
  , .unpairRight 6 7 6
  , .unpairRight 7 8 7
  , .unpairRight 8 9 8
  , .unpairRight 9 10 9
  , .unpairLeft 10 11 10
  , .pair 2 11 12 11
  , .pair 12 3 0 12
  , .halt 0
  ]

@[simp] theorem recoveryLegalSumBoundLoweringProgram_oracleFree :
    OracleFree recoveryLegalSumBoundLoweringProgram := by
  rfl

def recoveryLegalSumBoundLoweringFuel : ℕ := 13

def recoveryLegalSumBoundLoweringValues
    (inputLength handoff : ℕ) : List ℕ :=
  let lengthContext := recoveryLegalSumLengthContext handoff
  let arityStage := recoveryLegalSumArityStageOutput handoff
  let arityContext := recoveryLegalSumArityContext handoff
  let context := recoveryLegalSumContext handoff
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  let capHandoff := (Nat.unpair expectedRest).2
  let request :=
    nativeNatLeInput (recoveryLegalSumTermCount handoff)
      (handoffSelectedTermCap handoff)
  [ inputLength
  , recoveryLegalSumLengthStageOutput handoff
  , recoveryLegalSumTermCount handoff
  , lengthContext
  , arityStage
  , arityContext
  , context
  , modeRest
  , termsRest
  , expectedRest
  , capHandoff
  , handoffSelectedTermCap handoff
  , request
  , recoveryLegalSumBoundInput handoff
  ]

def recoveryLegalSumBoundLoweringBits
    (inputLength handoff : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalSumBoundLoweringValues inputLength handoff).foldr max 0

theorem recoveryLegalSumBoundLoweringValue_bits
    {inputLength handoff value : ℕ}
    (hvalue :
      value ∈ recoveryLegalSumBoundLoweringValues inputLength handoff) :
    natBitLength value ≤
      recoveryLegalSumBoundLoweringBits inputLength handoff := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

theorem run_recoveryLegalSumBoundLoweringProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumBoundLoweringProgram
        (recoveryLegalSumBoundLoweringBits inputLength handoff)
        recoveryLegalSumBoundLoweringFuel
        (initialNPOracleState inputLength
          (recoveryLegalSumLengthStageOutput handoff)) =
      some (recoveryLegalSumBoundInput handoff) := by
  let lengthContext := recoveryLegalSumLengthContext handoff
  let arityStage := recoveryLegalSumArityStageOutput handoff
  let arityContext := recoveryLegalSumArityContext handoff
  let context := recoveryLegalSumContext handoff
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  let capHandoff := (Nat.unpair expectedRest).2
  let request :=
    nativeNatLeInput (recoveryLegalSumTermCount handoff)
      (handoffSelectedTermCap handoff)
  have hbits :
      ∀ value ∈ recoveryLegalSumBoundLoweringValues inputLength handoff,
        natBitLength value ≤
          recoveryLegalSumBoundLoweringBits inputLength handoff := by
    intro value hvalue
    exact recoveryLegalSumBoundLoweringValue_bits hvalue
  have hcount := hbits (recoveryLegalSumTermCount handoff) (by
    simp [recoveryLegalSumBoundLoweringValues])
  have hlengthContext := hbits lengthContext (by
    simp [recoveryLegalSumBoundLoweringValues, lengthContext])
  have harityStage := hbits arityStage (by
    simp [recoveryLegalSumBoundLoweringValues, arityStage])
  have harityContext := hbits arityContext (by
    simp [recoveryLegalSumBoundLoweringValues, arityContext])
  have hcontext := hbits context (by
    simp [recoveryLegalSumBoundLoweringValues, context])
  have hmodeRest := hbits modeRest (by
    simp [recoveryLegalSumBoundLoweringValues, modeRest, context])
  have htermsRest := hbits termsRest (by
    simp [recoveryLegalSumBoundLoweringValues, termsRest, modeRest,
      context])
  have hexpectedRest := hbits expectedRest (by
    simp [recoveryLegalSumBoundLoweringValues, expectedRest, termsRest,
      modeRest, context])
  have hcapHandoff := hbits capHandoff (by
    simp [recoveryLegalSumBoundLoweringValues, capHandoff, expectedRest,
      termsRest, modeRest, context])
  have hcap := hbits (handoffSelectedTermCap handoff) (by
    simp [recoveryLegalSumBoundLoweringValues])
  have hrequest := hbits request (by
    simp [recoveryLegalSumBoundLoweringValues, request])
  have houtput := hbits (recoveryLegalSumBoundInput handoff) (by
    simp [recoveryLegalSumBoundLoweringValues])
  rw [show recoveryLegalSumBoundLoweringFuel = 12 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := recoveryLegalSumTermCount handoff)
    (by rfl) rfl
    (by simp [initialNPOracleState, recoveryLegalSumLengthStageOutput])
    hcount]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction (value := lengthContext)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, recoveryLegalSumLengthStageOutput,
      lengthContext])
    hlengthContext]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction (value := arityStage)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, lengthContext,
      recoveryLegalSumLengthContext, arityStage])
    harityStage]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := arityContext)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, arityStage,
      recoveryLegalSumArityStageOutput, arityContext])
    harityContext]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, arityContext,
      recoveryLegalSumArityContext, context])
    hcontext]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := modeRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context, modeRest])
    hmodeRest]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := termsRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, modeRest,
      termsRest])
    htermsRest]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := expectedRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, termsRest,
      expectedRest])
    hexpectedRest]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := capHandoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, expectedRest,
      capHandoff])
    hcapHandoff]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := handoffSelectedTermCap handoff)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, capHandoff,
        expectedRest, termsRest, modeRest, context,
        recoveryLegalSumContext])
    hcap]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := request)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, request,
      nativeNatLeInput])
    hrequest]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := recoveryLegalSumBoundInput handoff)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        recoveryLegalSumBoundInput, recoveryBoundedContextInput,
        request, lengthContext])
    houtput]
  exact run_halt_instruction (fuel := 0)
    (value := recoveryLegalSumBoundInput handoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

def recoveryLegalSumBoundOutput (handoff : ℕ) : ℕ :=
  recoveryBoundedContextOutput
    (recoveryLegalSumTermCount handoff)
    (handoffSelectedTermCap handoff)
    (recoveryLegalSumLengthContext handoff)

theorem run_recoveryLegalSumBoundProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryBoundedContextCheckProgram
        (recoveryBoundedContextCheckBits inputLength
          (recoveryLegalSumTermCount handoff)
          (handoffSelectedTermCap handoff)
          (recoveryLegalSumLengthContext handoff))
        (recoveryBoundedContextCheckFuel
          (recoveryLegalSumTermCount handoff)
          (handoffSelectedTermCap handoff))
        (initialNPOracleState inputLength
          (recoveryLegalSumBoundInput handoff)) =
      some (recoveryLegalSumBoundOutput handoff) := by
  exact run_recoveryBoundedContextCheckProgram inputLength
    (recoveryLegalSumTermCount handoff)
    (handoffSelectedTermCap handoff)
    (recoveryLegalSumLengthContext handoff)

def recoveryLegalTermCircuitArity (context : ℕ) : ℕ :=
  (Nat.unpair context).1

def recoveryLegalTermCircuitFamily (context : ℕ) : ℕ :=
  (Nat.unpair context).2

def recoveryLegalTermCircuitRequest
    (context validated : ℕ) : ℕ :=
  Nat.pair (recoveryLegalTermCircuitFamily context)
    (Nat.unpair (Nat.unpair validated).2).2

def recoveryLegalTermCircuitCallLoweringOutput
    (context validated : ℕ) : ℕ :=
  nativeInputRequest (recoveryLegalTermCircuitArity context)
    (recoveryLegalTermCircuitRequest context validated)

def recoveryLegalTermCircuitCallLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 1 2 1
  , .unpairRight 1 3 2
  , .unpairRight 0 4 3
  , .unpairRight 4 4 4
  , .pair 3 4 5 5
  , .pair 2 5 0 6
  , .halt 0
  ]

@[simp] theorem
    recoveryLegalTermCircuitCallLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermCircuitCallLoweringProgram := by
  rfl

def recoveryLegalTermCircuitCallLoweringValues
    (context validated : ℕ) : List ℕ :=
  [ context
  , validated
  , recoveryLegalTermCircuitArity context
  , recoveryLegalTermCircuitFamily context
  , (Nat.unpair validated).2
  , (Nat.unpair (Nat.unpair validated).2).2
  , recoveryLegalTermCircuitRequest context validated
  , recoveryLegalTermCircuitCallLoweringOutput context validated
  ]

def recoveryLegalTermCircuitCallLoweringBits
    (context validated : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermCircuitCallLoweringValues context validated).foldr max 0

theorem recoveryLegalTermCircuitCallLoweringValue_bits
    {context validated value : ℕ}
    (hvalue :
      value ∈
        recoveryLegalTermCircuitCallLoweringValues context validated) :
    natBitLength value ≤
      recoveryLegalTermCircuitCallLoweringBits context validated := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

private theorem run_recoveryLegalTermCircuitCallLoweringProgram
    (context validated : ℕ) :
    runNPOracleProgram recoveryLegalTermCircuitCallLoweringProgram
        (recoveryLegalTermCircuitCallLoweringBits context validated) 7
        (initialNPOracleState context validated) =
      some (recoveryLegalTermCircuitCallLoweringOutput
        context validated) := by
  have hbits :
      ∀ value ∈
          recoveryLegalTermCircuitCallLoweringValues context validated,
        natBitLength value ≤
          recoveryLegalTermCircuitCallLoweringBits context validated := by
    intro value hvalue
    exact recoveryLegalTermCircuitCallLoweringValue_bits hvalue
  simp [recoveryLegalTermCircuitCallLoweringProgram, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    recoveryLegalTermCircuitCallLoweringValues,
    recoveryLegalTermCircuitCallLoweringOutput,
    recoveryLegalTermCircuitRequest, recoveryLegalTermCircuitArity,
    recoveryLegalTermCircuitFamily, nativeInputRequest]

def recoveryLegalTermCircuitCallOutput
    (context validated : ℕ) : ℕ :=
  normalizedCircuitValidationOutput
    (recoveryLegalTermCircuitArity context)
    (recoveryLegalTermCircuitRequest context validated)

def recoveryLegalTermCircuitCallProgram : NPOracleProgram :=
  linkPrograms recoveryLegalTermCircuitCallLoweringProgram
    (nativeCallProgram normalizedCircuitValidationProgram)

@[simp] theorem recoveryLegalTermCircuitCallProgram_oracleFree :
    OracleFree recoveryLegalTermCircuitCallProgram :=
  oracleFree_linkPrograms
    recoveryLegalTermCircuitCallLoweringProgram_oracleFree <|
      nativeCallProgram_oracleFree
        normalizedCircuitValidationProgram_oracleFree

def recoveryLegalTermCircuitCallFuel
    (context validated : ℕ) : ℕ :=
  linkFuel (nativeCallProgram normalizedCircuitValidationProgram) 7 <|
    nativeCallFuel normalizedCircuitValidationProgram
      (normalizedCircuitValidationFuel
        (recoveryLegalTermCircuitArity context)
        (recoveryLegalTermCircuitRequest context validated))
      (recoveryLegalTermCircuitArity context)
      (recoveryLegalTermCircuitRequest context validated)

def recoveryLegalTermCircuitCallBits
    (context validated : ℕ) : ℕ :=
  max (natBitLength context) <|
    max (recoveryLegalTermCircuitCallLoweringBits context validated) <|
      nativeCallBits context
        (recoveryLegalTermCircuitArity context)
        (recoveryLegalTermCircuitRequest context validated)
        (recoveryLegalTermCircuitCallOutput context validated)
        (normalizedCircuitValidationBits
          (recoveryLegalTermCircuitArity context)
          (recoveryLegalTermCircuitRequest context validated))

theorem run_recoveryLegalTermCircuitCallProgram
    (context validated : ℕ) :
    runNPOracleProgram recoveryLegalTermCircuitCallProgram
        (recoveryLegalTermCircuitCallBits context validated)
        (recoveryLegalTermCircuitCallFuel context validated)
        (initialNPOracleState context validated) =
      some (recoveryLegalTermCircuitCallOutput context validated) := by
  let maximumBits := recoveryLegalTermCircuitCallBits context validated
  have hlength : natBitLength context ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength context by
      unfold natBitLength
      omega).trans hlength
  have hloweringBits :
      recoveryLegalTermCircuitCallLoweringBits context validated ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      nativeCallBits context
          (recoveryLegalTermCircuitArity context)
          (recoveryLegalTermCircuitRequest context validated)
          (recoveryLegalTermCircuitCallOutput context validated)
          (normalizedCircuitValidationBits
            (recoveryLegalTermCircuitArity context)
            (recoveryLegalTermCircuitRequest context validated)) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlowering :=
    run_bits_mono
      (run_recoveryLegalTermCircuitCallLoweringProgram context validated)
      hloweringBits
  have hnormalized :=
    run_normalizedCircuitValidationProgram
      (recoveryLegalTermCircuitArity context)
      (recoveryLegalTermCircuitRequest context validated)
  have hcall :=
    run_bits_mono
      (run_nativeCallProgram normalizedCircuitValidationProgram context
        (recoveryLegalTermCircuitArity context)
        (recoveryLegalTermCircuitRequest context validated)
        (recoveryLegalTermCircuitCallOutput context validated)
        (normalizedCircuitValidationBits
          (recoveryLegalTermCircuitArity context)
          (recoveryLegalTermCircuitRequest context validated))
        (normalizedCircuitValidationFuel
          (recoveryLegalTermCircuitArity context)
          (recoveryLegalTermCircuitRequest context validated))
        hnormalized)
      hcallBits
  have hrun :=
    run_linkPrograms hpositive hlength hlowering hcall
  simpa only [recoveryLegalTermCircuitCallProgram,
    recoveryLegalTermCircuitCallFuel] using hrun

theorem recoveryLegalTermCircuitCallOutput_ne_zero_iff
    (context validated : ℕ) :
    recoveryLegalTermCircuitCallOutput context validated ≠ 0 ↔
      (recoveryLegalTermCircuitFamily context = 0 ∧
        (decodeNormalizedSymmetricThresholdCircuit
          (recoveryLegalTermCircuitArity context)
          (Nat.unpair (Nat.unpair validated).2).2).isSome) ∨
      (recoveryLegalTermCircuitFamily context = 1 ∧
        (decodeNormalizedThresholdThresholdCircuit
          (recoveryLegalTermCircuitArity context)
          (Nat.unpair (Nat.unpair validated).2).2).isSome) := by
  simpa [recoveryLegalTermCircuitCallOutput,
    recoveryLegalTermCircuitRequest, normalizedCircuitExpectedFamily,
    normalizedCircuitRawCode] using
      (normalizedCircuitValidationOutput_ne_zero_iff
        (recoveryLegalTermCircuitArity context)
        (recoveryLegalTermCircuitRequest context validated))

def recoveryLegalTermCoefficientRequestBits (request : ℕ) : ℕ :=
  legalTermCoefficientValidationBits
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermCoefficientRequestFuel (request : ℕ) : ℕ :=
  legalTermCoefficientValidationFuel
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermCoefficientRequestOutput (request : ℕ) : ℕ :=
  legalTermCoefficientValidationOutput (Nat.unpair request).2

def recoveryLegalTermCoefficientListProgram : NPOracleProgram :=
  balancedValidationSummaryProgram legalTermCoefficientValidationProgram

@[simp] theorem recoveryLegalTermCoefficientListProgram_oracleFree :
    OracleFree recoveryLegalTermCoefficientListProgram :=
  balancedValidationSummaryProgram_oracleFree
    legalTermCoefficientValidationProgram
    legalTermCoefficientValidationProgram_oracleFree

def recoveryLegalTermCoefficientListOutput
    (inputLength raw : ℕ) : ℕ :=
  balancedValidationSummaryOutput inputLength raw
    recoveryLegalTermCoefficientRequestOutput

def recoveryLegalTermCoefficientListFuel
    (inputLength raw : ℕ) : ℕ :=
  balancedValidationSummaryFuel legalTermCoefficientValidationProgram
    recoveryLegalTermCoefficientRequestFuel inputLength raw
    recoveryLegalTermCoefficientRequestOutput

def recoveryLegalTermCoefficientListBits
    (inputLength raw : ℕ) : ℕ :=
  balancedValidationSummaryBits recoveryLegalTermCoefficientRequestBits
    recoveryLegalTermCoefficientRequestOutput inputLength raw

theorem run_recoveryLegalTermCoefficientListProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram recoveryLegalTermCoefficientListProgram
        (recoveryLegalTermCoefficientListBits inputLength raw)
        (recoveryLegalTermCoefficientListFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (recoveryLegalTermCoefficientListOutput inputLength raw) := by
  apply run_balancedValidationSummaryProgram
  intro request _
  exact run_legalTermCoefficientValidationProgram
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermCircuitRequestBits (request : ℕ) : ℕ :=
  recoveryLegalTermCircuitCallBits
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermCircuitRequestFuel (request : ℕ) : ℕ :=
  recoveryLegalTermCircuitCallFuel
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermCircuitRequestOutput (request : ℕ) : ℕ :=
  recoveryLegalTermCircuitCallOutput
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermCircuitListProgram : NPOracleProgram :=
  balancedValidationSummaryProgram recoveryLegalTermCircuitCallProgram

@[simp] theorem recoveryLegalTermCircuitListProgram_oracleFree :
    OracleFree recoveryLegalTermCircuitListProgram :=
  balancedValidationSummaryProgram_oracleFree
    recoveryLegalTermCircuitCallProgram
    recoveryLegalTermCircuitCallProgram_oracleFree

def recoveryLegalTermCircuitListOutput
    (context raw : ℕ) : ℕ :=
  balancedValidationSummaryOutput context raw
    recoveryLegalTermCircuitRequestOutput

def recoveryLegalTermCircuitListFuel
    (context raw : ℕ) : ℕ :=
  balancedValidationSummaryFuel recoveryLegalTermCircuitCallProgram
    recoveryLegalTermCircuitRequestFuel context raw
    recoveryLegalTermCircuitRequestOutput

def recoveryLegalTermCircuitListBits
    (context raw : ℕ) : ℕ :=
  balancedValidationSummaryBits recoveryLegalTermCircuitRequestBits
    recoveryLegalTermCircuitRequestOutput context raw

theorem run_recoveryLegalTermCircuitListProgram
    (context raw : ℕ) :
    runNPOracleProgram recoveryLegalTermCircuitListProgram
        (recoveryLegalTermCircuitListBits context raw)
        (recoveryLegalTermCircuitListFuel context raw)
        (initialNPOracleState context raw) =
      some (recoveryLegalTermCircuitListOutput context raw) := by
  apply run_balancedValidationSummaryProgram
  intro request _
  exact run_recoveryLegalTermCircuitCallProgram
    (Nat.unpair request).1 (Nat.unpair request).2

theorem recoveryLegalTermCircuitListOutput_ne_zero_iff
    (context raw : ℕ) :
    recoveryLegalTermCircuitListOutput context raw ≠ 0 ↔
      ∃ codes,
        decodeBalancedList raw = some codes ∧
          ∀ code, code ∈ codes →
            recoveryLegalTermCircuitCallOutput context code ≠ 0 := by
  simpa [recoveryLegalTermCircuitListOutput,
    recoveryLegalTermCircuitRequestOutput, nativeInputRequest] using
    (balancedValidationSummaryOutput_ne_zero_iff
      context raw recoveryLegalTermCircuitRequestOutput)

theorem recoveryLegalTermCircuitListOutput_ne_zero_iff_decoders
    (context raw : ℕ) :
    recoveryLegalTermCircuitListOutput context raw ≠ 0 ↔
      ∃ validatedCodes,
        decodeBalancedList raw = some validatedCodes ∧
          ∀ validated, validated ∈ validatedCodes →
            (recoveryLegalTermCircuitFamily context = 0 ∧
              (decodeNormalizedSymmetricThresholdCircuit
                (recoveryLegalTermCircuitArity context)
                (Nat.unpair (Nat.unpair validated).2).2).isSome) ∨
            (recoveryLegalTermCircuitFamily context = 1 ∧
              (decodeNormalizedThresholdThresholdCircuit
                (recoveryLegalTermCircuitArity context)
                (Nat.unpair (Nat.unpair validated).2).2).isSome) := by
  simpa only [recoveryLegalTermCircuitCallOutput_ne_zero_iff] using
    (recoveryLegalTermCircuitListOutput_ne_zero_iff context raw)

/-! ## Coefficient numerator/denominator width validation

The coefficient mapper above is the sole parser for legal terms and canonical
rationals.  This stage consumes its mapped summary: it never re-decodes
untrusted term syntax, and it treats the mapper's zero sentinel as failure. -/

def recoveryLegalTermValidatedRationalSummary (validated : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair validated).2).1

def recoveryLegalTermValidatedMagnitude (validated : ℕ) : ℕ :=
  let rationalData :=
    (Nat.unpair (recoveryLegalTermValidatedRationalSummary validated)).2
  let magnitudeDenominator := (Nat.unpair rationalData).2
  (Nat.unpair magnitudeDenominator).1

def recoveryLegalTermValidatedDenominator (validated : ℕ) : ℕ :=
  let rationalData :=
    (Nat.unpair (recoveryLegalTermValidatedRationalSummary validated)).2
  let magnitudeDenominator := (Nat.unpair rationalData).2
  (Nat.unpair magnitudeDenominator).2

def recoveryLegalTermCoefficientBitCapPrepareOutput
    (cap validated : ℕ) : ℕ :=
  if validated = 0 then
    0
  else
    Nat.pair
      (natBitCapInput cap
        (recoveryLegalTermValidatedMagnitude validated))
      (natBitCapInput cap
        (recoveryLegalTermValidatedDenominator validated))

def recoveryLegalTermCoefficientBitCapPrepareProgram : NPOracleProgram :=
  [ .branchZero 0 10 1
  , .unpairRight 0 2 2
  , .unpairLeft 2 3 3
  , .unpairRight 3 4 4
  , .unpairRight 4 5 5
  , .unpairLeft 5 6 6
  , .unpairRight 5 7 7
  , .pair 1 6 8 8
  , .pair 1 7 9 9
  , .pair 8 9 0 11
  , .set 0 0 11
  , .halt 0
  ]

@[simp] theorem
    recoveryLegalTermCoefficientBitCapPrepareProgram_oracleFree :
    OracleFree recoveryLegalTermCoefficientBitCapPrepareProgram := by
  rfl

def recoveryLegalTermCoefficientBitCapPrepareFuel : ℕ := 11

def recoveryLegalTermCoefficientBitCapPrepareValues
    (cap validated : ℕ) : List ℕ :=
  let payload := (Nat.unpair validated).2
  let rational := (Nat.unpair payload).1
  let rationalData := (Nat.unpair rational).2
  let magnitudeDenominator := (Nat.unpair rationalData).2
  let magnitude := (Nat.unpair magnitudeDenominator).1
  let denominator := (Nat.unpair magnitudeDenominator).2
  let magnitudeRequest := natBitCapInput cap magnitude
  let denominatorRequest := natBitCapInput cap denominator
  [ 0
  , cap
  , validated
  , payload
  , rational
  , rationalData
  , magnitudeDenominator
  , magnitude
  , denominator
  , magnitudeRequest
  , denominatorRequest
  , recoveryLegalTermCoefficientBitCapPrepareOutput cap validated
  ]

def recoveryLegalTermCoefficientBitCapPrepareBits
    (cap validated : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermCoefficientBitCapPrepareValues
      cap validated).foldr max 0

theorem recoveryLegalTermCoefficientBitCapPrepareValue_bits
    {cap validated value : ℕ}
    (hvalue :
      value ∈
        recoveryLegalTermCoefficientBitCapPrepareValues cap validated) :
    natBitLength value ≤
      recoveryLegalTermCoefficientBitCapPrepareBits cap validated := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

private theorem run_recoveryLegalTermCoefficientBitCapPrepareAssembly
    (cap magnitude denominator maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = 7)
    (hcap : state.registers 1 = cap)
    (hmagnitude : state.registers 6 = magnitude)
    (hdenominator : state.registers 7 = denominator)
    (hmagnitudeRequest :
      natBitLength (natBitCapInput cap magnitude) ≤ maximumBits)
    (hdenominatorRequest :
      natBitLength (natBitCapInput cap denominator) ≤ maximumBits)
    (houtput :
      natBitLength
        (Nat.pair (natBitCapInput cap magnitude)
          (natBitCapInput cap denominator)) ≤ maximumBits) :
    runNPOracleProgram recoveryLegalTermCoefficientBitCapPrepareProgram
        maximumBits 4 state =
      some
        (Nat.pair (natBitCapInput cap magnitude)
          (natBitCapInput cap denominator)) := by
  let magnitudeRequest := natBitCapInput cap magnitude
  let denominatorRequest := natBitCapInput cap denominator
  let output := Nat.pair magnitudeRequest denominatorRequest
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := magnitudeRequest)
    (by rfl) hpc
    (by simp [hcap, hmagnitude, magnitudeRequest, natBitCapInput])
    hmagnitudeRequest]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := denominatorRequest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcap, hdenominator,
      denominatorRequest, natBitCapInput])
    hdenominatorRequest]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output,
      magnitudeRequest, denominatorRequest]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output,
      magnitudeRequest, denominatorRequest]) houtput

set_option maxHeartbeats 600000 in
-- The exact preparation trace normalizes the signed rational summary twice.
theorem run_recoveryLegalTermCoefficientBitCapPrepareProgram
    (cap validated : ℕ) :
    runNPOracleProgram recoveryLegalTermCoefficientBitCapPrepareProgram
        (recoveryLegalTermCoefficientBitCapPrepareBits cap validated)
        recoveryLegalTermCoefficientBitCapPrepareFuel
        (initialNPOracleState cap validated) =
      some
        (recoveryLegalTermCoefficientBitCapPrepareOutput cap validated) := by
  let maximumBits :=
    recoveryLegalTermCoefficientBitCapPrepareBits cap validated
  let payload := (Nat.unpair validated).2
  let rational := (Nat.unpair payload).1
  let rationalData := (Nat.unpair rational).2
  let magnitudeDenominator := (Nat.unpair rationalData).2
  let magnitude := (Nat.unpair magnitudeDenominator).1
  let denominator := (Nat.unpair magnitudeDenominator).2
  let magnitudeRequest := natBitCapInput cap magnitude
  let denominatorRequest := natBitCapInput cap denominator
  let output := Nat.pair magnitudeRequest denominatorRequest
  have hbits :
      ∀ value ∈
          recoveryLegalTermCoefficientBitCapPrepareValues cap validated,
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact recoveryLegalTermCoefficientBitCapPrepareValue_bits hvalue
  have hzero := hbits 0 (by
    simp [recoveryLegalTermCoefficientBitCapPrepareValues])
  have hpayload := hbits payload (by
    simp [recoveryLegalTermCoefficientBitCapPrepareValues, payload])
  have hrational := hbits rational (by
    simp [recoveryLegalTermCoefficientBitCapPrepareValues, payload,
      rational])
  have hrationalData := hbits rationalData (by
    simp [recoveryLegalTermCoefficientBitCapPrepareValues, payload,
      rational, rationalData])
  have hmagnitudeDenominator := hbits magnitudeDenominator (by
    simp [recoveryLegalTermCoefficientBitCapPrepareValues, payload,
      rational, rationalData, magnitudeDenominator])
  have hmagnitude := hbits magnitude (by
    simp [recoveryLegalTermCoefficientBitCapPrepareValues, payload,
      rational, rationalData, magnitudeDenominator, magnitude])
  have hdenominator := hbits denominator (by
    simp [recoveryLegalTermCoefficientBitCapPrepareValues, payload,
      rational, rationalData, magnitudeDenominator, denominator])
  have hmagnitudeRequest := hbits magnitudeRequest (by
    simp [recoveryLegalTermCoefficientBitCapPrepareValues, payload,
      rational, rationalData, magnitudeDenominator, magnitude,
      magnitudeRequest])
  have hdenominatorRequest := hbits denominatorRequest (by
    simp [recoveryLegalTermCoefficientBitCapPrepareValues, payload,
      rational, rationalData, magnitudeDenominator, denominator,
      denominatorRequest])
  have hcap :
      (initialNPOracleState cap validated).registers 1 = cap := by
    simp [initialNPOracleState]
  rw [show recoveryLegalTermCoefficientBitCapPrepareFuel = 10 + 1 by rfl]
  rw [run_branchZero_instruction
    (program := recoveryLegalTermCoefficientBitCapPrepareProgram)
    (maximumBits := maximumBits) (fuel := 10)
    (pc := 0) (register := 0) (zeroTarget := 10) (nonzeroTarget := 1)
    (by rfl) (by rfl)]
  by_cases hvalidated : validated = 0
  · rw [if_pos (by
      simp [initialNPOracleState, hvalidated])]
    rw [show (10 : ℕ) = 9 + 1 by omega]
    rw [run_set_instruction
      (program := recoveryLegalTermCoefficientBitCapPrepareProgram)
      (maximumBits := maximumBits) (fuel := 9)
      (pc := 10) (register := 0) (value := 0) (next := 11)
      (by rfl) (by rfl) hzero]
    rw [show
      recoveryLegalTermCoefficientBitCapPrepareOutput cap validated = 0 by
        simp [recoveryLegalTermCoefficientBitCapPrepareOutput, hvalidated]]
    exact run_halt_instruction
      (program := recoveryLegalTermCoefficientBitCapPrepareProgram)
      (maximumBits := maximumBits) (fuel := 8) (pc := 11)
      (outputRegister := 0) (value := 0)
      (by rfl) (by rfl)
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump]) hzero
  · rw [if_neg (by
      simp [initialNPOracleState, hvalidated])]
    have houtputShape :
        recoveryLegalTermCoefficientBitCapPrepareOutput cap validated =
          output := by
      simp only [recoveryLegalTermCoefficientBitCapPrepareOutput,
        if_neg hvalidated]
      rfl
    have hprepared :=
      hbits
        (recoveryLegalTermCoefficientBitCapPrepareOutput cap validated) (by
          simp [recoveryLegalTermCoefficientBitCapPrepareValues])
    have houtput : natBitLength output ≤ maximumBits := by
      simpa only [houtputShape] using hprepared
    rw [show (10 : ℕ) = 9 + 1 by omega]
    rw [run_unpairRight_instruction (value := payload)
      (by rfl) rfl
      (by simp [initialNPOracleState, payload]) hpayload]
    rw [show (9 : ℕ) = 8 + 1 by omega]
    rw [run_unpairLeft_instruction (value := rational)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, rational,
        payload]) hrational]
    rw [show (8 : ℕ) = 7 + 1 by omega]
    rw [run_unpairRight_instruction (value := rationalData)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, rationalData,
        rational]) hrationalData]
    rw [show (7 : ℕ) = 6 + 1 by omega]
    rw [run_unpairRight_instruction (value := magnitudeDenominator)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump,
        magnitudeDenominator, rationalData]) hmagnitudeDenominator]
    rw [show (6 : ℕ) = 5 + 1 by omega]
    rw [run_unpairLeft_instruction (value := magnitude)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, magnitude,
        magnitudeDenominator]) hmagnitude]
    rw [show (5 : ℕ) = 4 + 1 by omega]
    rw [run_unpairRight_instruction (value := denominator)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, denominator,
        magnitudeDenominator]) hdenominator]
    rw [houtputShape]
    apply run_recoveryLegalTermCoefficientBitCapPrepareAssembly
      cap magnitude denominator maximumBits
    · rfl
    · exact hcap
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · exact hmagnitudeRequest
    · exact hdenominatorRequest
    · exact houtput

def recoveryLegalTermCoefficientBitCapPrepared
    (cap validated : ℕ) : ℕ :=
  recoveryLegalTermCoefficientBitCapPrepareOutput cap validated

def recoveryLegalTermCoefficientMagnitudeRequest
    (cap validated : ℕ) : ℕ :=
  (Nat.unpair
    (recoveryLegalTermCoefficientBitCapPrepared cap validated)).1

def recoveryLegalTermCoefficientDenominatorRequest
    (cap validated : ℕ) : ℕ :=
  (Nat.unpair
    (recoveryLegalTermCoefficientBitCapPrepared cap validated)).2

def recoveryLegalTermCoefficientMagnitudeBitCapOutput
    (cap validated : ℕ) : ℕ :=
  let request :=
    recoveryLegalTermCoefficientMagnitudeRequest cap validated
  natBitCapOutput (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermCoefficientDenominatorBitCapOutput
    (cap validated : ℕ) : ℕ :=
  let request :=
    recoveryLegalTermCoefficientDenominatorRequest cap validated
  natBitCapOutput (Nat.unpair request).1 (Nat.unpair request).2

/-- One success value for both coefficient coordinates.  The generic gate
keeps the denominator result exactly when the magnitude check succeeded. -/
def recoveryLegalTermCoefficientBitCapOutput
    (cap validated : ℕ) : ℕ :=
  recoveryBoundedContextGateOutput
    (recoveryLegalTermCoefficientMagnitudeBitCapOutput cap validated)
    (recoveryLegalTermCoefficientDenominatorBitCapOutput cap validated)

def recoveryLegalTermCoefficientBitCapProgram : NPOracleProgram :=
  linkPrograms recoveryLegalTermCoefficientBitCapPrepareProgram <|
    linkPrograms (pairedCallProgram natBitCapProgram)
      recoveryBoundedContextGateProgram

@[simp] theorem recoveryLegalTermCoefficientBitCapProgram_oracleFree :
    OracleFree recoveryLegalTermCoefficientBitCapProgram := by
  exact oracleFree_linkPrograms
    recoveryLegalTermCoefficientBitCapPrepareProgram_oracleFree <|
      oracleFree_linkPrograms
        (pairedCallProgram_oracleFree natBitCapProgram
          natBitCapProgram_oracleFree)
        recoveryBoundedContextGateProgram_oracleFree

def recoveryLegalTermCoefficientBitCapFuel
    (cap validated : ℕ) : ℕ :=
  let magnitudeRequest :=
    recoveryLegalTermCoefficientMagnitudeRequest cap validated
  let denominatorRequest :=
    recoveryLegalTermCoefficientDenominatorRequest cap validated
  linkFuel
    (linkPrograms (pairedCallProgram natBitCapProgram)
      recoveryBoundedContextGateProgram)
    recoveryLegalTermCoefficientBitCapPrepareFuel <|
      linkFuel recoveryBoundedContextGateProgram
        (pairedCallFuel natBitCapProgram
          (natBitCapFuel (Nat.unpair magnitudeRequest).1
            (Nat.unpair magnitudeRequest).2)
          (natBitCapFuel (Nat.unpair denominatorRequest).1
            (Nat.unpair denominatorRequest).2))
        4

def recoveryLegalTermCoefficientBitCapPairBits
    (cap validated : ℕ) : ℕ :=
  let magnitudeRequest :=
    recoveryLegalTermCoefficientMagnitudeRequest cap validated
  let denominatorRequest :=
    recoveryLegalTermCoefficientDenominatorRequest cap validated
  pairedCallBits cap
    (natBitCapBits cap (Nat.unpair magnitudeRequest).1
      (Nat.unpair magnitudeRequest).2)
    (natBitCapBits cap (Nat.unpair denominatorRequest).1
      (Nat.unpair denominatorRequest).2)
    magnitudeRequest denominatorRequest
    (recoveryLegalTermCoefficientMagnitudeBitCapOutput cap validated)
    (recoveryLegalTermCoefficientDenominatorBitCapOutput cap validated)

def recoveryLegalTermCoefficientBitCapPairFuel
    (cap validated : ℕ) : ℕ :=
  let magnitudeRequest :=
    recoveryLegalTermCoefficientMagnitudeRequest cap validated
  let denominatorRequest :=
    recoveryLegalTermCoefficientDenominatorRequest cap validated
  pairedCallFuel natBitCapProgram
    (natBitCapFuel (Nat.unpair magnitudeRequest).1
      (Nat.unpair magnitudeRequest).2)
    (natBitCapFuel (Nat.unpair denominatorRequest).1
      (Nat.unpair denominatorRequest).2)

set_option maxRecDepth 10000 in
private theorem run_recoveryLegalTermCoefficientBitCapRequest
    (inputLength request : ℕ) :
    runNPOracleProgram natBitCapProgram
        (natBitCapBits inputLength
          (Nat.unpair request).1 (Nat.unpair request).2)
        (natBitCapFuel (Nat.unpair request).1 (Nat.unpair request).2)
        (initialNPOracleState inputLength request) =
      some
        (natBitCapOutput
          (Nat.unpair request).1 (Nat.unpair request).2) := by
  have hrequest :
      natBitCapInput (Nat.unpair request).1 (Nat.unpair request).2 =
        request :=
    Nat.pair_unpair request
  simpa only [hrequest] using
    (run_natBitCapProgram inputLength
      (Nat.unpair request).1 (Nat.unpair request).2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
-- The paired-call specialization normalizes two linked bit-cap programs.
private theorem run_recoveryLegalTermCoefficientBitCapPairProgram
    (cap validated : ℕ) :
    runNPOracleProgram (pairedCallProgram natBitCapProgram)
        (recoveryLegalTermCoefficientBitCapPairBits cap validated)
        (recoveryLegalTermCoefficientBitCapPairFuel cap validated)
        (initialNPOracleState cap
          (recoveryLegalTermCoefficientBitCapPrepared cap validated)) =
      some
        (Nat.pair
          (recoveryLegalTermCoefficientMagnitudeBitCapOutput cap validated)
          (recoveryLegalTermCoefficientDenominatorBitCapOutput
            cap validated)) := by
  let prepared :=
    recoveryLegalTermCoefficientBitCapPrepared cap validated
  let magnitudeRequest :=
    recoveryLegalTermCoefficientMagnitudeRequest cap validated
  let denominatorRequest :=
    recoveryLegalTermCoefficientDenominatorRequest cap validated
  have hprepared :
      Nat.pair magnitudeRequest denominatorRequest = prepared :=
    Nat.pair_unpair prepared
  have hbits :
      recoveryLegalTermCoefficientBitCapPairBits cap validated =
        pairedCallBits cap
          (natBitCapBits cap (Nat.unpair magnitudeRequest).1
            (Nat.unpair magnitudeRequest).2)
          (natBitCapBits cap (Nat.unpair denominatorRequest).1
            (Nat.unpair denominatorRequest).2)
          magnitudeRequest denominatorRequest
          (natBitCapOutput (Nat.unpair magnitudeRequest).1
            (Nat.unpair magnitudeRequest).2)
          (natBitCapOutput (Nat.unpair denominatorRequest).1
            (Nat.unpair denominatorRequest).2) := by
    rfl
  have hfuel :
      recoveryLegalTermCoefficientBitCapPairFuel cap validated =
        pairedCallFuel natBitCapProgram
          (natBitCapFuel (Nat.unpair magnitudeRequest).1
            (Nat.unpair magnitudeRequest).2)
          (natBitCapFuel (Nat.unpair denominatorRequest).1
            (Nat.unpair denominatorRequest).2) := by
    rfl
  have hmagnitudeOutput :
      recoveryLegalTermCoefficientMagnitudeBitCapOutput cap validated =
        natBitCapOutput (Nat.unpair magnitudeRequest).1
          (Nat.unpair magnitudeRequest).2 := by
    rfl
  have hdenominatorOutput :
      recoveryLegalTermCoefficientDenominatorBitCapOutput cap validated =
        natBitCapOutput (Nat.unpair denominatorRequest).1
          (Nat.unpair denominatorRequest).2 := by
    rfl
  rw [hbits, hfuel, hmagnitudeOutput, hdenominatorOutput]
  change
    runNPOracleProgram (pairedCallProgram natBitCapProgram)
        (pairedCallBits cap
          (natBitCapBits cap (Nat.unpair magnitudeRequest).1
            (Nat.unpair magnitudeRequest).2)
          (natBitCapBits cap (Nat.unpair denominatorRequest).1
            (Nat.unpair denominatorRequest).2)
          magnitudeRequest denominatorRequest
          (natBitCapOutput (Nat.unpair magnitudeRequest).1
            (Nat.unpair magnitudeRequest).2)
          (natBitCapOutput (Nat.unpair denominatorRequest).1
            (Nat.unpair denominatorRequest).2))
        (pairedCallFuel natBitCapProgram
          (natBitCapFuel (Nat.unpair magnitudeRequest).1
            (Nat.unpair magnitudeRequest).2)
          (natBitCapFuel (Nat.unpair denominatorRequest).1
            (Nat.unpair denominatorRequest).2))
        (initialNPOracleState cap prepared) =
      _
  rw [← hprepared]
  have hmagnitude :
      runNPOracleProgram natBitCapProgram
          (natBitCapBits cap (Nat.unpair magnitudeRequest).1
            (Nat.unpair magnitudeRequest).2)
          (natBitCapFuel (Nat.unpair magnitudeRequest).1
            (Nat.unpair magnitudeRequest).2)
          (initialNPOracleState cap magnitudeRequest) =
        some
          (natBitCapOutput (Nat.unpair magnitudeRequest).1
            (Nat.unpair magnitudeRequest).2) :=
    run_recoveryLegalTermCoefficientBitCapRequest cap magnitudeRequest
  have hdenominator :
      runNPOracleProgram natBitCapProgram
          (natBitCapBits cap (Nat.unpair denominatorRequest).1
            (Nat.unpair denominatorRequest).2)
          (natBitCapFuel (Nat.unpair denominatorRequest).1
            (Nat.unpair denominatorRequest).2)
          (initialNPOracleState cap denominatorRequest) =
        some
          (natBitCapOutput (Nat.unpair denominatorRequest).1
            (Nat.unpair denominatorRequest).2) :=
    run_recoveryLegalTermCoefficientBitCapRequest cap denominatorRequest
  exact run_pairedCallProgram natBitCapProgram cap
    (natBitCapBits cap (Nat.unpair magnitudeRequest).1
      (Nat.unpair magnitudeRequest).2)
    (natBitCapBits cap (Nat.unpair denominatorRequest).1
      (Nat.unpair denominatorRequest).2)
    (natBitCapFuel (Nat.unpair magnitudeRequest).1
      (Nat.unpair magnitudeRequest).2)
    (natBitCapFuel (Nat.unpair denominatorRequest).1
      (Nat.unpair denominatorRequest).2)
    magnitudeRequest denominatorRequest
    (natBitCapOutput (Nat.unpair magnitudeRequest).1
      (Nat.unpair magnitudeRequest).2)
    (natBitCapOutput (Nat.unpair denominatorRequest).1
      (Nat.unpair denominatorRequest).2)
    hmagnitude hdenominator

def recoveryLegalTermCoefficientBitCapBits
    (cap validated : ℕ) : ℕ :=
  max 1 <| max (natBitLength cap) <|
    max
      (recoveryLegalTermCoefficientBitCapPrepareBits cap validated) <|
      max
        (recoveryLegalTermCoefficientBitCapPairBits cap validated)
        (recoveryBoundedContextGateBits
          (recoveryLegalTermCoefficientMagnitudeBitCapOutput cap validated)
          (recoveryLegalTermCoefficientDenominatorBitCapOutput
            cap validated))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
-- The linked pair and fail-closed gate normalize nested request/output codecs.
theorem run_recoveryLegalTermCoefficientBitCapProgram
    (cap validated : ℕ) :
    runNPOracleProgram recoveryLegalTermCoefficientBitCapProgram
        (recoveryLegalTermCoefficientBitCapBits cap validated)
        (recoveryLegalTermCoefficientBitCapFuel cap validated)
        (initialNPOracleState cap validated) =
      some (recoveryLegalTermCoefficientBitCapOutput cap validated) := by
  let maximumBits :=
    recoveryLegalTermCoefficientBitCapBits cap validated
  let prepared :=
    recoveryLegalTermCoefficientBitCapPrepared cap validated
  let magnitudeRequest :=
    recoveryLegalTermCoefficientMagnitudeRequest cap validated
  let denominatorRequest :=
    recoveryLegalTermCoefficientDenominatorRequest cap validated
  let magnitudeOutput :=
    recoveryLegalTermCoefficientMagnitudeBitCapOutput cap validated
  let denominatorOutput :=
    recoveryLegalTermCoefficientDenominatorBitCapOutput cap validated
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, recoveryLegalTermCoefficientBitCapBits]
  have hlength : natBitLength cap ≤ maximumBits := by
    simp [maximumBits, recoveryLegalTermCoefficientBitCapBits]
  have hprepareBits :
      recoveryLegalTermCoefficientBitCapPrepareBits cap validated ≤
        maximumBits := by
    simp [maximumBits, recoveryLegalTermCoefficientBitCapBits]
  have hpairBits :
      recoveryLegalTermCoefficientBitCapPairBits cap validated ≤
        maximumBits := by
    simp [maximumBits, recoveryLegalTermCoefficientBitCapBits]
  have hgateBits :
      recoveryBoundedContextGateBits magnitudeOutput denominatorOutput ≤
        maximumBits := by
    simp [maximumBits, recoveryLegalTermCoefficientBitCapBits,
      magnitudeOutput, denominatorOutput]
  have hprepare :
      runNPOracleProgram
          recoveryLegalTermCoefficientBitCapPrepareProgram maximumBits
          recoveryLegalTermCoefficientBitCapPrepareFuel
          (initialNPOracleState cap validated) =
        some prepared := by
    exact run_bits_mono
      (run_recoveryLegalTermCoefficientBitCapPrepareProgram cap validated)
      hprepareBits
  have hpair :
      runNPOracleProgram (pairedCallProgram natBitCapProgram) maximumBits
          (recoveryLegalTermCoefficientBitCapPairFuel cap validated)
          (initialNPOracleState cap prepared) =
        some (Nat.pair magnitudeOutput denominatorOutput) := by
    exact run_bits_mono
      (run_recoveryLegalTermCoefficientBitCapPairProgram cap validated)
      hpairBits
  have hgate :
      runNPOracleProgram recoveryBoundedContextGateProgram maximumBits 4
          (initialNPOracleState cap
            (Nat.pair magnitudeOutput denominatorOutput)) =
        some (recoveryLegalTermCoefficientBitCapOutput cap validated) := by
    exact run_bits_mono
      (run_recoveryBoundedContextGateProgram cap
        magnitudeOutput denominatorOutput)
      hgateBits
  have htail :=
    run_linkPrograms hpositive hlength hpair hgate
  have hrun :=
    run_linkPrograms hpositive hlength hprepare htail
  simpa only [maximumBits, recoveryLegalTermCoefficientBitCapProgram,
    recoveryLegalTermCoefficientBitCapFuel,
    recoveryLegalTermCoefficientBitCapPairFuel] using hrun

@[simp] theorem recoveryLegalTermCoefficientBitCapOutput_ne_zero_iff
    (cap validated : ℕ) :
    recoveryLegalTermCoefficientBitCapOutput cap validated ≠ 0 ↔
      validated ≠ 0 ∧
        natBitLength (recoveryLegalTermValidatedMagnitude validated) ≤ cap ∧
        natBitLength (recoveryLegalTermValidatedDenominator validated) ≤
          cap := by
  by_cases hvalidated : validated = 0
  · subst validated
    simp [recoveryLegalTermCoefficientBitCapOutput,
      recoveryLegalTermCoefficientMagnitudeBitCapOutput,
      recoveryLegalTermCoefficientMagnitudeRequest,
      recoveryLegalTermCoefficientBitCapPrepared,
      recoveryLegalTermCoefficientBitCapPrepareOutput,
      recoveryBoundedContextGateOutput, natBitCapOutput, natBitLength]
  · simp [recoveryLegalTermCoefficientBitCapOutput,
      recoveryLegalTermCoefficientMagnitudeBitCapOutput,
      recoveryLegalTermCoefficientDenominatorBitCapOutput,
      recoveryLegalTermCoefficientMagnitudeRequest,
      recoveryLegalTermCoefficientDenominatorRequest,
      recoveryLegalTermCoefficientBitCapPrepared,
      recoveryLegalTermCoefficientBitCapPrepareOutput, hvalidated,
      recoveryBoundedContextGateOutput, natBitCapOutput_ne_zero_iff,
      natBitCapInput]

def recoveryLegalTermCoefficientBitCapRequestOutput
    (request : ℕ) : ℕ :=
  recoveryLegalTermCoefficientBitCapOutput
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermCoefficientBitCapRequestFuel
    (request : ℕ) : ℕ :=
  recoveryLegalTermCoefficientBitCapFuel
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermCoefficientBitCapRequestBits
    (request : ℕ) : ℕ :=
  recoveryLegalTermCoefficientBitCapBits
    (Nat.unpair request).1 (Nat.unpair request).2

def recoveryLegalTermCoefficientBitCapListProgram : NPOracleProgram :=
  balancedValidationSummaryProgram
    recoveryLegalTermCoefficientBitCapProgram

@[simp] theorem recoveryLegalTermCoefficientBitCapListProgram_oracleFree :
    OracleFree recoveryLegalTermCoefficientBitCapListProgram :=
  balancedValidationSummaryProgram_oracleFree
    recoveryLegalTermCoefficientBitCapProgram
    recoveryLegalTermCoefficientBitCapProgram_oracleFree

def recoveryLegalTermCoefficientBitCapListOutput
    (cap raw : ℕ) : ℕ :=
  balancedValidationSummaryOutput cap raw
    recoveryLegalTermCoefficientBitCapRequestOutput

def recoveryLegalTermCoefficientBitCapListFuel
    (cap raw : ℕ) : ℕ :=
  balancedValidationSummaryFuel recoveryLegalTermCoefficientBitCapProgram
    recoveryLegalTermCoefficientBitCapRequestFuel
    cap raw recoveryLegalTermCoefficientBitCapRequestOutput

def recoveryLegalTermCoefficientBitCapListBits
    (cap raw : ℕ) : ℕ :=
  balancedValidationSummaryBits
    recoveryLegalTermCoefficientBitCapRequestBits
    recoveryLegalTermCoefficientBitCapRequestOutput cap raw

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in

theorem run_recoveryLegalTermCoefficientBitCapListProgram
    (cap raw : ℕ) :
    runNPOracleProgram recoveryLegalTermCoefficientBitCapListProgram
        (recoveryLegalTermCoefficientBitCapListBits cap raw)
        (recoveryLegalTermCoefficientBitCapListFuel cap raw)
        (initialNPOracleState cap raw) =
      some (recoveryLegalTermCoefficientBitCapListOutput cap raw) := by
  apply run_balancedValidationSummaryProgram
  intro request _
  exact run_recoveryLegalTermCoefficientBitCapProgram
    (Nat.unpair request).1 (Nat.unpair request).2

theorem recoveryLegalTermCoefficientBitCapListOutput_ne_zero_iff
    (cap raw : ℕ) :
    recoveryLegalTermCoefficientBitCapListOutput cap raw ≠ 0 ↔
      ∃ validatedCodes,
        decodeBalancedList raw = some validatedCodes ∧
          ∀ validated, validated ∈ validatedCodes →
            validated ≠ 0 ∧
              natBitLength
                  (recoveryLegalTermValidatedMagnitude validated) ≤ cap ∧
                natBitLength
                  (recoveryLegalTermValidatedDenominator validated) ≤
                    cap := by
  rw [recoveryLegalTermCoefficientBitCapListOutput,
    balancedValidationSummaryOutput_ne_zero_iff]
  simp only [recoveryLegalTermCoefficientBitCapRequestOutput,
    nativeInputRequest, Nat.unpair_pair,
    recoveryLegalTermCoefficientBitCapOutput_ne_zero_iff]

/-- Extract the terms slot from the checked context.  If an earlier bound
rejected, its zero sentinel stays zero throughout this projection. -/
def recoveryLegalTermCoefficientTermsCode (handoff : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair
      (Nat.unpair
        (Nat.unpair
          (Nat.unpair
            (Nat.unpair (recoveryLegalSumBoundOutput handoff)).2).2).2).2).2).1

def recoveryLegalTermCoefficientLoweringOutput (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalTermCoefficientTermsCode handoff)
    (recoveryLegalSumBoundOutput handoff)

def recoveryLegalTermCoefficientLoweringProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairRight 2 3 2
  , .unpairRight 3 4 3
  , .unpairRight 4 5 4
  , .unpairRight 5 6 5
  , .unpairLeft 6 7 6
  , .pair 7 0 0 7
  , .halt 0
  ]

@[simp] theorem recoveryLegalTermCoefficientLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermCoefficientLoweringProgram := by
  rfl

def recoveryLegalTermCoefficientLoweringFuel : ℕ := 8

def recoveryLegalTermCoefficientLoweringValues
    (inputLength handoff : ℕ) : List ℕ :=
  let bound := recoveryLegalSumBoundOutput handoff
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  [ inputLength
  , bound
  , arityStage
  , arityContext
  , context
  , modeRest
  , termsRest
  , recoveryLegalTermCoefficientTermsCode handoff
  , recoveryLegalTermCoefficientLoweringOutput handoff
  ]

def recoveryLegalTermCoefficientLoweringBits
    (inputLength handoff : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermCoefficientLoweringValues
      inputLength handoff).foldr max 0

theorem recoveryLegalTermCoefficientLoweringValue_bits
    {inputLength handoff value : ℕ}
    (hvalue :
      value ∈ recoveryLegalTermCoefficientLoweringValues
        inputLength handoff) :
    natBitLength value ≤
      recoveryLegalTermCoefficientLoweringBits inputLength handoff := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

theorem run_recoveryLegalTermCoefficientLoweringProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalTermCoefficientLoweringProgram
        (recoveryLegalTermCoefficientLoweringBits inputLength handoff)
        recoveryLegalTermCoefficientLoweringFuel
        (initialNPOracleState inputLength
          (recoveryLegalSumBoundOutput handoff)) =
      some (recoveryLegalTermCoefficientLoweringOutput handoff) := by
  let bound := recoveryLegalSumBoundOutput handoff
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  have hbits :
      ∀ value ∈ recoveryLegalTermCoefficientLoweringValues
          inputLength handoff,
        natBitLength value ≤
          recoveryLegalTermCoefficientLoweringBits inputLength handoff := by
    intro value hvalue
    exact recoveryLegalTermCoefficientLoweringValue_bits hvalue
  have harityStage := hbits arityStage (by
    simp [recoveryLegalTermCoefficientLoweringValues, bound,
      arityStage])
  have harityContext := hbits arityContext (by
    simp [recoveryLegalTermCoefficientLoweringValues, bound,
      arityStage, arityContext])
  have hcontext := hbits context (by
    simp [recoveryLegalTermCoefficientLoweringValues, bound,
      arityStage, arityContext, context])
  have hmodeRest := hbits modeRest (by
    simp [recoveryLegalTermCoefficientLoweringValues, bound,
      arityStage, arityContext, context, modeRest])
  have htermsRest := hbits termsRest (by
    simp [recoveryLegalTermCoefficientLoweringValues, bound,
      arityStage, arityContext, context, modeRest,
      termsRest])
  have hterms := hbits (recoveryLegalTermCoefficientTermsCode handoff) (by
    simp [recoveryLegalTermCoefficientLoweringValues])
  have houtput :=
    hbits (recoveryLegalTermCoefficientLoweringOutput handoff) (by
      simp [recoveryLegalTermCoefficientLoweringValues])
  rw [show recoveryLegalTermCoefficientLoweringFuel = 7 + 1 by rfl]
  rw [run_unpairRight_instruction (value := arityStage)
    (by rfl) rfl
    (by simp [initialNPOracleState, bound, arityStage])
    harityStage]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := arityContext)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, arityStage,
      arityContext])
    harityContext]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, arityContext,
      context])
    hcontext]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := modeRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context,
      modeRest])
    hmodeRest]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := termsRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, modeRest,
      termsRest])
    htermsRest]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := recoveryLegalTermCoefficientTermsCode handoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, termsRest, modeRest,
      context, arityContext, arityStage, bound,
      recoveryLegalTermCoefficientTermsCode])
    hterms]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := recoveryLegalTermCoefficientLoweringOutput handoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      initialNPOracleState, recoveryLegalTermCoefficientLoweringOutput])
    houtput]
  exact run_halt_instruction (fuel := 0)
    (value := recoveryLegalTermCoefficientLoweringOutput handoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

def recoveryLegalTermCoefficientStageOutput
    (inputLength handoff : ℕ) : ℕ :=
  Nat.pair
    (recoveryLegalTermCoefficientListOutput inputLength
      (recoveryLegalTermCoefficientTermsCode handoff))
    (recoveryLegalSumBoundOutput handoff)

def recoveryLegalTermCoefficientStageProgram : NPOracleProgram :=
  preserveRightProgram recoveryLegalTermCoefficientListProgram

@[simp] theorem recoveryLegalTermCoefficientStageProgram_oracleFree :
    OracleFree recoveryLegalTermCoefficientStageProgram :=
  preserveRightProgram_oracleFree
    recoveryLegalTermCoefficientListProgram
    recoveryLegalTermCoefficientListProgram_oracleFree

def recoveryLegalTermCoefficientStageFuel
    (inputLength handoff : ℕ) : ℕ :=
  preserveRightFuel <|
    recoveryLegalTermCoefficientListFuel inputLength
      (recoveryLegalTermCoefficientTermsCode handoff)

def recoveryLegalTermCoefficientStageBits
    (inputLength handoff : ℕ) : ℕ :=
  preserveRightBits
    (recoveryLegalTermCoefficientListBits inputLength
      (recoveryLegalTermCoefficientTermsCode handoff))
    (recoveryLegalTermCoefficientTermsCode handoff)
    (recoveryLegalSumBoundOutput handoff)
    (recoveryLegalTermCoefficientListOutput inputLength
      (recoveryLegalTermCoefficientTermsCode handoff))

theorem run_recoveryLegalTermCoefficientStageProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalTermCoefficientStageProgram
        (recoveryLegalTermCoefficientStageBits inputLength handoff)
        (recoveryLegalTermCoefficientStageFuel inputLength handoff)
        (initialNPOracleState inputLength
          (recoveryLegalTermCoefficientLoweringOutput handoff)) =
      some (recoveryLegalTermCoefficientStageOutput
        inputLength handoff) := by
  exact run_preserveRightProgram
    recoveryLegalTermCoefficientListProgram inputLength
    (recoveryLegalTermCoefficientListBits inputLength
      (recoveryLegalTermCoefficientTermsCode handoff))
    (recoveryLegalTermCoefficientListFuel inputLength
      (recoveryLegalTermCoefficientTermsCode handoff))
    (recoveryLegalTermCoefficientTermsCode handoff)
    (recoveryLegalSumBoundOutput handoff)
    (recoveryLegalTermCoefficientListOutput inputLength
      (recoveryLegalTermCoefficientTermsCode handoff))
    (run_recoveryLegalTermCoefficientListProgram inputLength
      (recoveryLegalTermCoefficientTermsCode handoff))

def recoveryLegalTermCoefficientMappedCode
    (inputLength handoff : ℕ) : ℕ :=
  let summary :=
    recoveryLegalTermCoefficientListOutput inputLength
      (recoveryLegalTermCoefficientTermsCode handoff)
  (Nat.unpair (Nat.unpair summary).2).1

def recoveryLegalTermBoundExpectedArity (handoff : ℕ) : ℕ :=
  let bound := recoveryLegalSumBoundOutput handoff
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  (Nat.unpair expectedRest).1

def recoveryLegalTermBoundHandoff (handoff : ℕ) : ℕ :=
  let bound := recoveryLegalSumBoundOutput handoff
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  let capHandoff := (Nat.unpair expectedRest).2
  (Nat.unpair capHandoff).2

def recoveryLegalTermCircuitContext (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalTermBoundExpectedArity handoff)
    (handoffMode (recoveryLegalTermBoundHandoff handoff)).pred

def recoveryLegalTermCircuitLoweringOutput
    (inputLength handoff : ℕ) : ℕ :=
  Nat.pair
    (nativeInputRequest (recoveryLegalTermCircuitContext handoff)
      (recoveryLegalTermCoefficientMappedCode inputLength handoff))
    (recoveryLegalTermCoefficientStageOutput inputLength handoff)

def recoveryLegalTermCircuitLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 2 4 3
  , .unpairLeft 4 5 4
  , .unpairRight 3 6 5
  , .unpairRight 6 7 6
  , .unpairRight 7 8 7
  , .unpairRight 8 9 8
  , .unpairRight 9 10 9
  , .unpairRight 10 11 10
  , .unpairLeft 11 12 11
  , .unpairRight 11 13 12
  , .unpairRight 13 14 13
  , .unpairLeft 14 15 14
  , .decrement 15 15
  , .pair 12 15 16 16
  , .pair 16 5 17 17
  , .pair 17 0 0 18
  , .halt 0
  ]

@[simp] theorem recoveryLegalTermCircuitLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermCircuitLoweringProgram := by
  rfl

def recoveryLegalTermCircuitLoweringFuel : ℕ := 19

def recoveryLegalTermCircuitLoweringValues
    (inputLength handoff : ℕ) : List ℕ :=
  let coefficientStage :=
    recoveryLegalTermCoefficientStageOutput inputLength handoff
  let coefficientSummary := (Nat.unpair coefficientStage).1
  let bound := (Nat.unpair coefficientStage).2
  let summaryData := (Nat.unpair coefficientSummary).2
  let mappedCode := (Nat.unpair summaryData).1
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  let expected := (Nat.unpair expectedRest).1
  let capHandoff := (Nat.unpair expectedRest).2
  let storedHandoff := (Nat.unpair capHandoff).2
  let mode := handoffMode storedHandoff
  let family := mode.pred
  let circuitContext := Nat.pair expected family
  let request := nativeInputRequest circuitContext mappedCode
  let output := Nat.pair request coefficientStage
  [ inputLength
  , coefficientStage
  , coefficientSummary
  , bound
  , summaryData
  , mappedCode
  , arityStage
  , arityContext
  , context
  , modeRest
  , termsRest
  , expectedRest
  , expected
  , capHandoff
  , storedHandoff
  , mode
  , family
  , circuitContext
  , request
  , output
  ]

def recoveryLegalTermCircuitLoweringCoreStateOf
    (inputLength coefficientStage coefficientSummary bound summaryData
      mappedCode arityStage arityContext context modeRest : ℕ) :
    NPOracleState :=
  let state₀ := initialNPOracleState inputLength coefficientStage
  let state₁ := (state₀.write 2 coefficientSummary).jump 1
  let state₂ := (state₁.write 3 bound).jump 2
  let state₃ := (state₂.write 4 summaryData).jump 3
  let state₄ := (state₃.write 5 mappedCode).jump 4
  let state₅ := (state₄.write 6 arityStage).jump 5
  let state₆ := (state₅.write 7 arityContext).jump 6
  let state₇ := (state₆.write 8 context).jump 7
  (state₇.write 9 modeRest).jump 8

def recoveryLegalTermCircuitLoweringCoreState
    (inputLength handoff : ℕ) : NPOracleState :=
  let coefficientStage :=
    recoveryLegalTermCoefficientStageOutput inputLength handoff
  let coefficientSummary := (Nat.unpair coefficientStage).1
  let bound := (Nat.unpair coefficientStage).2
  let summaryData := (Nat.unpair coefficientSummary).2
  let mappedCode := (Nat.unpair summaryData).1
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  recoveryLegalTermCircuitLoweringCoreStateOf inputLength coefficientStage
    coefficientSummary bound summaryData mappedCode arityStage arityContext
    context modeRest

def recoveryLegalTermCircuitLoweringPreparedStateOf
    (state₈ : NPOracleState)
    (termsRest expectedRest expected capHandoff storedHandoff mode family : ℕ) :
    NPOracleState :=
  let state₉ := (state₈.write 10 termsRest).jump 9
  let state₁₀ := (state₉.write 11 expectedRest).jump 10
  let state₁₁ := (state₁₀.write 12 expected).jump 11
  let state₁₂ := (state₁₁.write 13 capHandoff).jump 12
  let state₁₃ := (state₁₂.write 14 storedHandoff).jump 13
  let state₁₄ := (state₁₃.write 15 mode).jump 14
  (state₁₄.write 15 family).jump 15

def recoveryLegalTermCircuitLoweringPreparedState
    (inputLength handoff : ℕ) : NPOracleState :=
  let coefficientStage :=
    recoveryLegalTermCoefficientStageOutput inputLength handoff
  let bound := (Nat.unpair coefficientStage).2
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  let expected := (Nat.unpair expectedRest).1
  let capHandoff := (Nat.unpair expectedRest).2
  let storedHandoff := (Nat.unpair capHandoff).2
  let mode := handoffMode storedHandoff
  let family := mode.pred
  let state₈ :=
    recoveryLegalTermCircuitLoweringCoreState inputLength handoff
  recoveryLegalTermCircuitLoweringPreparedStateOf state₈ termsRest
    expectedRest expected capHandoff storedHandoff mode family

theorem recoveryLegalTermCircuitLoweringCoreStateOf_reg0
    (inputLength coefficientStage coefficientSummary bound summaryData
      mappedCode arityStage arityContext context modeRest : ℕ) :
    (recoveryLegalTermCircuitLoweringCoreStateOf inputLength coefficientStage
      coefficientSummary bound summaryData mappedCode arityStage arityContext
      context modeRest).registers 0 = coefficientStage := by
  rfl

theorem recoveryLegalTermCircuitLoweringCoreStateOf_reg5
    (inputLength coefficientStage coefficientSummary bound summaryData
      mappedCode arityStage arityContext context modeRest : ℕ) :
    (recoveryLegalTermCircuitLoweringCoreStateOf inputLength coefficientStage
      coefficientSummary bound summaryData mappedCode arityStage arityContext
      context modeRest).registers 5 = mappedCode := by
  rfl

theorem recoveryLegalTermCircuitLoweringCoreState_reg0
    (inputLength handoff : ℕ) :
    (recoveryLegalTermCircuitLoweringCoreState
      inputLength handoff).registers 0 =
        recoveryLegalTermCoefficientStageOutput inputLength handoff := by
  exact recoveryLegalTermCircuitLoweringCoreStateOf_reg0 _ _ _ _ _ _ _ _ _ _

theorem recoveryLegalTermCircuitLoweringCoreState_reg5
    (inputLength handoff : ℕ) :
    (recoveryLegalTermCircuitLoweringCoreState
      inputLength handoff).registers 5 =
        (Nat.unpair
          (Nat.unpair
            (Nat.unpair
              (recoveryLegalTermCoefficientStageOutput
                inputLength handoff)).1).2).1 := by
  exact recoveryLegalTermCircuitLoweringCoreStateOf_reg5 _ _ _ _ _ _ _ _ _ _

theorem recoveryLegalTermCircuitLoweringPreparedStateOf_pc
    (state₈ : NPOracleState)
    (termsRest expectedRest expected capHandoff storedHandoff mode family : ℕ) :
    (recoveryLegalTermCircuitLoweringPreparedStateOf state₈ termsRest
      expectedRest expected capHandoff storedHandoff mode family).pc = 15 := by
  rfl

theorem recoveryLegalTermCircuitLoweringPreparedStateOf_reg0
    (state₈ : NPOracleState)
    (termsRest expectedRest expected capHandoff storedHandoff mode family : ℕ) :
    (recoveryLegalTermCircuitLoweringPreparedStateOf state₈ termsRest
      expectedRest expected capHandoff storedHandoff mode family).registers 0 =
        state₈.registers 0 := by
  rfl

theorem recoveryLegalTermCircuitLoweringPreparedStateOf_reg5
    (state₈ : NPOracleState)
    (termsRest expectedRest expected capHandoff storedHandoff mode family : ℕ) :
    (recoveryLegalTermCircuitLoweringPreparedStateOf state₈ termsRest
      expectedRest expected capHandoff storedHandoff mode family).registers 5 =
        state₈.registers 5 := by
  rfl

theorem recoveryLegalTermCircuitLoweringPreparedStateOf_reg12
    (state₈ : NPOracleState)
    (termsRest expectedRest expected capHandoff storedHandoff mode family : ℕ) :
    (recoveryLegalTermCircuitLoweringPreparedStateOf state₈ termsRest
      expectedRest expected capHandoff storedHandoff mode family).registers 12 =
        expected := by
  rfl

theorem recoveryLegalTermCircuitLoweringPreparedStateOf_reg15
    (state₈ : NPOracleState)
    (termsRest expectedRest expected capHandoff storedHandoff mode family : ℕ) :
    (recoveryLegalTermCircuitLoweringPreparedStateOf state₈ termsRest
      expectedRest expected capHandoff storedHandoff mode family).registers 15 =
        family := by
  rfl

theorem recoveryLegalTermCircuitLoweringPreparedState_pc
    (inputLength handoff : ℕ) :
    (recoveryLegalTermCircuitLoweringPreparedState inputLength handoff).pc =
      15 := by
  exact recoveryLegalTermCircuitLoweringPreparedStateOf_pc _ _ _ _ _ _ _ _

theorem recoveryLegalTermCircuitLoweringPreparedState_reg0
    (inputLength handoff : ℕ) :
    (recoveryLegalTermCircuitLoweringPreparedState
      inputLength handoff).registers 0 =
        recoveryLegalTermCoefficientStageOutput inputLength handoff := by
  rw [show
    (recoveryLegalTermCircuitLoweringPreparedState
      inputLength handoff).registers 0 =
        (recoveryLegalTermCircuitLoweringCoreState
          inputLength handoff).registers 0 by
      exact recoveryLegalTermCircuitLoweringPreparedStateOf_reg0 _ _ _ _ _ _ _ _]
  exact recoveryLegalTermCircuitLoweringCoreState_reg0 inputLength handoff

theorem recoveryLegalTermCircuitLoweringPreparedState_reg5
    (inputLength handoff : ℕ) :
    (recoveryLegalTermCircuitLoweringPreparedState
      inputLength handoff).registers 5 =
        (Nat.unpair
          (Nat.unpair
            (Nat.unpair
              (recoveryLegalTermCoefficientStageOutput
                inputLength handoff)).1).2).1 := by
  rw [show
    (recoveryLegalTermCircuitLoweringPreparedState
      inputLength handoff).registers 5 =
        (recoveryLegalTermCircuitLoweringCoreState
          inputLength handoff).registers 5 by
      exact recoveryLegalTermCircuitLoweringPreparedStateOf_reg5 _ _ _ _ _ _ _ _]
  exact recoveryLegalTermCircuitLoweringCoreState_reg5 inputLength handoff

theorem recoveryLegalTermCircuitLoweringPreparedState_reg12
    (inputLength handoff : ℕ) :
    (recoveryLegalTermCircuitLoweringPreparedState
      inputLength handoff).registers 12 =
        (Nat.unpair
          (Nat.unpair
            (Nat.unpair
              (Nat.unpair
                (Nat.unpair
                  (Nat.unpair
                    (Nat.unpair
                      (Nat.unpair
                        (recoveryLegalTermCoefficientStageOutput
                          inputLength handoff)).2).2).2).2).2).2).2).1 := by
  exact recoveryLegalTermCircuitLoweringPreparedStateOf_reg12 _ _ _ _ _ _ _ _

theorem recoveryLegalTermCircuitLoweringPreparedState_reg15
    (inputLength handoff : ℕ) :
    (recoveryLegalTermCircuitLoweringPreparedState
      inputLength handoff).registers 15 =
        (handoffMode
          (Nat.unpair
            (Nat.unpair
              (Nat.unpair
                (Nat.unpair
                  (Nat.unpair
                    (Nat.unpair
                      (Nat.unpair
                        (Nat.unpair
                          (Nat.unpair
                            (recoveryLegalTermCoefficientStageOutput
                              inputLength handoff)).2).2).2).2).2).2).2).2).2).pred := by
  exact recoveryLegalTermCircuitLoweringPreparedStateOf_reg15 _ _ _ _ _ _ _ _

def recoveryLegalTermCircuitLoweringBits
    (inputLength handoff : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermCircuitLoweringValues
      inputLength handoff).foldr max 0

theorem recoveryLegalTermCircuitLoweringValue_bits
    {inputLength handoff value : ℕ}
    (hvalue :
      value ∈ recoveryLegalTermCircuitLoweringValues inputLength handoff) :
    natBitLength value ≤
      recoveryLegalTermCircuitLoweringBits inputLength handoff := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
-- Checkpointing keeps the decoded-register trace bounded, but the first
-- fifteen straight-line VM steps still exceed Lean's default elaboration fuel.
private theorem run_recoveryLegalTermCircuitLoweringProgram_prefix
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalTermCircuitLoweringProgram
        (recoveryLegalTermCircuitLoweringBits inputLength handoff)
        recoveryLegalTermCircuitLoweringFuel
        (initialNPOracleState inputLength
          (recoveryLegalTermCoefficientStageOutput inputLength handoff)) =
      runNPOracleProgram recoveryLegalTermCircuitLoweringProgram
        (recoveryLegalTermCircuitLoweringBits inputLength handoff) 4
        (recoveryLegalTermCircuitLoweringPreparedState
          inputLength handoff) := by
  let coefficientStage :=
    recoveryLegalTermCoefficientStageOutput inputLength handoff
  let coefficientSummary := (Nat.unpair coefficientStage).1
  let bound := (Nat.unpair coefficientStage).2
  let summaryData := (Nat.unpair coefficientSummary).2
  let mappedCode := (Nat.unpair summaryData).1
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  let expected := (Nat.unpair expectedRest).1
  let capHandoff := (Nat.unpair expectedRest).2
  let storedHandoff := (Nat.unpair capHandoff).2
  let mode := handoffMode storedHandoff
  let family := mode.pred
  have hbits :
      ∀ value ∈
          recoveryLegalTermCircuitLoweringValues inputLength handoff,
        natBitLength value ≤
          recoveryLegalTermCircuitLoweringBits inputLength handoff := by
    intro value hvalue
    exact recoveryLegalTermCircuitLoweringValue_bits hvalue
  have hcoefficientSummary := hbits coefficientSummary (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage,
      coefficientSummary])
  have hbound := hbits bound (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound])
  have hsummaryData := hbits summaryData (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage,
      coefficientSummary, summaryData])
  have hmapped := hbits mappedCode (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage,
      coefficientSummary, summaryData, mappedCode])
  have harityStage := hbits arityStage (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound,
      arityStage])
  have harityContext := hbits arityContext (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound,
      arityStage, arityContext])
  have hcontext := hbits context (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context])
  have hmodeRest := hbits modeRest (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest])
  have htermsRest := hbits termsRest (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest, termsRest])
  have hexpectedRest := hbits expectedRest (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest, termsRest, expectedRest])
  have hexpected := hbits expected (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest, termsRest, expectedRest,
      expected])
  have hcapHandoff := hbits capHandoff (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest, termsRest, expectedRest,
      capHandoff])
  have hstored := hbits storedHandoff (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest, termsRest, expectedRest,
      capHandoff, storedHandoff])
  have hmode := hbits mode (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest, termsRest, expectedRest,
      capHandoff, storedHandoff, mode])
  have hfamily := hbits family (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest, termsRest, expectedRest,
      capHandoff, storedHandoff, mode, family])
  rw [show recoveryLegalTermCircuitLoweringFuel = 18 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := coefficientSummary)
    (by rfl) rfl
    (by simp [initialNPOracleState, coefficientStage, coefficientSummary])
    hcoefficientSummary]
  rw [show 18 = 17 + 1 by omega]
  rw [run_unpairRight_instruction (value := bound)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, coefficientStage, bound])
    hbound]
  rw [show 17 = 16 + 1 by omega]
  rw [run_unpairRight_instruction (value := summaryData)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, coefficientSummary,
      summaryData])
    hsummaryData]
  rw [show 16 = 15 + 1 by omega]
  rw [run_unpairLeft_instruction (value := mappedCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, summaryData,
      mappedCode])
    hmapped]
  rw [show 15 = 14 + 1 by omega]
  rw [run_unpairRight_instruction (value := arityStage)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bound, arityStage])
    harityStage]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairRight_instruction (value := arityContext)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, arityStage,
      arityContext])
    harityContext]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, arityContext,
      context])
    hcontext]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction (value := modeRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context, modeRest])
    hmodeRest]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction (value := termsRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, modeRest, termsRest])
    htermsRest]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := expectedRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, termsRest,
      expectedRest])
    hexpectedRest]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := expected)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, expectedRest,
      expected])
    hexpected]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := capHandoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, expectedRest,
      capHandoff])
    hcapHandoff]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := storedHandoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capHandoff,
      storedHandoff])
    hstored]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := mode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, storedHandoff, mode,
      handoffMode])
    hmode]
  rw [show 5 = 4 + 1 by omega]
  rw [run_decrement_instruction (value := family)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, mode, family])
    hfamily]
  rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 400000 in
-- The suffix proves raw-register/semantic correspondence for the three packed
-- outputs; its controlled unfolding is slightly above the default budget.
theorem run_recoveryLegalTermCircuitLoweringProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalTermCircuitLoweringProgram
        (recoveryLegalTermCircuitLoweringBits inputLength handoff)
        recoveryLegalTermCircuitLoweringFuel
        (initialNPOracleState inputLength
          (recoveryLegalTermCoefficientStageOutput inputLength handoff)) =
      some (recoveryLegalTermCircuitLoweringOutput
        inputLength handoff) := by
  rw [run_recoveryLegalTermCircuitLoweringProgram_prefix]
  let coefficientStage :=
    recoveryLegalTermCoefficientStageOutput inputLength handoff
  let coefficientSummary := (Nat.unpair coefficientStage).1
  let bound := (Nat.unpair coefficientStage).2
  let summaryData := (Nat.unpair coefficientSummary).2
  let mappedCode := (Nat.unpair summaryData).1
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  let expected := (Nat.unpair expectedRest).1
  let capHandoff := (Nat.unpair expectedRest).2
  let storedHandoff := (Nat.unpair capHandoff).2
  let mode := handoffMode storedHandoff
  let family := mode.pred
  let circuitContext := Nat.pair expected family
  let request := nativeInputRequest circuitContext mappedCode
  let output := Nat.pair request coefficientStage
  have hbits :
      ∀ value ∈
          recoveryLegalTermCircuitLoweringValues inputLength handoff,
        natBitLength value ≤
          recoveryLegalTermCircuitLoweringBits inputLength handoff := by
    intro value hvalue
    exact recoveryLegalTermCircuitLoweringValue_bits hvalue
  have hcircuitContext := hbits circuitContext (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest, termsRest, expectedRest,
      expected, capHandoff, storedHandoff, mode, family, circuitContext])
  have hrequest := hbits request (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage,
      coefficientSummary, bound, summaryData, mappedCode, arityStage,
      arityContext, context, modeRest, termsRest, expectedRest, expected,
      capHandoff, storedHandoff, mode, family, circuitContext, request])
  have houtput := hbits output (by
    simp [recoveryLegalTermCircuitLoweringValues, coefficientStage,
      coefficientSummary, bound, summaryData, mappedCode, arityStage,
      arityContext, context, modeRest, termsRest, expectedRest, expected,
      capHandoff, storedHandoff, mode, family, circuitContext, request,
      output])
  have houtputShape :
      output =
        recoveryLegalTermCircuitLoweringOutput inputLength handoff := by
    simp [output, request, circuitContext, family, mode, storedHandoff,
      capHandoff, expected, expectedRest, termsRest, modeRest, context,
      arityContext, arityStage, mappedCode, summaryData, coefficientSummary,
      bound, coefficientStage, recoveryLegalTermCircuitLoweringOutput,
      recoveryLegalTermCoefficientStageOutput,
      recoveryLegalTermCircuitContext, recoveryLegalTermBoundExpectedArity,
      recoveryLegalTermBoundHandoff, recoveryLegalTermCoefficientMappedCode,
      Nat.unpair_pair]
  have hfinish (state : NPOracleState)
      (hpc : state.pc = 15)
      (hstage0 : state.registers 0 = coefficientStage)
      (hmapped5 : state.registers 5 = mappedCode)
      (hexpected12 : state.registers 12 = expected)
      (hfamily15 : state.registers 15 = family) :
      runNPOracleProgram recoveryLegalTermCircuitLoweringProgram
          (recoveryLegalTermCircuitLoweringBits inputLength handoff)
          4 state =
        some output := by
    rw [show 4 = 3 + 1 by omega]
    rw [run_pair_instruction (value := circuitContext)
      (by rfl) hpc
      (by rw [hexpected12, hfamily15])
      hcircuitContext]
    rw [show 3 = 2 + 1 by omega]
    rw [run_pair_instruction (value := request)
      (by rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, hmapped5, request,
          nativeInputRequest])
      hrequest]
    rw [show 2 = 1 + 1 by omega]
    rw [run_pair_instruction (value := output)
      (by rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, hstage0, output])
      houtput]
    exact run_halt_instruction (fuel := 0) (value := output)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      houtput
  rw [← houtputShape]
  exact hfinish
    (recoveryLegalTermCircuitLoweringPreparedState inputLength handoff)
    (recoveryLegalTermCircuitLoweringPreparedState_pc inputLength handoff)
    (recoveryLegalTermCircuitLoweringPreparedState_reg0 inputLength handoff)
    (recoveryLegalTermCircuitLoweringPreparedState_reg5 inputLength handoff)
    (recoveryLegalTermCircuitLoweringPreparedState_reg12 inputLength handoff)
    (recoveryLegalTermCircuitLoweringPreparedState_reg15 inputLength handoff)

def recoveryLegalTermCircuitStageOutput
    (inputLength handoff : ℕ) : ℕ :=
  Nat.pair
    (recoveryLegalTermCircuitListOutput
      (recoveryLegalTermCircuitContext handoff)
      (recoveryLegalTermCoefficientMappedCode inputLength handoff))
    (recoveryLegalTermCoefficientStageOutput inputLength handoff)

def recoveryLegalTermCircuitStageProgram : NPOracleProgram :=
  preserveRightProgram <|
    nativeCallProgram recoveryLegalTermCircuitListProgram

@[simp] theorem recoveryLegalTermCircuitStageProgram_oracleFree :
    OracleFree recoveryLegalTermCircuitStageProgram :=
  preserveRightProgram_oracleFree
    (nativeCallProgram recoveryLegalTermCircuitListProgram)
    (nativeCallProgram_oracleFree
      recoveryLegalTermCircuitListProgram_oracleFree)

def recoveryLegalTermCircuitStageFuel
    (inputLength handoff : ℕ) : ℕ :=
  preserveRightFuel <|
    nativeCallFuel recoveryLegalTermCircuitListProgram
      (recoveryLegalTermCircuitListFuel
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff))
      (recoveryLegalTermCircuitContext handoff)
      (recoveryLegalTermCoefficientMappedCode inputLength handoff)

def recoveryLegalTermCircuitStageBits
    (inputLength handoff : ℕ) : ℕ :=
  let context := recoveryLegalTermCircuitContext handoff
  let raw := recoveryLegalTermCoefficientMappedCode inputLength handoff
  let output := recoveryLegalTermCircuitListOutput context raw
  preserveRightBits
    (nativeCallBits inputLength context raw output
      (recoveryLegalTermCircuitListBits context raw))
    (nativeInputRequest context raw)
    (recoveryLegalTermCoefficientStageOutput inputLength handoff)
    output

theorem run_recoveryLegalTermCircuitStageProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalTermCircuitStageProgram
        (recoveryLegalTermCircuitStageBits inputLength handoff)
        (recoveryLegalTermCircuitStageFuel inputLength handoff)
        (initialNPOracleState inputLength
          (recoveryLegalTermCircuitLoweringOutput inputLength handoff)) =
      some (recoveryLegalTermCircuitStageOutput inputLength handoff) := by
  apply run_preserveRightProgram
    (nativeCallProgram recoveryLegalTermCircuitListProgram)
  exact run_nativeCallProgram recoveryLegalTermCircuitListProgram
    inputLength
    (recoveryLegalTermCircuitContext handoff)
    (recoveryLegalTermCoefficientMappedCode inputLength handoff)
    (recoveryLegalTermCircuitListOutput
      (recoveryLegalTermCircuitContext handoff)
      (recoveryLegalTermCoefficientMappedCode inputLength handoff))
    (recoveryLegalTermCircuitListBits
      (recoveryLegalTermCircuitContext handoff)
      (recoveryLegalTermCoefficientMappedCode inputLength handoff))
    (recoveryLegalTermCircuitListFuel
      (recoveryLegalTermCircuitContext handoff)
      (recoveryLegalTermCoefficientMappedCode inputLength handoff))
    (run_recoveryLegalTermCircuitListProgram
      (recoveryLegalTermCircuitContext handoff)
      (recoveryLegalTermCoefficientMappedCode inputLength handoff))

/-! ## Circuit-to-coefficient-width handoff

This lowering reads only the circuit stage's retained mapped coefficient
summary and trusted limit handoff.  Its right component is the complete
circuit-stage value, so a successful width check restores the existing
finalization input exactly. -/

def recoveryLegalTermBitCapCoefficientStage (circuitStage : ℕ) : ℕ :=
  (Nat.unpair circuitStage).2

def recoveryLegalTermBitCapMappedCode (circuitStage : ℕ) : ℕ :=
  let coefficientStage :=
    recoveryLegalTermBitCapCoefficientStage circuitStage
  let coefficientSummary := (Nat.unpair coefficientStage).1
  let summaryData := (Nat.unpair coefficientSummary).2
  (Nat.unpair summaryData).1

def recoveryLegalTermBitCapStoredHandoff (circuitStage : ℕ) : ℕ :=
  let coefficientStage :=
    recoveryLegalTermBitCapCoefficientStage circuitStage
  let bound := (Nat.unpair coefficientStage).2
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  let capHandoff := (Nat.unpair expectedRest).2
  (Nat.unpair capHandoff).2

def recoveryLegalTermBitCapSelectedCap (circuitStage : ℕ) : ℕ :=
  handoffSelectedCoefficientBitCap
    (recoveryLegalTermBitCapStoredHandoff circuitStage)

def recoveryLegalTermMassCapCode (circuitStage : ℕ) : ℕ :=
  handoffSelectedCoefficientMassCapCode
    (recoveryLegalTermBitCapStoredHandoff circuitStage)

def recoveryLegalTermBitCapLoweringContext (circuitStage : ℕ) : ℕ :=
  Nat.pair (recoveryLegalTermBitCapMappedCode circuitStage) <|
    Nat.pair (recoveryLegalTermMassCapCode circuitStage) circuitStage

def recoveryLegalTermBitCapLoweringOutput (circuitStage : ℕ) : ℕ :=
  Nat.pair
    (nativeInputRequest
      (recoveryLegalTermBitCapSelectedCap circuitStage)
      (recoveryLegalTermBitCapMappedCode circuitStage))
    (recoveryLegalTermBitCapLoweringContext circuitStage)

def recoveryLegalTermBitCapLoweringProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 2 3 2
  , .unpairRight 3 4 3
  , .unpairLeft 4 5 4
  , .unpairRight 2 6 5
  , .unpairRight 6 7 6
  , .unpairRight 7 8 7
  , .unpairRight 8 9 8
  , .unpairRight 9 10 9
  , .unpairRight 10 11 10
  , .unpairRight 11 12 11
  , .unpairRight 12 13 12
  , .unpairRight 13 14 13
  , .unpairLeft 14 15 14
  , .unpairRight 14 16 15
  , .unpairRight 16 16 16
  , .unpairRight 16 16 17
  , .unpairRight 16 16 18
  , .unpairRight 16 16 19
  , .unpairRight 16 16 20
  , .unpairRight 16 16 21
  , .branchZero 15 28 22
  , .decrement 15 23
  , .branchZero 15 26 24
  , .decrement 15 25
  , .branchZero 15 27 28
  , .unpairLeft 16 16 29
  , .unpairRight 16 16 29
  , .set 16 0 29
  , .unpairRight 16 16 30
  , .unpairRight 16 16 31
  , .unpairLeft 16 17 32
  , .unpairRight 16 19 33
  , .unpairLeft 19 19 34
  , .pair 17 5 18 35
  , .pair 19 0 20 36
  , .pair 5 20 21 37
  , .pair 18 21 0 38
  , .halt 0
  ]

@[simp] theorem recoveryLegalTermBitCapLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermBitCapLoweringProgram := by
  rfl

def recoveryLegalTermBitCapLoweringFuel : ℕ := 37

def recoveryLegalTermBitCapLoweringValues
    (inputLength circuitStage : ℕ) : List ℕ :=
  let coefficientStage :=
    recoveryLegalTermBitCapCoefficientStage circuitStage
  let coefficientSummary := (Nat.unpair coefficientStage).1
  let summaryData := (Nat.unpair coefficientSummary).2
  let mappedCode := recoveryLegalTermBitCapMappedCode circuitStage
  let bound := (Nat.unpair coefficientStage).2
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  let capHandoff := (Nat.unpair expectedRest).2
  let storedHandoff :=
    recoveryLegalTermBitCapStoredHandoff circuitStage
  let mode := handoffMode storedHandoff
  let handoffTail₀ := (Nat.unpair storedHandoff).2
  let handoffTail₁ := (Nat.unpair handoffTail₀).2
  let handoffTail₂ := (Nat.unpair handoffTail₁).2
  let limitsCode := (Nat.unpair handoffTail₂).2
  let limitsTail₀ := (Nat.unpair limitsCode).2
  let limitsTail₁ := (Nat.unpair limitsTail₀).2
  let legalPair := (Nat.unpair limitsTail₁).2
  let selected := handoffSelectedLegalLimits storedHandoff
  let selectedTail₀ := (Nat.unpair selected).2
  let selectedTail₁ := (Nat.unpair selectedTail₀).2
  let selectedTail₂ := (Nat.unpair selectedTail₁).2
  let cap := (Nat.unpair selectedTail₁).1
  let massCap := (Nat.unpair selectedTail₂).1
  let request := nativeInputRequest cap mappedCode
  let massContext := Nat.pair massCap circuitStage
  let loweringContext := Nat.pair mappedCode massContext
  [ 0
  , inputLength
  , circuitStage
  , coefficientStage
  , coefficientSummary
  , summaryData
  , mappedCode
  , bound
  , arityStage
  , arityContext
  , context
  , modeRest
  , termsRest
  , expectedRest
  , capHandoff
  , storedHandoff
  , mode
  , handoffTail₀
  , handoffTail₁
  , handoffTail₂
  , limitsCode
  , limitsTail₀
  , limitsTail₁
  , legalPair
  , (Nat.unpair legalPair).1
  , (Nat.unpair legalPair).2
  , selected
  , selectedTail₀
  , selectedTail₁
  , selectedTail₂
  , cap
  , massCap
  , request
  , massContext
  , loweringContext
  , recoveryLegalTermBitCapLoweringOutput circuitStage
  ]

def recoveryLegalTermBitCapLoweringTraceBits
    (inputLength circuitStage : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermBitCapLoweringValues
      inputLength circuitStage).foldr max 0

def recoveryLegalTermBitCapLoweringSuffixBits
    (circuitStage : ℕ) : ℕ :=
  let stored := recoveryLegalTermBitCapStoredHandoff circuitStage
  let mode := handoffMode stored
  let legalPair := handoffLegalLimitsPair stored
  let selected := handoffSelectedLegalLimits stored
  max (natBitLength mode) <|
    max (natBitLength (Nat.unpair legalPair).1) <|
      max (natBitLength (Nat.unpair legalPair).2) <|
        max (natBitLength (Nat.unpair selected).2) <|
          max (natBitLength (Nat.unpair (Nat.unpair selected).2).2) <|
            max
              (natBitLength
                (Nat.unpair (Nat.unpair (Nat.unpair selected).2).2).1) <|
              let selectedTail₂ :=
                (Nat.unpair (Nat.unpair (Nat.unpair selected).2).2).2
              max (natBitLength selectedTail₂) <|
                max (natBitLength (Nat.unpair selectedTail₂).1) <|
                  max
                    (natBitLength
                      (nativeInputRequest
                        (Nat.unpair
                          (Nat.unpair (Nat.unpair selected).2).2).1
                        (recoveryLegalTermBitCapMappedCode circuitStage)))
                    (natBitLength
                      (recoveryLegalTermBitCapLoweringOutput circuitStage))

def recoveryLegalTermBitCapLoweringBits
    (inputLength circuitStage : ℕ) : ℕ :=
  max
    (recoveryLegalTermBitCapLoweringTraceBits inputLength circuitStage)
    (recoveryLegalTermBitCapLoweringSuffixBits circuitStage)

theorem recoveryLegalTermBitCapLoweringValue_bits
    {inputLength circuitStage value : ℕ}
    (hvalue :
      value ∈
        recoveryLegalTermBitCapLoweringValues inputLength circuitStage) :
    natBitLength value ≤
      recoveryLegalTermBitCapLoweringBits inputLength circuitStage := by
  apply (natBitLength_mono (member_le_foldr_max hvalue)).trans
  exact Nat.le_max_left _ _

def recoveryLegalTermBitCapLoweringCoreStateOf
    (inputLength circuitStage coefficientStage coefficientSummary summaryData
      mappedCode bound arityStage arityContext context modeRest : ℕ) :
    NPOracleState :=
  let state₁ :=
    ((initialNPOracleState inputLength circuitStage).write
      2 coefficientStage).jump 1
  let state₂ := (state₁.write 3 coefficientSummary).jump 2
  let state₃ := (state₂.write 4 summaryData).jump 3
  let state₄ := (state₃.write 5 mappedCode).jump 4
  let state₅ := (state₄.write 6 bound).jump 5
  let state₆ := (state₅.write 7 arityStage).jump 6
  let state₇ := (state₆.write 8 arityContext).jump 7
  let state₈ := (state₇.write 9 context).jump 8
  (state₈.write 10 modeRest).jump 9

def recoveryLegalTermBitCapLoweringCoreState
    (inputLength circuitStage : ℕ) : NPOracleState :=
  let coefficientStage :=
    recoveryLegalTermBitCapCoefficientStage circuitStage
  let coefficientSummary := (Nat.unpair coefficientStage).1
  let summaryData := (Nat.unpair coefficientSummary).2
  let mappedCode := recoveryLegalTermBitCapMappedCode circuitStage
  let bound := (Nat.unpair coefficientStage).2
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  recoveryLegalTermBitCapLoweringCoreStateOf inputLength circuitStage
    coefficientStage coefficientSummary summaryData mappedCode bound
    arityStage arityContext context modeRest

def recoveryLegalTermBitCapLoweringHandoffStateOf
    (state₉ : NPOracleState)
    (termsRest expectedRest capHandoff storedHandoff mode handoffTail₀ : ℕ) :
    NPOracleState :=
  let state₁₀ := (state₉.write 11 termsRest).jump 10
  let state₁₁ := (state₁₀.write 12 expectedRest).jump 11
  let state₁₂ := (state₁₁.write 13 capHandoff).jump 12
  let state₁₃ := (state₁₂.write 14 storedHandoff).jump 13
  let state₁₄ := (state₁₃.write 15 mode).jump 14
  (state₁₄.write 16 handoffTail₀).jump 15

def recoveryLegalTermBitCapLoweringHandoffState
    (inputLength circuitStage : ℕ) : NPOracleState :=
  let coefficientStage :=
    recoveryLegalTermBitCapCoefficientStage circuitStage
  let bound := (Nat.unpair coefficientStage).2
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  let capHandoff := (Nat.unpair expectedRest).2
  let storedHandoff :=
    recoveryLegalTermBitCapStoredHandoff circuitStage
  let mode := handoffMode storedHandoff
  let handoffTail₀ := (Nat.unpair storedHandoff).2
  recoveryLegalTermBitCapLoweringHandoffStateOf
    (recoveryLegalTermBitCapLoweringCoreState inputLength circuitStage)
    termsRest expectedRest capHandoff storedHandoff mode handoffTail₀

def recoveryLegalTermBitCapLoweringPreparedStateOf
    (state₁₅ : NPOracleState)
    (handoffTail₁ handoffTail₂ limitsCode limitsTail₀ limitsTail₁
      legalPair : ℕ) : NPOracleState :=
  let state₁₆ := (state₁₅.write 16 handoffTail₁).jump 16
  let state₁₇ := (state₁₆.write 16 handoffTail₂).jump 17
  let state₁₈ := (state₁₇.write 16 limitsCode).jump 18
  let state₁₉ := (state₁₈.write 16 limitsTail₀).jump 19
  let state₂₀ := (state₁₉.write 16 limitsTail₁).jump 20
  (state₂₀.write 16 legalPair).jump 21

def recoveryLegalTermBitCapLoweringPreparedState
    (inputLength circuitStage : ℕ) : NPOracleState :=
  let storedHandoff :=
    recoveryLegalTermBitCapStoredHandoff circuitStage
  let handoffTail₀ := (Nat.unpair storedHandoff).2
  let handoffTail₁ := (Nat.unpair handoffTail₀).2
  let handoffTail₂ := (Nat.unpair handoffTail₁).2
  let limitsCode := (Nat.unpair handoffTail₂).2
  let limitsTail₀ := (Nat.unpair limitsCode).2
  let limitsTail₁ := (Nat.unpair limitsTail₀).2
  let legalPair := (Nat.unpair limitsTail₁).2
  recoveryLegalTermBitCapLoweringPreparedStateOf
    (recoveryLegalTermBitCapLoweringHandoffState inputLength circuitStage)
    handoffTail₁ handoffTail₂ limitsCode limitsTail₀ limitsTail₁ legalPair

theorem recoveryLegalTermBitCapLoweringCoreStateOf_reg0
    (inputLength circuitStage coefficientStage coefficientSummary summaryData
      mappedCode bound arityStage arityContext context modeRest : ℕ) :
    (recoveryLegalTermBitCapLoweringCoreStateOf inputLength circuitStage
      coefficientStage coefficientSummary summaryData mappedCode bound
      arityStage arityContext context modeRest).registers 0 =
        circuitStage := by
  rfl

theorem recoveryLegalTermBitCapLoweringCoreStateOf_reg5
    (inputLength circuitStage coefficientStage coefficientSummary summaryData
      mappedCode bound arityStage arityContext context modeRest : ℕ) :
    (recoveryLegalTermBitCapLoweringCoreStateOf inputLength circuitStage
      coefficientStage coefficientSummary summaryData mappedCode bound
      arityStage arityContext context modeRest).registers 5 =
        mappedCode := by
  rfl

theorem recoveryLegalTermBitCapLoweringHandoffStateOf_reg0
    (state₉ : NPOracleState)
    (termsRest expectedRest capHandoff storedHandoff mode handoffTail₀ : ℕ) :
    (recoveryLegalTermBitCapLoweringHandoffStateOf state₉ termsRest
      expectedRest capHandoff storedHandoff mode handoffTail₀).registers 0 =
        state₉.registers 0 := by
  rfl

theorem recoveryLegalTermBitCapLoweringHandoffStateOf_reg5
    (state₉ : NPOracleState)
    (termsRest expectedRest capHandoff storedHandoff mode handoffTail₀ : ℕ) :
    (recoveryLegalTermBitCapLoweringHandoffStateOf state₉ termsRest
      expectedRest capHandoff storedHandoff mode handoffTail₀).registers 5 =
        state₉.registers 5 := by
  rfl

theorem recoveryLegalTermBitCapLoweringHandoffStateOf_reg15
    (state₉ : NPOracleState)
    (termsRest expectedRest capHandoff storedHandoff mode handoffTail₀ : ℕ) :
    (recoveryLegalTermBitCapLoweringHandoffStateOf state₉ termsRest
      expectedRest capHandoff storedHandoff mode handoffTail₀).registers 15 =
        mode := by
  rfl

theorem recoveryLegalTermBitCapLoweringHandoffStateOf_reg16
    (state₉ : NPOracleState)
    (termsRest expectedRest capHandoff storedHandoff mode handoffTail₀ : ℕ) :
    (recoveryLegalTermBitCapLoweringHandoffStateOf state₉ termsRest
      expectedRest capHandoff storedHandoff mode handoffTail₀).registers 16 =
        handoffTail₀ := by
  rfl

theorem recoveryLegalTermBitCapLoweringPreparedStateOf_reg0
    (state₁₅ : NPOracleState)
    (handoffTail₁ handoffTail₂ limitsCode limitsTail₀ limitsTail₁
      legalPair : ℕ) :
    (recoveryLegalTermBitCapLoweringPreparedStateOf state₁₅ handoffTail₁
      handoffTail₂ limitsCode limitsTail₀ limitsTail₁ legalPair).registers 0 =
        state₁₅.registers 0 := by
  rfl

theorem recoveryLegalTermBitCapLoweringPreparedStateOf_reg5
    (state₁₅ : NPOracleState)
    (handoffTail₁ handoffTail₂ limitsCode limitsTail₀ limitsTail₁
      legalPair : ℕ) :
    (recoveryLegalTermBitCapLoweringPreparedStateOf state₁₅ handoffTail₁
      handoffTail₂ limitsCode limitsTail₀ limitsTail₁ legalPair).registers 5 =
        state₁₅.registers 5 := by
  rfl

theorem recoveryLegalTermBitCapLoweringPreparedStateOf_reg15
    (state₁₅ : NPOracleState)
    (handoffTail₁ handoffTail₂ limitsCode limitsTail₀ limitsTail₁
      legalPair : ℕ) :
    (recoveryLegalTermBitCapLoweringPreparedStateOf state₁₅ handoffTail₁
      handoffTail₂ limitsCode limitsTail₀ limitsTail₁ legalPair).registers 15 =
        state₁₅.registers 15 := by
  rfl

theorem recoveryLegalTermBitCapLoweringPreparedState_pc
    (inputLength circuitStage : ℕ) :
    (recoveryLegalTermBitCapLoweringPreparedState
      inputLength circuitStage).pc = 21 := by
  rfl

theorem recoveryLegalTermBitCapLoweringHandoffState_reg16
    (inputLength circuitStage : ℕ) :
    (recoveryLegalTermBitCapLoweringHandoffState
      inputLength circuitStage).registers 16 =
        (Nat.unpair
          (recoveryLegalTermBitCapStoredHandoff circuitStage)).2 := by
  unfold recoveryLegalTermBitCapLoweringHandoffState
  exact recoveryLegalTermBitCapLoweringHandoffStateOf_reg16 _ _ _ _ _ _ _

theorem recoveryLegalTermBitCapLoweringPreparedState_reg0
    (inputLength circuitStage : ℕ) :
    (recoveryLegalTermBitCapLoweringPreparedState
      inputLength circuitStage).registers 0 = circuitStage := by
  unfold recoveryLegalTermBitCapLoweringPreparedState
  rw [recoveryLegalTermBitCapLoweringPreparedStateOf_reg0]
  unfold recoveryLegalTermBitCapLoweringHandoffState
  rw [recoveryLegalTermBitCapLoweringHandoffStateOf_reg0]
  unfold recoveryLegalTermBitCapLoweringCoreState
  exact recoveryLegalTermBitCapLoweringCoreStateOf_reg0 _ _ _ _ _ _ _ _ _ _ _

theorem recoveryLegalTermBitCapLoweringPreparedState_reg5
    (inputLength circuitStage : ℕ) :
    (recoveryLegalTermBitCapLoweringPreparedState
      inputLength circuitStage).registers 5 =
        recoveryLegalTermBitCapMappedCode circuitStage := by
  unfold recoveryLegalTermBitCapLoweringPreparedState
  rw [recoveryLegalTermBitCapLoweringPreparedStateOf_reg5]
  unfold recoveryLegalTermBitCapLoweringHandoffState
  rw [recoveryLegalTermBitCapLoweringHandoffStateOf_reg5]
  unfold recoveryLegalTermBitCapLoweringCoreState
  exact recoveryLegalTermBitCapLoweringCoreStateOf_reg5 _ _ _ _ _ _ _ _ _ _ _

theorem recoveryLegalTermBitCapLoweringPreparedState_reg15
    (inputLength circuitStage : ℕ) :
    (recoveryLegalTermBitCapLoweringPreparedState
      inputLength circuitStage).registers 15 =
        handoffMode
          (recoveryLegalTermBitCapStoredHandoff circuitStage) := by
  unfold recoveryLegalTermBitCapLoweringPreparedState
  rw [recoveryLegalTermBitCapLoweringPreparedStateOf_reg15]
  unfold recoveryLegalTermBitCapLoweringHandoffState
  exact recoveryLegalTermBitCapLoweringHandoffStateOf_reg15 _ _ _ _ _ _ _

theorem recoveryLegalTermBitCapLoweringPreparedState_reg16
    (inputLength circuitStage : ℕ) :
    (recoveryLegalTermBitCapLoweringPreparedState
      inputLength circuitStage).registers 16 =
        handoffLegalLimitsPair
          (recoveryLegalTermBitCapStoredHandoff circuitStage) := by
  simp [recoveryLegalTermBitCapLoweringPreparedState,
    recoveryLegalTermBitCapLoweringPreparedStateOf,
    recoveryLegalTermBitCapLoweringHandoffState,
    handoffLegalLimitsPair, handoffLimitsCode]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in

private theorem run_recoveryLegalTermBitCapLoweringCorePrefix
    (inputLength circuitStage : ℕ) :
    runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
        (recoveryLegalTermBitCapLoweringBits inputLength circuitStage)
        recoveryLegalTermBitCapLoweringFuel
        (initialNPOracleState inputLength circuitStage) =
      runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
        (recoveryLegalTermBitCapLoweringBits inputLength circuitStage) 28
        (recoveryLegalTermBitCapLoweringCoreState
          inputLength circuitStage) := by
  let coefficientStage :=
    recoveryLegalTermBitCapCoefficientStage circuitStage
  let coefficientSummary := (Nat.unpair coefficientStage).1
  let summaryData := (Nat.unpair coefficientSummary).2
  let mappedCode := recoveryLegalTermBitCapMappedCode circuitStage
  let bound := (Nat.unpair coefficientStage).2
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  have hbits :
      ∀ value ∈ recoveryLegalTermBitCapLoweringValues
          inputLength circuitStage,
        natBitLength value ≤
          recoveryLegalTermBitCapLoweringBits inputLength circuitStage := by
    intro value hvalue
    exact recoveryLegalTermBitCapLoweringValue_bits hvalue
  have hcoefficientStage := hbits coefficientStage (by
    simp [recoveryLegalTermBitCapLoweringValues, coefficientStage])
  have hcoefficientSummary := hbits coefficientSummary (by
    simp [recoveryLegalTermBitCapLoweringValues, coefficientStage,
      coefficientSummary])
  have hsummaryData := hbits summaryData (by
    simp [recoveryLegalTermBitCapLoweringValues, coefficientStage,
      coefficientSummary, summaryData])
  have hmapped := hbits mappedCode (by
    simp [recoveryLegalTermBitCapLoweringValues, mappedCode])
  have hbound := hbits bound (by
    simp [recoveryLegalTermBitCapLoweringValues, coefficientStage, bound])
  have harityStage := hbits arityStage (by
    simp [recoveryLegalTermBitCapLoweringValues, coefficientStage, bound,
      arityStage])
  have harityContext := hbits arityContext (by
    simp [recoveryLegalTermBitCapLoweringValues, coefficientStage, bound,
      arityStage, arityContext])
  have hcontext := hbits context (by
    simp [recoveryLegalTermBitCapLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context])
  have hmodeRest := hbits modeRest (by
    simp [recoveryLegalTermBitCapLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest])
  rw [show recoveryLegalTermBitCapLoweringFuel = 36 + 1 by rfl]
  rw [run_unpairRight_instruction (value := coefficientStage)
    (by rfl) rfl
    (by simp [initialNPOracleState, coefficientStage,
      recoveryLegalTermBitCapCoefficientStage])
    hcoefficientStage]
  rw [show (36 : ℕ) = 35 + 1 by omega]
  rw [run_unpairLeft_instruction (value := coefficientSummary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, coefficientStage,
      coefficientSummary])
    hcoefficientSummary]
  rw [show (35 : ℕ) = 34 + 1 by omega]
  rw [run_unpairRight_instruction (value := summaryData)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, coefficientSummary,
      summaryData])
    hsummaryData]
  rw [show (34 : ℕ) = 33 + 1 by omega]
  rw [run_unpairLeft_instruction (value := mappedCode)
    (by rfl) rfl
    (by
      have hmappedShape : (Nat.unpair summaryData).1 = mappedCode := by
        rfl
      simpa only [NPOracleState.write, NPOracleState.jump, if_true] using
        hmappedShape)
    hmapped]
  rw [show (33 : ℕ) = 32 + 1 by omega]
  rw [run_unpairRight_instruction (value := bound)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, coefficientStage,
      bound])
    hbound]
  rw [show (32 : ℕ) = 31 + 1 by omega]
  rw [run_unpairRight_instruction (value := arityStage)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bound, arityStage])
    harityStage]
  rw [show (31 : ℕ) = 30 + 1 by omega]
  rw [run_unpairRight_instruction (value := arityContext)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, arityStage,
      arityContext])
    harityContext]
  rw [show (30 : ℕ) = 29 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, arityContext,
      context])
    hcontext]
  rw [show (29 : ℕ) = 28 + 1 by omega]
  rw [run_unpairRight_instruction (value := modeRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context, modeRest])
    hmodeRest]
  rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in

private theorem run_recoveryLegalTermBitCapLoweringHandoffPrefix
    (inputLength circuitStage : ℕ) :
    runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
        (recoveryLegalTermBitCapLoweringBits inputLength circuitStage) 28
        (recoveryLegalTermBitCapLoweringCoreState
          inputLength circuitStage) =
      runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
        (recoveryLegalTermBitCapLoweringBits inputLength circuitStage) 22
        (recoveryLegalTermBitCapLoweringHandoffState
          inputLength circuitStage) := by
  let coefficientStage :=
    recoveryLegalTermBitCapCoefficientStage circuitStage
  let bound := (Nat.unpair coefficientStage).2
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  let capHandoff := (Nat.unpair expectedRest).2
  let storedHandoff :=
    recoveryLegalTermBitCapStoredHandoff circuitStage
  let mode := handoffMode storedHandoff
  let handoffTail₀ := (Nat.unpair storedHandoff).2
  have hbits :
      ∀ value ∈ recoveryLegalTermBitCapLoweringValues
          inputLength circuitStage,
        natBitLength value ≤
          recoveryLegalTermBitCapLoweringBits inputLength circuitStage := by
    intro value hvalue
    exact recoveryLegalTermBitCapLoweringValue_bits hvalue
  have htermsRest := hbits termsRest (by
    simp [recoveryLegalTermBitCapLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest, termsRest])
  have hexpectedRest := hbits expectedRest (by
    simp [recoveryLegalTermBitCapLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest, termsRest, expectedRest])
  have hcapHandoff := hbits capHandoff (by
    simp [recoveryLegalTermBitCapLoweringValues, coefficientStage, bound,
      arityStage, arityContext, context, modeRest, termsRest, expectedRest,
      capHandoff])
  have hstoredHandoff := hbits storedHandoff (by
    simp [recoveryLegalTermBitCapLoweringValues, storedHandoff])
  have hmode := hbits mode (by
    simp [recoveryLegalTermBitCapLoweringValues, storedHandoff, mode])
  have hhandoffTail₀ := hbits handoffTail₀ (by
    simp [recoveryLegalTermBitCapLoweringValues, storedHandoff,
      handoffTail₀])
  rw [show (28 : ℕ) = 27 + 1 by omega]
  rw [run_unpairRight_instruction (value := termsRest)
    (by rfl) rfl
    (by
      simp [recoveryLegalTermBitCapLoweringCoreState,
        recoveryLegalTermBitCapLoweringCoreStateOf, coefficientStage, bound,
        arityStage, arityContext, context, modeRest, termsRest])
    htermsRest]
  rw [show (27 : ℕ) = 26 + 1 by omega]
  rw [run_unpairRight_instruction (value := expectedRest)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, termsRest,
      expectedRest])
    hexpectedRest]
  rw [show (26 : ℕ) = 25 + 1 by omega]
  rw [run_unpairRight_instruction (value := capHandoff)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, expectedRest,
      capHandoff])
    hcapHandoff]
  rw [show (25 : ℕ) = 24 + 1 by omega]
  rw [run_unpairRight_instruction (value := storedHandoff)
    (by rfl) rfl
    (by
      have hstoredShape : (Nat.unpair capHandoff).2 = storedHandoff := by
        rfl
      simpa only [NPOracleState.write, NPOracleState.jump, if_true] using
        hstoredShape)
    hstoredHandoff]
  rw [show (24 : ℕ) = 23 + 1 by omega]
  rw [run_unpairLeft_instruction (value := mode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, storedHandoff, mode,
      handoffMode])
    hmode]
  rw [show (23 : ℕ) = 22 + 1 by omega]
  rw [run_unpairRight_instruction (value := handoffTail₀)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, storedHandoff,
      handoffTail₀])
    hhandoffTail₀]
  rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in

private theorem run_recoveryLegalTermBitCapLoweringLimitsPrefix
    (inputLength circuitStage : ℕ) :
    runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
        (recoveryLegalTermBitCapLoweringBits inputLength circuitStage) 22
        (recoveryLegalTermBitCapLoweringHandoffState
          inputLength circuitStage) =
      runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
        (recoveryLegalTermBitCapLoweringBits inputLength circuitStage) 16
        (recoveryLegalTermBitCapLoweringPreparedState
          inputLength circuitStage) := by
  let storedHandoff :=
    recoveryLegalTermBitCapStoredHandoff circuitStage
  let handoffTail₀ := (Nat.unpair storedHandoff).2
  let handoffTail₁ := (Nat.unpair handoffTail₀).2
  let handoffTail₂ := (Nat.unpair handoffTail₁).2
  let limitsCode := (Nat.unpair handoffTail₂).2
  let limitsTail₀ := (Nat.unpair limitsCode).2
  let limitsTail₁ := (Nat.unpair limitsTail₀).2
  let legalPair := (Nat.unpair limitsTail₁).2
  have hbits :
      ∀ value ∈ recoveryLegalTermBitCapLoweringValues
          inputLength circuitStage,
        natBitLength value ≤
          recoveryLegalTermBitCapLoweringBits inputLength circuitStage := by
    intro value hvalue
    exact recoveryLegalTermBitCapLoweringValue_bits hvalue
  have hhandoffTail₁ := hbits handoffTail₁ (by
    simp [recoveryLegalTermBitCapLoweringValues, storedHandoff,
      handoffTail₀, handoffTail₁])
  have hhandoffTail₂ := hbits handoffTail₂ (by
    simp [recoveryLegalTermBitCapLoweringValues, storedHandoff,
      handoffTail₀, handoffTail₁, handoffTail₂])
  have hlimitsCode := hbits limitsCode (by
    simp [recoveryLegalTermBitCapLoweringValues, storedHandoff,
      handoffTail₀, handoffTail₁, handoffTail₂, limitsCode])
  have hlimitsTail₀ := hbits limitsTail₀ (by
    simp [recoveryLegalTermBitCapLoweringValues, storedHandoff,
      handoffTail₀, handoffTail₁, handoffTail₂, limitsCode, limitsTail₀])
  have hlimitsTail₁ := hbits limitsTail₁ (by
    simp [recoveryLegalTermBitCapLoweringValues, storedHandoff,
      handoffTail₀, handoffTail₁, handoffTail₂, limitsCode, limitsTail₀,
      limitsTail₁])
  have hlegalPair := hbits legalPair (by
    simp [recoveryLegalTermBitCapLoweringValues, storedHandoff,
      handoffTail₀, handoffTail₁, handoffTail₂, limitsCode, limitsTail₀,
      limitsTail₁, legalPair])
  rw [show (22 : ℕ) = 21 + 1 by omega]
  rw [run_unpairRight_instruction (value := handoffTail₁)
    (by rfl) rfl
    (by
      rw [recoveryLegalTermBitCapLoweringHandoffState_reg16])
    hhandoffTail₁]
  rw [show (21 : ℕ) = 20 + 1 by omega]
  rw [run_unpairRight_instruction (value := handoffTail₂)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, handoffTail₁,
      handoffTail₂])
    hhandoffTail₂]
  rw [show (20 : ℕ) = 19 + 1 by omega]
  rw [run_unpairRight_instruction (value := limitsCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, handoffTail₂,
      limitsCode])
    hlimitsCode]
  rw [show (19 : ℕ) = 18 + 1 by omega]
  rw [run_unpairRight_instruction (value := limitsTail₀)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, limitsCode,
      limitsTail₀])
    hlimitsTail₀]
  rw [show (18 : ℕ) = 17 + 1 by omega]
  rw [run_unpairRight_instruction (value := limitsTail₁)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, limitsTail₀,
      limitsTail₁])
    hlimitsTail₁]
  rw [show (17 : ℕ) = 16 + 1 by omega]
  rw [run_unpairRight_instruction (value := legalPair)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, limitsTail₁,
      legalPair])
    hlegalPair]
  rfl

set_option maxHeartbeats 800000 in
-- The fixed ABI assembly proof normalizes the complete retained handoff tree.
private theorem run_recoveryLegalTermBitCapLoweringAssembly
    (circuitStage selected maximumBits extra : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 29)
    (hselected : state.registers 16 = selected)
    (hmapped :
      state.registers 5 =
        recoveryLegalTermBitCapMappedCode circuitStage)
    (hstage : state.registers 0 = circuitStage)
    (hselectedValue :
      selected =
        handoffSelectedLegalLimits
          (recoveryLegalTermBitCapStoredHandoff circuitStage))
    (htail₀ :
      natBitLength (Nat.unpair selected).2 ≤ maximumBits)
    (htail₁ :
      natBitLength (Nat.unpair (Nat.unpair selected).2).2 ≤ maximumBits)
    (hcap :
      natBitLength
        (Nat.unpair (Nat.unpair (Nat.unpair selected).2).2).1 ≤
          maximumBits)
    (htail₂ :
      natBitLength
        (Nat.unpair (Nat.unpair (Nat.unpair selected).2).2).2 ≤
          maximumBits)
    (hmassCap :
      natBitLength
        (Nat.unpair
          (Nat.unpair (Nat.unpair (Nat.unpair selected).2).2).2).1 ≤
          maximumBits)
    (hrequest :
      natBitLength
        (nativeInputRequest
          (Nat.unpair (Nat.unpair (Nat.unpair selected).2).2).1
          (recoveryLegalTermBitCapMappedCode circuitStage)) ≤ maximumBits)
    (houtput :
      natBitLength (recoveryLegalTermBitCapLoweringOutput circuitStage) ≤
        maximumBits) :
    runNPOracleProgram recoveryLegalTermBitCapLoweringProgram maximumBits
        (extra + 10) state =
      some (recoveryLegalTermBitCapLoweringOutput circuitStage) := by
  let selectedTail₀ := (Nat.unpair selected).2
  let selectedTail₁ := (Nat.unpair selectedTail₀).2
  let selectedTail₂ := (Nat.unpair selectedTail₁).2
  let cap := (Nat.unpair selectedTail₁).1
  let massCap := (Nat.unpair selectedTail₂).1
  let mapped := recoveryLegalTermBitCapMappedCode circuitStage
  let request := nativeInputRequest cap mapped
  let massContext := Nat.pair massCap circuitStage
  let context := Nat.pair mapped massContext
  let output := Nat.pair request context
  have hcapValue : cap = recoveryLegalTermBitCapSelectedCap circuitStage := by
    simp [cap, selectedTail₁, selectedTail₀,
      recoveryLegalTermBitCapSelectedCap, hselectedValue,
      handoffSelectedCoefficientBitCap]
  have hmassCapValue :
      massCap = recoveryLegalTermMassCapCode circuitStage := by
    simp [massCap, selectedTail₂, selectedTail₁, selectedTail₀,
      recoveryLegalTermMassCapCode, hselectedValue,
      handoffSelectedCoefficientMassCapCode]
  have houtputShape :
      output = recoveryLegalTermBitCapLoweringOutput circuitStage := by
    simp [output, request, context, massContext,
      recoveryLegalTermBitCapLoweringOutput,
      recoveryLegalTermBitCapLoweringContext, hcapValue, hmassCapValue,
      mapped]
  have houtput' : natBitLength output ≤ maximumBits := by
    rw [houtputShape]
    exact houtput
  have hcontext : natBitLength context ≤ maximumBits := by
    simpa [output] using
      (natBitLength_mono (Nat.unpair_right_le output)).trans houtput'
  have hmassContext : natBitLength massContext ≤ maximumBits := by
    simpa [context] using
      (natBitLength_mono (Nat.unpair_right_le context)).trans hcontext
  rw [show extra + 10 = (extra + 9) + 1 by omega]
  rw [run_unpairRight_instruction (value := selectedTail₀)
    (by rfl) hpc (by simp [hselected, selectedTail₀]) htail₀]
  rw [show extra + 9 = (extra + 8) + 1 by omega]
  rw [run_unpairRight_instruction (value := selectedTail₁)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, selectedTail₀,
      selectedTail₁]) htail₁]
  rw [show extra + 8 = (extra + 7) + 1 by omega]
  rw [run_unpairLeft_instruction (value := cap)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, selectedTail₁, cap])
    hcap]
  rw [show extra + 7 = (extra + 6) + 1 by omega]
  rw [run_unpairRight_instruction (value := selectedTail₂)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, selectedTail₁,
      selectedTail₂]) htail₂]
  rw [show extra + 6 = (extra + 5) + 1 by omega]
  rw [run_unpairLeft_instruction (value := massCap)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, selectedTail₂,
      massCap]) hmassCap]
  rw [show extra + 5 = (extra + 4) + 1 by omega]
  rw [run_pair_instruction (value := request)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, cap, mapped,
      request, nativeInputRequest, hmapped]) hrequest]
  rw [show extra + 4 = (extra + 3) + 1 by omega]
  rw [run_pair_instruction (value := massContext)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, massContext, massCap,
      hstage]) hmassContext]
  rw [show extra + 3 = (extra + 2) + 1 by omega]
  rw [run_pair_instruction (value := context)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context, massContext,
      mapped, hmapped]) hcontext]
  rw [show extra + 2 = (extra + 1) + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output, request,
      context]) houtput']
  rw [← houtputShape]
  exact run_halt_instruction (fuel := extra) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output]) houtput'

set_option maxHeartbeats 800000 in
-- Four mode branches share one exact assembly trace and fail closed otherwise.
private theorem run_recoveryLegalTermBitCapLoweringSuffix
    (inputLength circuitStage : ℕ) (state : NPOracleState)
    (hpc : state.pc = 21)
    (hmode :
      state.registers 15 =
        handoffMode (recoveryLegalTermBitCapStoredHandoff circuitStage))
    (hlegal :
      state.registers 16 =
        handoffLegalLimitsPair
          (recoveryLegalTermBitCapStoredHandoff circuitStage))
    (hmapped :
      state.registers 5 =
        recoveryLegalTermBitCapMappedCode circuitStage)
    (hstage : state.registers 0 = circuitStage) :
    runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
        (recoveryLegalTermBitCapLoweringBits inputLength circuitStage)
        16 state =
      some (recoveryLegalTermBitCapLoweringOutput circuitStage) := by
  let stored := recoveryLegalTermBitCapStoredHandoff circuitStage
  let mode := handoffMode stored
  let legalPair := handoffLegalLimitsPair stored
  let selected := handoffSelectedLegalLimits stored
  let maximumBits :=
    recoveryLegalTermBitCapLoweringBits inputLength circuitStage
  change state.registers 15 = mode at hmode
  change state.registers 16 = legalPair at hlegal
  have hbits :
      ∀ value ∈
          recoveryLegalTermBitCapLoweringValues inputLength circuitStage,
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact recoveryLegalTermBitCapLoweringValue_bits hvalue
  have hzero : natBitLength 0 ≤ maximumBits := by
    apply hbits 0
    simp [recoveryLegalTermBitCapLoweringValues]
  have hmodeBits : natBitLength mode ≤ maximumBits := by
    simp [maximumBits, recoveryLegalTermBitCapLoweringBits,
      recoveryLegalTermBitCapLoweringSuffixBits, mode, stored]
  have hleftBits :
      natBitLength (Nat.unpair legalPair).1 ≤ maximumBits := by
    simp [maximumBits, recoveryLegalTermBitCapLoweringBits,
      recoveryLegalTermBitCapLoweringSuffixBits, legalPair, stored]
  have hrightBits :
      natBitLength (Nat.unpair legalPair).2 ≤ maximumBits := by
    simp [maximumBits, recoveryLegalTermBitCapLoweringBits,
      recoveryLegalTermBitCapLoweringSuffixBits, legalPair, stored]
  have htail₀ :
      natBitLength (Nat.unpair selected).2 ≤ maximumBits := by
    simp [maximumBits, recoveryLegalTermBitCapLoweringBits,
      recoveryLegalTermBitCapLoweringSuffixBits, selected, stored]
  have htail₂ :
      natBitLength
        (Nat.unpair (Nat.unpair (Nat.unpair selected).2).2).2 ≤
          maximumBits := by
    simp [maximumBits, recoveryLegalTermBitCapLoweringBits,
      recoveryLegalTermBitCapLoweringSuffixBits, selected, stored]
  have hmassCap :
      natBitLength
        (Nat.unpair
          (Nat.unpair (Nat.unpair (Nat.unpair selected).2).2).2).1 ≤
          maximumBits := by
    simp [maximumBits, recoveryLegalTermBitCapLoweringBits,
      recoveryLegalTermBitCapLoweringSuffixBits, selected, stored]
  have htail₁ :
      natBitLength (Nat.unpair (Nat.unpair selected).2).2 ≤
        maximumBits := by
    simp [maximumBits, recoveryLegalTermBitCapLoweringBits,
      recoveryLegalTermBitCapLoweringSuffixBits, selected, stored]
  have hcap :
      natBitLength
        (Nat.unpair (Nat.unpair (Nat.unpair selected).2).2).1 ≤
          maximumBits := by
    simp [maximumBits, recoveryLegalTermBitCapLoweringBits,
      recoveryLegalTermBitCapLoweringSuffixBits, selected, stored]
  have hrequest :
      natBitLength
        (nativeInputRequest
          (Nat.unpair (Nat.unpair (Nat.unpair selected).2).2).1
          (recoveryLegalTermBitCapMappedCode circuitStage)) ≤
            maximumBits := by
    simp [maximumBits, recoveryLegalTermBitCapLoweringBits,
      recoveryLegalTermBitCapLoweringSuffixBits, selected, stored]
  have houtput :
      natBitLength (recoveryLegalTermBitCapLoweringOutput circuitStage) ≤
        maximumBits := by
    simp [maximumBits, recoveryLegalTermBitCapLoweringBits,
      recoveryLegalTermBitCapLoweringSuffixBits]
  have hassembly (extra : ℕ) (selectedValue : ℕ)
      (nextState : NPOracleState)
      (hnextPc : nextState.pc = 29)
      (hnextSelected : nextState.registers 16 = selectedValue)
      (hnextMapped :
        nextState.registers 5 =
          recoveryLegalTermBitCapMappedCode circuitStage)
      (hnextStage : nextState.registers 0 = circuitStage)
      (hselectedValue : selectedValue = selected) :
      runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
          maximumBits (extra + 10) nextState =
        some (recoveryLegalTermBitCapLoweringOutput circuitStage) := by
    apply run_recoveryLegalTermBitCapLoweringAssembly
      circuitStage selectedValue maximumBits extra nextState
    · exact hnextPc
    · exact hnextSelected
    · exact hnextMapped
    · exact hnextStage
    · simpa [selected, stored] using hselectedValue
    · simpa [hselectedValue] using htail₀
    · simpa [hselectedValue] using htail₁
    · simpa [hselectedValue] using hcap
    · simpa [hselectedValue] using htail₂
    · simpa [hselectedValue] using hmassCap
    · simpa [hselectedValue] using hrequest
    · exact houtput
  rw [show (16 : ℕ) = 15 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) hpc]
  by_cases hmodeZero : mode = 0
  · rw [show state.registers 15 = 0 by
      simpa [mode, stored, hmodeZero] using hmode]
    rw [if_pos rfl]
    let state₂₈ := state.jump 28
    rw [show (15 : ℕ) = 14 + 1 by omega]
    rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
    let state₂₉ := (state₂₈.write 16 0).jump 29
    change
      runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
          maximumBits 14 state₂₉ = _
    apply hassembly 4 0 state₂₉
    · rfl
    · rfl
    · simp [state₂₉, state₂₈, hmapped]
    · simp [state₂₉, state₂₈, hstage]
    · simp [selected, stored, handoffSelectedLegalLimits, mode,
        hmodeZero]
  · rw [show state.registers 15 = mode by exact hmode]
    rw [if_neg hmodeZero]
    let state₂₂ := state.jump 22
    rw [show (15 : ℕ) = 14 + 1 by omega]
    rw [run_decrement_instruction (value := mode.pred)
      (by rfl) rfl
      (by
        simp only [NPOracleState.jump]
        rw [hmode])
      ((decrement_bits_le mode).trans hmodeBits)]
    let state₂₃ := (state₂₂.write 15 mode.pred).jump 23
    have hstate₂₃Mapped :
        state₂₃.registers 5 =
          recoveryLegalTermBitCapMappedCode circuitStage := by
      simp only [state₂₃, state₂₂, NPOracleState.write,
        NPOracleState.jump, if_neg (by omega : 5 ≠ 15)]
      exact hmapped
    have hstate₂₃Stage : state₂₃.registers 0 = circuitStage := by
      simp only [state₂₃, state₂₂, NPOracleState.write,
        NPOracleState.jump, if_neg (by omega : 0 ≠ 15)]
      exact hstage
    have hstate₂₃Legal : state₂₃.registers 16 = legalPair := by
      simp only [state₂₃, state₂₂, NPOracleState.write,
        NPOracleState.jump, if_neg (by omega : 16 ≠ 15)]
      exact hlegal
    change
      runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
          maximumBits 14 state₂₃ = _
    rw [show (14 : ℕ) = 13 + 1 by omega]
    rw [run_branchZero_instruction (by rfl) rfl]
    by_cases hmodeOne : mode = 1
    · rw [show state₂₃.registers 15 = 0 by
        simp [state₂₃, hmodeOne]]
      rw [if_pos rfl]
      let state₂₆ := state₂₃.jump 26
      rw [show (13 : ℕ) = 12 + 1 by omega]
      rw [run_unpairLeft_instruction
        (value := (Nat.unpair legalPair).1)
        (by rfl) rfl
        (by
          change
            (Nat.unpair (state₂₃.registers 16)).1 =
              (Nat.unpair legalPair).1
          rw [hstate₂₃Legal])
        hleftBits]
      let state₂₉ :=
        (state₂₆.write 16 (Nat.unpair legalPair).1).jump 29
      change
        runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
          maximumBits 12 state₂₉ = _
      apply hassembly 2 (Nat.unpair legalPair).1 state₂₉
      · rfl
      · simp [state₂₉, NPOracleState.write, NPOracleState.jump]
      · simp only [state₂₉, state₂₆, NPOracleState.write,
          NPOracleState.jump, if_neg (by omega : 5 ≠ 16)]
        exact hstate₂₃Mapped
      · simp only [state₂₉, state₂₆, NPOracleState.write,
          NPOracleState.jump, if_neg (by omega : 0 ≠ 16)]
        exact hstate₂₃Stage
      · change
          (Nat.unpair (handoffLegalLimitsPair stored)).1 =
            handoffSelectedLegalLimits stored
        simp [handoffSelectedLegalLimits, mode, hmodeOne]
    · rw [show state₂₃.registers 15 = mode.pred by simp [state₂₃]]
      have hmodePred : mode.pred ≠ 0 := by
        simp only [Nat.pred_eq_sub_one]
        omega
      rw [if_neg hmodePred]
      let state₂₄ := state₂₃.jump 24
      rw [show (13 : ℕ) = 12 + 1 by omega]
      rw [run_decrement_instruction (value := mode.pred.pred)
        (by rfl) rfl
        (by simp [state₂₃])
        ((decrement_bits_le mode.pred).trans <|
          (decrement_bits_le mode).trans hmodeBits)]
      let state₂₅ := (state₂₄.write 15 mode.pred.pred).jump 25
      have hstate₂₅Mapped :
          state₂₅.registers 5 =
            recoveryLegalTermBitCapMappedCode circuitStage := by
        simp only [state₂₅, state₂₄, NPOracleState.write,
          NPOracleState.jump, if_neg (by omega : 5 ≠ 15)]
        exact hstate₂₃Mapped
      have hstate₂₅Stage : state₂₅.registers 0 = circuitStage := by
        simp only [state₂₅, state₂₄, NPOracleState.write,
          NPOracleState.jump, if_neg (by omega : 0 ≠ 15)]
        exact hstate₂₃Stage
      have hstate₂₅Legal : state₂₅.registers 16 = legalPair := by
        simp only [state₂₅, state₂₄, NPOracleState.write,
          NPOracleState.jump, if_neg (by omega : 16 ≠ 15)]
        exact hstate₂₃Legal
      change
        runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
            maximumBits 12 state₂₅ = _
      rw [show (12 : ℕ) = 11 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      by_cases hmodeTwo : mode = 2
      · rw [show state₂₅.registers 15 = 0 by
          simp [state₂₅, hmodeTwo]]
        rw [if_pos rfl]
        let state₂₇ := state₂₅.jump 27
        rw [show (11 : ℕ) = 10 + 1 by omega]
        rw [run_unpairRight_instruction
          (value := (Nat.unpair legalPair).2)
          (by rfl) rfl
          (by
            change
              (Nat.unpair (state₂₅.registers 16)).2 =
                (Nat.unpair legalPair).2
            rw [hstate₂₅Legal])
          hrightBits]
        let state₂₉ :=
          (state₂₇.write 16 (Nat.unpair legalPair).2).jump 29
        change
          runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
              maximumBits 10 state₂₉ = _
        apply hassembly 0 (Nat.unpair legalPair).2 state₂₉
        · rfl
        · simp only [state₂₉, state₂₇, NPOracleState.write,
            NPOracleState.jump, if_true]
        · simp only [state₂₉, state₂₇, NPOracleState.write,
            NPOracleState.jump, if_neg (by omega : 5 ≠ 16)]
          exact hstate₂₅Mapped
        · simp only [state₂₉, state₂₇, NPOracleState.write,
            NPOracleState.jump, if_neg (by omega : 0 ≠ 16)]
          exact hstate₂₅Stage
        · change
            (Nat.unpair (handoffLegalLimitsPair stored)).2 =
              handoffSelectedLegalLimits stored
          simp [handoffSelectedLegalLimits, mode, hmodeTwo]
      · rw [show state₂₅.registers 15 = mode.pred.pred by
          simp [state₂₅]]
        have hmodePredPred : mode.pred.pred ≠ 0 := by
          simp only [Nat.pred_eq_sub_one]
          omega
        rw [if_neg hmodePredPred]
        let state₂₈ := state₂₅.jump 28
        rw [show (11 : ℕ) = 10 + 1 by omega]
        rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
        let state₂₉ := (state₂₈.write 16 0).jump 29
        change
          runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
              maximumBits 10 state₂₉ = _
        apply hassembly 0 0 state₂₉
        · rfl
        · simp only [state₂₉, state₂₈, NPOracleState.write,
            NPOracleState.jump, if_true]
        · simp only [state₂₉, state₂₈, NPOracleState.write,
            NPOracleState.jump, if_neg (by omega : 5 ≠ 16)]
          exact hstate₂₅Mapped
        · simp only [state₂₉, state₂₈, NPOracleState.write,
            NPOracleState.jump, if_neg (by omega : 0 ≠ 16)]
          exact hstate₂₅Stage
        · change 0 = handoffSelectedLegalLimits stored
          simp [handoffSelectedLegalLimits, mode, hmodeOne, hmodeTwo]

theorem run_recoveryLegalTermBitCapLoweringProgram
    (inputLength circuitStage : ℕ) :
    runNPOracleProgram recoveryLegalTermBitCapLoweringProgram
        (recoveryLegalTermBitCapLoweringBits inputLength circuitStage)
        recoveryLegalTermBitCapLoweringFuel
        (initialNPOracleState inputLength circuitStage) =
      some (recoveryLegalTermBitCapLoweringOutput circuitStage) := by
  rw [run_recoveryLegalTermBitCapLoweringCorePrefix,
    run_recoveryLegalTermBitCapLoweringHandoffPrefix,
    run_recoveryLegalTermBitCapLoweringLimitsPrefix]
  exact run_recoveryLegalTermBitCapLoweringSuffix inputLength circuitStage
    (recoveryLegalTermBitCapLoweringPreparedState inputLength circuitStage)
    (recoveryLegalTermBitCapLoweringPreparedState_pc
      inputLength circuitStage)
    (recoveryLegalTermBitCapLoweringPreparedState_reg15
      inputLength circuitStage)
    (recoveryLegalTermBitCapLoweringPreparedState_reg16
      inputLength circuitStage)
    (recoveryLegalTermBitCapLoweringPreparedState_reg5
      inputLength circuitStage)
    (recoveryLegalTermBitCapLoweringPreparedState_reg0
      inputLength circuitStage)

def recoveryLegalTermBitCapStageOutput (circuitStage : ℕ) : ℕ :=
  Nat.pair
    (recoveryLegalTermCoefficientBitCapListOutput
      (recoveryLegalTermBitCapSelectedCap circuitStage)
      (recoveryLegalTermBitCapMappedCode circuitStage))
    (recoveryLegalTermBitCapLoweringContext circuitStage)

def recoveryLegalTermBitCapStageProgram : NPOracleProgram :=
  preserveRightProgram <|
    nativeCallProgram recoveryLegalTermCoefficientBitCapListProgram

@[simp] theorem recoveryLegalTermBitCapStageProgram_oracleFree :
    OracleFree recoveryLegalTermBitCapStageProgram :=
  preserveRightProgram_oracleFree
    (nativeCallProgram recoveryLegalTermCoefficientBitCapListProgram)
    (nativeCallProgram_oracleFree
      recoveryLegalTermCoefficientBitCapListProgram_oracleFree)

def recoveryLegalTermBitCapStageFuel (circuitStage : ℕ) : ℕ :=
  preserveRightFuel <|
    nativeCallFuel recoveryLegalTermCoefficientBitCapListProgram
      (recoveryLegalTermCoefficientBitCapListFuel
        (recoveryLegalTermBitCapSelectedCap circuitStage)
        (recoveryLegalTermBitCapMappedCode circuitStage))
      (recoveryLegalTermBitCapSelectedCap circuitStage)
      (recoveryLegalTermBitCapMappedCode circuitStage)

def recoveryLegalTermBitCapStageBits
    (inputLength circuitStage : ℕ) : ℕ :=
  let cap := recoveryLegalTermBitCapSelectedCap circuitStage
  let raw := recoveryLegalTermBitCapMappedCode circuitStage
  let output := recoveryLegalTermCoefficientBitCapListOutput cap raw
  preserveRightBits
    (nativeCallBits inputLength cap raw output
      (recoveryLegalTermCoefficientBitCapListBits cap raw))
    (nativeInputRequest cap raw)
    (recoveryLegalTermBitCapLoweringContext circuitStage) output

private theorem run_recoveryLegalTermBitCapStageProgram
    (inputLength circuitStage : ℕ) :
    runNPOracleProgram recoveryLegalTermBitCapStageProgram
        (recoveryLegalTermBitCapStageBits inputLength circuitStage)
        (recoveryLegalTermBitCapStageFuel circuitStage)
        (initialNPOracleState inputLength
          (recoveryLegalTermBitCapLoweringOutput circuitStage)) =
      some (recoveryLegalTermBitCapStageOutput circuitStage) := by
  apply run_preserveRightProgram
    (nativeCallProgram recoveryLegalTermCoefficientBitCapListProgram)
  exact run_nativeCallProgram
    recoveryLegalTermCoefficientBitCapListProgram inputLength
    (recoveryLegalTermBitCapSelectedCap circuitStage)
    (recoveryLegalTermBitCapMappedCode circuitStage)
    (recoveryLegalTermCoefficientBitCapListOutput
      (recoveryLegalTermBitCapSelectedCap circuitStage)
      (recoveryLegalTermBitCapMappedCode circuitStage))
    (recoveryLegalTermCoefficientBitCapListBits
      (recoveryLegalTermBitCapSelectedCap circuitStage)
      (recoveryLegalTermBitCapMappedCode circuitStage))
    (recoveryLegalTermCoefficientBitCapListFuel
      (recoveryLegalTermBitCapSelectedCap circuitStage)
      (recoveryLegalTermBitCapMappedCode circuitStage))
    (run_recoveryLegalTermCoefficientBitCapListProgram
      (recoveryLegalTermBitCapSelectedCap circuitStage)
      (recoveryLegalTermBitCapMappedCode circuitStage))

theorem recoveryLegalTermBitCapMappedCode_circuitStage
    (inputLength handoff : ℕ) :
    recoveryLegalTermBitCapMappedCode
        (recoveryLegalTermCircuitStageOutput inputLength handoff) =
      recoveryLegalTermCoefficientMappedCode inputLength handoff := by
  simp [recoveryLegalTermBitCapMappedCode,
    recoveryLegalTermBitCapCoefficientStage,
    recoveryLegalTermCircuitStageOutput,
    recoveryLegalTermCoefficientStageOutput,
    recoveryLegalTermCoefficientMappedCode]

theorem recoveryLegalTermBitCapStoredHandoff_circuitStage_of_le
    (inputLength handoff : ℕ)
    (hle :
      recoveryLegalSumTermCount handoff ≤
        handoffSelectedTermCap handoff) :
    recoveryLegalTermBitCapStoredHandoff
        (recoveryLegalTermCircuitStageOutput inputLength handoff) =
      handoff := by
  simp [recoveryLegalTermBitCapStoredHandoff,
    recoveryLegalTermBitCapCoefficientStage,
    recoveryLegalTermCircuitStageOutput,
    recoveryLegalTermCoefficientStageOutput,
    recoveryLegalSumBoundOutput, recoveryBoundedContextOutput,
    recoveryLegalSumLengthContext, recoveryLegalSumArityStageOutput,
    recoveryLegalSumArityContext, recoveryLegalSumContext, hle]

theorem recoveryLegalTermBitCapSelectedCap_circuitStage_of_le
    (inputLength handoff : ℕ)
    (hle :
      recoveryLegalSumTermCount handoff ≤
        handoffSelectedTermCap handoff) :
    recoveryLegalTermBitCapSelectedCap
        (recoveryLegalTermCircuitStageOutput inputLength handoff) =
      handoffSelectedCoefficientBitCap handoff := by
  simp [recoveryLegalTermBitCapSelectedCap,
    recoveryLegalTermBitCapStoredHandoff_circuitStage_of_le
      inputLength handoff hle]

/-! ## Exact coefficient-mass validation

The coefficient pass already produced one canonical rational summary per term.
The production path projects those summaries once, folds them with the shared
exact accumulator, and compares cross-products against the selected rational
cap.  No raw coefficient is decoded again. -/

def recoveryLegalTermRationalSummaryProjectionOutput
    (request : ℕ) : ℕ :=
  let validated := (Nat.unpair request).2
  recoveryLegalTermValidatedRationalSummary validated

def recoveryLegalTermRationalSummaryProjectionProgram :
    NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 2 0 2
  , .halt 0
  ]

@[simp] theorem
    recoveryLegalTermRationalSummaryProjectionProgram_oracleFree :
    OracleFree recoveryLegalTermRationalSummaryProjectionProgram := by
  rfl

def recoveryLegalTermRationalSummaryProjectionBits
    (request : ℕ) : ℕ :=
  natBitLength <| max request <|
    max (Nat.unpair request).2 <|
      max (Nat.unpair (Nat.unpair request).2).2
        (recoveryLegalTermRationalSummaryProjectionOutput request)

private theorem run_recoveryLegalTermRationalSummaryProjectionProgram
    (request : ℕ) :
    runNPOracleProgram recoveryLegalTermRationalSummaryProjectionProgram
        (recoveryLegalTermRationalSummaryProjectionBits request) 3
        (initialNPOracleState (Nat.unpair request).1
          (Nat.unpair request).2) =
      some (recoveryLegalTermRationalSummaryProjectionOutput request) := by
  let validated := (Nat.unpair request).2
  let payload := (Nat.unpair validated).2
  let output := (Nat.unpair payload).1
  let maximumBits := recoveryLegalTermRationalSummaryProjectionBits request
  have hrequest : natBitLength request ≤ maximumBits :=
    natBitLength_mono (Nat.le_max_left _ _)
  have hvalidated : natBitLength validated ≤ maximumBits :=
    (natBitLength_mono (Nat.unpair_right_le request)).trans hrequest
  have hpayload : natBitLength payload ≤ maximumBits :=
    (natBitLength_mono (Nat.unpair_right_le validated)).trans hvalidated
  have houtput : natBitLength output ≤ maximumBits :=
    (natBitLength_mono (Nat.unpair_left_le payload)).trans hpayload
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := payload)
    (by rfl) rfl
    (by simp [initialNPOracleState, validated, payload]) hpayload]
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, payload, output])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output]) houtput

def recoveryLegalTermRationalSummaryListProgram : NPOracleProgram :=
  balancedValidationSummaryProgram
    recoveryLegalTermRationalSummaryProjectionProgram

@[simp] theorem
    recoveryLegalTermRationalSummaryListProgram_oracleFree :
    OracleFree recoveryLegalTermRationalSummaryListProgram :=
  balancedValidationSummaryProgram_oracleFree _
    recoveryLegalTermRationalSummaryProjectionProgram_oracleFree

def recoveryLegalTermRationalSummaryListOutput
    (inputLength raw : ℕ) : ℕ :=
  balancedValidationSummaryOutput inputLength raw
    recoveryLegalTermRationalSummaryProjectionOutput

def recoveryLegalTermRationalSummaryListFuel
    (inputLength raw : ℕ) : ℕ :=
  balancedValidationSummaryFuel
    recoveryLegalTermRationalSummaryProjectionProgram
    (fun _ => 3) inputLength raw
    recoveryLegalTermRationalSummaryProjectionOutput

def recoveryLegalTermRationalSummaryListBits
    (inputLength raw : ℕ) : ℕ :=
  balancedValidationSummaryBits
    recoveryLegalTermRationalSummaryProjectionBits
    recoveryLegalTermRationalSummaryProjectionOutput inputLength raw

private theorem run_recoveryLegalTermRationalSummaryListProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram recoveryLegalTermRationalSummaryListProgram
        (recoveryLegalTermRationalSummaryListBits inputLength raw)
        (recoveryLegalTermRationalSummaryListFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (recoveryLegalTermRationalSummaryListOutput inputLength raw) := by
  apply run_balancedValidationSummaryProgram
  intro request _
  exact run_recoveryLegalTermRationalSummaryProjectionProgram request

/-- The shared mass fold owns register `r9`; this fixed entry instruction
installs its canonical `0/1` accumulator before entering the unchanged fold. -/
private def initializedRationalMassFoldProgram : NPOracleProgram :=
  [.set 9 rationalMassInitialAccumulator 1] ++
    rationalMassFoldProgram.map (relocateInstruction 1 0)

private theorem initializedRationalMassFoldProgram_foldAt :
    ProgramRelocatedAt initializedRationalMassFoldProgram
      rationalMassFoldProgram 1 0 := by
  intro pc instruction hlookup
  have hpc : pc < rationalMassFoldProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [initializedRationalMassFoldProgram]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_cons, List.length_nil]
  rw [show 1 + pc - 1 = pc by omega, List.getElem?_map, hlookup]
  rfl

@[simp] private theorem initializedRationalMassFoldProgram_oracleFree :
    OracleFree initializedRationalMassFoldProgram := by
  have hsource : containsSAT rationalMassFoldProgram = false :=
    (oracleFree_iff_containsSAT_false rationalMassFoldProgram).mp
      rationalMassFoldProgram_oracleFree
  rw [oracleFree_iff_containsSAT_false]
  simpa [initializedRationalMassFoldProgram, containsSAT, List.any_map,
    Function.comp_def] using hsource

def initializedRationalMassFoldBits
    (inputLength : ℕ) (summaries : List ℕ) : ℕ :=
  max (natBitLength rationalMassInitialAccumulator)
    (rationalMassFoldBits inputLength summaries)

/-- The shared mass fold's charge, one step past the accumulator installation.
Public so the resource ledger can connect `rationalMassFoldFuel` to the
validator's mass stage without re-deriving the fold's traversal. -/
def initializedRationalMassFoldFuel (summaries : List ℕ) : ℕ :=
  rationalMassFoldFuel summaries + 1

private theorem run_initializedRationalMassFoldProgram
    (inputLength : ℕ) (summaries : List ℕ) :
    runNPOracleProgram initializedRationalMassFoldProgram
        (initializedRationalMassFoldBits inputLength summaries)
        (initializedRationalMassFoldFuel summaries)
        (initialNPOracleState inputLength (encodeBalancedList summaries)) =
      some (rationalMassFold summaries) := by
  let maximumBits := initializedRationalMassFoldBits inputLength summaries
  have haccumulator :
      natBitLength rationalMassInitialAccumulator ≤ maximumBits :=
    Nat.le_max_left _ _
  have hfoldBits :
      rationalMassFoldBits inputLength summaries ≤ maximumBits :=
    Nat.le_max_right _ _
  have hfold := run_bits_mono
    (run_rationalMassFoldProgram inputLength summaries) hfoldBits
  rw [show initializedRationalMassFoldFuel summaries =
      rationalMassFoldFuel summaries + 1 by rfl]
  rw [run_set_instruction
    (program := initializedRationalMassFoldProgram)
    (maximumBits := maximumBits)
    (fuel := rationalMassFoldFuel summaries)
    (pc := 0) (register := 9)
    (value := rationalMassInitialAccumulator) (next := 1)
    (by simp [initializedRationalMassFoldProgram])
    (by rfl) haccumulator]
  have hstate :
      ((initialNPOracleState inputLength (encodeBalancedList summaries)).write
          9 rationalMassInitialAccumulator).jump 1 =
        relocateState 1 0 (fun _ => 0)
          (rationalMassFoldInitialState inputLength summaries) := by
    congr 1
  rw [hstate]
  exact run_relocated (fun _ => 0)
    initializedRationalMassFoldProgram_foldAt hfold

def recoveryLegalTermMassBitFlag (bitCapStage : ℕ) : ℕ :=
  (Nat.unpair bitCapStage).1

def recoveryLegalTermMassLoweringContext (bitCapStage : ℕ) : ℕ :=
  (Nat.unpair bitCapStage).2

def recoveryLegalTermMassMappedCode (bitCapStage : ℕ) : ℕ :=
  (Nat.unpair (recoveryLegalTermMassLoweringContext bitCapStage)).1

def recoveryLegalTermMassCapContext (bitCapStage : ℕ) : ℕ :=
  (Nat.unpair (recoveryLegalTermMassLoweringContext bitCapStage)).2

def recoveryLegalTermMassStageCapCode (bitCapStage : ℕ) : ℕ :=
  (Nat.unpair (recoveryLegalTermMassCapContext bitCapStage)).1

def recoveryLegalTermMassCircuitStage (bitCapStage : ℕ) : ℕ :=
  (Nat.unpair (recoveryLegalTermMassCapContext bitCapStage)).2

/-- Context restored after the mass check.  This is exactly the shape consumed
by the pre-existing bit-cap gate, so no alternate finalization path survives. -/
def recoveryLegalTermMassFinalContext (bitCapStage : ℕ) : ℕ :=
  Nat.pair (recoveryLegalTermMassBitFlag bitCapStage)
    (recoveryLegalTermMassCircuitStage bitCapStage)

def recoveryLegalTermMassSummaryLoweringOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  Nat.pair
    (nativeInputRequest inputLength
      (recoveryLegalTermMassMappedCode bitCapStage)) <|
    Nat.pair (recoveryLegalTermMassStageCapCode bitCapStage)
      (recoveryLegalTermMassFinalContext bitCapStage)

def recoveryLegalTermMassSummaryLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .pair 1 4 8 7
  , .pair 2 7 9 8
  , .pair 6 9 10 9
  , .pair 8 10 0 10
  , .halt 0
  ]

@[simp] theorem
    recoveryLegalTermMassSummaryLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermMassSummaryLoweringProgram := by
  rfl

def recoveryLegalTermMassSummaryLoweringValues
    (inputLength bitCapStage : ℕ) : List ℕ :=
  [ inputLength
  , bitCapStage
  , recoveryLegalTermMassBitFlag bitCapStage
  , recoveryLegalTermMassLoweringContext bitCapStage
  , recoveryLegalTermMassMappedCode bitCapStage
  , recoveryLegalTermMassCapContext bitCapStage
  , recoveryLegalTermMassStageCapCode bitCapStage
  , recoveryLegalTermMassCircuitStage bitCapStage
  , nativeInputRequest inputLength
      (recoveryLegalTermMassMappedCode bitCapStage)
  , recoveryLegalTermMassFinalContext bitCapStage
  , Nat.pair (recoveryLegalTermMassStageCapCode bitCapStage)
      (recoveryLegalTermMassFinalContext bitCapStage)
  , recoveryLegalTermMassSummaryLoweringOutput inputLength bitCapStage
  ]

def recoveryLegalTermMassSummaryLoweringBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermMassSummaryLoweringValues inputLength bitCapStage).foldr
      max 0

private theorem run_recoveryLegalTermMassSummaryLoweringProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassSummaryLoweringProgram
        (recoveryLegalTermMassSummaryLoweringBits inputLength bitCapStage) 11
        (initialNPOracleState inputLength bitCapStage) =
      some (recoveryLegalTermMassSummaryLoweringOutput
        inputLength bitCapStage) := by
  let flag := recoveryLegalTermMassBitFlag bitCapStage
  let loweringContext := recoveryLegalTermMassLoweringContext bitCapStage
  let mapped := recoveryLegalTermMassMappedCode bitCapStage
  let capContext := recoveryLegalTermMassCapContext bitCapStage
  let cap := recoveryLegalTermMassStageCapCode bitCapStage
  let circuitStage := recoveryLegalTermMassCircuitStage bitCapStage
  let request := nativeInputRequest inputLength mapped
  let finalContext := Nat.pair flag circuitStage
  let capFinal := Nat.pair cap finalContext
  let output := Nat.pair request capFinal
  let maximumBits :=
    recoveryLegalTermMassSummaryLoweringBits inputLength bitCapStage
  have hbits :
      ∀ value ∈ recoveryLegalTermMassSummaryLoweringValues
          inputLength bitCapStage,
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact natBitLength_mono (member_le_foldr_max hvalue)
  have hflag := hbits flag (by
    simp [recoveryLegalTermMassSummaryLoweringValues, flag])
  have hloweringContext := hbits loweringContext (by
    simp [recoveryLegalTermMassSummaryLoweringValues, loweringContext])
  have hmapped := hbits mapped (by
    simp [recoveryLegalTermMassSummaryLoweringValues, mapped])
  have hcapContext := hbits capContext (by
    simp [recoveryLegalTermMassSummaryLoweringValues, capContext])
  have hcap := hbits cap (by
    simp [recoveryLegalTermMassSummaryLoweringValues, cap])
  have hcircuit := hbits circuitStage (by
    simp [recoveryLegalTermMassSummaryLoweringValues, circuitStage])
  have hrequest := hbits request (by
    simp [recoveryLegalTermMassSummaryLoweringValues, request, mapped])
  have houtputShape :
      output = recoveryLegalTermMassSummaryLoweringOutput
        inputLength bitCapStage := by
    simp [output, request, capFinal, finalContext, flag, circuitStage,
      cap, mapped, recoveryLegalTermMassSummaryLoweringOutput,
      recoveryLegalTermMassFinalContext]
  have houtput : natBitLength output ≤ maximumBits := by
    rw [houtputShape]
    apply hbits
    simp [recoveryLegalTermMassSummaryLoweringValues]
  have hcapFinal : natBitLength capFinal ≤ maximumBits := by
    simpa [output] using
      (natBitLength_mono (Nat.unpair_right_le output)).trans houtput
  have hfinalContext : natBitLength finalContext ≤ maximumBits := by
    simpa [capFinal] using
      (natBitLength_mono (Nat.unpair_right_le capFinal)).trans hcapFinal
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := flag)
    (by rfl) rfl
    (by simp [initialNPOracleState, flag,
      recoveryLegalTermMassBitFlag]) hflag]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := loweringContext)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump, loweringContext,
      recoveryLegalTermMassLoweringContext]) hloweringContext]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := mapped)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, loweringContext,
      mapped, recoveryLegalTermMassMappedCode]) hmapped]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := capContext)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, loweringContext,
      capContext, recoveryLegalTermMassCapContext]) hcapContext]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := cap)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capContext, cap,
      recoveryLegalTermMassStageCapCode]) hcap]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := circuitStage)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capContext,
      circuitStage, recoveryLegalTermMassCircuitStage]) hcircuit]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := request)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump, request, mapped,
      nativeInputRequest]) hrequest]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := finalContext)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, finalContext,
      flag, circuitStage]) hfinalContext]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := capFinal)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capFinal,
      cap, finalContext]) hcapFinal]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output,
      request, capFinal]) houtput]
  rw [← houtputShape]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output]) houtput

def recoveryLegalTermMassSummaryStageOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  Nat.pair
    (recoveryLegalTermRationalSummaryListOutput inputLength
      (recoveryLegalTermMassMappedCode bitCapStage)) <|
    Nat.pair (recoveryLegalTermMassStageCapCode bitCapStage)
      (recoveryLegalTermMassFinalContext bitCapStage)

def recoveryLegalTermMassSummaryStageProgram : NPOracleProgram :=
  preserveRightProgram <|
    nativeCallProgram recoveryLegalTermRationalSummaryListProgram

@[simp] theorem recoveryLegalTermMassSummaryStageProgram_oracleFree :
    OracleFree recoveryLegalTermMassSummaryStageProgram :=
  preserveRightProgram_oracleFree _ <|
    nativeCallProgram_oracleFree
      recoveryLegalTermRationalSummaryListProgram_oracleFree

def recoveryLegalTermMassSummaryStageFuel
    (inputLength bitCapStage : ℕ) : ℕ :=
  preserveRightFuel <|
    nativeCallFuel recoveryLegalTermRationalSummaryListProgram
      (recoveryLegalTermRationalSummaryListFuel inputLength
        (recoveryLegalTermMassMappedCode bitCapStage))
      inputLength (recoveryLegalTermMassMappedCode bitCapStage)

def recoveryLegalTermMassSummaryStageBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  let raw := recoveryLegalTermMassMappedCode bitCapStage
  let output := recoveryLegalTermRationalSummaryListOutput inputLength raw
  preserveRightBits
    (nativeCallBits inputLength inputLength raw output
      (recoveryLegalTermRationalSummaryListBits inputLength raw))
    (nativeInputRequest inputLength raw)
    (Nat.pair (recoveryLegalTermMassStageCapCode bitCapStage)
      (recoveryLegalTermMassFinalContext bitCapStage)) output

private theorem run_recoveryLegalTermMassSummaryStageProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassSummaryStageProgram
        (recoveryLegalTermMassSummaryStageBits inputLength bitCapStage)
        (recoveryLegalTermMassSummaryStageFuel inputLength bitCapStage)
        (initialNPOracleState inputLength
          (recoveryLegalTermMassSummaryLoweringOutput
            inputLength bitCapStage)) =
      some (recoveryLegalTermMassSummaryStageOutput
        inputLength bitCapStage) := by
  apply run_preserveRightProgram
    (nativeCallProgram recoveryLegalTermRationalSummaryListProgram)
  exact run_nativeCallProgram recoveryLegalTermRationalSummaryListProgram
    inputLength inputLength (recoveryLegalTermMassMappedCode bitCapStage)
    (recoveryLegalTermRationalSummaryListOutput inputLength
      (recoveryLegalTermMassMappedCode bitCapStage))
    (recoveryLegalTermRationalSummaryListBits inputLength
      (recoveryLegalTermMassMappedCode bitCapStage))
    (recoveryLegalTermRationalSummaryListFuel inputLength
      (recoveryLegalTermMassMappedCode bitCapStage))
    (run_recoveryLegalTermRationalSummaryListProgram inputLength
      (recoveryLegalTermMassMappedCode bitCapStage))

def recoveryLegalTermMassSummaryOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  (Nat.unpair
    (recoveryLegalTermMassSummaryStageOutput inputLength bitCapStage)).1

def recoveryLegalTermMassSummaryFlag
    (inputLength bitCapStage : ℕ) : ℕ :=
  (Nat.unpair (recoveryLegalTermMassSummaryOutput
    inputLength bitCapStage)).1

def recoveryLegalTermMassSummaryCode
    (inputLength bitCapStage : ℕ) : ℕ :=
  let summary := recoveryLegalTermMassSummaryOutput inputLength bitCapStage
  if recoveryLegalTermMassSummaryFlag inputLength bitCapStage = 0 then
    encodeBalancedList []
  else
    (Nat.unpair (Nat.unpair summary).2).1

def recoveryLegalTermMassFoldContext
    (inputLength bitCapStage : ℕ) : ℕ :=
  Nat.pair (recoveryLegalTermMassSummaryFlag inputLength bitCapStage)
    (Nat.unpair
      (recoveryLegalTermMassSummaryStageOutput inputLength bitCapStage)).2

def recoveryLegalTermMassFoldLoweringOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  Nat.pair (recoveryLegalTermMassSummaryCode inputLength bitCapStage)
    (recoveryLegalTermMassFoldContext inputLength bitCapStage)

def recoveryLegalTermMassFoldLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .branchZero 4 6 4
  , .unpairRight 2 5 5
  , .unpairLeft 5 6 7
  , .set 6 (encodeBalancedList []) 7
  , .pair 4 3 7 8
  , .pair 6 7 0 9
  , .halt 0
  ]

@[simp] theorem recoveryLegalTermMassFoldLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermMassFoldLoweringProgram := by
  rfl

def recoveryLegalTermMassFoldLoweringValues
    (inputLength bitCapStage : ℕ) : List ℕ :=
  let stage := recoveryLegalTermMassSummaryStageOutput inputLength bitCapStage
  let summary := recoveryLegalTermMassSummaryOutput inputLength bitCapStage
  [ inputLength, stage, summary, (Nat.unpair stage).2
  , recoveryLegalTermMassSummaryFlag inputLength bitCapStage
  , (Nat.unpair summary).2
  , (Nat.unpair (Nat.unpair summary).2).1
  , encodeBalancedList []
  , recoveryLegalTermMassSummaryCode inputLength bitCapStage
  , recoveryLegalTermMassFoldContext inputLength bitCapStage
  , recoveryLegalTermMassFoldLoweringOutput inputLength bitCapStage
  ]

def recoveryLegalTermMassFoldLoweringBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermMassFoldLoweringValues inputLength bitCapStage).foldr
      max 0

private theorem run_recoveryLegalTermMassFoldLoweringProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassFoldLoweringProgram
        (recoveryLegalTermMassFoldLoweringBits inputLength bitCapStage) 9
        (initialNPOracleState inputLength
          (recoveryLegalTermMassSummaryStageOutput
            inputLength bitCapStage)) =
      some (recoveryLegalTermMassFoldLoweringOutput
        inputLength bitCapStage) := by
  let stage := recoveryLegalTermMassSummaryStageOutput inputLength bitCapStage
  let summary := recoveryLegalTermMassSummaryOutput inputLength bitCapStage
  let capFinal := (Nat.unpair stage).2
  let flag := recoveryLegalTermMassSummaryFlag inputLength bitCapStage
  let data := (Nat.unpair summary).2
  let rawCode := (Nat.unpair data).1
  let code := recoveryLegalTermMassSummaryCode inputLength bitCapStage
  let context := Nat.pair flag capFinal
  let output := Nat.pair code context
  let maximumBits :=
    recoveryLegalTermMassFoldLoweringBits inputLength bitCapStage
  have hbits :
      ∀ value ∈ recoveryLegalTermMassFoldLoweringValues
          inputLength bitCapStage,
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact natBitLength_mono (member_le_foldr_max hvalue)
  have hsummary := hbits summary (by
    simp [recoveryLegalTermMassFoldLoweringValues, summary])
  have hcapFinal := hbits capFinal (by
    simp [recoveryLegalTermMassFoldLoweringValues, stage, capFinal])
  have hflag := hbits flag (by
    simp [recoveryLegalTermMassFoldLoweringValues, flag])
  have hdata := hbits data (by
    simp [recoveryLegalTermMassFoldLoweringValues, summary, data])
  have hrawCode := hbits rawCode (by
    simp [recoveryLegalTermMassFoldLoweringValues, summary, data,
      rawCode])
  have hempty := hbits (encodeBalancedList []) (by
    simp [recoveryLegalTermMassFoldLoweringValues])
  have hcode := hbits code (by
    simp [recoveryLegalTermMassFoldLoweringValues, code])
  have hcontext : natBitLength context ≤ maximumBits := by
    have := hbits (recoveryLegalTermMassFoldContext inputLength bitCapStage)
      (by simp [recoveryLegalTermMassFoldLoweringValues])
    simpa [context, recoveryLegalTermMassFoldContext, flag, capFinal, stage]
      using this
  have houtput : natBitLength output ≤ maximumBits := by
    have := hbits
      (recoveryLegalTermMassFoldLoweringOutput inputLength bitCapStage)
      (by simp [recoveryLegalTermMassFoldLoweringValues])
    simpa [output, recoveryLegalTermMassFoldLoweringOutput, context,
      recoveryLegalTermMassFoldContext, code, flag, capFinal, stage] using this
  have houtputShape :
      output = recoveryLegalTermMassFoldLoweringOutput
        inputLength bitCapStage := by
    simp [recoveryLegalTermMassFoldLoweringOutput, output, code, context,
      recoveryLegalTermMassFoldContext, flag, capFinal, stage]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := summary)
    (by rfl) rfl
    (by simp [initialNPOracleState, summary,
      recoveryLegalTermMassSummaryOutput]) hsummary]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := capFinal)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, stage, capFinal]) hcapFinal]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := flag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, summary, flag,
      recoveryLegalTermMassSummaryFlag]) hflag]
  let branchState :=
    (((((initialNPOracleState inputLength stage).write 2 summary).jump 1).write
      3 capFinal).jump 2 |>.write 4 flag).jump 3
  have hbranchFlag : branchState.registers 4 = flag := by
    simp [branchState, NPOracleState.write, NPOracleState.jump]
  have hbranchCapFinal : branchState.registers 3 = capFinal := by
    simp [branchState, NPOracleState.write, NPOracleState.jump]
  rw [show 6 = 5 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  change
    runNPOracleProgram recoveryLegalTermMassFoldLoweringProgram maximumBits 5
      (branchState.jump (if branchState.registers 4 = 0 then 6 else 4)) = _
  rw [hbranchFlag]
  by_cases hzero : flag = 0
  · rw [if_pos hzero]
    rw [show 5 = 4 + 1 by omega]
    rw [run_set_instruction (value := encodeBalancedList [])
      (by rfl) rfl hempty]
    have hcodeEmpty : code = encodeBalancedList [] := by
      simp [code, recoveryLegalTermMassSummaryCode, flag, hzero]
    rw [show 4 = 3 + 1 by omega]
    rw [run_pair_instruction (value := context)
      (by rfl) rfl
      (by simpa [NPOracleState.write, NPOracleState.jump, context] using
        And.intro hbranchFlag hbranchCapFinal) hcontext]
    rw [show 3 = 2 + 1 by omega]
    rw [run_pair_instruction (value := output)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, output, code,
        context, hcodeEmpty]) houtput]
    rw [← houtputShape]
    exact run_halt_instruction (fuel := 1) (value := output)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, output]) houtput
  · rw [if_neg hzero]
    rw [show 5 = 4 + 1 by omega]
    rw [run_unpairRight_instruction (value := data)
      (by rfl) rfl
      (by simp [branchState, initialNPOracleState, NPOracleState.jump,
        summary, data]) hdata]
    rw [show 4 = 3 + 1 by omega]
    rw [run_unpairLeft_instruction (value := rawCode)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, data, rawCode])
      hrawCode]
    have hcodeRaw : code = rawCode := by
      simp [code, recoveryLegalTermMassSummaryCode, flag, hzero, rawCode,
        data, summary]
    rw [show 3 = 2 + 1 by omega]
    rw [run_pair_instruction (value := context)
      (by rfl) rfl
      (by simpa [NPOracleState.write, NPOracleState.jump, context] using
        And.intro hbranchFlag hbranchCapFinal) hcontext]
    rw [show 2 = 1 + 1 by omega]
    rw [run_pair_instruction (value := output)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, output, code,
        context, hcodeRaw]) houtput]
    rw [← houtputShape]
    exact run_halt_instruction (fuel := 0) (value := output)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, output]) houtput

def recoveryLegalTermMassSummaries
    (inputLength bitCapStage : ℕ) : List ℕ :=
  let raw := recoveryLegalTermMassMappedCode bitCapStage
  if balancedValidationAllOutput inputLength raw
      recoveryLegalTermRationalSummaryProjectionOutput = 0 then
    []
  else
    balancedValidationMapOutputs inputLength raw
      recoveryLegalTermRationalSummaryProjectionOutput

theorem recoveryLegalTermMassSummaryCode_eq_encode
    (inputLength bitCapStage : ℕ) :
    recoveryLegalTermMassSummaryCode inputLength bitCapStage =
      encodeBalancedList
        (recoveryLegalTermMassSummaries inputLength bitCapStage) := by
  let raw := recoveryLegalTermMassMappedCode bitCapStage
  by_cases hrejected :
      balancedValidationAllOutput inputLength raw
        recoveryLegalTermRationalSummaryProjectionOutput = 0
  · simp [recoveryLegalTermMassSummaryCode,
      recoveryLegalTermMassSummaryFlag,
      recoveryLegalTermMassSummaryOutput,
      recoveryLegalTermMassSummaryStageOutput,
      recoveryLegalTermRationalSummaryListOutput,
      balancedValidationSummaryOutput, hrejected,
      recoveryLegalTermMassSummaries, raw]
  · simp [recoveryLegalTermMassSummaryCode,
      recoveryLegalTermMassSummaryFlag,
      recoveryLegalTermMassSummaryOutput,
      recoveryLegalTermMassSummaryStageOutput,
      recoveryLegalTermRationalSummaryListOutput,
      balancedValidationSummaryOutput, balancedValidationSummaryData,
      hrejected, recoveryLegalTermMassSummaries, raw]

def recoveryLegalTermMassFoldStageOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  Nat.pair
    (rationalMassFold
      (recoveryLegalTermMassSummaries inputLength bitCapStage))
    (recoveryLegalTermMassFoldContext inputLength bitCapStage)

def recoveryLegalTermMassFoldStageProgram : NPOracleProgram :=
  preserveRightProgram initializedRationalMassFoldProgram

@[simp] theorem recoveryLegalTermMassFoldStageProgram_oracleFree :
    OracleFree recoveryLegalTermMassFoldStageProgram :=
  preserveRightProgram_oracleFree _ initializedRationalMassFoldProgram_oracleFree

def recoveryLegalTermMassFoldStageFuel
    (inputLength bitCapStage : ℕ) : ℕ :=
  preserveRightFuel <|
    initializedRationalMassFoldFuel
      (recoveryLegalTermMassSummaries inputLength bitCapStage)

def recoveryLegalTermMassFoldStageBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  let summaries := recoveryLegalTermMassSummaries inputLength bitCapStage
  preserveRightBits (initializedRationalMassFoldBits inputLength summaries)
    (encodeBalancedList summaries)
    (recoveryLegalTermMassFoldContext inputLength bitCapStage)
    (rationalMassFold summaries)

private theorem run_recoveryLegalTermMassFoldStageProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassFoldStageProgram
        (recoveryLegalTermMassFoldStageBits inputLength bitCapStage)
        (recoveryLegalTermMassFoldStageFuel inputLength bitCapStage)
        (initialNPOracleState inputLength
          (recoveryLegalTermMassFoldLoweringOutput
            inputLength bitCapStage)) =
      some (recoveryLegalTermMassFoldStageOutput
        inputLength bitCapStage) := by
  have hcode := recoveryLegalTermMassSummaryCode_eq_encode
    inputLength bitCapStage
  rw [show recoveryLegalTermMassFoldLoweringOutput inputLength bitCapStage =
      Nat.pair
        (encodeBalancedList
          (recoveryLegalTermMassSummaries inputLength bitCapStage))
        (recoveryLegalTermMassFoldContext inputLength bitCapStage) by
    simp [recoveryLegalTermMassFoldLoweringOutput, hcode]]
  exact run_preserveRightProgram initializedRationalMassFoldProgram
    inputLength
    (initializedRationalMassFoldBits inputLength
      (recoveryLegalTermMassSummaries inputLength bitCapStage))
    (initializedRationalMassFoldFuel
      (recoveryLegalTermMassSummaries inputLength bitCapStage))
    (encodeBalancedList
      (recoveryLegalTermMassSummaries inputLength bitCapStage))
    (recoveryLegalTermMassFoldContext inputLength bitCapStage)
    (rationalMassFold
      (recoveryLegalTermMassSummaries inputLength bitCapStage))
    (run_initializedRationalMassFoldProgram inputLength
      (recoveryLegalTermMassSummaries inputLength bitCapStage))

def recoveryLegalTermMassCapValidationContext
    (inputLength bitCapStage : ℕ) : ℕ :=
  let foldStage := recoveryLegalTermMassFoldStageOutput inputLength bitCapStage
  let fold := (Nat.unpair foldStage).1
  let foldContext := (Nat.unpair foldStage).2
  let summaryFlag := (Nat.unpair foldContext).1
  let capFinal := (Nat.unpair foldContext).2
  let finalContext := (Nat.unpair capFinal).2
  Nat.pair fold (Nat.pair summaryFlag finalContext)

def recoveryLegalTermMassCapLoweringOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  let foldContext := (Nat.unpair
    (recoveryLegalTermMassFoldStageOutput inputLength bitCapStage)).2
  let cap := (Nat.unpair (Nat.unpair foldContext).2).1
  Nat.pair cap
    (recoveryLegalTermMassCapValidationContext inputLength bitCapStage)

def recoveryLegalTermMassCapLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .pair 4 7 8 7
  , .pair 2 8 9 8
  , .pair 6 9 0 9
  , .halt 0
  ]

@[simp] theorem recoveryLegalTermMassCapLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermMassCapLoweringProgram := by
  rfl

def recoveryLegalTermMassCapLoweringValues
    (inputLength bitCapStage : ℕ) : List ℕ :=
  let stage := recoveryLegalTermMassFoldStageOutput inputLength bitCapStage
  let foldContext := (Nat.unpair stage).2
  let capFinal := (Nat.unpair foldContext).2
  [ inputLength, stage, (Nat.unpair stage).1, foldContext
  , (Nat.unpair foldContext).1, capFinal, (Nat.unpair capFinal).1
  , (Nat.unpair capFinal).2
  , Nat.pair (Nat.unpair foldContext).1 (Nat.unpair capFinal).2
  , recoveryLegalTermMassCapValidationContext inputLength bitCapStage
  , recoveryLegalTermMassCapLoweringOutput inputLength bitCapStage
  ]

def recoveryLegalTermMassCapLoweringBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermMassCapLoweringValues inputLength bitCapStage).foldr
      max 0

private theorem run_recoveryLegalTermMassCapLoweringProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassCapLoweringProgram
        (recoveryLegalTermMassCapLoweringBits inputLength bitCapStage) 10
        (initialNPOracleState inputLength
          (recoveryLegalTermMassFoldStageOutput inputLength bitCapStage)) =
      some (recoveryLegalTermMassCapLoweringOutput
        inputLength bitCapStage) := by
  let stage := recoveryLegalTermMassFoldStageOutput inputLength bitCapStage
  let fold := (Nat.unpair stage).1
  let foldContext := (Nat.unpair stage).2
  let summaryFlag := (Nat.unpair foldContext).1
  let capFinal := (Nat.unpair foldContext).2
  let cap := (Nat.unpair capFinal).1
  let finalContext := (Nat.unpair capFinal).2
  let summaryFinal := Nat.pair summaryFlag finalContext
  let context := Nat.pair fold summaryFinal
  let output := Nat.pair cap context
  let maximumBits :=
    recoveryLegalTermMassCapLoweringBits inputLength bitCapStage
  have hbits :
      ∀ value ∈ recoveryLegalTermMassCapLoweringValues
          inputLength bitCapStage,
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact natBitLength_mono (member_le_foldr_max hvalue)
  have hfold := hbits fold (by
    simp [recoveryLegalTermMassCapLoweringValues, stage, fold])
  have hfoldContext := hbits foldContext (by
    simp [recoveryLegalTermMassCapLoweringValues, stage, foldContext])
  have hsummaryFlag := hbits summaryFlag (by
    simp [recoveryLegalTermMassCapLoweringValues, stage, foldContext,
      summaryFlag])
  have hcapFinal := hbits capFinal (by
    simp [recoveryLegalTermMassCapLoweringValues, stage, foldContext,
      capFinal])
  have hcap := hbits cap (by
    simp [recoveryLegalTermMassCapLoweringValues, stage, foldContext,
      capFinal, cap])
  have hfinal := hbits finalContext (by
    simp [recoveryLegalTermMassCapLoweringValues, stage, foldContext,
      capFinal, finalContext])
  have hsummaryFinal := hbits summaryFinal (by
    simp [recoveryLegalTermMassCapLoweringValues, stage, foldContext,
      capFinal, summaryFinal, summaryFlag, finalContext])
  have hcontext := hbits context (by
    simp [recoveryLegalTermMassCapLoweringValues, stage, foldContext,
      capFinal, context, fold, summaryFinal, summaryFlag, finalContext,
      recoveryLegalTermMassCapValidationContext])
  have houtput := hbits output (by
    simp [recoveryLegalTermMassCapLoweringValues, stage, foldContext,
      capFinal, output, cap, context, fold, summaryFinal, summaryFlag,
      finalContext, recoveryLegalTermMassCapValidationContext,
      recoveryLegalTermMassCapLoweringOutput])
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := fold)
    (by rfl) rfl (by simp [initialNPOracleState, stage, fold]) hfold]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := foldContext)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, stage, foldContext]) hfoldContext]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := summaryFlag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, foldContext,
      summaryFlag]) hsummaryFlag]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := capFinal)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, foldContext,
      capFinal]) hcapFinal]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := cap)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capFinal, cap]) hcap]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := finalContext)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capFinal,
      finalContext]) hfinal]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := summaryFinal)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, summaryFinal,
      summaryFlag, finalContext]) hsummaryFinal]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := context)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context, fold,
      summaryFinal]) hcontext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output, cap,
      context]) houtput]
  rw [show recoveryLegalTermMassCapLoweringOutput inputLength bitCapStage =
      output by
    simp [recoveryLegalTermMassCapLoweringOutput,
      recoveryLegalTermMassCapValidationContext, output, context,
      summaryFinal, finalContext, cap, capFinal, summaryFlag, fold,
      foldContext, stage]]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output]) houtput

def recoveryLegalTermMassCapStageOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  let capLowering := recoveryLegalTermMassCapLoweringOutput
    inputLength bitCapStage
  Nat.pair (rationalValidationOutput (Nat.unpair capLowering).1)
    (Nat.unpair capLowering).2

def recoveryLegalTermMassCapStageProgram : NPOracleProgram :=
  preserveRightProgram rationalValidationProgram

@[simp] theorem recoveryLegalTermMassCapStageProgram_oracleFree :
    OracleFree recoveryLegalTermMassCapStageProgram :=
  preserveRightProgram_oracleFree _ rationalValidationProgram_oracleFree

def recoveryLegalTermMassCapStageFuel
    (inputLength bitCapStage : ℕ) : ℕ :=
  let cap := (Nat.unpair
    (recoveryLegalTermMassCapLoweringOutput inputLength bitCapStage)).1
  preserveRightFuel (rationalValidationFuel inputLength cap)

def recoveryLegalTermMassCapStageBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  let lowering := recoveryLegalTermMassCapLoweringOutput inputLength bitCapStage
  let cap := (Nat.unpair lowering).1
  preserveRightBits (rationalValidationBits inputLength cap) cap
    (Nat.unpair lowering).2 (rationalValidationOutput cap)

set_option maxHeartbeats 800000 in
-- `preserveRightProgram` exposes both the rational validator and retained context.
private theorem run_recoveryLegalTermMassCapStageProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassCapStageProgram
        (recoveryLegalTermMassCapStageBits inputLength bitCapStage)
        (recoveryLegalTermMassCapStageFuel inputLength bitCapStage)
        (initialNPOracleState inputLength
          (recoveryLegalTermMassCapLoweringOutput inputLength bitCapStage)) =
      some (recoveryLegalTermMassCapStageOutput
        inputLength bitCapStage) := by
  let lowering := recoveryLegalTermMassCapLoweringOutput
    inputLength bitCapStage
  let cap := (Nat.unpair lowering).1
  let context := (Nat.unpair lowering).2
  have hlowering : lowering = Nat.pair cap context := by
    simp [cap, context]
  rw [show recoveryLegalTermMassCapLoweringOutput inputLength bitCapStage =
      Nat.pair cap context by simpa [lowering] using hlowering]
  have hrun := run_preserveRightProgram rationalValidationProgram inputLength
    (rationalValidationBits inputLength cap)
    (rationalValidationFuel inputLength cap) cap context
    (rationalValidationOutput cap)
    (run_rationalValidationProgram inputLength cap)
  simpa only [recoveryLegalTermMassCapStageProgram,
    recoveryLegalTermMassCapStageBits,
    recoveryLegalTermMassCapStageFuel,
    recoveryLegalTermMassCapStageOutput, Nat.unpair_pair] using hrun

def recoveryLegalTermMassCapSummary
    (inputLength bitCapStage : ℕ) : ℕ :=
  (Nat.unpair
    (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)).1

def recoveryLegalTermMassFoldValue
    (inputLength bitCapStage : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair
    (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)).2).1

def recoveryLegalTermMassLeftProductLoweringOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  let capSummary := recoveryLegalTermMassCapSummary inputLength bitCapStage
  let fold := recoveryLegalTermMassFoldValue inputLength bitCapStage
  Nat.pair
    (bitSerialMulInput (Nat.unpair fold).1
      (rationalSummaryDenominator capSummary))
    (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)

def recoveryLegalTermMassLeftProductLoweringProgram :
    NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 2 5 4
  , .unpairRight 5 6 5
  , .unpairRight 6 7 6
  , .unpairLeft 4 8 7
  , .pair 8 7 9 8
  , .pair 9 0 0 9
  , .halt 0
  ]

@[simp] theorem
    recoveryLegalTermMassLeftProductLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermMassLeftProductLoweringProgram := by
  rfl

def recoveryLegalTermMassLeftProductLoweringValues
    (inputLength bitCapStage : ℕ) : List ℕ :=
  let stage := recoveryLegalTermMassCapStageOutput inputLength bitCapStage
  let capSummary := recoveryLegalTermMassCapSummary inputLength bitCapStage
  let fold := recoveryLegalTermMassFoldValue inputLength bitCapStage
  let capPayload := (Nat.unpair capSummary).2
  let capRational := (Nat.unpair capPayload).2
  [ inputLength, stage, capSummary, (Nat.unpair stage).2, fold, capPayload
  , capRational, rationalSummaryDenominator capSummary
  , (Nat.unpair fold).1
  , bitSerialMulInput (Nat.unpair fold).1
      (rationalSummaryDenominator capSummary)
  , recoveryLegalTermMassLeftProductLoweringOutput inputLength bitCapStage
  ]

def recoveryLegalTermMassLeftProductLoweringBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermMassLeftProductLoweringValues inputLength bitCapStage).foldr
      max 0

private theorem run_recoveryLegalTermMassLeftProductLoweringProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassLeftProductLoweringProgram
        (recoveryLegalTermMassLeftProductLoweringBits inputLength bitCapStage)
        10
        (initialNPOracleState inputLength
          (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)) =
      some (recoveryLegalTermMassLeftProductLoweringOutput
        inputLength bitCapStage) := by
  let stage := recoveryLegalTermMassCapStageOutput inputLength bitCapStage
  let capSummary := recoveryLegalTermMassCapSummary inputLength bitCapStage
  let context := (Nat.unpair stage).2
  let fold := recoveryLegalTermMassFoldValue inputLength bitCapStage
  let capPayload := (Nat.unpair capSummary).2
  let capRational := (Nat.unpair capPayload).2
  let capDenominator := rationalSummaryDenominator capSummary
  let massNumerator := (Nat.unpair fold).1
  let request := bitSerialMulInput massNumerator capDenominator
  let output := Nat.pair request stage
  let maximumBits :=
    recoveryLegalTermMassLeftProductLoweringBits inputLength bitCapStage
  have hbits :
      ∀ value ∈ recoveryLegalTermMassLeftProductLoweringValues
          inputLength bitCapStage,
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact natBitLength_mono (member_le_foldr_max hvalue)
  have hcapSummary := hbits capSummary (by
    simp [recoveryLegalTermMassLeftProductLoweringValues, capSummary])
  have hcontext := hbits context (by
    simp [recoveryLegalTermMassLeftProductLoweringValues, stage, context])
  have hfold := hbits fold (by
    simp [recoveryLegalTermMassLeftProductLoweringValues, fold])
  have hcapPayload := hbits capPayload (by
    simp [recoveryLegalTermMassLeftProductLoweringValues,
      capSummary, capPayload])
  have hcapRational := hbits capRational (by
    simp [recoveryLegalTermMassLeftProductLoweringValues,
      capSummary, capPayload, capRational])
  have hcapDenominator := hbits capDenominator (by
    simp [recoveryLegalTermMassLeftProductLoweringValues,
      capSummary, capDenominator,
      rationalSummaryDenominator])
  have hmassNumerator := hbits massNumerator (by
    simp [recoveryLegalTermMassLeftProductLoweringValues, fold,
      massNumerator])
  have hrequest := hbits request (by
    simp [recoveryLegalTermMassLeftProductLoweringValues, fold,
      capSummary, request, massNumerator, capDenominator])
  have houtput := hbits output (by
    simp [recoveryLegalTermMassLeftProductLoweringValues, stage, fold,
      capSummary, output, request, massNumerator, capDenominator,
      recoveryLegalTermMassLeftProductLoweringOutput])
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := capSummary)
    (by rfl) rfl
    (by simp [initialNPOracleState, capSummary,
      recoveryLegalTermMassCapSummary]) hcapSummary]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, stage, context]) hcontext]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := fold)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context, fold,
      recoveryLegalTermMassFoldValue, stage]) hfold]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := capPayload)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capSummary,
      capPayload]) hcapPayload]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := capRational)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capPayload,
      capRational]) hcapRational]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := capDenominator)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capRational,
      capPayload, capSummary, capDenominator,
      rationalSummaryDenominator]) hcapDenominator]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := massNumerator)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, fold,
      massNumerator]) hmassNumerator]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := request)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, request,
      massNumerator, capDenominator, bitSerialMulInput]) hrequest]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, output, request, stage]) houtput]
  rw [show recoveryLegalTermMassLeftProductLoweringOutput
      inputLength bitCapStage = output by
    simp [recoveryLegalTermMassLeftProductLoweringOutput, output, request,
      massNumerator, capDenominator, fold, capSummary, stage]]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output]) houtput

def recoveryLegalTermMassLeftProductStageOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  let capSummary := recoveryLegalTermMassCapSummary inputLength bitCapStage
  let fold := recoveryLegalTermMassFoldValue inputLength bitCapStage
  Nat.pair ((Nat.unpair fold).1 * rationalSummaryDenominator capSummary)
    (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)

def recoveryLegalTermMassLeftProductStageProgram : NPOracleProgram :=
  preserveRightProgram bitSerialMulProgram

@[simp] theorem
    recoveryLegalTermMassLeftProductStageProgram_oracleFree :
    OracleFree recoveryLegalTermMassLeftProductStageProgram :=
  preserveRightProgram_oracleFree _ bitSerialMulProgram_oracleFree

def recoveryLegalTermMassLeftProductStageFuel
    (inputLength bitCapStage : ℕ) : ℕ :=
  let capSummary := recoveryLegalTermMassCapSummary inputLength bitCapStage
  preserveRightFuel <| bitSerialMulFuel (rationalSummaryDenominator capSummary)

def recoveryLegalTermMassLeftProductStageBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  let capSummary := recoveryLegalTermMassCapSummary inputLength bitCapStage
  let fold := recoveryLegalTermMassFoldValue inputLength bitCapStage
  let left := (Nat.unpair fold).1
  let right := rationalSummaryDenominator capSummary
  preserveRightBits (bitSerialMulBits inputLength left right)
    (bitSerialMulInput left right)
    (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)
    (left * right)

private theorem run_recoveryLegalTermMassLeftProductStageProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassLeftProductStageProgram
        (recoveryLegalTermMassLeftProductStageBits inputLength bitCapStage)
        (recoveryLegalTermMassLeftProductStageFuel inputLength bitCapStage)
        (initialNPOracleState inputLength
          (recoveryLegalTermMassLeftProductLoweringOutput
            inputLength bitCapStage)) =
      some (recoveryLegalTermMassLeftProductStageOutput
        inputLength bitCapStage) := by
  exact run_preserveRightProgram bitSerialMulProgram inputLength
    (bitSerialMulBits inputLength
      (Nat.unpair (recoveryLegalTermMassFoldValue inputLength bitCapStage)).1
      (rationalSummaryDenominator
        (recoveryLegalTermMassCapSummary inputLength bitCapStage)))
    (bitSerialMulFuel (rationalSummaryDenominator
      (recoveryLegalTermMassCapSummary inputLength bitCapStage)))
    (bitSerialMulInput
      (Nat.unpair (recoveryLegalTermMassFoldValue inputLength bitCapStage)).1
      (rationalSummaryDenominator
        (recoveryLegalTermMassCapSummary inputLength bitCapStage)))
    (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)
    ((Nat.unpair (recoveryLegalTermMassFoldValue inputLength bitCapStage)).1 *
      rationalSummaryDenominator
        (recoveryLegalTermMassCapSummary inputLength bitCapStage))
    (run_bitSerialMulProgram inputLength
      (Nat.unpair (recoveryLegalTermMassFoldValue inputLength bitCapStage)).1
      (rationalSummaryDenominator
        (recoveryLegalTermMassCapSummary inputLength bitCapStage)))

def recoveryLegalTermMassLeftProduct
    (inputLength bitCapStage : ℕ) : ℕ :=
  (Nat.unpair
    (recoveryLegalTermMassLeftProductStageOutput inputLength bitCapStage)).1

def recoveryLegalTermMassRightProductLoweringOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  let capSummary := recoveryLegalTermMassCapSummary inputLength bitCapStage
  let fold := recoveryLegalTermMassFoldValue inputLength bitCapStage
  Nat.pair
    (bitSerialMulInput (rationalSummaryMagnitude capSummary)
      (Nat.unpair fold).2) <|
    Nat.pair (recoveryLegalTermMassLeftProduct inputLength bitCapStage)
      (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)

def recoveryLegalTermMassRightProductLoweringProgram :
    NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 4 7 6
  , .unpairRight 7 8 7
  , .unpairLeft 8 9 8
  , .unpairRight 6 10 9
  , .pair 9 10 11 10
  , .pair 2 3 12 11
  , .pair 11 12 0 12
  , .halt 0
  ]

@[simp] theorem
    recoveryLegalTermMassRightProductLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermMassRightProductLoweringProgram := by
  rfl

def recoveryLegalTermMassRightProductLoweringValues
    (inputLength bitCapStage : ℕ) : List ℕ :=
  let leftStage := recoveryLegalTermMassLeftProductStageOutput
    inputLength bitCapStage
  let capStage := (Nat.unpair leftStage).2
  let capSummary := (Nat.unpair capStage).1
  let capPayload := (Nat.unpair capSummary).2
  let capRational := (Nat.unpair capPayload).2
  let capContext := (Nat.unpair capStage).2
  let fold := (Nat.unpair capContext).1
  [ inputLength, leftStage, (Nat.unpair leftStage).1, capStage, capSummary
  , capContext, fold, capPayload, capRational
  , rationalSummaryMagnitude capSummary, (Nat.unpair fold).2
  , bitSerialMulInput (rationalSummaryMagnitude capSummary)
      (Nat.unpair fold).2
  , Nat.pair (Nat.unpair leftStage).1 capStage
  , recoveryLegalTermMassRightProductLoweringOutput inputLength bitCapStage
  ]

def recoveryLegalTermMassRightProductLoweringBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermMassRightProductLoweringValues inputLength bitCapStage).foldr
      max 0

set_option maxHeartbeats 800000 in
-- The straight-line trace reconstructs both exact product operands and context.
private theorem run_recoveryLegalTermMassRightProductLoweringProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassRightProductLoweringProgram
        (recoveryLegalTermMassRightProductLoweringBits inputLength bitCapStage)
        13
        (initialNPOracleState inputLength
          (recoveryLegalTermMassLeftProductStageOutput
            inputLength bitCapStage)) =
      some (recoveryLegalTermMassRightProductLoweringOutput
        inputLength bitCapStage) := by
  let leftStage := recoveryLegalTermMassLeftProductStageOutput
    inputLength bitCapStage
  let leftProduct := (Nat.unpair leftStage).1
  let capStage := (Nat.unpair leftStage).2
  let capSummary := (Nat.unpair capStage).1
  let capContext := (Nat.unpair capStage).2
  let fold := (Nat.unpair capContext).1
  let capPayload := (Nat.unpair capSummary).2
  let capRational := (Nat.unpair capPayload).2
  let capMagnitude := rationalSummaryMagnitude capSummary
  let massDenominator := (Nat.unpair fold).2
  let request := bitSerialMulInput capMagnitude massDenominator
  let retained := Nat.pair leftProduct capStage
  let output := Nat.pair request retained
  let maximumBits :=
    recoveryLegalTermMassRightProductLoweringBits inputLength bitCapStage
  have hbits :
      ∀ value ∈ recoveryLegalTermMassRightProductLoweringValues
          inputLength bitCapStage,
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact natBitLength_mono (member_le_foldr_max hvalue)
  have hleftProduct := hbits leftProduct (by
    simp [recoveryLegalTermMassRightProductLoweringValues, leftStage,
      leftProduct])
  have hcapStage := hbits capStage (by
    simp [recoveryLegalTermMassRightProductLoweringValues, leftStage,
      capStage])
  have hcapSummary := hbits capSummary (by
    simp [recoveryLegalTermMassRightProductLoweringValues, leftStage,
      capStage, capSummary])
  have hcapContext := hbits capContext (by
    simp [recoveryLegalTermMassRightProductLoweringValues, leftStage,
      capStage, capContext])
  have hfold := hbits fold (by
    simp [recoveryLegalTermMassRightProductLoweringValues, leftStage,
      capStage, capContext, fold])
  have hcapPayload := hbits capPayload (by
    simp [recoveryLegalTermMassRightProductLoweringValues, leftStage,
      capStage, capSummary, capPayload])
  have hcapRational := hbits capRational (by
    simp [recoveryLegalTermMassRightProductLoweringValues, leftStage,
      capStage, capSummary, capPayload, capRational])
  have hcapMagnitude := hbits capMagnitude (by
    simp [recoveryLegalTermMassRightProductLoweringValues, leftStage,
      capStage, capSummary, capMagnitude,
      rationalSummaryMagnitude])
  have hmassDenominator := hbits massDenominator (by
    simp [recoveryLegalTermMassRightProductLoweringValues, leftStage,
      capStage, capContext, fold, massDenominator])
  have hrequest := hbits request (by
    simp [recoveryLegalTermMassRightProductLoweringValues, leftStage,
      capStage, capContext, fold, capSummary, request, capMagnitude,
      massDenominator])
  have hretained := hbits retained (by
    simp [recoveryLegalTermMassRightProductLoweringValues, leftStage,
      capStage, retained, leftProduct])
  have hleftStageShape :
      leftStage = Nat.pair leftProduct capStage := by
    exact (Nat.pair_unpair leftStage).symm
  have hleftProductShape :
      leftProduct = recoveryLegalTermMassLeftProduct
        inputLength bitCapStage := by
    rfl
  have hcapStageShape :
      capStage = recoveryLegalTermMassCapStageOutput
        inputLength bitCapStage := by
    simp [capStage, leftStage,
      recoveryLegalTermMassLeftProductStageOutput]
  have hcapSummaryShape :
      capSummary = recoveryLegalTermMassCapSummary
        inputLength bitCapStage := by
    simp [capSummary, hcapStageShape,
      recoveryLegalTermMassCapSummary]
  have hfoldShape :
      fold = recoveryLegalTermMassFoldValue inputLength bitCapStage := by
    simp [fold, capContext, hcapStageShape,
      recoveryLegalTermMassFoldValue]
  have houtputShape :
      output = recoveryLegalTermMassRightProductLoweringOutput
        inputLength bitCapStage := by
    simp [output, request, retained,
      recoveryLegalTermMassRightProductLoweringOutput,
      recoveryLegalTermMassLeftProduct, hleftProductShape, hcapStageShape,
      hcapSummaryShape, hfoldShape, capMagnitude, massDenominator]
  have houtput : natBitLength output ≤ maximumBits := by
    rw [houtputShape]
    apply hbits
    simp [recoveryLegalTermMassRightProductLoweringValues]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := leftProduct)
    (by rfl) rfl
    (by simp [initialNPOracleState, leftStage, leftProduct]) hleftProduct]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction (value := capStage)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, leftStage, capStage]) hcapStage]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := capSummary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capStage,
      capSummary]) hcapSummary]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := capContext)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capStage,
      capContext]) hcapContext]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := fold)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capContext,
      fold]) hfold]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := capPayload)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capSummary,
      capPayload]) hcapPayload]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := capRational)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capPayload,
      capRational]) hcapRational]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := capMagnitude)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capRational,
      capPayload, capSummary, capMagnitude,
      rationalSummaryMagnitude]) hcapMagnitude]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := massDenominator)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, fold,
      massDenominator]) hmassDenominator]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := request)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, request,
      capMagnitude, massDenominator, bitSerialMulInput]) hrequest]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := retained)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, retained,
      leftProduct, capStage]) hretained]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output, request,
      retained]) houtput]
  rw [← houtputShape]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output]) houtput

def recoveryLegalTermMassRightProductStageOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  let capSummary := recoveryLegalTermMassCapSummary inputLength bitCapStage
  let fold := recoveryLegalTermMassFoldValue inputLength bitCapStage
  Nat.pair (rationalSummaryMagnitude capSummary * (Nat.unpair fold).2) <|
    Nat.pair (recoveryLegalTermMassLeftProduct inputLength bitCapStage)
      (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)

def recoveryLegalTermMassRightProductStageProgram : NPOracleProgram :=
  preserveRightProgram bitSerialMulProgram

@[simp] theorem
    recoveryLegalTermMassRightProductStageProgram_oracleFree :
    OracleFree recoveryLegalTermMassRightProductStageProgram :=
  preserveRightProgram_oracleFree _ bitSerialMulProgram_oracleFree

def recoveryLegalTermMassRightProductStageFuel
    (inputLength bitCapStage : ℕ) : ℕ :=
  let fold := recoveryLegalTermMassFoldValue inputLength bitCapStage
  preserveRightFuel (bitSerialMulFuel (Nat.unpair fold).2)

def recoveryLegalTermMassRightProductStageBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  let capSummary := recoveryLegalTermMassCapSummary inputLength bitCapStage
  let fold := recoveryLegalTermMassFoldValue inputLength bitCapStage
  let left := rationalSummaryMagnitude capSummary
  let right := (Nat.unpair fold).2
  let retained := Nat.pair
    (recoveryLegalTermMassLeftProduct inputLength bitCapStage)
    (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)
  preserveRightBits (bitSerialMulBits inputLength left right)
    (bitSerialMulInput left right) retained (left * right)

set_option maxHeartbeats 800000 in
-- Relocated bit-serial multiplication carries a deeply paired retained context.
private theorem run_recoveryLegalTermMassRightProductStageProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassRightProductStageProgram
        (recoveryLegalTermMassRightProductStageBits inputLength bitCapStage)
        (recoveryLegalTermMassRightProductStageFuel inputLength bitCapStage)
        (initialNPOracleState inputLength
          (recoveryLegalTermMassRightProductLoweringOutput
            inputLength bitCapStage)) =
      some (recoveryLegalTermMassRightProductStageOutput
        inputLength bitCapStage) := by
  let capSummary := recoveryLegalTermMassCapSummary inputLength bitCapStage
  let fold := recoveryLegalTermMassFoldValue inputLength bitCapStage
  let left := rationalSummaryMagnitude capSummary
  let right := (Nat.unpair fold).2
  let retained := Nat.pair
    (recoveryLegalTermMassLeftProduct inputLength bitCapStage)
    (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)
  have hrun := run_preserveRightProgram bitSerialMulProgram inputLength
    (bitSerialMulBits inputLength left right)
    (bitSerialMulFuel right) (bitSerialMulInput left right) retained
    (left * right) (run_bitSerialMulProgram inputLength left right)
  simpa [recoveryLegalTermMassRightProductStageProgram,
    recoveryLegalTermMassRightProductStageBits,
    recoveryLegalTermMassRightProductStageFuel,
    recoveryLegalTermMassRightProductLoweringOutput,
    recoveryLegalTermMassRightProductStageOutput,
    capSummary, fold, left, right, retained] using hrun

def recoveryLegalTermMassRightProduct
    (inputLength bitCapStage : ℕ) : ℕ :=
  (Nat.unpair
    (recoveryLegalTermMassRightProductStageOutput inputLength bitCapStage)).1

def recoveryLegalTermMassLeLoweringOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  Nat.pair
    (nativeNatLeInput
      (recoveryLegalTermMassLeftProduct inputLength bitCapStage)
      (recoveryLegalTermMassRightProduct inputLength bitCapStage))
    (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)

def recoveryLegalTermMassLeLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 4 2 6 5
  , .pair 6 5 0 6
  , .halt 0
  ]

@[simp] theorem recoveryLegalTermMassLeLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermMassLeLoweringProgram := by
  rfl

def recoveryLegalTermMassLeLoweringValues
    (inputLength bitCapStage : ℕ) : List ℕ :=
  let stage := recoveryLegalTermMassRightProductStageOutput
    inputLength bitCapStage
  let retained := (Nat.unpair stage).2
  [ inputLength, stage, (Nat.unpair stage).1, retained
  , (Nat.unpair retained).1, (Nat.unpair retained).2
  , nativeNatLeInput (Nat.unpair retained).1 (Nat.unpair stage).1
  , recoveryLegalTermMassLeLoweringOutput inputLength bitCapStage
  ]

def recoveryLegalTermMassLeLoweringBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermMassLeLoweringValues inputLength bitCapStage).foldr max 0

set_option maxRecDepth 4000 in
private theorem run_recoveryLegalTermMassLeLoweringProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassLeLoweringProgram
        (recoveryLegalTermMassLeLoweringBits inputLength bitCapStage) 7
        (initialNPOracleState inputLength
          (recoveryLegalTermMassRightProductStageOutput
            inputLength bitCapStage)) =
      some (recoveryLegalTermMassLeLoweringOutput
        inputLength bitCapStage) := by
  let stage := recoveryLegalTermMassRightProductStageOutput
    inputLength bitCapStage
  let rightProduct := (Nat.unpair stage).1
  let retained := (Nat.unpair stage).2
  let leftProduct := (Nat.unpair retained).1
  let capStage := (Nat.unpair retained).2
  let request := nativeNatLeInput leftProduct rightProduct
  let output := Nat.pair request capStage
  let maximumBits :=
    recoveryLegalTermMassLeLoweringBits inputLength bitCapStage
  have hbits :
      ∀ value ∈ recoveryLegalTermMassLeLoweringValues inputLength bitCapStage,
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact natBitLength_mono (member_le_foldr_max hvalue)
  have hright := hbits rightProduct (by
    simp [recoveryLegalTermMassLeLoweringValues, stage, rightProduct])
  have hretained := hbits retained (by
    simp [recoveryLegalTermMassLeLoweringValues, stage, retained])
  have hleft := hbits leftProduct (by
    simp [recoveryLegalTermMassLeLoweringValues, stage, retained,
      leftProduct])
  have hcapStage := hbits capStage (by
    simp [recoveryLegalTermMassLeLoweringValues, stage, retained,
      capStage])
  have hrequest := hbits request (by
    simp [recoveryLegalTermMassLeLoweringValues, stage, retained,
      request, leftProduct, rightProduct])
  have hstageShape : stage = Nat.pair rightProduct retained :=
    (Nat.pair_unpair stage).symm
  have hretainedShape : retained = Nat.pair leftProduct capStage :=
    (Nat.pair_unpair retained).symm
  have hrightShape :
      rightProduct = recoveryLegalTermMassRightProduct
        inputLength bitCapStage := by
    rfl
  have hretainedExact :
      retained = Nat.pair
        (recoveryLegalTermMassLeftProduct inputLength bitCapStage)
        (recoveryLegalTermMassCapStageOutput inputLength bitCapStage) := by
    simp only [retained, stage,
      recoveryLegalTermMassRightProductStageOutput, Nat.unpair_pair]
  have hleftShape :
      leftProduct = recoveryLegalTermMassLeftProduct
        inputLength bitCapStage := by
    have := congrArg (fun value => (Nat.unpair value).1) hretainedExact
    simpa only [leftProduct, Nat.unpair_pair] using this
  have hcapStageShape :
      capStage = recoveryLegalTermMassCapStageOutput
        inputLength bitCapStage := by
    have := congrArg (fun value => (Nat.unpair value).2) hretainedExact
    simpa only [capStage, Nat.unpair_pair] using this
  have houtputShape :
      output = recoveryLegalTermMassLeLoweringOutput
        inputLength bitCapStage := by
    simp [output, request, recoveryLegalTermMassLeLoweringOutput,
      recoveryLegalTermMassLeftProduct, recoveryLegalTermMassRightProduct,
      hrightShape, hleftShape, hcapStageShape]
  have houtput : natBitLength output ≤ maximumBits := by
    rw [houtputShape]
    apply hbits
    simp [recoveryLegalTermMassLeLoweringValues]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := rightProduct)
    (by rfl) rfl
    (by simp [initialNPOracleState, stage, rightProduct]) hright]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := retained)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, stage, retained]) hretained]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := leftProduct)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, retained,
      leftProduct]) hleft]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := capStage)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, retained,
      capStage]) hcapStage]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := request)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, request,
      leftProduct, rightProduct, nativeNatLeInput]) hrequest]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output, request,
      capStage]) houtput]
  rw [← houtputShape]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output]) houtput

def recoveryLegalTermMassLeStageOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  Nat.pair
    (nativeNatLeOutput
      (recoveryLegalTermMassLeftProduct inputLength bitCapStage)
      (recoveryLegalTermMassRightProduct inputLength bitCapStage))
    (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)

def recoveryLegalTermMassLeStageProgram : NPOracleProgram :=
  preserveRightProgram nativeNatLeProgram

@[simp] theorem recoveryLegalTermMassLeStageProgram_oracleFree :
    OracleFree recoveryLegalTermMassLeStageProgram :=
  preserveRightProgram_oracleFree _ nativeNatLeProgram_oracleFree

def recoveryLegalTermMassLeStageFuel
    (inputLength bitCapStage : ℕ) : ℕ :=
  preserveRightFuel <| nativeNatLeFuel
    (recoveryLegalTermMassLeftProduct inputLength bitCapStage)
    (recoveryLegalTermMassRightProduct inputLength bitCapStage)

def recoveryLegalTermMassLeStageBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  let left := recoveryLegalTermMassLeftProduct inputLength bitCapStage
  let right := recoveryLegalTermMassRightProduct inputLength bitCapStage
  preserveRightBits (nativeNatLeBits left right)
    (nativeNatLeInput left right)
    (recoveryLegalTermMassCapStageOutput inputLength bitCapStage)
    (nativeNatLeOutput left right)

set_option maxHeartbeats 800000 in
-- The preserved native comparison proof normalizes both verified product stages.
private theorem run_recoveryLegalTermMassLeStageProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassLeStageProgram
        (recoveryLegalTermMassLeStageBits inputLength bitCapStage)
        (recoveryLegalTermMassLeStageFuel inputLength bitCapStage)
        (initialNPOracleState inputLength
          (recoveryLegalTermMassLeLoweringOutput inputLength bitCapStage)) =
      some (recoveryLegalTermMassLeStageOutput inputLength bitCapStage) := by
  let left := recoveryLegalTermMassLeftProduct inputLength bitCapStage
  let right := recoveryLegalTermMassRightProduct inputLength bitCapStage
  let context := recoveryLegalTermMassCapStageOutput inputLength bitCapStage
  have hrun := run_preserveRightProgram nativeNatLeProgram inputLength
    (nativeNatLeBits left right) (nativeNatLeFuel left right)
    (nativeNatLeInput left right) context (nativeNatLeOutput left right)
    (run_nativeNatLeProgram inputLength left right)
  simpa [recoveryLegalTermMassLeStageProgram,
    recoveryLegalTermMassLeStageBits, recoveryLegalTermMassLeStageFuel,
    recoveryLegalTermMassLeLoweringOutput,
    recoveryLegalTermMassLeStageOutput, left, right, context] using hrun

def recoveryLegalTermMassAccepts
    (inputLength bitCapStage : ℕ) : Prop :=
  let leStage := recoveryLegalTermMassLeStageOutput inputLength bitCapStage
  let capStage := (Nat.unpair leStage).2
  let capSummary := (Nat.unpair capStage).1
  let capContext := (Nat.unpair capStage).2
  let fold := (Nat.unpair capContext).1
  let summaryFinal := (Nat.unpair capContext).2
  (Nat.unpair leStage).1 ≠ 0 ∧
    rationalSummaryFlag capSummary ≠ 0 ∧
    rationalSummarySign capSummary = 0 ∧
    (Nat.unpair fold).2 ≠ 0 ∧
    (Nat.unpair summaryFinal).1 ≠ 0

private instance (inputLength bitCapStage : ℕ) :
    Decidable (recoveryLegalTermMassAccepts inputLength bitCapStage) := by
  unfold recoveryLegalTermMassAccepts
  infer_instance

/-- Exact, cross-multiplied coefficient-mass comparison used by the recovery
validator.  The validated cap and nonzero denominators make this equivalent to
comparing the rational coefficient mass with the selected rational cap. -/
def recoveryLegalTermCoefficientMassWithinCap
    (inputLength handoff : ℕ) : Prop :=
  let bitCapStage := recoveryLegalTermBitCapStageOutput
    (recoveryLegalTermCircuitStageOutput inputLength handoff)
  let capSummary := recoveryLegalTermMassCapSummary inputLength bitCapStage
  let fold := recoveryLegalTermMassFoldValue inputLength bitCapStage
  (Nat.unpair fold).1 * rationalSummaryDenominator capSummary ≤
      rationalSummaryMagnitude capSummary * (Nat.unpair fold).2 ∧
    rationalSummaryFlag capSummary ≠ 0 ∧
    rationalSummarySign capSummary = 0 ∧
    (Nat.unpair fold).2 ≠ 0 ∧
    recoveryLegalTermMassSummaryFlag inputLength bitCapStage ≠ 0

/-- Exact rational value accumulated from the canonical coefficient summaries. -/
def recoveryLegalTermCoefficientMass (inputLength handoff : ℕ) : ℚ :=
  let bitCapStage := recoveryLegalTermBitCapStageOutput
    (recoveryLegalTermCircuitStageOutput inputLength handoff)
  rationalMassValue (recoveryLegalTermMassFoldValue inputLength bitCapStage)

/-- Typed correspondence premise for a decoded legal circuit sum.  Keeping this
as one named boundary prevents downstream proofs from reinterpreting the codec. -/
def recoveryLegalTermMassSummariesRepresent
    {Circuit : CanonicalWitnessCodec.CircuitFamily} (inputLength handoff : ℕ)
    (description : LegalCircuitSumDescription Circuit) : Prop :=
  let bitCapStage := recoveryLegalTermBitCapStageOutput
    (recoveryLegalTermCircuitStageOutput inputLength handoff)
  recoveryLegalTermMassSummaries inputLength bitCapStage =
    description.terms.map fun term =>
      canonicalRationalSummary term.coefficient

theorem recoveryLegalTermCoefficientMass_eq_legalCircuitSum
    {Circuit : CanonicalWitnessCodec.CircuitFamily} (inputLength handoff : ℕ)
    (description : LegalCircuitSumDescription Circuit)
    (hrepresent :
      recoveryLegalTermMassSummariesRepresent inputLength handoff description) :
    recoveryLegalTermCoefficientMass inputLength handoff =
      description.coefficientMass := by
  let bitCapStage := recoveryLegalTermBitCapStageOutput
    (recoveryLegalTermCircuitStageOutput inputLength handoff)
  have hsummaries :
      recoveryLegalTermMassSummaries inputLength bitCapStage =
        description.terms.map fun term =>
          canonicalRationalSummary term.coefficient := by
    simpa [recoveryLegalTermMassSummariesRepresent, bitCapStage] using hrepresent
  have hfold :
      recoveryLegalTermMassFoldValue inputLength bitCapStage =
        rationalMassFold
          (recoveryLegalTermMassSummaries inputLength bitCapStage) := by
    simp [recoveryLegalTermMassFoldValue,
      recoveryLegalTermMassCapStageOutput,
      recoveryLegalTermMassCapLoweringOutput,
      recoveryLegalTermMassCapValidationContext,
      recoveryLegalTermMassFoldStageOutput]
  rw [recoveryLegalTermCoefficientMass, show
    recoveryLegalTermBitCapStageOutput
        (recoveryLegalTermCircuitStageOutput inputLength handoff) =
      bitCapStage by rfl, hfold, hsummaries]
  exact rationalMassFold_legalCircuitSum_coefficientMass description

set_option maxHeartbeats 800000 in
-- This bridge normalizes the executable stages to their exact arithmetic contract.
theorem recoveryLegalTermMassAccepts_iff_coefficientMassWithinCap
    (inputLength handoff : ℕ) :
    recoveryLegalTermMassAccepts inputLength
        (recoveryLegalTermBitCapStageOutput
          (recoveryLegalTermCircuitStageOutput inputLength handoff)) ↔
      recoveryLegalTermCoefficientMassWithinCap inputLength handoff := by
  simp [recoveryLegalTermCoefficientMassWithinCap,
    recoveryLegalTermMassAccepts, recoveryLegalTermMassLeStageOutput,
    recoveryLegalTermMassLeftProduct, recoveryLegalTermMassRightProduct,
    recoveryLegalTermMassLeftProductStageOutput,
    recoveryLegalTermMassRightProductStageOutput,
    recoveryLegalTermMassCapSummary, recoveryLegalTermMassFoldValue,
    recoveryLegalTermMassCapStageOutput,
    recoveryLegalTermMassCapLoweringOutput,
    recoveryLegalTermMassCapValidationContext,
    recoveryLegalTermMassFoldStageOutput,
    recoveryLegalTermMassFoldContext, nativeNatLeOutput_eq]

def recoveryLegalTermMassBranchFlag
    (leFlag capFlag capSign massDenominator summaryFlag : ℕ) : ℕ :=
  if leFlag ≠ 0 ∧ capFlag ≠ 0 ∧ capSign = 0 ∧
      massDenominator ≠ 0 ∧ summaryFlag ≠ 0 then 1 else 0

def recoveryLegalTermMassComparisonFlag
    (inputLength bitCapStage : ℕ) : ℕ :=
  let leStage := recoveryLegalTermMassLeStageOutput inputLength bitCapStage
  let capStage := (Nat.unpair leStage).2
  let capSummary := (Nat.unpair capStage).1
  let capContext := (Nat.unpair capStage).2
  let fold := (Nat.unpair capContext).1
  let summaryFinal := (Nat.unpair capContext).2
  recoveryLegalTermMassBranchFlag (Nat.unpair leStage).1
    (rationalSummaryFlag capSummary) (rationalSummarySign capSummary)
    (Nat.unpair fold).2 (Nat.unpair summaryFinal).1

def recoveryLegalTermMassComparisonOutput
    (inputLength bitCapStage : ℕ) : ℕ :=
  let leStage := recoveryLegalTermMassLeStageOutput inputLength bitCapStage
  let capContext := (Nat.unpair (Nat.unpair leStage).2).2
  let finalContext := (Nat.unpair (Nat.unpair capContext).2).2
  Nat.pair (recoveryLegalTermMassComparisonFlag inputLength bitCapStage)
    finalContext

def recoveryLegalTermMassComparisonProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .unpairLeft 4 10 9
  , .unpairRight 4 11 10
  , .unpairLeft 11 12 11
  , .unpairRight 6 13 12
  , .branchZero 2 18 13
  , .branchZero 10 18 14
  , .branchZero 13 18 15
  , .branchZero 8 18 16
  , .branchZero 12 17 18
  , .set 14 1 19
  , .set 14 0 19
  , .pair 14 9 0 20
  , .halt 0
  ]

@[simp] theorem recoveryLegalTermMassComparisonProgram_oracleFree :
    OracleFree recoveryLegalTermMassComparisonProgram := by
  rfl

def recoveryLegalTermMassComparisonValues
    (inputLength bitCapStage : ℕ) : List ℕ :=
  let stage := recoveryLegalTermMassLeStageOutput inputLength bitCapStage
  let capStage := (Nat.unpair stage).2
  let capSummary := (Nat.unpair capStage).1
  let capContext := (Nat.unpair capStage).2
  let fold := (Nat.unpair capContext).1
  let summaryFinal := (Nat.unpair capContext).2
  [ inputLength, stage, (Nat.unpair stage).1, capStage, capSummary, capContext
  , fold, summaryFinal, (Nat.unpair summaryFinal).1
  , (Nat.unpair summaryFinal).2, rationalSummaryFlag capSummary
  , (Nat.unpair capSummary).2, rationalSummarySign capSummary
  , (Nat.unpair fold).2, 0, 1
  , Nat.pair 0 (Nat.unpair summaryFinal).2
  , Nat.pair 1 (Nat.unpair summaryFinal).2
  , recoveryLegalTermMassComparisonFlag inputLength bitCapStage
  , recoveryLegalTermMassComparisonOutput inputLength bitCapStage
  ]

def recoveryLegalTermMassComparisonBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  let stage := recoveryLegalTermMassLeStageOutput inputLength bitCapStage
  let capContext := (Nat.unpair (Nat.unpair stage).2).2
  let finalContext := (Nat.unpair (Nat.unpair capContext).2).2
  max (natBitLength (Nat.pair 0 finalContext)) <|
    max (natBitLength (Nat.pair 1 finalContext)) <|
      natBitLength <|
        (recoveryLegalTermMassComparisonValues inputLength bitCapStage).foldr
          max 0

def recoveryLegalTermMassComparisonCheckedState
    (inputLength bitCapStage : ℕ) : NPOracleState :=
  let stage := recoveryLegalTermMassLeStageOutput inputLength bitCapStage
  let leFlag := (Nat.unpair stage).1
  let capStage := (Nat.unpair stage).2
  let capSummary := (Nat.unpair capStage).1
  let capContext := (Nat.unpair capStage).2
  let fold := (Nat.unpair capContext).1
  let summaryFinal := (Nat.unpair capContext).2
  let state₁ := ((initialNPOracleState inputLength stage).write 2 leFlag).jump 1
  let state₂ := (state₁.write 3 capStage).jump 2
  let state₃ := (state₂.write 4 capSummary).jump 3
  let state₄ := (state₃.write 5 capContext).jump 4
  let state₅ := (state₄.write 6 fold).jump 5
  let state₆ := (state₅.write 7 summaryFinal).jump 6
  let state₇ := (state₆.write 8 (Nat.unpair summaryFinal).1).jump 7
  let state₈ := (state₇.write 9 (Nat.unpair summaryFinal).2).jump 8
  let state₉ := (state₈.write 10 (rationalSummaryFlag capSummary)).jump 9
  let state₁₀ := (state₉.write 11 (Nat.unpair capSummary).2).jump 10
  let state₁₁ := (state₁₀.write 12 (rationalSummarySign capSummary)).jump 11
  (state₁₁.write 13 (Nat.unpair fold).2).jump 12

@[simp] theorem recoveryLegalTermMassComparisonCheckedState_pc
    (inputLength bitCapStage : ℕ) :
    (recoveryLegalTermMassComparisonCheckedState
      inputLength bitCapStage).pc = 12 := by
  simp only [recoveryLegalTermMassComparisonCheckedState,
    NPOracleState.write, NPOracleState.jump]

@[simp] theorem recoveryLegalTermMassComparisonCheckedState_reg2
    (inputLength bitCapStage : ℕ) :
    (recoveryLegalTermMassComparisonCheckedState
      inputLength bitCapStage).registers 2 =
      (Nat.unpair
        (recoveryLegalTermMassLeStageOutput inputLength bitCapStage)).1 := by
  simp only [recoveryLegalTermMassComparisonCheckedState,
    initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  simp

@[simp] theorem recoveryLegalTermMassComparisonCheckedState_reg10
    (inputLength bitCapStage : ℕ) :
    (recoveryLegalTermMassComparisonCheckedState
      inputLength bitCapStage).registers 10 =
      rationalSummaryFlag
        (Nat.unpair (Nat.unpair
          (recoveryLegalTermMassLeStageOutput inputLength bitCapStage)).2).1 := by
  simp only [recoveryLegalTermMassComparisonCheckedState,
    initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  simp

@[simp] theorem recoveryLegalTermMassComparisonCheckedState_reg13
    (inputLength bitCapStage : ℕ) :
    (recoveryLegalTermMassComparisonCheckedState
      inputLength bitCapStage).registers 13 =
      (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair
        (recoveryLegalTermMassLeStageOutput inputLength bitCapStage)).2).2).1).2 := by
  simp only [recoveryLegalTermMassComparisonCheckedState,
    initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  simp

@[simp] theorem recoveryLegalTermMassComparisonCheckedState_reg8
    (inputLength bitCapStage : ℕ) :
    (recoveryLegalTermMassComparisonCheckedState
      inputLength bitCapStage).registers 8 =
      (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair
        (recoveryLegalTermMassLeStageOutput inputLength bitCapStage)).2).2).2).1 := by
  simp only [recoveryLegalTermMassComparisonCheckedState,
    initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  simp

@[simp] theorem recoveryLegalTermMassComparisonCheckedState_reg12
    (inputLength bitCapStage : ℕ) :
    (recoveryLegalTermMassComparisonCheckedState
      inputLength bitCapStage).registers 12 =
      rationalSummarySign
        (Nat.unpair (Nat.unpair
          (recoveryLegalTermMassLeStageOutput inputLength bitCapStage)).2).1 := by
  simp only [recoveryLegalTermMassComparisonCheckedState,
    initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  simp

@[simp] theorem recoveryLegalTermMassComparisonCheckedState_reg9
    (inputLength bitCapStage : ℕ) :
    (recoveryLegalTermMassComparisonCheckedState
      inputLength bitCapStage).registers 9 =
      (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair
        (recoveryLegalTermMassLeStageOutput inputLength bitCapStage)).2).2).2).2 := by
  simp only [recoveryLegalTermMassComparisonCheckedState,
    initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  simp

set_option maxRecDepth 4000 in
private theorem run_recoveryLegalTermMassComparisonParser
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassComparisonProgram
        (recoveryLegalTermMassComparisonBits inputLength bitCapStage) 21
        (initialNPOracleState inputLength
          (recoveryLegalTermMassLeStageOutput inputLength bitCapStage)) =
      runNPOracleProgram recoveryLegalTermMassComparisonProgram
        (recoveryLegalTermMassComparisonBits inputLength bitCapStage) 9
        (recoveryLegalTermMassComparisonCheckedState
          inputLength bitCapStage) := by
  let stage := recoveryLegalTermMassLeStageOutput inputLength bitCapStage
  let leFlag := (Nat.unpair stage).1
  let capStage := (Nat.unpair stage).2
  let capSummary := (Nat.unpair capStage).1
  let capContext := (Nat.unpair capStage).2
  let fold := (Nat.unpair capContext).1
  let summaryFinal := (Nat.unpair capContext).2
  let summaryFlag := (Nat.unpair summaryFinal).1
  let finalContext := (Nat.unpair summaryFinal).2
  let capFlag := rationalSummaryFlag capSummary
  let capPayload := (Nat.unpair capSummary).2
  let capSign := rationalSummarySign capSummary
  let massDenominator := (Nat.unpair fold).2
  let maximumBits :=
    recoveryLegalTermMassComparisonBits inputLength bitCapStage
  have hbits :
      ∀ value ∈ recoveryLegalTermMassComparisonValues inputLength bitCapStage,
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact (natBitLength_mono (member_le_foldr_max hvalue)).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hle := hbits leFlag (by
    simp [recoveryLegalTermMassComparisonValues, stage, leFlag])
  have hcapStage := hbits capStage (by
    simp [recoveryLegalTermMassComparisonValues, stage, capStage])
  have hcapSummary := hbits capSummary (by
    simp [recoveryLegalTermMassComparisonValues, stage, capStage,
      capSummary])
  have hcapContext := hbits capContext (by
    simp [recoveryLegalTermMassComparisonValues, stage, capStage,
      capContext])
  have hfold := hbits fold (by
    simp [recoveryLegalTermMassComparisonValues, stage, capStage,
      capContext, fold])
  have hsummaryFinal := hbits summaryFinal (by
    simp [recoveryLegalTermMassComparisonValues, stage, capStage,
      capContext, summaryFinal])
  have hsummaryFlag := hbits summaryFlag (by
    simp [recoveryLegalTermMassComparisonValues, stage, capStage,
      capContext, summaryFinal, summaryFlag])
  have hfinal := hbits finalContext (by
    simp [recoveryLegalTermMassComparisonValues, stage, capStage,
      capContext, summaryFinal, finalContext])
  have hcapFlag := hbits capFlag (by
    simp [recoveryLegalTermMassComparisonValues, stage, capStage,
      capSummary, capFlag, rationalSummaryFlag])
  have hcapPayload := hbits capPayload (by
    simp [recoveryLegalTermMassComparisonValues, stage, capStage,
      capSummary, capPayload])
  have hcapSign := hbits capSign (by
    simp [recoveryLegalTermMassComparisonValues, stage, capStage,
      capSummary, capSign, rationalSummarySign])
  have hmassDenominator := hbits massDenominator (by
    simp [recoveryLegalTermMassComparisonValues, stage, capStage,
      capContext, fold, massDenominator])
  rw [show 21 = 20 + 1 by omega]
  rw [run_unpairLeft_instruction (value := leFlag)
    (by rfl) rfl (by simp [initialNPOracleState, stage, leFlag]) hle]
  rw [show 20 = 19 + 1 by omega]
  rw [run_unpairRight_instruction (value := capStage)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, stage, capStage]) hcapStage]
  rw [show 19 = 18 + 1 by omega]
  rw [run_unpairLeft_instruction (value := capSummary)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capStage,
      capSummary]) hcapSummary]
  rw [show 18 = 17 + 1 by omega]
  rw [run_unpairRight_instruction (value := capContext)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capStage,
      capContext]) hcapContext]
  rw [show 17 = 16 + 1 by omega]
  rw [run_unpairLeft_instruction (value := fold)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capContext,
      fold]) hfold]
  rw [show 16 = 15 + 1 by omega]
  rw [run_unpairRight_instruction (value := summaryFinal)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capContext,
      summaryFinal]) hsummaryFinal]
  rw [show 15 = 14 + 1 by omega]
  rw [run_unpairLeft_instruction (value := summaryFlag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, summaryFinal,
      summaryFlag]) hsummaryFlag]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairRight_instruction (value := finalContext)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, summaryFinal,
      finalContext]) hfinal]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := capFlag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capSummary, capFlag,
      rationalSummaryFlag]) hcapFlag]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction (value := capPayload)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capSummary,
      capPayload]) hcapPayload]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := capSign)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, capPayload,
      capSummary, capSign, rationalSummarySign]) hcapSign]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := massDenominator)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, fold,
      massDenominator]) hmassDenominator]
  rfl

set_option maxRecDepth 4000 in
private theorem run_recoveryLegalTermMassComparisonBranches
    (maximumBits leFlag capFlag capSign massDenominator summaryFlag
      finalContext : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 12)
    (hle : state.registers 2 = leFlag)
    (hcap : state.registers 10 = capFlag)
    (hmass : state.registers 13 = massDenominator)
    (hsummary : state.registers 8 = summaryFlag)
    (hsign : state.registers 12 = capSign)
    (hfinal : state.registers 9 = finalContext)
    (hzero : natBitLength 0 ≤ maximumBits)
    (hone : natBitLength 1 ≤ maximumBits)
    (hpairZero : natBitLength (Nat.pair 0 finalContext) ≤ maximumBits)
    (hpairOne : natBitLength (Nat.pair 1 finalContext) ≤ maximumBits) :
    runNPOracleProgram recoveryLegalTermMassComparisonProgram maximumBits 9
        state =
      some (Nat.pair
        (recoveryLegalTermMassBranchFlag leFlag capFlag capSign
          massDenominator summaryFlag) finalContext) := by
  have hfinish (flag extra pc : ℕ) (nextState : NPOracleState)
      (hnextPc : nextState.pc = pc)
      (hpcFlag : (flag = 0 ∧ pc = 18) ∨ (flag = 1 ∧ pc = 17))
      (hnextFinal : nextState.registers 9 = finalContext) :
      runNPOracleProgram recoveryLegalTermMassComparisonProgram maximumBits
          (extra + 3) nextState = some (Nat.pair flag finalContext) := by
    rcases hpcFlag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [show extra + 3 = (extra + 2) + 1 by omega]
      rw [run_set_instruction (value := 0) (by rfl) hnextPc hzero]
      rw [show extra + 2 = (extra + 1) + 1 by omega]
      rw [run_pair_instruction (value := Nat.pair 0 finalContext)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hnextFinal])
        hpairZero]
      exact run_halt_instruction (fuel := extra)
        (value := Nat.pair 0 finalContext) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hpairZero
    · rw [show extra + 3 = (extra + 2) + 1 by omega]
      rw [run_set_instruction (value := 1) (by rfl) hnextPc hone]
      rw [show extra + 2 = (extra + 1) + 1 by omega]
      rw [run_pair_instruction (value := Nat.pair 1 finalContext)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hnextFinal])
        hpairOne]
      exact run_halt_instruction (fuel := extra)
        (value := Nat.pair 1 finalContext) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hpairOne
  rw [show 9 = 8 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) hpc, hle]
  by_cases hleZero : leFlag = 0
  · rw [if_pos hleZero]
    have hrun := hfinish 0 5 18 (state.jump 18) rfl
      (Or.inl ⟨rfl, rfl⟩) (by simpa [NPOracleState.jump] using hfinal)
    simpa [recoveryLegalTermMassBranchFlag, hleZero] using hrun
  · rw [if_neg hleZero]
    rw [show 8 = 7 + 1 by omega]
    rw [run_branchZero_instruction (by rfl) rfl]
    rw [show (state.jump 13).registers 10 = capFlag by
      simpa [NPOracleState.jump] using hcap]
    by_cases hcapZero : capFlag = 0
    · rw [if_pos hcapZero]
      have hrun := hfinish 0 4 18 ((state.jump 13).jump 18) rfl
        (Or.inl ⟨rfl, rfl⟩) (by simpa [NPOracleState.jump] using hfinal)
      simpa [recoveryLegalTermMassBranchFlag, hleZero, hcapZero] using hrun
    · rw [if_neg hcapZero]
      rw [show 7 = 6 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show ((state.jump 13).jump 14).registers 13 = massDenominator by
        simpa [NPOracleState.jump] using hmass]
      by_cases hmassZero : massDenominator = 0
      · rw [if_pos hmassZero]
        have hrun := hfinish 0 3 18
          (((state.jump 13).jump 14).jump 18) rfl
          (Or.inl ⟨rfl, rfl⟩) (by simpa [NPOracleState.jump] using hfinal)
        simpa [recoveryLegalTermMassBranchFlag, hleZero, hcapZero,
          hmassZero] using hrun
      · rw [if_neg hmassZero]
        rw [show 6 = 5 + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show (((state.jump 13).jump 14).jump 15).registers 8 =
            summaryFlag by simpa [NPOracleState.jump] using hsummary]
        by_cases hsummaryZero : summaryFlag = 0
        · rw [if_pos hsummaryZero]
          have hrun := hfinish 0 2 18
            ((((state.jump 13).jump 14).jump 15).jump 18) rfl
            (Or.inl ⟨rfl, rfl⟩) (by simpa [NPOracleState.jump] using hfinal)
          simpa [recoveryLegalTermMassBranchFlag, hleZero, hcapZero,
            hmassZero, hsummaryZero] using hrun
        · rw [if_neg hsummaryZero]
          rw [show 5 = 4 + 1 by omega]
          rw [run_branchZero_instruction (by rfl) rfl]
          rw [show ((((state.jump 13).jump 14).jump 15).jump 16).registers
              12 = capSign by simpa [NPOracleState.jump] using hsign]
          by_cases hsignZero : capSign = 0
          · rw [if_pos hsignZero]
            have hrun := hfinish 1 1 17
              (((((state.jump 13).jump 14).jump 15).jump 16).jump 17) rfl
              (Or.inr ⟨rfl, rfl⟩)
              (by simpa [NPOracleState.jump] using hfinal)
            simpa [recoveryLegalTermMassBranchFlag, hleZero, hcapZero,
              hmassZero, hsummaryZero, hsignZero] using hrun
          · rw [if_neg hsignZero]
            have hrun := hfinish 0 1 18
              (((((state.jump 13).jump 14).jump 15).jump 16).jump 18) rfl
              (Or.inl ⟨rfl, rfl⟩)
              (by simpa [NPOracleState.jump] using hfinal)
            simpa [recoveryLegalTermMassBranchFlag, hleZero, hcapZero,
              hmassZero, hsummaryZero, hsignZero] using hrun

set_option maxHeartbeats 800000 in
-- The final trace discharges all fail-closed branches against one semantic flag.
set_option maxRecDepth 4000 in
private theorem run_recoveryLegalTermMassComparisonProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassComparisonProgram
        (recoveryLegalTermMassComparisonBits inputLength bitCapStage) 21
        (initialNPOracleState inputLength
          (recoveryLegalTermMassLeStageOutput inputLength bitCapStage)) =
      some (recoveryLegalTermMassComparisonOutput
        inputLength bitCapStage) := by
  rw [run_recoveryLegalTermMassComparisonParser]
  let stage := recoveryLegalTermMassLeStageOutput inputLength bitCapStage
  let capStage := (Nat.unpair stage).2
  let capSummary := (Nat.unpair capStage).1
  let capContext := (Nat.unpair capStage).2
  let fold := (Nat.unpair capContext).1
  let summaryFinal := (Nat.unpair capContext).2
  let finalContext := (Nat.unpair summaryFinal).2
  let maximumBits :=
    recoveryLegalTermMassComparisonBits inputLength bitCapStage
  have hbranches := run_recoveryLegalTermMassComparisonBranches
    maximumBits (Nat.unpair stage).1 (rationalSummaryFlag capSummary)
    (rationalSummarySign capSummary) (Nat.unpair fold).2
    (Nat.unpair summaryFinal).1 finalContext
    (recoveryLegalTermMassComparisonCheckedState inputLength bitCapStage)
    (recoveryLegalTermMassComparisonCheckedState_pc inputLength bitCapStage)
  have hpairZero : natBitLength (Nat.pair 0 finalContext) ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpairOne : natBitLength (Nat.pair 1 finalContext) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength (Nat.pair 0 finalContext) by
      unfold natBitLength
      omega).trans hpairZero
  have hzero : natBitLength 0 ≤ maximumBits := by
    simpa [natBitLength] using hpositive
  have hone : natBitLength 1 ≤ maximumBits := by
    simpa [natBitLength] using hpositive
  have hrun := hbranches
    (recoveryLegalTermMassComparisonCheckedState_reg2
      inputLength bitCapStage)
    (recoveryLegalTermMassComparisonCheckedState_reg10
      inputLength bitCapStage)
    (recoveryLegalTermMassComparisonCheckedState_reg13
      inputLength bitCapStage)
    (recoveryLegalTermMassComparisonCheckedState_reg8
      inputLength bitCapStage)
    (recoveryLegalTermMassComparisonCheckedState_reg12
      inputLength bitCapStage)
    (recoveryLegalTermMassComparisonCheckedState_reg9
      inputLength bitCapStage)
    hzero hone hpairZero hpairOne
  simpa [recoveryLegalTermMassComparisonOutput,
    recoveryLegalTermMassComparisonFlag, stage, capStage, capSummary,
    capContext, fold, summaryFinal, finalContext, maximumBits] using hrun

/-- The sole executable coefficient-mass path: canonical summaries, an exact
rational fold, two verified products, and a fail-closed comparison. -/
def recoveryLegalTermMassProgram : NPOracleProgram :=
  linkPrograms recoveryLegalTermMassSummaryLoweringProgram <|
    linkPrograms recoveryLegalTermMassSummaryStageProgram <|
      linkPrograms recoveryLegalTermMassFoldLoweringProgram <|
        linkPrograms recoveryLegalTermMassFoldStageProgram <|
          linkPrograms recoveryLegalTermMassCapLoweringProgram <|
            linkPrograms recoveryLegalTermMassCapStageProgram <|
              linkPrograms recoveryLegalTermMassLeftProductLoweringProgram <|
                linkPrograms recoveryLegalTermMassLeftProductStageProgram <|
                  linkPrograms recoveryLegalTermMassRightProductLoweringProgram <|
                    linkPrograms recoveryLegalTermMassRightProductStageProgram <|
                      linkPrograms recoveryLegalTermMassLeLoweringProgram <|
                        linkPrograms recoveryLegalTermMassLeStageProgram
                          recoveryLegalTermMassComparisonProgram

@[simp] theorem recoveryLegalTermMassProgram_oracleFree :
    OracleFree recoveryLegalTermMassProgram := by
  exact oracleFree_linkPrograms
    recoveryLegalTermMassSummaryLoweringProgram_oracleFree <|
      oracleFree_linkPrograms recoveryLegalTermMassSummaryStageProgram_oracleFree <|
        oracleFree_linkPrograms recoveryLegalTermMassFoldLoweringProgram_oracleFree <|
          oracleFree_linkPrograms recoveryLegalTermMassFoldStageProgram_oracleFree <|
            oracleFree_linkPrograms recoveryLegalTermMassCapLoweringProgram_oracleFree <|
              oracleFree_linkPrograms recoveryLegalTermMassCapStageProgram_oracleFree <|
                oracleFree_linkPrograms
                  recoveryLegalTermMassLeftProductLoweringProgram_oracleFree <|
                    oracleFree_linkPrograms
                      recoveryLegalTermMassLeftProductStageProgram_oracleFree <|
                        oracleFree_linkPrograms
                          recoveryLegalTermMassRightProductLoweringProgram_oracleFree <|
                            oracleFree_linkPrograms
                              recoveryLegalTermMassRightProductStageProgram_oracleFree <|
                                oracleFree_linkPrograms
                                  recoveryLegalTermMassLeLoweringProgram_oracleFree <|
                                    oracleFree_linkPrograms
                                      recoveryLegalTermMassLeStageProgram_oracleFree
                                      recoveryLegalTermMassComparisonProgram_oracleFree

def recoveryLegalTermMassFuel
    (inputLength bitCapStage : ℕ) : ℕ :=
  linkFuel
    (linkPrograms recoveryLegalTermMassSummaryStageProgram <|
      linkPrograms recoveryLegalTermMassFoldLoweringProgram <|
        linkPrograms recoveryLegalTermMassFoldStageProgram <|
          linkPrograms recoveryLegalTermMassCapLoweringProgram <|
            linkPrograms recoveryLegalTermMassCapStageProgram <|
              linkPrograms recoveryLegalTermMassLeftProductLoweringProgram <|
                linkPrograms recoveryLegalTermMassLeftProductStageProgram <|
                  linkPrograms recoveryLegalTermMassRightProductLoweringProgram <|
                    linkPrograms recoveryLegalTermMassRightProductStageProgram <|
                      linkPrograms recoveryLegalTermMassLeLoweringProgram <|
                        linkPrograms recoveryLegalTermMassLeStageProgram
                          recoveryLegalTermMassComparisonProgram)
    11 <|
      linkFuel
        (linkPrograms recoveryLegalTermMassFoldLoweringProgram <|
          linkPrograms recoveryLegalTermMassFoldStageProgram <|
            linkPrograms recoveryLegalTermMassCapLoweringProgram <|
              linkPrograms recoveryLegalTermMassCapStageProgram <|
                linkPrograms recoveryLegalTermMassLeftProductLoweringProgram <|
                  linkPrograms recoveryLegalTermMassLeftProductStageProgram <|
                    linkPrograms recoveryLegalTermMassRightProductLoweringProgram <|
                      linkPrograms recoveryLegalTermMassRightProductStageProgram <|
                        linkPrograms recoveryLegalTermMassLeLoweringProgram <|
                          linkPrograms recoveryLegalTermMassLeStageProgram
                            recoveryLegalTermMassComparisonProgram)
        (recoveryLegalTermMassSummaryStageFuel inputLength bitCapStage) <|
          linkFuel
            (linkPrograms recoveryLegalTermMassFoldStageProgram <|
              linkPrograms recoveryLegalTermMassCapLoweringProgram <|
                linkPrograms recoveryLegalTermMassCapStageProgram <|
                  linkPrograms recoveryLegalTermMassLeftProductLoweringProgram <|
                    linkPrograms recoveryLegalTermMassLeftProductStageProgram <|
                      linkPrograms recoveryLegalTermMassRightProductLoweringProgram <|
                        linkPrograms recoveryLegalTermMassRightProductStageProgram <|
                          linkPrograms recoveryLegalTermMassLeLoweringProgram <|
                            linkPrograms recoveryLegalTermMassLeStageProgram
                              recoveryLegalTermMassComparisonProgram)
            9 <|
              linkFuel
                (linkPrograms recoveryLegalTermMassCapLoweringProgram <|
                  linkPrograms recoveryLegalTermMassCapStageProgram <|
                    linkPrograms recoveryLegalTermMassLeftProductLoweringProgram <|
                      linkPrograms recoveryLegalTermMassLeftProductStageProgram <|
                        linkPrograms recoveryLegalTermMassRightProductLoweringProgram <|
                          linkPrograms recoveryLegalTermMassRightProductStageProgram <|
                            linkPrograms recoveryLegalTermMassLeLoweringProgram <|
                              linkPrograms recoveryLegalTermMassLeStageProgram
                                recoveryLegalTermMassComparisonProgram)
                (recoveryLegalTermMassFoldStageFuel inputLength bitCapStage) <|
                  linkFuel
                    (linkPrograms recoveryLegalTermMassCapStageProgram <|
                      linkPrograms recoveryLegalTermMassLeftProductLoweringProgram <|
                        linkPrograms recoveryLegalTermMassLeftProductStageProgram <|
                          linkPrograms recoveryLegalTermMassRightProductLoweringProgram <|
                            linkPrograms recoveryLegalTermMassRightProductStageProgram <|
                              linkPrograms recoveryLegalTermMassLeLoweringProgram <|
                                linkPrograms recoveryLegalTermMassLeStageProgram
                                  recoveryLegalTermMassComparisonProgram)
                    10 <|
                      linkFuel
                        (linkPrograms recoveryLegalTermMassLeftProductLoweringProgram <|
                          linkPrograms recoveryLegalTermMassLeftProductStageProgram <|
                            linkPrograms recoveryLegalTermMassRightProductLoweringProgram <|
                              linkPrograms recoveryLegalTermMassRightProductStageProgram <|
                                linkPrograms recoveryLegalTermMassLeLoweringProgram <|
                                  linkPrograms recoveryLegalTermMassLeStageProgram
                                    recoveryLegalTermMassComparisonProgram)
                        (recoveryLegalTermMassCapStageFuel inputLength bitCapStage) <|
                          linkFuel
                            (linkPrograms recoveryLegalTermMassLeftProductStageProgram <|
                              linkPrograms recoveryLegalTermMassRightProductLoweringProgram <|
                                linkPrograms recoveryLegalTermMassRightProductStageProgram <|
                                  linkPrograms recoveryLegalTermMassLeLoweringProgram <|
                                    linkPrograms recoveryLegalTermMassLeStageProgram
                                      recoveryLegalTermMassComparisonProgram)
                            10 <|
                              linkFuel
                                (linkPrograms recoveryLegalTermMassRightProductLoweringProgram <|
                                  linkPrograms recoveryLegalTermMassRightProductStageProgram <|
                                    linkPrograms recoveryLegalTermMassLeLoweringProgram <|
                                      linkPrograms recoveryLegalTermMassLeStageProgram
                                        recoveryLegalTermMassComparisonProgram)
                                (recoveryLegalTermMassLeftProductStageFuel
                                  inputLength bitCapStage) <|
                                  linkFuel
                                    (linkPrograms recoveryLegalTermMassRightProductStageProgram <|
                                      linkPrograms recoveryLegalTermMassLeLoweringProgram <|
                                        linkPrograms recoveryLegalTermMassLeStageProgram
                                          recoveryLegalTermMassComparisonProgram)
                                    13 <|
                                      linkFuel
                                        (linkPrograms recoveryLegalTermMassLeLoweringProgram <|
                                          linkPrograms recoveryLegalTermMassLeStageProgram
                                            recoveryLegalTermMassComparisonProgram)
                                        (recoveryLegalTermMassRightProductStageFuel
                                          inputLength bitCapStage) <|
                                          linkFuel
                                            (linkPrograms recoveryLegalTermMassLeStageProgram
                                              recoveryLegalTermMassComparisonProgram)
                                            7 <|
                                              linkFuel recoveryLegalTermMassComparisonProgram
                                                (recoveryLegalTermMassLeStageFuel
                                                  inputLength bitCapStage) 21

def recoveryLegalTermMassStageBits
    (inputLength bitCapStage : ℕ) : List ℕ :=
  [ natBitLength inputLength
  , recoveryLegalTermMassSummaryLoweringBits inputLength bitCapStage
  , recoveryLegalTermMassSummaryStageBits inputLength bitCapStage
  , recoveryLegalTermMassFoldLoweringBits inputLength bitCapStage
  , recoveryLegalTermMassFoldStageBits inputLength bitCapStage
  , recoveryLegalTermMassCapLoweringBits inputLength bitCapStage
  , recoveryLegalTermMassCapStageBits inputLength bitCapStage
  , recoveryLegalTermMassLeftProductLoweringBits inputLength bitCapStage
  , recoveryLegalTermMassLeftProductStageBits inputLength bitCapStage
  , recoveryLegalTermMassRightProductLoweringBits inputLength bitCapStage
  , recoveryLegalTermMassRightProductStageBits inputLength bitCapStage
  , recoveryLegalTermMassLeLoweringBits inputLength bitCapStage
  , recoveryLegalTermMassLeStageBits inputLength bitCapStage
  , recoveryLegalTermMassComparisonBits inputLength bitCapStage
  ]

def recoveryLegalTermMassBits
    (inputLength bitCapStage : ℕ) : ℕ :=
  (recoveryLegalTermMassStageBits inputLength bitCapStage).foldr max 0

theorem recoveryLegalTermMassStage_bits
    {inputLength bitCapStage bits : ℕ}
    (hbits : bits ∈ recoveryLegalTermMassStageBits inputLength bitCapStage) :
    bits ≤ recoveryLegalTermMassBits inputLength bitCapStage :=
  member_le_foldr_max hbits

set_option maxHeartbeats 800000 in
-- Linking thirteen verified stages builds the closed fuel and bit envelope once.
private theorem run_recoveryLegalTermMassProgram
    (inputLength bitCapStage : ℕ) :
    runNPOracleProgram recoveryLegalTermMassProgram
        (recoveryLegalTermMassBits inputLength bitCapStage)
        (recoveryLegalTermMassFuel inputLength bitCapStage)
        (initialNPOracleState inputLength bitCapStage) =
      some (recoveryLegalTermMassComparisonOutput inputLength bitCapStage) := by
  let maximumBits := recoveryLegalTermMassBits inputLength bitCapStage
  have hlength : natBitLength inputLength ≤ maximumBits :=
    recoveryLegalTermMassStage_bits (by
      simp [recoveryLegalTermMassStageBits])
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hstage {bits : ℕ}
      (hbits : bits ∈ recoveryLegalTermMassStageBits inputLength bitCapStage) :
      bits ≤ maximumBits :=
    recoveryLegalTermMassStage_bits hbits
  have hsummaryLowering := run_bits_mono
    (run_recoveryLegalTermMassSummaryLoweringProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hsummaryStage := run_bits_mono
    (run_recoveryLegalTermMassSummaryStageProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hfoldLowering := run_bits_mono
    (run_recoveryLegalTermMassFoldLoweringProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hfoldStage := run_bits_mono
    (run_recoveryLegalTermMassFoldStageProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hcapLowering := run_bits_mono
    (run_recoveryLegalTermMassCapLoweringProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hcapStage := run_bits_mono
    (run_recoveryLegalTermMassCapStageProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hleftLowering := run_bits_mono
    (run_recoveryLegalTermMassLeftProductLoweringProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hleftStage := run_bits_mono
    (run_recoveryLegalTermMassLeftProductStageProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hrightLowering := run_bits_mono
    (run_recoveryLegalTermMassRightProductLoweringProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hrightStage := run_bits_mono
    (run_recoveryLegalTermMassRightProductStageProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hleLowering := run_bits_mono
    (run_recoveryLegalTermMassLeLoweringProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hleStage := run_bits_mono
    (run_recoveryLegalTermMassLeStageProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hcomparison := run_bits_mono
    (run_recoveryLegalTermMassComparisonProgram inputLength bitCapStage)
    (hstage (by simp [recoveryLegalTermMassStageBits]))
  have hleTail := run_linkPrograms hpositive hlength hleStage hcomparison
  have hleLoweringTail := run_linkPrograms hpositive hlength hleLowering hleTail
  have hrightStageTail := run_linkPrograms hpositive hlength hrightStage hleLoweringTail
  have hrightLoweringTail :=
    run_linkPrograms hpositive hlength hrightLowering hrightStageTail
  have hleftStageTail := run_linkPrograms hpositive hlength hleftStage hrightLoweringTail
  have hleftLoweringTail :=
    run_linkPrograms hpositive hlength hleftLowering hleftStageTail
  have hcapStageTail := run_linkPrograms hpositive hlength hcapStage hleftLoweringTail
  have hcapLoweringTail := run_linkPrograms hpositive hlength hcapLowering hcapStageTail
  have hfoldStageTail := run_linkPrograms hpositive hlength hfoldStage hcapLoweringTail
  have hfoldLoweringTail := run_linkPrograms hpositive hlength hfoldLowering hfoldStageTail
  have hsummaryStageTail :=
    run_linkPrograms hpositive hlength hsummaryStage hfoldLoweringTail
  have hrun := run_linkPrograms hpositive hlength hsummaryLowering hsummaryStageTail
  rw [recoveryLegalTermMassProgram, recoveryLegalTermMassFuel]
  exact hrun

def recoveryLegalSumFlagGateOutput (input : ℕ) : ℕ :=
  recoveryBoundedContextGateOutput
    (Nat.unpair input).1 (Nat.unpair input).2

def recoveryLegalSumFlagGateBits (input : ℕ) : ℕ :=
  natBitLength input

private theorem run_recoveryLegalSumFlagGateProgram
    (inputLength input : ℕ) :
    runNPOracleProgram recoveryBoundedContextGateProgram
        (recoveryLegalSumFlagGateBits input) 4
        (initialNPOracleState inputLength input) =
      some (recoveryLegalSumFlagGateOutput input) := by
  have hpair :
      Nat.pair (Nat.unpair input).1 (Nat.unpair input).2 = input :=
    Nat.pair_unpair input
  have hrun :=
    run_recoveryBoundedContextGateProgram inputLength
      (Nat.unpair input).1 (Nat.unpair input).2
  simpa only [recoveryLegalSumFlagGateBits,
    recoveryLegalSumFlagGateOutput, recoveryBoundedContextGateBits,
    hpair] using hrun

theorem recoveryLegalTermMassComparisonFinalContext_eq
    (inputLength bitCapStage : ℕ) :
    (Nat.unpair
      (Nat.unpair
        (Nat.unpair
          (Nat.unpair
            (recoveryLegalTermMassLeStageOutput
              inputLength bitCapStage)).2).2).2).2 =
      recoveryLegalTermMassFinalContext bitCapStage := by
  simp only [recoveryLegalTermMassLeStageOutput, Nat.unpair_pair,
    recoveryLegalTermMassCapStageOutput,
    recoveryLegalTermMassCapLoweringOutput,
    recoveryLegalTermMassCapValidationContext,
    recoveryLegalTermMassFoldStageOutput,
    recoveryLegalTermMassFoldContext,
    recoveryLegalTermMassSummaryStageOutput]

theorem recoveryLegalTermMassFinalContext_bitCapStageOutput
    (circuitStage : ℕ) :
    recoveryLegalTermMassFinalContext
        (recoveryLegalTermBitCapStageOutput circuitStage) =
      Nat.pair
        (recoveryLegalTermCoefficientBitCapListOutput
          (recoveryLegalTermBitCapSelectedCap circuitStage)
          (recoveryLegalTermBitCapMappedCode circuitStage))
        circuitStage := by
  simp [recoveryLegalTermMassFinalContext,
    recoveryLegalTermMassBitFlag, recoveryLegalTermMassCircuitStage,
    recoveryLegalTermMassCapContext, recoveryLegalTermMassLoweringContext,
    recoveryLegalTermBitCapStageOutput,
    recoveryLegalTermBitCapLoweringContext]

def recoveryLegalTermResourceCircuitStage (input : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair input).2).2

def recoveryLegalTermResourceSummaryTree (input : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair
      (Nat.unpair (recoveryLegalTermResourceCircuitStage input)).1).2).1

def recoveryLegalTermResourceExpectedRest (input : ℕ) : ℕ :=
  let coefficientStage :=
    (Nat.unpair (recoveryLegalTermResourceCircuitStage input)).2
  let bound := (Nat.unpair coefficientStage).2
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  (Nat.unpair termsRest).2

def recoveryLegalTermResourceExpectedArity (input : ℕ) : ℕ :=
  (Nat.unpair (recoveryLegalTermResourceExpectedRest input)).1

def recoveryLegalTermResourceStoredHandoff (input : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair (recoveryLegalTermResourceExpectedRest input)).2).2

def recoveryLegalTermResourceHandoffLoweringOutput (input : ℕ) : ℕ :=
  Nat.pair (recoveryLegalTermResourceStoredHandoff input)
    (Nat.pair (recoveryLegalTermResourceExpectedArity input)
      (Nat.pair (recoveryLegalTermResourceSummaryTree input) input))

def recoveryLegalTermResourceHandoffLoweringProgram :
    NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairRight 2 2 2
  , .unpairLeft 2 3 3
  , .unpairRight 3 3 4
  , .unpairLeft 3 3 5
  , .unpairRight 2 4 6
  , .unpairRight 4 4 7
  , .unpairRight 4 4 8
  , .unpairRight 4 4 9
  , .unpairRight 4 4 10
  , .unpairRight 4 4 11
  , .unpairRight 4 4 12
  , .unpairRight 4 4 13
  , .unpairLeft 4 5 14
  , .unpairRight 4 4 15
  , .unpairRight 4 4 16
  , .pair 3 0 3 17
  , .pair 5 3 3 18
  , .pair 4 3 0 19
  , .halt 0
  ]

@[simp] theorem
    recoveryLegalTermResourceHandoffLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermResourceHandoffLoweringProgram := by
  rfl

def recoveryLegalTermResourceHandoffLoweringFuel : ℕ := 20

def recoveryLegalTermResourceHandoffLoweringValues (input : ℕ) :
    List ℕ :=
  let circuitStage := recoveryLegalTermResourceCircuitStage input
  let listOutput := (Nat.unpair circuitStage).1
  let summaryData := (Nat.unpair listOutput).2
  let tree := recoveryLegalTermResourceSummaryTree input
  let coefficientStage := (Nat.unpair circuitStage).2
  let bound := (Nat.unpair coefficientStage).2
  let arityStage := (Nat.unpair bound).2
  let arityContext := (Nat.unpair arityStage).2
  let context := (Nat.unpair arityContext).2
  let modeRest := (Nat.unpair context).2
  let termsRest := (Nat.unpair modeRest).2
  let expectedRest := (Nat.unpair termsRest).2
  let arity := (Nat.unpair expectedRest).1
  let capHandoff := (Nat.unpair expectedRest).2
  let storedHandoff := (Nat.unpair capHandoff).2
  [ input
  , (Nat.unpair input).2
  , circuitStage
  , listOutput
  , summaryData
  , tree
  , coefficientStage
  , bound
  , arityStage
  , arityContext
  , context
  , modeRest
  , termsRest
  , expectedRest
  , arity
  , capHandoff
  , storedHandoff
  , Nat.pair tree input
  , Nat.pair arity (Nat.pair tree input)
  , recoveryLegalTermResourceHandoffLoweringOutput input
  ]

def recoveryLegalTermResourceHandoffLoweringBits (input : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermResourceHandoffLoweringValues input).foldr max 0

theorem recoveryLegalTermResourceHandoffLoweringValue_bits
    {input value : ℕ}
    (hvalue :
      value ∈ recoveryLegalTermResourceHandoffLoweringValues input) :
    natBitLength value ≤
      recoveryLegalTermResourceHandoffLoweringBits input := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- The exact 20-step trace expands a nested projection ledger at each write.
private theorem run_recoveryLegalTermResourceHandoffLoweringProgram
    (inputLength input : ℕ) :
    runNPOracleProgram recoveryLegalTermResourceHandoffLoweringProgram
        (recoveryLegalTermResourceHandoffLoweringBits input)
        recoveryLegalTermResourceHandoffLoweringFuel
        (initialNPOracleState inputLength input) =
      some (recoveryLegalTermResourceHandoffLoweringOutput input) := by
  have hbits :
      ∀ value ∈ recoveryLegalTermResourceHandoffLoweringValues input,
        natBitLength value ≤
          recoveryLegalTermResourceHandoffLoweringBits input := by
    intro value hvalue
    exact recoveryLegalTermResourceHandoffLoweringValue_bits hvalue
  simp [recoveryLegalTermResourceHandoffLoweringProgram,
    recoveryLegalTermResourceHandoffLoweringFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    recoveryLegalTermResourceHandoffLoweringValues,
    recoveryLegalTermResourceHandoffLoweringOutput,
    recoveryLegalTermResourceCircuitStage,
    recoveryLegalTermResourceSummaryTree,
    recoveryLegalTermResourceExpectedRest,
    recoveryLegalTermResourceExpectedArity,
    recoveryLegalTermResourceStoredHandoff]

/-- Read the trusted mode tag and the pair of mode-specific limit records out
of the retained handoff, keeping the rest of the lowering untouched. -/
def recoveryLegalTermResourceLimitsProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairRight 5 5 5
  , .unpairRight 5 5 6
  , .unpairRight 5 5 7
  , .unpairRight 5 5 8
  , .unpairRight 5 5 9
  , .unpairRight 5 5 10
  , .pair 4 5 4 11
  , .pair 4 3 0 12
  , .halt 0
  ]

@[simp] theorem recoveryLegalTermResourceLimitsProgram_oracleFree :
    OracleFree recoveryLegalTermResourceLimitsProgram := by
  rfl

def recoveryLegalTermResourceLimitsFuel : ℕ := 13

def recoveryLegalTermResourceLimitsValues
    (handoff rest : ℕ) : List ℕ :=
  let handoffTail₀ := (Nat.unpair handoff).2
  let handoffTail₁ := (Nat.unpair handoffTail₀).2
  let handoffTail₂ := (Nat.unpair handoffTail₁).2
  let limitsCode := (Nat.unpair handoffTail₂).2
  let limitsTail₀ := (Nat.unpair limitsCode).2
  let limitsTail₁ := (Nat.unpair limitsTail₀).2
  let legalPair := (Nat.unpair limitsTail₁).2
  [ Nat.pair handoff rest
  , handoff
  , rest
  , handoffMode handoff
  , handoffTail₀
  , handoffTail₁
  , handoffTail₂
  , limitsCode
  , limitsTail₀
  , limitsTail₁
  , legalPair
  , Nat.pair (handoffMode handoff) legalPair
  , Nat.pair (Nat.pair (handoffMode handoff) legalPair) rest
  ]

def recoveryLegalTermResourceLimitsBits
    (handoff rest : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermResourceLimitsValues handoff rest).foldr max 0

theorem recoveryLegalTermResourceLimitsValue_bits
    {handoff rest value : ℕ}
    (hvalue : value ∈ recoveryLegalTermResourceLimitsValues handoff rest) :
    natBitLength value ≤
      recoveryLegalTermResourceLimitsBits handoff rest := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- The exact 13-step trace expands a nested limits ledger at each write.
private theorem run_recoveryLegalTermResourceLimitsProgram
    (inputLength handoff rest : ℕ) :
    runNPOracleProgram recoveryLegalTermResourceLimitsProgram
        (recoveryLegalTermResourceLimitsBits handoff rest)
        recoveryLegalTermResourceLimitsFuel
        (initialNPOracleState inputLength (Nat.pair handoff rest)) =
      some
        (Nat.pair
          (Nat.pair (handoffMode handoff) (handoffLegalLimitsPair handoff))
          rest) := by
  have hbits :
      ∀ value ∈ recoveryLegalTermResourceLimitsValues handoff rest,
        natBitLength value ≤
          recoveryLegalTermResourceLimitsBits handoff rest := by
    intro value hvalue
    exact recoveryLegalTermResourceLimitsValue_bits hvalue
  simp [recoveryLegalTermResourceLimitsProgram,
    recoveryLegalTermResourceLimitsFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    recoveryLegalTermResourceLimitsValues, handoffMode,
    handoffLegalLimitsPair, handoffLimitsCode]

/-- Select the mode-specific limit record.  Any mode outside the two published
recovery families collapses the selection to the zero sentinel, so a later
projection can never read a foreign record. -/
def recoveryLegalTermResourceSelectProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .branchZero 4 11 5
  , .decrement 4 6
  , .branchZero 4 9 7
  , .decrement 4 8
  , .branchZero 4 10 11
  , .unpairLeft 5 5 12
  , .unpairRight 5 5 12
  , .set 5 0 12
  , .pair 5 3 0 13
  , .halt 0
  ]

@[simp] theorem recoveryLegalTermResourceSelectProgram_oracleFree :
    OracleFree recoveryLegalTermResourceSelectProgram := by
  rfl

def recoveryLegalTermResourceSelectFuel : ℕ := 14

def recoveryLegalTermResourceSelectValues
    (handoff rest : ℕ) : List ℕ :=
  let mode := handoffMode handoff
  let legalPair := handoffLegalLimitsPair handoff
  [ Nat.pair (Nat.pair mode legalPair) rest
  , Nat.pair mode legalPair
  , rest
  , mode
  , mode - 1
  , mode - 1 - 1
  , legalPair
  , (Nat.unpair legalPair).1
  , (Nat.unpair legalPair).2
  , 0
  , handoffSelectedLegalLimits handoff
  , Nat.pair (handoffSelectedLegalLimits handoff) rest
  ]

def recoveryLegalTermResourceSelectBits
    (handoff rest : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermResourceSelectValues handoff rest).foldr max 0

theorem recoveryLegalTermResourceSelectValue_bits
    {handoff rest value : ℕ}
    (hvalue : value ∈ recoveryLegalTermResourceSelectValues handoff rest) :
    natBitLength value ≤
      recoveryLegalTermResourceSelectBits handoff rest := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
-- Each of the three mode branches replays the same 14-step register trace.
private theorem run_recoveryLegalTermResourceSelectProgram
    (inputLength handoff rest : ℕ) :
    runNPOracleProgram recoveryLegalTermResourceSelectProgram
        (recoveryLegalTermResourceSelectBits handoff rest)
        recoveryLegalTermResourceSelectFuel
        (initialNPOracleState inputLength
          (Nat.pair
            (Nat.pair (handoffMode handoff) (handoffLegalLimitsPair handoff))
            rest)) =
      some (Nat.pair (handoffSelectedLegalLimits handoff) rest) := by
  have hbits :
      ∀ value ∈ recoveryLegalTermResourceSelectValues handoff rest,
        natBitLength value ≤
          recoveryLegalTermResourceSelectBits handoff rest := by
    intro value hvalue
    exact recoveryLegalTermResourceSelectValue_bits hvalue
  have hmodeBits :
      natBitLength (handoffMode handoff) ≤
        recoveryLegalTermResourceSelectBits handoff rest := by
    apply hbits
    simp [recoveryLegalTermResourceSelectValues]
  have hdecrement :
      natBitLength (handoffMode handoff - 1) ≤
        recoveryLegalTermResourceSelectBits handoff rest :=
    (natBitLength_mono (Nat.sub_le _ 1)).trans hmodeBits
  have hdecrementTwice :
      natBitLength (handoffMode handoff - 1 - 1) ≤
        recoveryLegalTermResourceSelectBits handoff rest :=
    (natBitLength_mono
      ((Nat.sub_le (handoffMode handoff - 1) 1).trans
        (Nat.sub_le (handoffMode handoff) 1))).trans hmodeBits
  by_cases hone : handoffMode handoff = 1
  · simp [recoveryLegalTermResourceSelectProgram,
      recoveryLegalTermResourceSelectFuel, runNPOracleProgram,
      initialNPOracleState, NPOracleState.boundedWrite, hbits,
      recoveryLegalTermResourceSelectValues, handoffSelectedLegalLimits,
      hone]
  · by_cases htwo : handoffMode handoff = 2
    · simp [recoveryLegalTermResourceSelectProgram,
        recoveryLegalTermResourceSelectFuel, runNPOracleProgram,
        initialNPOracleState, NPOracleState.boundedWrite, hbits,
        recoveryLegalTermResourceSelectValues,
        handoffSelectedLegalLimits, htwo]
    · by_cases hzero : handoffMode handoff = 0
      · simp [recoveryLegalTermResourceSelectProgram,
          recoveryLegalTermResourceSelectFuel, runNPOracleProgram,
          initialNPOracleState, NPOracleState.boundedWrite, hbits,
          recoveryLegalTermResourceSelectValues, handoffSelectedLegalLimits,
          hzero]
      · have hdecrementZero : handoffMode handoff - 1 ≠ 0 := by omega
        have hdecrementTwiceZero :
            handoffMode handoff - 1 - 1 ≠ 0 := by omega
        have hselected : handoffSelectedLegalLimits handoff = 0 := by
          simp only [handoffSelectedLegalLimits, if_neg hone, if_neg htwo]
        simp [recoveryLegalTermResourceSelectProgram,
          recoveryLegalTermResourceSelectFuel, runNPOracleProgram,
          initialNPOracleState, NPOracleState.boundedWrite, hbits,
          recoveryLegalTermResourceSelectValues, hselected,
          Nat.pred_eq_sub_one, hzero, hdecrementZero, hdecrementTwiceZero]

/-- The last field pair of a selected limit record holds the wire cap and the
description cap in declaration order. -/
def recoveryLegalTermResourceCapPair (selected : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair (Nat.unpair (Nat.unpair selected).2).2).2).2

def recoveryLegalTermResourceCapPairProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 2 2 3
  , .unpairRight 2 2 4
  , .unpairRight 2 2 5
  , .unpairRight 2 2 6
  , .pair 2 3 0 7
  , .halt 0
  ]

@[simp] theorem recoveryLegalTermResourceCapPairProgram_oracleFree :
    OracleFree recoveryLegalTermResourceCapPairProgram := by
  rfl

def recoveryLegalTermResourceCapPairFuel : ℕ := 8

def recoveryLegalTermResourceCapPairValues
    (selected rest : ℕ) : List ℕ :=
  let tail₀ := (Nat.unpair selected).2
  let tail₁ := (Nat.unpair tail₀).2
  let tail₂ := (Nat.unpair tail₁).2
  [ Nat.pair selected rest
  , selected
  , rest
  , tail₀
  , tail₁
  , tail₂
  , recoveryLegalTermResourceCapPair selected
  , Nat.pair (recoveryLegalTermResourceCapPair selected) rest
  ]

def recoveryLegalTermResourceCapPairBits
    (selected rest : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermResourceCapPairValues selected rest).foldr max 0

theorem recoveryLegalTermResourceCapPairValue_bits
    {selected rest value : ℕ}
    (hvalue : value ∈ recoveryLegalTermResourceCapPairValues selected rest) :
    natBitLength value ≤
      recoveryLegalTermResourceCapPairBits selected rest := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

private theorem run_recoveryLegalTermResourceCapPairProgram
    (inputLength selected rest : ℕ) :
    runNPOracleProgram recoveryLegalTermResourceCapPairProgram
        (recoveryLegalTermResourceCapPairBits selected rest)
        recoveryLegalTermResourceCapPairFuel
        (initialNPOracleState inputLength (Nat.pair selected rest)) =
      some
        (Nat.pair (recoveryLegalTermResourceCapPair selected) rest) := by
  have hbits :
      ∀ value ∈ recoveryLegalTermResourceCapPairValues selected rest,
        natBitLength value ≤
          recoveryLegalTermResourceCapPairBits selected rest := by
    intro value hvalue
    exact recoveryLegalTermResourceCapPairValue_bits hvalue
  simp [recoveryLegalTermResourceCapPairProgram,
    recoveryLegalTermResourceCapPairFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    recoveryLegalTermResourceCapPairValues,
    recoveryLegalTermResourceCapPair]

private theorem handoffSelectedWireCap_capPair (handoff : ℕ) :
    handoffSelectedWireCap handoff =
      (Nat.unpair
        (recoveryLegalTermResourceCapPair
          (handoffSelectedLegalLimits handoff))).1 :=
  rfl

private theorem handoffSelectedDescriptionCap_capPair (handoff : ℕ) :
    handoffSelectedDescriptionCap handoff =
      (Nat.unpair
        (recoveryLegalTermResourceCapPair
          (handoffSelectedLegalLimits handoff))).2 :=
  rfl

def recoveryLegalTermWireRequestProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairLeft 2 3 2
  , .unpairRight 0 4 3
  , .unpairLeft 4 5 4
  , .unpairRight 4 4 5
  , .unpairLeft 4 6 6
  , .unpairRight 4 4 7
  , .pair 5 3 3 8
  , .pair 3 6 3 9
  , .pair 3 4 0 10
  , .halt 0
  ]

@[simp] theorem recoveryLegalTermWireRequestProgram_oracleFree :
    OracleFree recoveryLegalTermWireRequestProgram := by
  rfl

def recoveryLegalTermDescriptionRequestProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 2 3 2
  , .unpairRight 0 4 3
  , .unpairLeft 4 5 4
  , .unpairRight 4 4 5
  , .unpairLeft 4 6 6
  , .unpairRight 4 4 7
  , .pair 5 3 3 8
  , .pair 3 6 3 9
  , .pair 3 4 0 10
  , .halt 0
  ]

@[simp] theorem
    recoveryLegalTermDescriptionRequestProgram_oracleFree :
    OracleFree recoveryLegalTermDescriptionRequestProgram := by
  rfl

def recoveryLegalTermResourceRequestFuel : ℕ := 11

def recoveryLegalTermResourceRequestValues
    (capPair arity tree retained cap : ℕ) : List ℕ :=
  [ Nat.pair capPair (Nat.pair arity (Nat.pair tree retained))
  , capPair
  , cap
  , Nat.pair arity (Nat.pair tree retained)
  , arity
  , Nat.pair tree retained
  , tree
  , retained
  , Nat.pair arity cap
  , nativeInputRequest (Nat.pair arity cap) tree
  , Nat.pair (nativeInputRequest (Nat.pair arity cap) tree) retained
  ]

def recoveryLegalTermResourceRequestBits
    (capPair arity tree retained cap : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalTermResourceRequestValues
      capPair arity tree retained cap).foldr max 0

theorem recoveryLegalTermResourceRequestValue_bits
    {capPair arity tree retained cap value : ℕ}
    (hvalue :
      value ∈
        recoveryLegalTermResourceRequestValues
          capPair arity tree retained cap) :
    natBitLength value ≤
      recoveryLegalTermResourceRequestBits capPair arity tree retained cap := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in

private theorem run_recoveryLegalTermWireRequestProgram
    (inputLength capPair arity tree retained : ℕ) :
    runNPOracleProgram recoveryLegalTermWireRequestProgram
        (recoveryLegalTermResourceRequestBits capPair arity tree retained
          (Nat.unpair capPair).1)
        recoveryLegalTermResourceRequestFuel
        (initialNPOracleState inputLength
          (Nat.pair capPair (Nat.pair arity (Nat.pair tree retained)))) =
      some
        (Nat.pair
          (nativeInputRequest
            (Nat.pair arity (Nat.unpair capPair).1) tree)
          retained) := by
  have hbits :
      ∀ value ∈
          recoveryLegalTermResourceRequestValues capPair arity tree retained
            (Nat.unpair capPair).1,
        natBitLength value ≤
          recoveryLegalTermResourceRequestBits capPair arity tree retained
            (Nat.unpair capPair).1 := by
    intro value hvalue
    exact recoveryLegalTermResourceRequestValue_bits hvalue
  simp [recoveryLegalTermWireRequestProgram,
    recoveryLegalTermResourceRequestFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    recoveryLegalTermResourceRequestValues, nativeInputRequest]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- The description twin replays the same 11-step trace on the second cap.
private theorem run_recoveryLegalTermDescriptionRequestProgram
    (inputLength capPair arity tree retained : ℕ) :
    runNPOracleProgram recoveryLegalTermDescriptionRequestProgram
        (recoveryLegalTermResourceRequestBits capPair arity tree retained
          (Nat.unpair capPair).2)
        recoveryLegalTermResourceRequestFuel
        (initialNPOracleState inputLength
          (Nat.pair capPair (Nat.pair arity (Nat.pair tree retained)))) =
      some
        (Nat.pair
          (nativeInputRequest
            (Nat.pair arity (Nat.unpair capPair).2) tree)
          retained) := by
  have hbits :
      ∀ value ∈
          recoveryLegalTermResourceRequestValues capPair arity tree retained
            (Nat.unpair capPair).2,
        natBitLength value ≤
          recoveryLegalTermResourceRequestBits capPair arity tree retained
            (Nat.unpair capPair).2 := by
    intro value hvalue
    exact recoveryLegalTermResourceRequestValue_bits hvalue
  simp [recoveryLegalTermDescriptionRequestProgram,
    recoveryLegalTermResourceRequestFuel, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite, hbits,
    recoveryLegalTermResourceRequestValues, nativeInputRequest]

/-! ### One linked context chain per resource coordinate -/

def recoveryLegalTermWireChainProgram : NPOracleProgram :=
  linkPrograms recoveryLegalTermResourceLimitsProgram <|
    linkPrograms recoveryLegalTermResourceSelectProgram <|
      linkPrograms recoveryLegalTermResourceCapPairProgram
        recoveryLegalTermWireRequestProgram

@[simp] theorem recoveryLegalTermWireChainProgram_oracleFree :
    OracleFree recoveryLegalTermWireChainProgram :=
  oracleFree_linkPrograms recoveryLegalTermResourceLimitsProgram_oracleFree <|
    oracleFree_linkPrograms
      recoveryLegalTermResourceSelectProgram_oracleFree <|
        oracleFree_linkPrograms
          recoveryLegalTermResourceCapPairProgram_oracleFree
          recoveryLegalTermWireRequestProgram_oracleFree

def recoveryLegalTermDescriptionChainProgram : NPOracleProgram :=
  linkPrograms recoveryLegalTermResourceLimitsProgram <|
    linkPrograms recoveryLegalTermResourceSelectProgram <|
      linkPrograms recoveryLegalTermResourceCapPairProgram
        recoveryLegalTermDescriptionRequestProgram

@[simp] theorem recoveryLegalTermDescriptionChainProgram_oracleFree :
    OracleFree recoveryLegalTermDescriptionChainProgram :=
  oracleFree_linkPrograms recoveryLegalTermResourceLimitsProgram_oracleFree <|
    oracleFree_linkPrograms
      recoveryLegalTermResourceSelectProgram_oracleFree <|
        oracleFree_linkPrograms
          recoveryLegalTermResourceCapPairProgram_oracleFree
          recoveryLegalTermDescriptionRequestProgram_oracleFree

def recoveryLegalTermWireChainFuel : ℕ :=
  linkFuel
    (linkPrograms recoveryLegalTermResourceSelectProgram <|
      linkPrograms recoveryLegalTermResourceCapPairProgram
        recoveryLegalTermWireRequestProgram)
    recoveryLegalTermResourceLimitsFuel <|
      linkFuel
        (linkPrograms recoveryLegalTermResourceCapPairProgram
          recoveryLegalTermWireRequestProgram)
        recoveryLegalTermResourceSelectFuel <|
          linkFuel recoveryLegalTermWireRequestProgram
            recoveryLegalTermResourceCapPairFuel
            recoveryLegalTermResourceRequestFuel

def recoveryLegalTermDescriptionChainFuel : ℕ :=
  linkFuel
    (linkPrograms recoveryLegalTermResourceSelectProgram <|
      linkPrograms recoveryLegalTermResourceCapPairProgram
        recoveryLegalTermDescriptionRequestProgram)
    recoveryLegalTermResourceLimitsFuel <|
      linkFuel
        (linkPrograms recoveryLegalTermResourceCapPairProgram
          recoveryLegalTermDescriptionRequestProgram)
        recoveryLegalTermResourceSelectFuel <|
          linkFuel recoveryLegalTermDescriptionRequestProgram
            recoveryLegalTermResourceCapPairFuel
            recoveryLegalTermResourceRequestFuel

def recoveryLegalTermResourceChainBits
    (inputLength storedHandoff arity tree retained cap : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max
      (recoveryLegalTermResourceLimitsBits storedHandoff
        (Nat.pair arity (Nat.pair tree retained))) <|
      max
        (recoveryLegalTermResourceSelectBits storedHandoff
          (Nat.pair arity (Nat.pair tree retained))) <|
        max
          (recoveryLegalTermResourceCapPairBits
            (handoffSelectedLegalLimits storedHandoff)
            (Nat.pair arity (Nat.pair tree retained)))
          (recoveryLegalTermResourceRequestBits
            (recoveryLegalTermResourceCapPair
              (handoffSelectedLegalLimits storedHandoff))
            arity tree retained cap)

private theorem run_recoveryLegalTermWireChainProgram
    (inputLength storedHandoff arity tree retained : ℕ) :
    runNPOracleProgram recoveryLegalTermWireChainProgram
        (recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedWireCap storedHandoff))
        recoveryLegalTermWireChainFuel
        (initialNPOracleState inputLength
          (Nat.pair storedHandoff
            (Nat.pair arity (Nat.pair tree retained)))) =
      some
        (Nat.pair
          (nativeInputRequest
            (Nat.pair arity (handoffSelectedWireCap storedHandoff)) tree)
          retained) := by
  have hlength :
      natBitLength inputLength ≤
        recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedWireCap storedHandoff) :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤
        recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedWireCap storedHandoff) :=
    (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hlimitsBits :
      recoveryLegalTermResourceLimitsBits storedHandoff
          (Nat.pair arity (Nat.pair tree retained)) ≤
        recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedWireCap storedHandoff) :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hselectBits :
      recoveryLegalTermResourceSelectBits storedHandoff
          (Nat.pair arity (Nat.pair tree retained)) ≤
        recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedWireCap storedHandoff) :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hcapPairBits :
      recoveryLegalTermResourceCapPairBits
          (handoffSelectedLegalLimits storedHandoff)
          (Nat.pair arity (Nat.pair tree retained)) ≤
        recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedWireCap storedHandoff) :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hrequestBits :
      recoveryLegalTermResourceRequestBits
          (recoveryLegalTermResourceCapPair
            (handoffSelectedLegalLimits storedHandoff))
          arity tree retained (handoffSelectedWireCap storedHandoff) ≤
        recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedWireCap storedHandoff) :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hlimits :=
    run_bits_mono
      (run_recoveryLegalTermResourceLimitsProgram inputLength storedHandoff
        (Nat.pair arity (Nat.pair tree retained)))
      hlimitsBits
  have hselect :=
    run_bits_mono
      (run_recoveryLegalTermResourceSelectProgram inputLength storedHandoff
        (Nat.pair arity (Nat.pair tree retained)))
      hselectBits
  have hcapPair :=
    run_bits_mono
      (run_recoveryLegalTermResourceCapPairProgram inputLength
        (handoffSelectedLegalLimits storedHandoff)
        (Nat.pair arity (Nat.pair tree retained)))
      hcapPairBits
  have hrequest :=
    run_bits_mono
      (run_recoveryLegalTermWireRequestProgram inputLength
        (recoveryLegalTermResourceCapPair
          (handoffSelectedLegalLimits storedHandoff))
        arity tree retained)
      hrequestBits
  have htail₂ := run_linkPrograms hpositive hlength hcapPair hrequest
  have htail₁ := run_linkPrograms hpositive hlength hselect htail₂
  have hrun := run_linkPrograms hpositive hlength hlimits htail₁
  simpa only [recoveryLegalTermWireChainProgram,
    recoveryLegalTermWireChainFuel, handoffSelectedWireCap_capPair] using hrun

private theorem run_recoveryLegalTermDescriptionChainProgram
    (inputLength storedHandoff arity tree retained : ℕ) :
    runNPOracleProgram recoveryLegalTermDescriptionChainProgram
        (recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedDescriptionCap storedHandoff))
        recoveryLegalTermDescriptionChainFuel
        (initialNPOracleState inputLength
          (Nat.pair storedHandoff
            (Nat.pair arity (Nat.pair tree retained)))) =
      some
        (Nat.pair
          (nativeInputRequest
            (Nat.pair arity (handoffSelectedDescriptionCap storedHandoff))
            tree)
          retained) := by
  have hlength :
      natBitLength inputLength ≤
        recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedDescriptionCap storedHandoff) :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤
        recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedDescriptionCap storedHandoff) :=
    (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hlimitsBits :
      recoveryLegalTermResourceLimitsBits storedHandoff
          (Nat.pair arity (Nat.pair tree retained)) ≤
        recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedDescriptionCap storedHandoff) :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hselectBits :
      recoveryLegalTermResourceSelectBits storedHandoff
          (Nat.pair arity (Nat.pair tree retained)) ≤
        recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedDescriptionCap storedHandoff) :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hcapPairBits :
      recoveryLegalTermResourceCapPairBits
          (handoffSelectedLegalLimits storedHandoff)
          (Nat.pair arity (Nat.pair tree retained)) ≤
        recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedDescriptionCap storedHandoff) :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hrequestBits :
      recoveryLegalTermResourceRequestBits
          (recoveryLegalTermResourceCapPair
            (handoffSelectedLegalLimits storedHandoff))
          arity tree retained
          (handoffSelectedDescriptionCap storedHandoff) ≤
        recoveryLegalTermResourceChainBits inputLength storedHandoff arity
          tree retained (handoffSelectedDescriptionCap storedHandoff) :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hlimits :=
    run_bits_mono
      (run_recoveryLegalTermResourceLimitsProgram inputLength storedHandoff
        (Nat.pair arity (Nat.pair tree retained)))
      hlimitsBits
  have hselect :=
    run_bits_mono
      (run_recoveryLegalTermResourceSelectProgram inputLength storedHandoff
        (Nat.pair arity (Nat.pair tree retained)))
      hselectBits
  have hcapPair :=
    run_bits_mono
      (run_recoveryLegalTermResourceCapPairProgram inputLength
        (handoffSelectedLegalLimits storedHandoff)
        (Nat.pair arity (Nat.pair tree retained)))
      hcapPairBits
  have hrequest :=
    run_bits_mono
      (run_recoveryLegalTermDescriptionRequestProgram inputLength
        (recoveryLegalTermResourceCapPair
          (handoffSelectedLegalLimits storedHandoff))
        arity tree retained)
      hrequestBits
  have htail₂ := run_linkPrograms hpositive hlength hcapPair hrequest
  have htail₁ := run_linkPrograms hpositive hlength hselect htail₂
  have hrun := run_linkPrograms hpositive hlength hlimits htail₁
  simpa only [recoveryLegalTermDescriptionChainProgram,
    recoveryLegalTermDescriptionChainFuel,
    handoffSelectedDescriptionCap_capPair] using hrun

/-! ### The two lowered resource requests -/

def recoveryLegalTermWireContext (input : ℕ) : ℕ :=
  Nat.pair (recoveryLegalTermResourceExpectedArity input)
    (handoffSelectedWireCap (recoveryLegalTermResourceStoredHandoff input))

def recoveryLegalTermDescriptionContext (input : ℕ) : ℕ :=
  Nat.pair (recoveryLegalTermResourceExpectedArity input)
    (handoffSelectedDescriptionCap
      (recoveryLegalTermResourceStoredHandoff input))

def recoveryLegalTermWireLoweringOutput (input : ℕ) : ℕ :=
  Nat.pair
    (nativeInputRequest (recoveryLegalTermWireContext input)
      (recoveryLegalTermResourceSummaryTree input))
    input

def recoveryLegalTermDescriptionLoweringOutput (input : ℕ) : ℕ :=
  Nat.pair
    (nativeInputRequest (recoveryLegalTermDescriptionContext input)
      (recoveryLegalTermResourceSummaryTree input))
    input

def recoveryLegalTermWireLoweringProgram : NPOracleProgram :=
  linkPrograms recoveryLegalTermResourceHandoffLoweringProgram
    recoveryLegalTermWireChainProgram

@[simp] theorem recoveryLegalTermWireLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermWireLoweringProgram :=
  oracleFree_linkPrograms
    recoveryLegalTermResourceHandoffLoweringProgram_oracleFree
    recoveryLegalTermWireChainProgram_oracleFree

def recoveryLegalTermDescriptionLoweringProgram : NPOracleProgram :=
  linkPrograms recoveryLegalTermResourceHandoffLoweringProgram
    recoveryLegalTermDescriptionChainProgram

@[simp] theorem
    recoveryLegalTermDescriptionLoweringProgram_oracleFree :
    OracleFree recoveryLegalTermDescriptionLoweringProgram :=
  oracleFree_linkPrograms
    recoveryLegalTermResourceHandoffLoweringProgram_oracleFree
    recoveryLegalTermDescriptionChainProgram_oracleFree

def recoveryLegalTermWireLoweringFuel : ℕ :=
  linkFuel recoveryLegalTermWireChainProgram
    recoveryLegalTermResourceHandoffLoweringFuel
    recoveryLegalTermWireChainFuel

def recoveryLegalTermDescriptionLoweringFuel : ℕ :=
  linkFuel recoveryLegalTermDescriptionChainProgram
    recoveryLegalTermResourceHandoffLoweringFuel
    recoveryLegalTermDescriptionChainFuel

def recoveryLegalTermWireLoweringBits
    (inputLength input : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryLegalTermResourceHandoffLoweringBits input)
      (recoveryLegalTermResourceChainBits inputLength
        (recoveryLegalTermResourceStoredHandoff input)
        (recoveryLegalTermResourceExpectedArity input)
        (recoveryLegalTermResourceSummaryTree input) input
        (handoffSelectedWireCap
          (recoveryLegalTermResourceStoredHandoff input)))

def recoveryLegalTermDescriptionLoweringBits
    (inputLength input : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryLegalTermResourceHandoffLoweringBits input)
      (recoveryLegalTermResourceChainBits inputLength
        (recoveryLegalTermResourceStoredHandoff input)
        (recoveryLegalTermResourceExpectedArity input)
        (recoveryLegalTermResourceSummaryTree input) input
        (handoffSelectedDescriptionCap
          (recoveryLegalTermResourceStoredHandoff input)))

private theorem run_recoveryLegalTermWireLoweringProgram
    (inputLength input : ℕ) :
    runNPOracleProgram recoveryLegalTermWireLoweringProgram
        (recoveryLegalTermWireLoweringBits inputLength input)
        recoveryLegalTermWireLoweringFuel
        (initialNPOracleState inputLength input) =
      some (recoveryLegalTermWireLoweringOutput input) := by
  have hlength :
      natBitLength inputLength ≤
        recoveryLegalTermWireLoweringBits inputLength input :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤ recoveryLegalTermWireLoweringBits inputLength input :=
    (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hhandoffBits :
      recoveryLegalTermResourceHandoffLoweringBits input ≤
        recoveryLegalTermWireLoweringBits inputLength input :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hchainBits :
      recoveryLegalTermResourceChainBits inputLength
          (recoveryLegalTermResourceStoredHandoff input)
          (recoveryLegalTermResourceExpectedArity input)
          (recoveryLegalTermResourceSummaryTree input) input
          (handoffSelectedWireCap
            (recoveryLegalTermResourceStoredHandoff input)) ≤
        recoveryLegalTermWireLoweringBits inputLength input :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hhandoff :=
    run_bits_mono
      (run_recoveryLegalTermResourceHandoffLoweringProgram inputLength input)
      hhandoffBits
  have hchain :=
    run_bits_mono
      (run_recoveryLegalTermWireChainProgram inputLength
        (recoveryLegalTermResourceStoredHandoff input)
        (recoveryLegalTermResourceExpectedArity input)
        (recoveryLegalTermResourceSummaryTree input) input)
      hchainBits
  have hrun :=
    run_linkPrograms hpositive hlength hhandoff hchain
  simpa only [recoveryLegalTermWireLoweringProgram,
    recoveryLegalTermWireLoweringFuel, recoveryLegalTermWireLoweringOutput,
    recoveryLegalTermWireContext] using hrun

private theorem run_recoveryLegalTermDescriptionLoweringProgram
    (inputLength input : ℕ) :
    runNPOracleProgram recoveryLegalTermDescriptionLoweringProgram
        (recoveryLegalTermDescriptionLoweringBits inputLength input)
        recoveryLegalTermDescriptionLoweringFuel
        (initialNPOracleState inputLength input) =
      some (recoveryLegalTermDescriptionLoweringOutput input) := by
  have hlength :
      natBitLength inputLength ≤
        recoveryLegalTermDescriptionLoweringBits inputLength input :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤ recoveryLegalTermDescriptionLoweringBits inputLength input :=
    (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hhandoffBits :
      recoveryLegalTermResourceHandoffLoweringBits input ≤
        recoveryLegalTermDescriptionLoweringBits inputLength input :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hchainBits :
      recoveryLegalTermResourceChainBits inputLength
          (recoveryLegalTermResourceStoredHandoff input)
          (recoveryLegalTermResourceExpectedArity input)
          (recoveryLegalTermResourceSummaryTree input) input
          (handoffSelectedDescriptionCap
            (recoveryLegalTermResourceStoredHandoff input)) ≤
        recoveryLegalTermDescriptionLoweringBits inputLength input :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hhandoff :=
    run_bits_mono
      (run_recoveryLegalTermResourceHandoffLoweringProgram inputLength input)
      hhandoffBits
  have hchain :=
    run_bits_mono
      (run_recoveryLegalTermDescriptionChainProgram inputLength
        (recoveryLegalTermResourceStoredHandoff input)
        (recoveryLegalTermResourceExpectedArity input)
        (recoveryLegalTermResourceSummaryTree input) input)
      hchainBits
  have hrun :=
    run_linkPrograms hpositive hlength hhandoff hchain
  simpa only [recoveryLegalTermDescriptionLoweringProgram,
    recoveryLegalTermDescriptionLoweringFuel,
    recoveryLegalTermDescriptionLoweringOutput,
    recoveryLegalTermDescriptionContext] using hrun

/-! ### Discharging the validated-summary hypothesis of both resource passes

The tree consumed by the two passes is the circuit stage's own retained
`encodeBalancedList` of validator outputs.  If that stage rejected, the tree is
the zero sentinel and decodes to the empty list, so no projection ever reaches
a rejected term. -/

theorem recoveryLegalTermResourceExpectedArity_of_circuitStage
    {inputLength handoff input : ℕ}
    (hstage :
      recoveryLegalTermResourceCircuitStage input =
        recoveryLegalTermCircuitStageOutput inputLength handoff) :
    recoveryLegalTermResourceExpectedArity input =
      recoveryLegalTermCircuitArity
        (recoveryLegalTermCircuitContext handoff) := by
  simp [recoveryLegalTermResourceExpectedArity,
    recoveryLegalTermResourceExpectedRest, hstage,
    recoveryLegalTermCircuitStageOutput,
    recoveryLegalTermCoefficientStageOutput,
    recoveryLegalTermCircuitArity, recoveryLegalTermCircuitContext,
    recoveryLegalTermBoundExpectedArity]

theorem recoveryLegalTermResourceSummaryTree_of_circuitStage
    {inputLength handoff input : ℕ}
    (hstage :
      recoveryLegalTermResourceCircuitStage input =
        recoveryLegalTermCircuitStageOutput inputLength handoff) :
    recoveryLegalTermResourceSummaryTree input =
      (Nat.unpair
        (Nat.unpair
          (recoveryLegalTermCircuitListOutput
            (recoveryLegalTermCircuitContext handoff)
            (recoveryLegalTermCoefficientMappedCode inputLength
              handoff))).2).1 := by
  simp [recoveryLegalTermResourceSummaryTree, hstage,
    recoveryLegalTermCircuitStageOutput]

private theorem balancedValidationMapCodes_zero :
    balancedValidationMapCodes 0 = [] := by
  have hencode : encodeBalancedList ([] : List ℕ) = 0 := by
    rw [encodeBalancedList]
  have hzero : decodeBalancedList 0 = some ([] : List ℕ) := by
    rw [← hencode]
    exact decodeBalancedList_encode ([] : List ℕ)
  rw [balancedValidationMapCodes, hzero, Option.getD_some]

private def RecoveryLegalTermResourceValidated (input : ℕ) : Prop :=
  ∀ summary ∈
      balancedValidationMapCodes
        (recoveryLegalTermResourceSummaryTree input),
    ∃ request,
      summary =
        normalizedCircuitValidationOutput
          (recoveryLegalTermResourceExpectedArity input) request ∧
        normalizedCircuitValidationOutput
          (recoveryLegalTermResourceExpectedArity input) request ≠ 0

theorem recoveryLegalTermResourceSummaries_validated
    {inputLength handoff input summary : ℕ}
    (hstage :
      recoveryLegalTermResourceCircuitStage input =
        recoveryLegalTermCircuitStageOutput inputLength handoff)
    (hsummary :
      summary ∈
        balancedValidationMapCodes
          (recoveryLegalTermResourceSummaryTree input)) :
    ∃ request,
      summary =
        normalizedCircuitValidationOutput
          (recoveryLegalTermResourceExpectedArity input) request ∧
        normalizedCircuitValidationOutput
            (recoveryLegalTermResourceExpectedArity input) request ≠ 0 := by
  rw [recoveryLegalTermResourceSummaryTree_of_circuitStage hstage] at hsummary
  rw [recoveryLegalTermResourceExpectedArity_of_circuitStage hstage]
  by_cases hreject :
      recoveryLegalTermCircuitListOutput
          (recoveryLegalTermCircuitContext handoff)
          (recoveryLegalTermCoefficientMappedCode inputLength handoff) = 0
  · rw [hreject] at hsummary
    simp [balancedValidationMapCodes_zero] at hsummary
  · obtain ⟨codes, hdecode, hall⟩ :=
      (recoveryLegalTermCircuitListOutput_ne_zero_iff
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff)).1
        hreject
    have hpayload :
        (Nat.unpair
          (recoveryLegalTermCircuitListOutput
            (recoveryLegalTermCircuitContext handoff)
            (recoveryLegalTermCoefficientMappedCode inputLength
              handoff))).2 =
          balancedValidationSummaryData
            (recoveryLegalTermCircuitContext handoff)
            (recoveryLegalTermCoefficientMappedCode inputLength handoff)
            recoveryLegalTermCircuitRequestOutput :=
      balancedValidationSummaryOutput_payload _ _ _ hreject
    have hcodes :
        balancedValidationMapCodes
            (recoveryLegalTermCoefficientMappedCode inputLength handoff) =
          codes := by
      rw [balancedValidationMapCodes, hdecode, Option.getD_some]
    have htree :
        (Nat.unpair
          (Nat.unpair
            (recoveryLegalTermCircuitListOutput
              (recoveryLegalTermCircuitContext handoff)
              (recoveryLegalTermCoefficientMappedCode inputLength
                handoff))).2).1 =
          encodeBalancedList
            (codes.map
              (fun code =>
                recoveryLegalTermCircuitCallOutput
                  (recoveryLegalTermCircuitContext handoff) code)) := by
      rw [hpayload]
      simp [balancedValidationSummaryData, balancedValidationMapOutputs,
        balancedValidationMapRequests, hcodes, List.map_map,
        Function.comp_def, recoveryLegalTermCircuitRequestOutput,
        nativeInputRequest]
    rw [htree, balancedValidationMapCodes, decodeBalancedList_encode,
      Option.getD_some] at hsummary
    obtain ⟨code, hcode, hvalue⟩ := List.mem_map.mp hsummary
    refine
      ⟨recoveryLegalTermCircuitRequest
        (recoveryLegalTermCircuitContext handoff) code, ?_, ?_⟩
    · rw [← hvalue]
      rfl
    · have hnonzero := hall code hcode
      simpa only [recoveryLegalTermCircuitCallOutput] using hnonzero

theorem recoveryLegalTermResourceArity_wireContext (input : ℕ) :
    recoveryLegalTermResourceArity (recoveryLegalTermWireContext input) =
      recoveryLegalTermResourceExpectedArity input := by
  simp [recoveryLegalTermResourceArity, recoveryLegalTermWireContext]

theorem recoveryLegalTermResourceArity_descriptionContext
    (input : ℕ) :
    recoveryLegalTermResourceArity
        (recoveryLegalTermDescriptionContext input) =
      recoveryLegalTermResourceExpectedArity input := by
  simp [recoveryLegalTermResourceArity, recoveryLegalTermDescriptionContext]

theorem recoveryLegalTermResourceValidated_of_circuitStage
    {inputLength handoff input : ℕ}
    (hstage :
      recoveryLegalTermResourceCircuitStage input =
        recoveryLegalTermCircuitStageOutput inputLength handoff) :
    RecoveryLegalTermResourceValidated input := fun _ hsummary =>
  recoveryLegalTermResourceSummaries_validated hstage hsummary

theorem recoveryLegalTermResourceSummaryTree_zero :
    recoveryLegalTermResourceSummaryTree 0 = 0 := by
  simp [recoveryLegalTermResourceSummaryTree,
    recoveryLegalTermResourceCircuitStage]

theorem recoveryLegalTermResourceValidated_zero :
    RecoveryLegalTermResourceValidated 0 := by
  intro summary hsummary
  rw [recoveryLegalTermResourceSummaryTree_zero,
    balancedValidationMapCodes_zero] at hsummary
  exact absurd hsummary (List.not_mem_nil)

theorem recoveryLegalTermWireResource_runnable
    {input : ℕ} (hvalidated : RecoveryLegalTermResourceValidated input) :
    ∀ summary ∈
        balancedValidationMapCodes
          (recoveryLegalTermResourceSummaryTree input),
      runNPOracleProgram normalizedCircuitResourceProgram
          (normalizedCircuitResourceBits
            (recoveryLegalTermResourceArity
              (recoveryLegalTermWireContext input)) summary)
          (normalizedCircuitResourceFuel
            (recoveryLegalTermResourceArity
              (recoveryLegalTermWireContext input)) summary)
          (initialNPOracleState
            (recoveryLegalTermResourceArity
              (recoveryLegalTermWireContext input)) summary) =
        some (normalizedCircuitResourceMetric summary) := by
  intro summary hsummary
  obtain ⟨request, hrequest, hnonzero⟩ := hvalidated summary hsummary
  rw [recoveryLegalTermResourceArity_wireContext, hrequest]
  exact run_normalizedCircuitResourceProgram_of_validation
    (recoveryLegalTermResourceExpectedArity input) request hnonzero

theorem recoveryLegalTermDescriptionResource_runnable
    {input : ℕ} (hvalidated : RecoveryLegalTermResourceValidated input) :
    ∀ summary ∈
        balancedValidationMapCodes
          (recoveryLegalTermResourceSummaryTree input),
      runNPOracleProgram normalizedCircuitDescriptionProgram
          (normalizedCircuitDescriptionBits
            (recoveryLegalTermResourceArity
              (recoveryLegalTermDescriptionContext input)) summary)
          (normalizedCircuitDescriptionFuel
            (recoveryLegalTermResourceArity
              (recoveryLegalTermDescriptionContext input)) summary)
          (initialNPOracleState
            (recoveryLegalTermResourceArity
              (recoveryLegalTermDescriptionContext input)) summary) =
        some
          (normalizedCircuitDescriptionMetric
            (recoveryLegalTermResourceArity
              (recoveryLegalTermDescriptionContext input)) summary) := by
  intro summary hsummary
  obtain ⟨request, hrequest, hnonzero⟩ := hvalidated summary hsummary
  rw [recoveryLegalTermResourceArity_descriptionContext, hrequest]
  exact run_normalizedCircuitDescriptionProgram_of_validation
    (recoveryLegalTermResourceExpectedArity input) request hnonzero

/-! ### The two gated resource stages -/

def recoveryLegalTermWireStageValue (input : ℕ) : ℕ :=
  recoveryLegalTermWireListOutput (recoveryLegalTermWireContext input)
    (recoveryLegalTermResourceSummaryTree input)

def recoveryLegalTermDescriptionStageValue (input : ℕ) : ℕ :=
  recoveryLegalTermDescriptionListOutput
    (recoveryLegalTermDescriptionContext input)
    (recoveryLegalTermResourceSummaryTree input)

def recoveryLegalTermWireGateOutput (input : ℕ) : ℕ :=
  recoveryLegalSumFlagGateOutput
    (Nat.pair (recoveryLegalTermWireStageValue input) input)

def recoveryLegalTermDescriptionGateOutput (input : ℕ) : ℕ :=
  recoveryLegalSumFlagGateOutput
    (Nat.pair (recoveryLegalTermDescriptionStageValue input) input)

theorem recoveryLegalTermWireGateOutput_eq (input : ℕ) :
    recoveryLegalTermWireGateOutput input =
      if recoveryLegalTermWireStageValue input = 0 then 0 else input := by
  simp [recoveryLegalTermWireGateOutput, recoveryLegalSumFlagGateOutput,
    recoveryBoundedContextGateOutput]

theorem recoveryLegalTermDescriptionGateOutput_eq (input : ℕ) :
    recoveryLegalTermDescriptionGateOutput input =
      if recoveryLegalTermDescriptionStageValue input = 0 then 0
      else input := by
  simp [recoveryLegalTermDescriptionGateOutput,
    recoveryLegalSumFlagGateOutput, recoveryBoundedContextGateOutput]

def recoveryLegalTermWireStageProgram : NPOracleProgram :=
  linkPrograms recoveryLegalTermWireLoweringProgram <|
    linkPrograms
      (preserveRightProgram
        (nativeCallProgram recoveryLegalTermWireListProgram))
      recoveryBoundedContextGateProgram

@[simp] theorem recoveryLegalTermWireStageProgram_oracleFree :
    OracleFree recoveryLegalTermWireStageProgram :=
  oracleFree_linkPrograms recoveryLegalTermWireLoweringProgram_oracleFree <|
    oracleFree_linkPrograms
      (preserveRightProgram_oracleFree
        (nativeCallProgram recoveryLegalTermWireListProgram)
        (nativeCallProgram_oracleFree
          recoveryLegalTermWireListProgram_oracleFree))
      recoveryBoundedContextGateProgram_oracleFree

def recoveryLegalTermDescriptionStageProgram : NPOracleProgram :=
  linkPrograms recoveryLegalTermDescriptionLoweringProgram <|
    linkPrograms
      (preserveRightProgram
        (nativeCallProgram recoveryLegalTermDescriptionListProgram))
      recoveryBoundedContextGateProgram

@[simp] theorem recoveryLegalTermDescriptionStageProgram_oracleFree :
    OracleFree recoveryLegalTermDescriptionStageProgram :=
  oracleFree_linkPrograms
    recoveryLegalTermDescriptionLoweringProgram_oracleFree <|
      oracleFree_linkPrograms
        (preserveRightProgram_oracleFree
          (nativeCallProgram recoveryLegalTermDescriptionListProgram)
          (nativeCallProgram_oracleFree
            recoveryLegalTermDescriptionListProgram_oracleFree))
        recoveryBoundedContextGateProgram_oracleFree

def recoveryLegalTermWireStageFuel (input : ℕ) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram
        (nativeCallProgram recoveryLegalTermWireListProgram))
      recoveryBoundedContextGateProgram)
    recoveryLegalTermWireLoweringFuel <|
      linkFuel recoveryBoundedContextGateProgram
        (preserveRightFuel
          (nativeCallFuel recoveryLegalTermWireListProgram
            (recoveryLegalTermWireListFuel
              (recoveryLegalTermWireContext input)
              (recoveryLegalTermResourceSummaryTree input))
            (recoveryLegalTermWireContext input)
            (recoveryLegalTermResourceSummaryTree input)))
        4

def recoveryLegalTermDescriptionStageFuel (input : ℕ) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram
        (nativeCallProgram recoveryLegalTermDescriptionListProgram))
      recoveryBoundedContextGateProgram)
    recoveryLegalTermDescriptionLoweringFuel <|
      linkFuel recoveryBoundedContextGateProgram
        (preserveRightFuel
          (nativeCallFuel recoveryLegalTermDescriptionListProgram
            (recoveryLegalTermDescriptionListFuel
              (recoveryLegalTermDescriptionContext input)
              (recoveryLegalTermResourceSummaryTree input))
            (recoveryLegalTermDescriptionContext input)
            (recoveryLegalTermResourceSummaryTree input)))
        4

def recoveryLegalTermWireStageBits
    (inputLength input : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryLegalTermWireLoweringBits inputLength input) <|
      max
        (preserveRightBits
          (nativeCallBits inputLength (recoveryLegalTermWireContext input)
            (recoveryLegalTermResourceSummaryTree input)
            (recoveryLegalTermWireStageValue input)
            (recoveryLegalTermWireListBits
              (recoveryLegalTermWireContext input)
              (recoveryLegalTermResourceSummaryTree input)))
          (nativeInputRequest (recoveryLegalTermWireContext input)
            (recoveryLegalTermResourceSummaryTree input))
          input (recoveryLegalTermWireStageValue input))
        (recoveryLegalSumFlagGateBits
          (Nat.pair (recoveryLegalTermWireStageValue input) input))

def recoveryLegalTermDescriptionStageBits
    (inputLength input : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryLegalTermDescriptionLoweringBits inputLength input) <|
      max
        (preserveRightBits
          (nativeCallBits inputLength
            (recoveryLegalTermDescriptionContext input)
            (recoveryLegalTermResourceSummaryTree input)
            (recoveryLegalTermDescriptionStageValue input)
            (recoveryLegalTermDescriptionListBits
              (recoveryLegalTermDescriptionContext input)
              (recoveryLegalTermResourceSummaryTree input)))
          (nativeInputRequest (recoveryLegalTermDescriptionContext input)
            (recoveryLegalTermResourceSummaryTree input))
          input (recoveryLegalTermDescriptionStageValue input))
        (recoveryLegalSumFlagGateBits
          (Nat.pair (recoveryLegalTermDescriptionStageValue input) input))

private theorem run_recoveryLegalTermWireStageProgram
    {inputLength input : ℕ}
    (hvalidated : RecoveryLegalTermResourceValidated input) :
    runNPOracleProgram recoveryLegalTermWireStageProgram
        (recoveryLegalTermWireStageBits inputLength input)
        (recoveryLegalTermWireStageFuel input)
        (initialNPOracleState inputLength input) =
      some (recoveryLegalTermWireGateOutput input) := by
  have hlength :
      natBitLength inputLength ≤
        recoveryLegalTermWireStageBits inputLength input :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤ recoveryLegalTermWireStageBits inputLength input :=
    (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hloweringBits :
      recoveryLegalTermWireLoweringBits inputLength input ≤
        recoveryLegalTermWireStageBits inputLength input :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      preserveRightBits
          (nativeCallBits inputLength (recoveryLegalTermWireContext input)
            (recoveryLegalTermResourceSummaryTree input)
            (recoveryLegalTermWireStageValue input)
            (recoveryLegalTermWireListBits
              (recoveryLegalTermWireContext input)
              (recoveryLegalTermResourceSummaryTree input)))
          (nativeInputRequest (recoveryLegalTermWireContext input)
            (recoveryLegalTermResourceSummaryTree input))
          input (recoveryLegalTermWireStageValue input) ≤
        recoveryLegalTermWireStageBits inputLength input :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hgateBits :
      recoveryLegalSumFlagGateBits
          (Nat.pair (recoveryLegalTermWireStageValue input) input) ≤
        recoveryLegalTermWireStageBits inputLength input :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hlowering :=
    run_bits_mono
      (run_recoveryLegalTermWireLoweringProgram inputLength input)
      hloweringBits
  have hcall :=
    run_bits_mono
      (run_preserveRightProgram
        (nativeCallProgram recoveryLegalTermWireListProgram) inputLength
        (nativeCallBits inputLength (recoveryLegalTermWireContext input)
          (recoveryLegalTermResourceSummaryTree input)
          (recoveryLegalTermWireStageValue input)
          (recoveryLegalTermWireListBits
            (recoveryLegalTermWireContext input)
            (recoveryLegalTermResourceSummaryTree input)))
        (nativeCallFuel recoveryLegalTermWireListProgram
          (recoveryLegalTermWireListFuel
            (recoveryLegalTermWireContext input)
            (recoveryLegalTermResourceSummaryTree input))
          (recoveryLegalTermWireContext input)
          (recoveryLegalTermResourceSummaryTree input))
        (nativeInputRequest (recoveryLegalTermWireContext input)
          (recoveryLegalTermResourceSummaryTree input))
        input (recoveryLegalTermWireStageValue input)
        (run_nativeCallProgram recoveryLegalTermWireListProgram inputLength
          (recoveryLegalTermWireContext input)
          (recoveryLegalTermResourceSummaryTree input)
          (recoveryLegalTermWireStageValue input)
          (recoveryLegalTermWireListBits
            (recoveryLegalTermWireContext input)
            (recoveryLegalTermResourceSummaryTree input))
          (recoveryLegalTermWireListFuel
            (recoveryLegalTermWireContext input)
            (recoveryLegalTermResourceSummaryTree input))
          (run_recoveryLegalTermWireListProgram
            (recoveryLegalTermWireContext input)
            (recoveryLegalTermResourceSummaryTree input)
            (recoveryLegalTermWireResource_runnable hvalidated))))
      hcallBits
  have hgate :=
    run_bits_mono
      (run_recoveryLegalSumFlagGateProgram inputLength
        (Nat.pair (recoveryLegalTermWireStageValue input) input))
      hgateBits
  have htail := run_linkPrograms hpositive hlength hcall hgate
  have hrun := run_linkPrograms hpositive hlength hlowering htail
  simpa only [recoveryLegalTermWireStageProgram,
    recoveryLegalTermWireStageFuel, recoveryLegalTermWireGateOutput,
    recoveryLegalTermWireLoweringOutput] using hrun

private theorem run_recoveryLegalTermDescriptionStageProgram
    {inputLength input : ℕ}
    (hvalidated : RecoveryLegalTermResourceValidated input) :
    runNPOracleProgram recoveryLegalTermDescriptionStageProgram
        (recoveryLegalTermDescriptionStageBits inputLength input)
        (recoveryLegalTermDescriptionStageFuel input)
        (initialNPOracleState inputLength input) =
      some (recoveryLegalTermDescriptionGateOutput input) := by
  have hlength :
      natBitLength inputLength ≤
        recoveryLegalTermDescriptionStageBits inputLength input :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤ recoveryLegalTermDescriptionStageBits inputLength input :=
    (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hloweringBits :
      recoveryLegalTermDescriptionLoweringBits inputLength input ≤
        recoveryLegalTermDescriptionStageBits inputLength input :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      preserveRightBits
          (nativeCallBits inputLength
            (recoveryLegalTermDescriptionContext input)
            (recoveryLegalTermResourceSummaryTree input)
            (recoveryLegalTermDescriptionStageValue input)
            (recoveryLegalTermDescriptionListBits
              (recoveryLegalTermDescriptionContext input)
              (recoveryLegalTermResourceSummaryTree input)))
          (nativeInputRequest (recoveryLegalTermDescriptionContext input)
            (recoveryLegalTermResourceSummaryTree input))
          input (recoveryLegalTermDescriptionStageValue input) ≤
        recoveryLegalTermDescriptionStageBits inputLength input :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hgateBits :
      recoveryLegalSumFlagGateBits
          (Nat.pair (recoveryLegalTermDescriptionStageValue input) input) ≤
        recoveryLegalTermDescriptionStageBits inputLength input :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hlowering :=
    run_bits_mono
      (run_recoveryLegalTermDescriptionLoweringProgram inputLength input)
      hloweringBits
  have hcall :=
    run_bits_mono
      (run_preserveRightProgram
        (nativeCallProgram recoveryLegalTermDescriptionListProgram)
        inputLength
        (nativeCallBits inputLength
          (recoveryLegalTermDescriptionContext input)
          (recoveryLegalTermResourceSummaryTree input)
          (recoveryLegalTermDescriptionStageValue input)
          (recoveryLegalTermDescriptionListBits
            (recoveryLegalTermDescriptionContext input)
            (recoveryLegalTermResourceSummaryTree input)))
        (nativeCallFuel recoveryLegalTermDescriptionListProgram
          (recoveryLegalTermDescriptionListFuel
            (recoveryLegalTermDescriptionContext input)
            (recoveryLegalTermResourceSummaryTree input))
          (recoveryLegalTermDescriptionContext input)
          (recoveryLegalTermResourceSummaryTree input))
        (nativeInputRequest (recoveryLegalTermDescriptionContext input)
          (recoveryLegalTermResourceSummaryTree input))
        input (recoveryLegalTermDescriptionStageValue input)
        (run_nativeCallProgram recoveryLegalTermDescriptionListProgram
          inputLength (recoveryLegalTermDescriptionContext input)
          (recoveryLegalTermResourceSummaryTree input)
          (recoveryLegalTermDescriptionStageValue input)
          (recoveryLegalTermDescriptionListBits
            (recoveryLegalTermDescriptionContext input)
            (recoveryLegalTermResourceSummaryTree input))
          (recoveryLegalTermDescriptionListFuel
            (recoveryLegalTermDescriptionContext input)
            (recoveryLegalTermResourceSummaryTree input))
          (run_recoveryLegalTermDescriptionListProgram
            (recoveryLegalTermDescriptionContext input)
            (recoveryLegalTermResourceSummaryTree input)
            (recoveryLegalTermDescriptionResource_runnable hvalidated))))
      hcallBits
  have hgate :=
    run_bits_mono
      (run_recoveryLegalSumFlagGateProgram inputLength
        (Nat.pair (recoveryLegalTermDescriptionStageValue input) input))
      hgateBits
  have htail := run_linkPrograms hpositive hlength hcall hgate
  have hrun := run_linkPrograms hpositive hlength hlowering htail
  simpa only [recoveryLegalTermDescriptionStageProgram,
    recoveryLegalTermDescriptionStageFuel,
    recoveryLegalTermDescriptionGateOutput,
    recoveryLegalTermDescriptionLoweringOutput] using hrun

/-! ### The two resource gates inside the legal-sum envelope

Both gates run on the mass stage's own output, so the retained context reaching
the existing finalization chain is unchanged.  A rejected wire pass replaces
that context with the zero sentinel, and the description pass then sees an
empty summary tree, so no projection of a sentinel ever occurs. -/

def recoveryLegalSumMassStageOutput (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalTermMassComparisonOutput inputLength
    (recoveryLegalTermBitCapStageOutput
      (recoveryLegalTermCircuitStageOutput inputLength handoff))

theorem recoveryLegalTermResourceCircuitStage_massStage
    (inputLength handoff : ℕ) :
    recoveryLegalTermResourceCircuitStage
        (recoveryLegalSumMassStageOutput inputLength handoff) =
      recoveryLegalTermCircuitStageOutput inputLength handoff := by
  simp only [recoveryLegalSumMassStageOutput,
    recoveryLegalTermResourceCircuitStage,
    recoveryLegalTermMassComparisonOutput, Nat.unpair_pair,
    recoveryLegalTermMassComparisonFinalContext_eq,
    recoveryLegalTermMassFinalContext_bitCapStageOutput]

def recoveryLegalSumWireGateOutput (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalTermWireGateOutput
    (recoveryLegalSumMassStageOutput inputLength handoff)

def recoveryLegalSumDescriptionGateOutput
    (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalTermDescriptionGateOutput
    (recoveryLegalSumWireGateOutput inputLength handoff)

theorem recoveryLegalSumMassStage_validated
    (inputLength handoff : ℕ) :
    RecoveryLegalTermResourceValidated
      (recoveryLegalSumMassStageOutput inputLength handoff) :=
  recoveryLegalTermResourceValidated_of_circuitStage
    (recoveryLegalTermResourceCircuitStage_massStage inputLength handoff)

theorem recoveryLegalSumWireGate_validated
    (inputLength handoff : ℕ) :
    RecoveryLegalTermResourceValidated
      (recoveryLegalSumWireGateOutput inputLength handoff) := by
  rw [recoveryLegalSumWireGateOutput, recoveryLegalTermWireGateOutput_eq]
  by_cases hreject :
      recoveryLegalTermWireStageValue
        (recoveryLegalSumMassStageOutput inputLength handoff) = 0
  · rw [if_pos hreject]
    exact recoveryLegalTermResourceValidated_zero
  · rw [if_neg hreject]
    exact recoveryLegalSumMassStage_validated inputLength handoff

def recoveryLegalSumResourceStageProgram : NPOracleProgram :=
  linkPrograms recoveryLegalTermWireStageProgram
    recoveryLegalTermDescriptionStageProgram

@[simp] theorem recoveryLegalSumResourceStageProgram_oracleFree :
    OracleFree recoveryLegalSumResourceStageProgram :=
  oracleFree_linkPrograms recoveryLegalTermWireStageProgram_oracleFree
    recoveryLegalTermDescriptionStageProgram_oracleFree

def recoveryLegalSumResourceStageFuel
    (inputLength handoff : ℕ) : ℕ :=
  linkFuel recoveryLegalTermDescriptionStageProgram
    (recoveryLegalTermWireStageFuel
      (recoveryLegalSumMassStageOutput inputLength handoff))
    (recoveryLegalTermDescriptionStageFuel
      (recoveryLegalSumWireGateOutput inputLength handoff))

def recoveryLegalSumResourceStageBits
    (inputLength handoff : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max
      (recoveryLegalTermWireStageBits inputLength
        (recoveryLegalSumMassStageOutput inputLength handoff))
      (recoveryLegalTermDescriptionStageBits inputLength
        (recoveryLegalSumWireGateOutput inputLength handoff))

private theorem run_recoveryLegalSumResourceStageProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumResourceStageProgram
        (recoveryLegalSumResourceStageBits inputLength handoff)
        (recoveryLegalSumResourceStageFuel inputLength handoff)
        (initialNPOracleState inputLength
          (recoveryLegalSumMassStageOutput inputLength handoff)) =
      some (recoveryLegalSumDescriptionGateOutput inputLength handoff) := by
  have hlength :
      natBitLength inputLength ≤
        recoveryLegalSumResourceStageBits inputLength handoff :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤ recoveryLegalSumResourceStageBits inputLength handoff :=
    (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hwireBits :
      recoveryLegalTermWireStageBits inputLength
          (recoveryLegalSumMassStageOutput inputLength handoff) ≤
        recoveryLegalSumResourceStageBits inputLength handoff :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hdescriptionBits :
      recoveryLegalTermDescriptionStageBits inputLength
          (recoveryLegalSumWireGateOutput inputLength handoff) ≤
        recoveryLegalSumResourceStageBits inputLength handoff :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hwire :=
    run_bits_mono
      (run_recoveryLegalTermWireStageProgram (inputLength := inputLength)
        (recoveryLegalSumMassStage_validated inputLength handoff))
      hwireBits
  have hdescription :=
    run_bits_mono
      (run_recoveryLegalTermDescriptionStageProgram
        (inputLength := inputLength)
        (recoveryLegalSumWireGate_validated inputLength handoff))
      hdescriptionBits
  have hrun := run_linkPrograms hpositive hlength hwire hdescription
  simpa only [recoveryLegalSumResourceStageProgram,
    recoveryLegalSumResourceStageFuel, recoveryLegalSumWireGateOutput,
    recoveryLegalSumDescriptionGateOutput] using hrun

def recoveryLegalSumMassGateOutput
    (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalSumFlagGateOutput
    (recoveryLegalSumDescriptionGateOutput inputLength handoff)

def recoveryLegalSumBitCapGateOutput
    (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalSumFlagGateOutput
    (recoveryLegalSumMassGateOutput inputLength handoff)

def recoveryLegalSumCircuitGateOutput
    (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalSumFlagGateOutput
    (recoveryLegalSumBitCapGateOutput inputLength handoff)

def recoveryLegalSumCoefficientGateOutput
    (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalSumFlagGateOutput
    (recoveryLegalSumCircuitGateOutput inputLength handoff)

def recoveryLegalSumTermsGateOutput
    (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalSumFlagGateOutput
    (recoveryLegalSumCoefficientGateOutput inputLength handoff)

def recoveryLegalSumArityGateOutput
    (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalSumFlagGateOutput
    (recoveryLegalSumTermsGateOutput inputLength handoff)

def recoveryLegalSumQGateOutput
    (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalSumFlagGateOutput
    (recoveryLegalSumArityGateOutput inputLength handoff)

def recoveryLegalSumTupleGateOutput
    (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalSumFlagGateOutput
    (recoveryLegalSumQGateOutput inputLength handoff)

def recoveryLegalSumModeGateOutput
    (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalSumFlagGateOutput
    (recoveryLegalSumTupleGateOutput inputLength handoff)

def recoveryLegalSumHandoffProjectionOutput (input : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair input).2).2).2

def recoveryLegalSumHandoffProjectionProgram : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .unpairRight 0 0 2
  , .unpairRight 0 0 3
  , .halt 0
  ]

@[simp] theorem
    recoveryLegalSumHandoffProjectionProgram_oracleFree :
    OracleFree recoveryLegalSumHandoffProjectionProgram := by
  rfl

def recoveryLegalSumHandoffProjectionValues
    (inputLength input : ℕ) : List ℕ :=
  [ inputLength
  , input
  , (Nat.unpair input).2
  , (Nat.unpair (Nat.unpair input).2).2
  , recoveryLegalSumHandoffProjectionOutput input
  ]

def recoveryLegalSumHandoffProjectionBits
    (inputLength input : ℕ) : ℕ :=
  natBitLength <|
    (recoveryLegalSumHandoffProjectionValues inputLength input).foldr max 0

theorem recoveryLegalSumHandoffProjectionValue_bits
    {inputLength input value : ℕ}
    (hvalue :
      value ∈
        recoveryLegalSumHandoffProjectionValues inputLength input) :
    natBitLength value ≤
      recoveryLegalSumHandoffProjectionBits inputLength input := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

private theorem run_recoveryLegalSumHandoffProjectionProgram
    (inputLength input : ℕ) :
    runNPOracleProgram recoveryLegalSumHandoffProjectionProgram
        (recoveryLegalSumHandoffProjectionBits inputLength input) 4
        (initialNPOracleState inputLength input) =
      some (recoveryLegalSumHandoffProjectionOutput input) := by
  let tail₀ := (Nat.unpair input).2
  let tail₁ := (Nat.unpair tail₀).2
  let output := (Nat.unpair tail₁).2
  have htail₀ :
      natBitLength tail₀ ≤
        recoveryLegalSumHandoffProjectionBits inputLength input := by
    apply recoveryLegalSumHandoffProjectionValue_bits
    simp [recoveryLegalSumHandoffProjectionValues, tail₀]
  have htail₁ :
      natBitLength tail₁ ≤
        recoveryLegalSumHandoffProjectionBits inputLength input := by
    apply recoveryLegalSumHandoffProjectionValue_bits
    simp [recoveryLegalSumHandoffProjectionValues, tail₀, tail₁]
  have houtput :
      natBitLength output ≤
        recoveryLegalSumHandoffProjectionBits inputLength input := by
    apply recoveryLegalSumHandoffProjectionValue_bits
    simp [recoveryLegalSumHandoffProjectionValues,
      recoveryLegalSumHandoffProjectionOutput, tail₀, tail₁, output]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := tail₀)
    (by rfl) rfl
    (by simp [initialNPOracleState, tail₀])
    htail₀]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := tail₁)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tail₀, tail₁])
    htail₁]
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairRight_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tail₁, output])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

def recoveryLegalSumEnvelopeOutput
    (inputLength handoff : ℕ) : ℕ :=
  recoveryLegalSumHandoffProjectionOutput
    (recoveryLegalSumModeGateOutput inputLength handoff)

def recoveryLegalSumPostBitCapFinalizationProgram :
    NPOracleProgram :=
  linkPrograms recoveryBoundedContextGateProgram <|
    linkPrograms recoveryBoundedContextGateProgram <|
      linkPrograms recoveryBoundedContextGateProgram <|
        linkPrograms recoveryBoundedContextGateProgram <|
          linkPrograms recoveryBoundedContextGateProgram <|
            linkPrograms recoveryBoundedContextGateProgram <|
              linkPrograms recoveryBoundedContextGateProgram
                recoveryLegalSumHandoffProjectionProgram

@[simp] theorem
    recoveryLegalSumPostBitCapFinalizationProgram_oracleFree :
    OracleFree recoveryLegalSumPostBitCapFinalizationProgram := by
  exact oracleFree_linkPrograms
    recoveryBoundedContextGateProgram_oracleFree <|
      oracleFree_linkPrograms recoveryBoundedContextGateProgram_oracleFree <|
        oracleFree_linkPrograms
          recoveryBoundedContextGateProgram_oracleFree <|
            oracleFree_linkPrograms
              recoveryBoundedContextGateProgram_oracleFree <|
                oracleFree_linkPrograms
                  recoveryBoundedContextGateProgram_oracleFree <|
                    oracleFree_linkPrograms
                      recoveryBoundedContextGateProgram_oracleFree
                      <| oracleFree_linkPrograms
                    recoveryBoundedContextGateProgram_oracleFree
                    recoveryLegalSumHandoffProjectionProgram_oracleFree

def recoveryLegalSumPostBitCapFinalizationFuel : ℕ :=
  linkFuel
    (linkPrograms recoveryBoundedContextGateProgram <|
      linkPrograms recoveryBoundedContextGateProgram <|
        linkPrograms recoveryBoundedContextGateProgram <|
          linkPrograms recoveryBoundedContextGateProgram <|
            linkPrograms recoveryBoundedContextGateProgram <|
              linkPrograms recoveryBoundedContextGateProgram
                recoveryLegalSumHandoffProjectionProgram)
    4 <|
      linkFuel
        (linkPrograms recoveryBoundedContextGateProgram <|
          linkPrograms recoveryBoundedContextGateProgram <|
            linkPrograms recoveryBoundedContextGateProgram <|
              linkPrograms recoveryBoundedContextGateProgram <|
                linkPrograms recoveryBoundedContextGateProgram
                  recoveryLegalSumHandoffProjectionProgram)
        4 <|
          linkFuel
            (linkPrograms recoveryBoundedContextGateProgram <|
              linkPrograms recoveryBoundedContextGateProgram <|
                linkPrograms recoveryBoundedContextGateProgram <|
                  linkPrograms recoveryBoundedContextGateProgram
                    recoveryLegalSumHandoffProjectionProgram)
            4 <|
              linkFuel
                (linkPrograms recoveryBoundedContextGateProgram <|
                  linkPrograms recoveryBoundedContextGateProgram <|
                    linkPrograms recoveryBoundedContextGateProgram
                      recoveryLegalSumHandoffProjectionProgram)
                4 <|
                  linkFuel
                    (linkPrograms recoveryBoundedContextGateProgram <|
                      linkPrograms recoveryBoundedContextGateProgram
                        recoveryLegalSumHandoffProjectionProgram)
                    4 <|
                      linkFuel
                        (linkPrograms recoveryBoundedContextGateProgram
                          recoveryLegalSumHandoffProjectionProgram)
                        4 <|
                          linkFuel recoveryLegalSumHandoffProjectionProgram
                            4 4

def recoveryLegalSumFinalizationProgram : NPOracleProgram :=
  linkPrograms recoveryBoundedContextGateProgram <|
    linkPrograms recoveryBoundedContextGateProgram
      recoveryLegalSumPostBitCapFinalizationProgram

@[simp] theorem recoveryLegalSumFinalizationProgram_oracleFree :
    OracleFree recoveryLegalSumFinalizationProgram :=
  oracleFree_linkPrograms recoveryBoundedContextGateProgram_oracleFree
    (oracleFree_linkPrograms recoveryBoundedContextGateProgram_oracleFree
      recoveryLegalSumPostBitCapFinalizationProgram_oracleFree)

def recoveryLegalSumFinalizationFuel : ℕ :=
  linkFuel
    (linkPrograms recoveryBoundedContextGateProgram
      recoveryLegalSumPostBitCapFinalizationProgram)
    4 <| linkFuel recoveryLegalSumPostBitCapFinalizationProgram 4
      recoveryLegalSumPostBitCapFinalizationFuel

def recoveryLegalSumFinalizationStageBits
    (inputLength handoff : ℕ) : List ℕ :=
  [ natBitLength inputLength
  , recoveryLegalSumFlagGateBits
      (recoveryLegalSumDescriptionGateOutput inputLength handoff)
  , recoveryLegalSumFlagGateBits
      (recoveryLegalSumMassGateOutput inputLength handoff)
  , recoveryLegalSumFlagGateBits
      (recoveryLegalSumBitCapGateOutput inputLength handoff)
  , recoveryLegalSumFlagGateBits
      (recoveryLegalSumCircuitGateOutput inputLength handoff)
  , recoveryLegalSumFlagGateBits
      (recoveryLegalSumCoefficientGateOutput inputLength handoff)
  , recoveryLegalSumFlagGateBits
      (recoveryLegalSumTermsGateOutput inputLength handoff)
  , recoveryLegalSumFlagGateBits
      (recoveryLegalSumArityGateOutput inputLength handoff)
  , recoveryLegalSumFlagGateBits
      (recoveryLegalSumQGateOutput inputLength handoff)
  , recoveryLegalSumFlagGateBits
      (recoveryLegalSumTupleGateOutput inputLength handoff)
  , recoveryLegalSumHandoffProjectionBits inputLength
      (recoveryLegalSumModeGateOutput inputLength handoff)
  ]

def recoveryLegalSumFinalizationBits
    (inputLength handoff : ℕ) : ℕ :=
  (recoveryLegalSumFinalizationStageBits inputLength handoff).foldr max 0

theorem recoveryLegalSumFinalizationStage_bits
    {inputLength handoff bits : ℕ}
    (hbits :
      bits ∈ recoveryLegalSumFinalizationStageBits inputLength handoff) :
    bits ≤ recoveryLegalSumFinalizationBits inputLength handoff :=
  member_le_foldr_max hbits

private theorem run_recoveryLegalSumFinalizationProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumFinalizationProgram
        (recoveryLegalSumFinalizationBits inputLength handoff)
        recoveryLegalSumFinalizationFuel
        (initialNPOracleState inputLength
          (recoveryLegalSumDescriptionGateOutput inputLength handoff)) =
      some (recoveryLegalSumEnvelopeOutput inputLength handoff) := by
  let maximumBits :=
    recoveryLegalSumFinalizationBits inputLength handoff
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply recoveryLegalSumFinalizationStage_bits
    simp [recoveryLegalSumFinalizationStageBits]
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hmass :
      runNPOracleProgram recoveryBoundedContextGateProgram maximumBits 4
          (initialNPOracleState inputLength
            (recoveryLegalSumDescriptionGateOutput inputLength handoff)) =
        some (recoveryLegalSumMassGateOutput inputLength handoff) := by
    exact run_bits_mono
      (run_recoveryLegalSumFlagGateProgram inputLength
        (recoveryLegalSumDescriptionGateOutput inputLength handoff))
      (recoveryLegalSumFinalizationStage_bits (by
        simp [recoveryLegalSumFinalizationStageBits]))
  have hbitCap :
      runNPOracleProgram recoveryBoundedContextGateProgram maximumBits 4
          (initialNPOracleState inputLength
            (recoveryLegalSumMassGateOutput inputLength handoff)) =
        some (recoveryLegalSumBitCapGateOutput inputLength handoff) := by
    exact run_bits_mono
      (run_recoveryLegalSumFlagGateProgram inputLength
        (recoveryLegalSumMassGateOutput inputLength handoff))
      (recoveryLegalSumFinalizationStage_bits (by
        simp [recoveryLegalSumFinalizationStageBits]))
  have hcircuit :
      runNPOracleProgram recoveryBoundedContextGateProgram maximumBits 4
          (initialNPOracleState inputLength
            (recoveryLegalSumBitCapGateOutput inputLength handoff)) =
        some (recoveryLegalSumCircuitGateOutput inputLength handoff) := by
    exact run_bits_mono
      (run_recoveryLegalSumFlagGateProgram inputLength
        (recoveryLegalSumBitCapGateOutput inputLength handoff))
      (recoveryLegalSumFinalizationStage_bits (by
        simp [recoveryLegalSumFinalizationStageBits]))
  have hcoefficient :
      runNPOracleProgram recoveryBoundedContextGateProgram maximumBits 4
          (initialNPOracleState inputLength
            (recoveryLegalSumCircuitGateOutput inputLength handoff)) =
        some (recoveryLegalSumCoefficientGateOutput inputLength handoff) := by
    exact run_bits_mono
      (run_recoveryLegalSumFlagGateProgram inputLength
        (recoveryLegalSumCircuitGateOutput inputLength handoff))
      (recoveryLegalSumFinalizationStage_bits (by
        simp [recoveryLegalSumFinalizationStageBits]))
  have hterms :
      runNPOracleProgram recoveryBoundedContextGateProgram maximumBits 4
          (initialNPOracleState inputLength
            (recoveryLegalSumCoefficientGateOutput inputLength handoff)) =
        some (recoveryLegalSumTermsGateOutput inputLength handoff) := by
    exact run_bits_mono
      (run_recoveryLegalSumFlagGateProgram inputLength
        (recoveryLegalSumCoefficientGateOutput inputLength handoff))
      (recoveryLegalSumFinalizationStage_bits (by
        simp [recoveryLegalSumFinalizationStageBits]))
  have harity :
      runNPOracleProgram recoveryBoundedContextGateProgram maximumBits 4
          (initialNPOracleState inputLength
            (recoveryLegalSumTermsGateOutput inputLength handoff)) =
        some (recoveryLegalSumArityGateOutput inputLength handoff) := by
    exact run_bits_mono
      (run_recoveryLegalSumFlagGateProgram inputLength
        (recoveryLegalSumTermsGateOutput inputLength handoff))
      (recoveryLegalSumFinalizationStage_bits (by
        simp [recoveryLegalSumFinalizationStageBits]))
  have hq :
      runNPOracleProgram recoveryBoundedContextGateProgram maximumBits 4
          (initialNPOracleState inputLength
            (recoveryLegalSumArityGateOutput inputLength handoff)) =
        some (recoveryLegalSumQGateOutput inputLength handoff) := by
    exact run_bits_mono
      (run_recoveryLegalSumFlagGateProgram inputLength
        (recoveryLegalSumArityGateOutput inputLength handoff))
      (recoveryLegalSumFinalizationStage_bits (by
        simp [recoveryLegalSumFinalizationStageBits]))
  have htuple :
      runNPOracleProgram recoveryBoundedContextGateProgram maximumBits 4
          (initialNPOracleState inputLength
            (recoveryLegalSumQGateOutput inputLength handoff)) =
        some (recoveryLegalSumTupleGateOutput inputLength handoff) := by
    exact run_bits_mono
      (run_recoveryLegalSumFlagGateProgram inputLength
        (recoveryLegalSumQGateOutput inputLength handoff))
      (recoveryLegalSumFinalizationStage_bits (by
        simp [recoveryLegalSumFinalizationStageBits]))
  have hmode :
      runNPOracleProgram recoveryBoundedContextGateProgram maximumBits 4
          (initialNPOracleState inputLength
            (recoveryLegalSumTupleGateOutput inputLength handoff)) =
        some (recoveryLegalSumModeGateOutput inputLength handoff) := by
    exact run_bits_mono
      (run_recoveryLegalSumFlagGateProgram inputLength
        (recoveryLegalSumTupleGateOutput inputLength handoff))
      (recoveryLegalSumFinalizationStage_bits (by
        simp [recoveryLegalSumFinalizationStageBits]))
  have hprojection :
      runNPOracleProgram recoveryLegalSumHandoffProjectionProgram
          maximumBits 4
          (initialNPOracleState inputLength
            (recoveryLegalSumModeGateOutput inputLength handoff)) =
        some (recoveryLegalSumEnvelopeOutput inputLength handoff) := by
    exact run_bits_mono
      (run_recoveryLegalSumHandoffProjectionProgram inputLength
        (recoveryLegalSumModeGateOutput inputLength handoff))
      (recoveryLegalSumFinalizationStage_bits (by
        simp [recoveryLegalSumFinalizationStageBits]))
  have hmodeTail :=
    run_linkPrograms hpositive hlength hmode hprojection
  have htupleTail :=
    run_linkPrograms hpositive hlength htuple hmodeTail
  have hqTail :=
    run_linkPrograms hpositive hlength hq htupleTail
  have harityTail :=
    run_linkPrograms hpositive hlength harity hqTail
  have htermsTail :=
    run_linkPrograms hpositive hlength hterms harityTail
  have hcoefficientTail :=
    run_linkPrograms hpositive hlength hcoefficient htermsTail
  have hpostBitCap :=
    run_linkPrograms hpositive hlength hcircuit hcoefficientTail
  have hbitCapTail :=
    run_linkPrograms hpositive hlength hbitCap hpostBitCap
  have hrun :=
    run_linkPrograms hpositive hlength hmass hbitCapTail
  rw [recoveryLegalSumFinalizationProgram,
    recoveryLegalSumFinalizationFuel,
    recoveryLegalSumPostBitCapFinalizationProgram,
    recoveryLegalSumPostBitCapFinalizationFuel]
  exact hrun

def recoveryLegalSumResourceTailProgram : NPOracleProgram :=
  linkPrograms recoveryLegalSumResourceStageProgram
    recoveryLegalSumFinalizationProgram

@[simp] theorem recoveryLegalSumResourceTailProgram_oracleFree :
    OracleFree recoveryLegalSumResourceTailProgram :=
  oracleFree_linkPrograms recoveryLegalSumResourceStageProgram_oracleFree
    recoveryLegalSumFinalizationProgram_oracleFree

def recoveryLegalSumResourceTailFuel
    (inputLength handoff : ℕ) : ℕ :=
  linkFuel recoveryLegalSumFinalizationProgram
    (recoveryLegalSumResourceStageFuel inputLength handoff)
    recoveryLegalSumFinalizationFuel

def recoveryLegalSumResourceTailBits
    (inputLength handoff : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryLegalSumResourceStageBits inputLength handoff)
      (recoveryLegalSumFinalizationBits inputLength handoff)

private theorem run_recoveryLegalSumResourceTailProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumResourceTailProgram
        (recoveryLegalSumResourceTailBits inputLength handoff)
        (recoveryLegalSumResourceTailFuel inputLength handoff)
        (initialNPOracleState inputLength
          (recoveryLegalSumMassStageOutput inputLength handoff)) =
      some (recoveryLegalSumEnvelopeOutput inputLength handoff) := by
  have hlength :
      natBitLength inputLength ≤
        recoveryLegalSumResourceTailBits inputLength handoff :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤ recoveryLegalSumResourceTailBits inputLength handoff :=
    (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hstageBits :
      recoveryLegalSumResourceStageBits inputLength handoff ≤
        recoveryLegalSumResourceTailBits inputLength handoff :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hfinalizationBits :
      recoveryLegalSumFinalizationBits inputLength handoff ≤
        recoveryLegalSumResourceTailBits inputLength handoff :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hstage :=
    run_bits_mono
      (run_recoveryLegalSumResourceStageProgram inputLength handoff)
      hstageBits
  have hfinalization :=
    run_bits_mono
      (run_recoveryLegalSumFinalizationProgram inputLength handoff)
      hfinalizationBits
  have hrun := run_linkPrograms hpositive hlength hstage hfinalization
  simpa only [recoveryLegalSumResourceTailProgram,
    recoveryLegalSumResourceTailFuel] using hrun

def recoveryLegalSumBoundStageProgram : NPOracleProgram :=
  linkPrograms recoveryLegalSumBoundLoweringProgram
    recoveryBoundedContextCheckProgram

@[simp] theorem recoveryLegalSumBoundStageProgram_oracleFree :
    OracleFree recoveryLegalSumBoundStageProgram :=
  oracleFree_linkPrograms recoveryLegalSumBoundLoweringProgram_oracleFree
    recoveryBoundedContextCheckProgram_oracleFree

def recoveryLegalSumBoundStageFuel (handoff : ℕ) : ℕ :=
  linkFuel recoveryBoundedContextCheckProgram
    recoveryLegalSumBoundLoweringFuel <|
      recoveryBoundedContextCheckFuel
        (recoveryLegalSumTermCount handoff)
        (handoffSelectedTermCap handoff)

def recoveryLegalSumBoundStageBits
    (inputLength handoff : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryLegalSumBoundLoweringBits inputLength handoff) <|
      recoveryBoundedContextCheckBits inputLength
        (recoveryLegalSumTermCount handoff)
        (handoffSelectedTermCap handoff)
        (recoveryLegalSumLengthContext handoff)

private theorem run_recoveryLegalSumBoundStageProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumBoundStageProgram
        (recoveryLegalSumBoundStageBits inputLength handoff)
        (recoveryLegalSumBoundStageFuel handoff)
        (initialNPOracleState inputLength
          (recoveryLegalSumLengthStageOutput handoff)) =
      some (recoveryLegalSumBoundOutput handoff) := by
  let maximumBits := recoveryLegalSumBoundStageBits inputLength handoff
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hloweringBits :
      recoveryLegalSumBoundLoweringBits inputLength handoff ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcheckBits :
      recoveryBoundedContextCheckBits inputLength
          (recoveryLegalSumTermCount handoff)
          (handoffSelectedTermCap handoff)
          (recoveryLegalSumLengthContext handoff) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlowering :=
    run_bits_mono
      (run_recoveryLegalSumBoundLoweringProgram inputLength handoff)
      hloweringBits
  have hcheck :=
    run_bits_mono
      (run_recoveryLegalSumBoundProgram inputLength handoff)
      hcheckBits
  have hrun :=
    run_linkPrograms hpositive hlength hlowering hcheck
  rw [recoveryLegalSumBoundStageProgram, recoveryLegalSumBoundStageFuel]
  exact hrun

def recoveryLegalSumSyntaxProgram : NPOracleProgram :=
  linkPrograms recoveryLegalSumTupleLoweringProgram <|
    linkPrograms recoveryLegalSumTupleStageProgram <|
      linkPrograms recoveryLegalSumProjectionProgram <|
        linkPrograms recoveryLegalSumQStageProgram <|
          linkPrograms recoveryLegalSumArityLoweringProgram <|
            linkPrograms recoveryLegalSumArityStageProgram <|
              linkPrograms recoveryLegalSumTermsLoweringProgram <|
                linkPrograms recoveryLegalSumTermsStageProgram <|
                  linkPrograms recoveryLegalSumLengthLoweringProgram
                    recoveryLegalSumLengthStageProgram

@[simp] theorem recoveryLegalSumSyntaxProgram_oracleFree :
    OracleFree recoveryLegalSumSyntaxProgram := by
  exact oracleFree_linkPrograms
    recoveryLegalSumTupleLoweringProgram_oracleFree <|
      oracleFree_linkPrograms recoveryLegalSumTupleStageProgram_oracleFree <|
        oracleFree_linkPrograms recoveryLegalSumProjectionProgram_oracleFree <|
          oracleFree_linkPrograms recoveryLegalSumQStageProgram_oracleFree <|
            oracleFree_linkPrograms
              recoveryLegalSumArityLoweringProgram_oracleFree <|
                oracleFree_linkPrograms
                  recoveryLegalSumArityStageProgram_oracleFree <|
                    oracleFree_linkPrograms
                      recoveryLegalSumTermsLoweringProgram_oracleFree <|
                        oracleFree_linkPrograms
                          recoveryLegalSumTermsStageProgram_oracleFree <|
                            oracleFree_linkPrograms
                              recoveryLegalSumLengthLoweringProgram_oracleFree
                              recoveryLegalSumLengthStageProgram_oracleFree

def recoveryLegalSumSyntaxFuel (handoff : ℕ) : ℕ :=
  linkFuel
    (linkPrograms recoveryLegalSumTupleStageProgram <|
      linkPrograms recoveryLegalSumProjectionProgram <|
        linkPrograms recoveryLegalSumQStageProgram <|
          linkPrograms recoveryLegalSumArityLoweringProgram <|
            linkPrograms recoveryLegalSumArityStageProgram <|
              linkPrograms recoveryLegalSumTermsLoweringProgram <|
                linkPrograms recoveryLegalSumTermsStageProgram <|
                  linkPrograms recoveryLegalSumLengthLoweringProgram
                    recoveryLegalSumLengthStageProgram)
    recoveryLegalSumTupleLoweringFuel <|
      linkFuel
        (linkPrograms recoveryLegalSumProjectionProgram <|
          linkPrograms recoveryLegalSumQStageProgram <|
            linkPrograms recoveryLegalSumArityLoweringProgram <|
              linkPrograms recoveryLegalSumArityStageProgram <|
                linkPrograms recoveryLegalSumTermsLoweringProgram <|
                  linkPrograms recoveryLegalSumTermsStageProgram <|
                    linkPrograms recoveryLegalSumLengthLoweringProgram
                      recoveryLegalSumLengthStageProgram)
        recoveryLegalSumTupleStageFuel <|
          linkFuel
            (linkPrograms recoveryLegalSumQStageProgram <|
              linkPrograms recoveryLegalSumArityLoweringProgram <|
                linkPrograms recoveryLegalSumArityStageProgram <|
                  linkPrograms recoveryLegalSumTermsLoweringProgram <|
                    linkPrograms recoveryLegalSumTermsStageProgram <|
                      linkPrograms recoveryLegalSumLengthLoweringProgram
                        recoveryLegalSumLengthStageProgram)
            recoveryLegalSumProjectionFuel <|
              linkFuel
                (linkPrograms recoveryLegalSumArityLoweringProgram <|
                  linkPrograms recoveryLegalSumArityStageProgram <|
                    linkPrograms recoveryLegalSumTermsLoweringProgram <|
                      linkPrograms recoveryLegalSumTermsStageProgram <|
                        linkPrograms recoveryLegalSumLengthLoweringProgram
                          recoveryLegalSumLengthStageProgram)
                (recoveryLegalSumQStageFuel handoff) <|
                  linkFuel
                    (linkPrograms recoveryLegalSumArityStageProgram <|
                      linkPrograms recoveryLegalSumTermsLoweringProgram <|
                        linkPrograms recoveryLegalSumTermsStageProgram <|
                          linkPrograms recoveryLegalSumLengthLoweringProgram
                            recoveryLegalSumLengthStageProgram)
                    recoveryLegalSumArityLoweringFuel <|
                      linkFuel
                        (linkPrograms recoveryLegalSumTermsLoweringProgram <|
                          linkPrograms recoveryLegalSumTermsStageProgram <|
                            linkPrograms recoveryLegalSumLengthLoweringProgram
                              recoveryLegalSumLengthStageProgram)
                        (recoveryLegalSumArityStageFuel handoff) <|
                          linkFuel
                            (linkPrograms recoveryLegalSumTermsStageProgram <|
                              linkPrograms
                                recoveryLegalSumLengthLoweringProgram
                                recoveryLegalSumLengthStageProgram)
                            recoveryLegalSumTermsLoweringFuel <|
                              linkFuel
                                (linkPrograms
                                  recoveryLegalSumLengthLoweringProgram
                                  recoveryLegalSumLengthStageProgram)
                                (recoveryLegalSumTermsStageFuel handoff) <|
                                  linkFuel recoveryLegalSumLengthStageProgram
                                    recoveryLegalSumLengthLoweringFuel
                                    (recoveryLegalSumLengthStageFuel handoff)

def recoveryLegalSumSyntaxStageBits
    (inputLength handoff : ℕ) : List ℕ :=
  [ natBitLength inputLength
  , recoveryLegalSumTupleLoweringBits inputLength handoff
  , recoveryLegalSumTupleStageBits inputLength handoff
  , recoveryLegalSumProjectionBits inputLength handoff
  , recoveryLegalSumQStageBits inputLength handoff
  , recoveryLegalSumArityLoweringBits inputLength handoff
  , recoveryLegalSumArityStageBits inputLength handoff
  , recoveryLegalSumTermsLoweringBits inputLength handoff
  , recoveryLegalSumTermsStageBits inputLength handoff
  , recoveryLegalSumLengthLoweringBits inputLength handoff
  , recoveryLegalSumLengthStageBits inputLength handoff
  ]

def recoveryLegalSumSyntaxBits
    (inputLength handoff : ℕ) : ℕ :=
  (recoveryLegalSumSyntaxStageBits inputLength handoff).foldr max 0

theorem recoveryLegalSumSyntaxStage_bits
    {inputLength handoff bits : ℕ}
    (hbits : bits ∈ recoveryLegalSumSyntaxStageBits inputLength handoff) :
    bits ≤ recoveryLegalSumSyntaxBits inputLength handoff :=
  member_le_foldr_max hbits

private theorem run_recoveryLegalSumSyntaxProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumSyntaxProgram
        (recoveryLegalSumSyntaxBits inputLength handoff)
        (recoveryLegalSumSyntaxFuel handoff)
        (initialNPOracleState inputLength handoff) =
      some (recoveryLegalSumLengthStageOutput handoff) := by
  let maximumBits := recoveryLegalSumSyntaxBits inputLength handoff
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply recoveryLegalSumSyntaxStage_bits
    simp [recoveryLegalSumSyntaxStageBits]
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hstage {bits : ℕ}
      (hbits : bits ∈ recoveryLegalSumSyntaxStageBits inputLength handoff) :
      bits ≤ maximumBits := by
    exact recoveryLegalSumSyntaxStage_bits hbits
  have htupleLowering :=
    run_bits_mono
      (run_recoveryLegalSumTupleLoweringProgram inputLength handoff)
      (hstage (by
        simp [recoveryLegalSumSyntaxStageBits]))
  have htuple :=
    run_bits_mono
      (run_recoveryLegalSumTupleStageProgram inputLength handoff)
      (hstage (by
        simp [recoveryLegalSumSyntaxStageBits]))
  have hprojection :=
    run_bits_mono
      (run_recoveryLegalSumProjectionProgram inputLength handoff)
      (hstage (by
        simp [recoveryLegalSumSyntaxStageBits]))
  have hq :=
    run_bits_mono
      (run_recoveryLegalSumQStageProgram inputLength handoff)
      (hstage (by
        simp [recoveryLegalSumSyntaxStageBits]))
  have harityLowering :=
    run_bits_mono
      (run_recoveryLegalSumArityLoweringProgram inputLength handoff)
      (hstage (by
        simp [recoveryLegalSumSyntaxStageBits]))
  have harity :=
    run_bits_mono
      (run_recoveryLegalSumArityStageProgram inputLength handoff)
      (hstage (by
        simp [recoveryLegalSumSyntaxStageBits]))
  have htermsLowering :=
    run_bits_mono
      (run_recoveryLegalSumTermsLoweringProgram inputLength handoff)
      (hstage (by
        simp [recoveryLegalSumSyntaxStageBits]))
  have hterms :=
    run_bits_mono
      (run_recoveryLegalSumTermsStageProgram inputLength handoff)
      (hstage (by
        simp [recoveryLegalSumSyntaxStageBits]))
  have hlengthLowering :=
    run_bits_mono
      (run_recoveryLegalSumLengthLoweringProgram inputLength handoff)
      (hstage (by
        simp [recoveryLegalSumSyntaxStageBits]))
  have hlengthStage :=
    run_bits_mono
      (run_recoveryLegalSumLengthStageProgram inputLength handoff)
      (hstage (by
        simp [recoveryLegalSumSyntaxStageBits]))
  have hlengthTail :=
    run_linkPrograms hpositive hlength hlengthLowering hlengthStage
  have htermsTail :=
    run_linkPrograms hpositive hlength hterms hlengthTail
  have htermsLoweringTail :=
    run_linkPrograms hpositive hlength htermsLowering htermsTail
  have harityTail :=
    run_linkPrograms hpositive hlength harity htermsLoweringTail
  have harityLoweringTail :=
    run_linkPrograms hpositive hlength harityLowering harityTail
  have hqTail :=
    run_linkPrograms hpositive hlength hq harityLoweringTail
  have hprojectionTail :=
    run_linkPrograms hpositive hlength hprojection hqTail
  have htupleTail :=
    run_linkPrograms hpositive hlength htuple hprojectionTail
  have hrun :=
    run_linkPrograms hpositive hlength htupleLowering htupleTail
  rw [recoveryLegalSumSyntaxProgram, recoveryLegalSumSyntaxFuel]
  exact hrun

def recoveryLegalSumEnvelopeProgram : NPOracleProgram :=
  linkPrograms recoveryLegalSumSyntaxProgram <|
    linkPrograms recoveryLegalSumBoundStageProgram <|
      linkPrograms recoveryLegalTermCoefficientLoweringProgram <|
        linkPrograms recoveryLegalTermCoefficientStageProgram <|
          linkPrograms recoveryLegalTermCircuitLoweringProgram <|
            linkPrograms recoveryLegalTermCircuitStageProgram <|
              linkPrograms recoveryLegalTermBitCapLoweringProgram <|
                linkPrograms recoveryLegalTermBitCapStageProgram <|
                  linkPrograms recoveryLegalTermMassProgram
                    recoveryLegalSumResourceTailProgram

@[simp] theorem recoveryLegalSumEnvelopeProgram_oracleFree :
    OracleFree recoveryLegalSumEnvelopeProgram := by
  exact oracleFree_linkPrograms recoveryLegalSumSyntaxProgram_oracleFree <|
    oracleFree_linkPrograms recoveryLegalSumBoundStageProgram_oracleFree <|
      oracleFree_linkPrograms
        recoveryLegalTermCoefficientLoweringProgram_oracleFree <|
          oracleFree_linkPrograms
            recoveryLegalTermCoefficientStageProgram_oracleFree <|
              oracleFree_linkPrograms
                recoveryLegalTermCircuitLoweringProgram_oracleFree <|
                  oracleFree_linkPrograms
                    recoveryLegalTermCircuitStageProgram_oracleFree <|
                      oracleFree_linkPrograms
                        recoveryLegalTermBitCapLoweringProgram_oracleFree <|
                          oracleFree_linkPrograms
                            recoveryLegalTermBitCapStageProgram_oracleFree <|
                              oracleFree_linkPrograms
                                recoveryLegalTermMassProgram_oracleFree
                                recoveryLegalSumResourceTailProgram_oracleFree

def recoveryLegalSumEnvelopeFuel
    (inputLength handoff : ℕ) : ℕ :=
  linkFuel
    (linkPrograms recoveryLegalSumBoundStageProgram <|
      linkPrograms recoveryLegalTermCoefficientLoweringProgram <|
        linkPrograms recoveryLegalTermCoefficientStageProgram <|
          linkPrograms recoveryLegalTermCircuitLoweringProgram <|
            linkPrograms recoveryLegalTermCircuitStageProgram <|
              linkPrograms recoveryLegalTermBitCapLoweringProgram <|
                linkPrograms recoveryLegalTermBitCapStageProgram <|
                  linkPrograms recoveryLegalTermMassProgram
                    recoveryLegalSumResourceTailProgram)
    (recoveryLegalSumSyntaxFuel handoff) <|
      linkFuel
        (linkPrograms recoveryLegalTermCoefficientLoweringProgram <|
          linkPrograms recoveryLegalTermCoefficientStageProgram <|
            linkPrograms recoveryLegalTermCircuitLoweringProgram <|
              linkPrograms recoveryLegalTermCircuitStageProgram <|
                linkPrograms recoveryLegalTermBitCapLoweringProgram <|
                  linkPrograms recoveryLegalTermBitCapStageProgram <|
                    linkPrograms recoveryLegalTermMassProgram
                      recoveryLegalSumResourceTailProgram)
        (recoveryLegalSumBoundStageFuel handoff)
        <| linkFuel
          (linkPrograms recoveryLegalTermCoefficientStageProgram <|
            linkPrograms recoveryLegalTermCircuitLoweringProgram <|
              linkPrograms recoveryLegalTermCircuitStageProgram <|
                linkPrograms recoveryLegalTermBitCapLoweringProgram <|
                  linkPrograms recoveryLegalTermBitCapStageProgram <|
                    linkPrograms recoveryLegalTermMassProgram
                      recoveryLegalSumResourceTailProgram)
          recoveryLegalTermCoefficientLoweringFuel
          <| linkFuel
            (linkPrograms recoveryLegalTermCircuitLoweringProgram <|
              linkPrograms recoveryLegalTermCircuitStageProgram <|
                linkPrograms recoveryLegalTermBitCapLoweringProgram <|
                  linkPrograms recoveryLegalTermBitCapStageProgram <|
                    linkPrograms recoveryLegalTermMassProgram
                      recoveryLegalSumResourceTailProgram)
            (recoveryLegalTermCoefficientStageFuel inputLength handoff)
            <| linkFuel
              (linkPrograms recoveryLegalTermCircuitStageProgram <|
                linkPrograms recoveryLegalTermBitCapLoweringProgram <|
                  linkPrograms recoveryLegalTermBitCapStageProgram <|
                    linkPrograms recoveryLegalTermMassProgram
                      recoveryLegalSumResourceTailProgram)
              recoveryLegalTermCircuitLoweringFuel
              <| linkFuel
                (linkPrograms recoveryLegalTermBitCapLoweringProgram <|
                  linkPrograms recoveryLegalTermBitCapStageProgram <|
                    linkPrograms recoveryLegalTermMassProgram
                      recoveryLegalSumResourceTailProgram)
                (recoveryLegalTermCircuitStageFuel inputLength handoff)
                <| linkFuel
                  (linkPrograms recoveryLegalTermBitCapStageProgram <|
                    linkPrograms recoveryLegalTermMassProgram
                      recoveryLegalSumResourceTailProgram)
                  recoveryLegalTermBitCapLoweringFuel
                  <| linkFuel
                    (linkPrograms recoveryLegalTermMassProgram
                      recoveryLegalSumResourceTailProgram)
                    (recoveryLegalTermBitCapStageFuel
                      (recoveryLegalTermCircuitStageOutput
                        inputLength handoff))
                    <| linkFuel recoveryLegalSumResourceTailProgram
                      (recoveryLegalTermMassFuel inputLength
                        (recoveryLegalTermBitCapStageOutput
                          (recoveryLegalTermCircuitStageOutput
                            inputLength handoff)))
                      (recoveryLegalSumResourceTailFuel inputLength handoff)

def recoveryLegalSumEnvelopeBits
    (inputLength handoff : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryLegalSumSyntaxBits inputLength handoff) <|
      max (recoveryLegalSumBoundStageBits inputLength handoff) <|
        max (recoveryLegalTermCoefficientLoweringBits inputLength handoff) <|
          max (recoveryLegalTermCoefficientStageBits inputLength handoff) <|
            max (recoveryLegalTermCircuitLoweringBits inputLength handoff) <|
              max (recoveryLegalTermCircuitStageBits inputLength handoff) <|
                max
                  (recoveryLegalTermBitCapLoweringBits inputLength
                    (recoveryLegalTermCircuitStageOutput inputLength handoff))
                  <| max
                    (recoveryLegalTermBitCapStageBits inputLength
                      (recoveryLegalTermCircuitStageOutput
                        inputLength handoff))
                    <| max
                      (recoveryLegalTermMassBits inputLength
                        (recoveryLegalTermBitCapStageOutput
                          (recoveryLegalTermCircuitStageOutput
                            inputLength handoff)))
                      (recoveryLegalSumResourceTailBits inputLength handoff)

theorem run_recoveryLegalSumEnvelopeProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryLegalSumEnvelopeProgram
        (recoveryLegalSumEnvelopeBits inputLength handoff)
        (recoveryLegalSumEnvelopeFuel inputLength handoff)
        (initialNPOracleState inputLength handoff) =
      some (recoveryLegalSumEnvelopeOutput inputLength handoff) := by
  let maximumBits := recoveryLegalSumEnvelopeBits inputLength handoff
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hsyntaxBits :
      recoveryLegalSumSyntaxBits inputLength handoff ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hboundBits :
      recoveryLegalSumBoundStageBits inputLength handoff ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcoefficientLoweringBits :
      recoveryLegalTermCoefficientLoweringBits inputLength handoff ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcoefficientStageBits :
      recoveryLegalTermCoefficientStageBits inputLength handoff ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcircuitLoweringBits :
      recoveryLegalTermCircuitLoweringBits inputLength handoff ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcircuitStageBits :
      recoveryLegalTermCircuitStageBits inputLength handoff ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hbitCapLoweringBits :
      recoveryLegalTermBitCapLoweringBits inputLength
          (recoveryLegalTermCircuitStageOutput inputLength handoff) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans <|
                (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hbitCapStageBits :
      recoveryLegalTermBitCapStageBits inputLength
          (recoveryLegalTermCircuitStageOutput inputLength handoff) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans <|
                (Nat.le_max_right _ _).trans <|
                  (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hmassBits :
      recoveryLegalTermMassBits inputLength
          (recoveryLegalTermBitCapStageOutput
            (recoveryLegalTermCircuitStageOutput inputLength handoff)) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans <|
                (Nat.le_max_right _ _).trans <|
                  (Nat.le_max_right _ _).trans <|
                    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hfinalBits :
      recoveryLegalSumResourceTailBits inputLength handoff ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans <|
                (Nat.le_max_right _ _).trans <|
                  (Nat.le_max_right _ _).trans <|
                    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hsyntax :=
    run_bits_mono
      (run_recoveryLegalSumSyntaxProgram inputLength handoff)
      hsyntaxBits
  have hbound :=
    run_bits_mono
      (run_recoveryLegalSumBoundStageProgram inputLength handoff)
      hboundBits
  have hcoefficientLowering :=
    run_bits_mono
      (run_recoveryLegalTermCoefficientLoweringProgram inputLength handoff)
      hcoefficientLoweringBits
  have hcoefficientStage :=
    run_bits_mono
      (run_recoveryLegalTermCoefficientStageProgram inputLength handoff)
      hcoefficientStageBits
  have hcircuitLowering :=
    run_bits_mono
      (run_recoveryLegalTermCircuitLoweringProgram inputLength handoff)
      hcircuitLoweringBits
  have hcircuitStage :=
    run_bits_mono
      (run_recoveryLegalTermCircuitStageProgram inputLength handoff)
      hcircuitStageBits
  have hbitCapLowering :=
    run_bits_mono
      (run_recoveryLegalTermBitCapLoweringProgram inputLength
        (recoveryLegalTermCircuitStageOutput inputLength handoff))
      hbitCapLoweringBits
  have hbitCapStage :=
    run_bits_mono
      (run_recoveryLegalTermBitCapStageProgram inputLength
        (recoveryLegalTermCircuitStageOutput inputLength handoff))
      hbitCapStageBits
  have hmass :=
    run_bits_mono
      (run_recoveryLegalTermMassProgram inputLength
        (recoveryLegalTermBitCapStageOutput
          (recoveryLegalTermCircuitStageOutput inputLength handoff)))
      hmassBits
  have hfinal :=
    run_bits_mono
      (run_recoveryLegalSumResourceTailProgram inputLength handoff)
      hfinalBits
  have hmassTail :=
    run_linkPrograms hpositive hlength hmass hfinal
  have hbitCapStageTail :=
    run_linkPrograms hpositive hlength hbitCapStage hmassTail
  have hbitCapLoweringTail :=
    run_linkPrograms hpositive hlength hbitCapLowering hbitCapStageTail
  have hcircuitStageTail :=
    run_linkPrograms hpositive hlength hcircuitStage hbitCapLoweringTail
  have hcircuitLoweringTail :=
    run_linkPrograms hpositive hlength hcircuitLowering hcircuitStageTail
  have hcoefficientTail :=
    run_linkPrograms hpositive hlength hcoefficientStage
      hcircuitLoweringTail
  have hcoefficientLoweringTail :=
    run_linkPrograms hpositive hlength hcoefficientLowering hcoefficientTail
  have htail :=
    run_linkPrograms hpositive hlength hbound hcoefficientLoweringTail
  have hrun :=
    run_linkPrograms hpositive hlength hsyntax htail
  rw [recoveryLegalSumEnvelopeProgram, recoveryLegalSumEnvelopeFuel]
  exact hrun

def recoveryValidatorLegalSumPrefixOutput
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  recoveryLegalSumEnvelopeOutput inputLength
    (recoveryValidatorOraclePrefixOutput limits raw)

def recoveryValidatorLegalSumPrefixProgram : NPOracleProgram :=
  linkPrograms recoveryValidatorOraclePrefixProgram
    recoveryLegalSumEnvelopeProgram

@[simp] theorem recoveryValidatorLegalSumPrefixProgram_oracleFree :
    OracleFree recoveryValidatorLegalSumPrefixProgram :=
  oracleFree_linkPrograms recoveryValidatorOraclePrefixProgram_oracleFree
    recoveryLegalSumEnvelopeProgram_oracleFree

def recoveryValidatorLegalSumPrefixFuel
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  linkFuel recoveryLegalSumEnvelopeProgram
    (recoveryValidatorOraclePrefixFuel limits raw) <|
      recoveryLegalSumEnvelopeFuel inputLength
        (recoveryValidatorOraclePrefixOutput limits raw)

def recoveryValidatorLegalSumPrefixBits
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryValidatorOraclePrefixBits inputLength limits raw)
      (recoveryLegalSumEnvelopeBits inputLength
        (recoveryValidatorOraclePrefixOutput limits raw))

theorem run_recoveryValidatorLegalSumPrefixProgram
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryValidatorLegalSumPrefixProgram
        (recoveryValidatorLegalSumPrefixBits inputLength limits raw)
        (recoveryValidatorLegalSumPrefixFuel inputLength limits raw)
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits raw)) =
      some (recoveryValidatorLegalSumPrefixOutput
        inputLength limits raw) := by
  let handoff := recoveryValidatorOraclePrefixOutput limits raw
  let maximumBits :=
    recoveryValidatorLegalSumPrefixBits inputLength limits raw
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have horacleBits :
      recoveryValidatorOraclePrefixBits inputLength limits raw ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsumBits :
      recoveryLegalSumEnvelopeBits inputLength handoff ≤ maximumBits := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have horacle :=
    run_bits_mono
      (run_recoveryValidatorOraclePrefixProgram inputLength limits raw)
      horacleBits
  have hsum :=
    run_bits_mono
      (run_recoveryLegalSumEnvelopeProgram inputLength handoff)
      hsumBits
  have hrun :=
    run_linkPrograms hpositive hlength horacle hsum
  rw [recoveryValidatorLegalSumPrefixProgram,
    recoveryValidatorLegalSumPrefixFuel]
  exact hrun

@[simp] theorem recoveryLegalSumFlagGateOutput_zero :
    recoveryLegalSumFlagGateOutput 0 = 0 := by
  simp [recoveryLegalSumFlagGateOutput,
    recoveryBoundedContextGateOutput]

theorem recoveryLegalSumFlagGateOutput_pair
    (flag context : ℕ) :
    recoveryLegalSumFlagGateOutput (Nat.pair flag context) =
      if flag = 0 then 0 else context := by
  simp [recoveryLegalSumFlagGateOutput,
    recoveryBoundedContextGateOutput]

theorem recoveryLegalTermMassComparisonFlag_ne_zero_iff
    (inputLength bitCapStage : ℕ) :
    recoveryLegalTermMassComparisonFlag inputLength bitCapStage ≠ 0 ↔
      recoveryLegalTermMassAccepts inputLength bitCapStage := by
  simp [recoveryLegalTermMassComparisonFlag,
    recoveryLegalTermMassBranchFlag, recoveryLegalTermMassAccepts]

theorem recoveryLegalSumMassGateOutput_eq
    (inputLength handoff : ℕ) :
    recoveryLegalSumMassGateOutput inputLength handoff =
      if recoveryLegalTermWireStageValue
            (recoveryLegalSumMassStageOutput inputLength handoff) ≠ 0 ∧
          recoveryLegalTermDescriptionStageValue
            (recoveryLegalSumMassStageOutput inputLength handoff) ≠ 0 ∧
          recoveryLegalTermMassAccepts inputLength
            (recoveryLegalTermBitCapStageOutput
              (recoveryLegalTermCircuitStageOutput inputLength handoff)) then
        recoveryLegalTermMassFinalContext
          (recoveryLegalTermBitCapStageOutput
            (recoveryLegalTermCircuitStageOutput inputLength handoff))
      else 0 := by
  by_cases hwire :
      recoveryLegalTermWireStageValue
        (recoveryLegalSumMassStageOutput inputLength handoff) = 0
  · have hdescriptionGate :
        recoveryLegalSumDescriptionGateOutput inputLength handoff = 0 := by
      rw [recoveryLegalSumDescriptionGateOutput,
        recoveryLegalSumWireGateOutput, recoveryLegalTermWireGateOutput_eq,
        if_pos hwire, recoveryLegalTermDescriptionGateOutput_eq]
      by_cases hzero : recoveryLegalTermDescriptionStageValue 0 = 0
      · rw [if_pos hzero]
      · rw [if_neg hzero]
    rw [recoveryLegalSumMassGateOutput, hdescriptionGate,
      recoveryLegalSumFlagGateOutput_zero,
      if_neg (fun haccepts => haccepts.1 hwire)]
  · have hwireGate :
        recoveryLegalSumWireGateOutput inputLength handoff =
          recoveryLegalSumMassStageOutput inputLength handoff := by
      rw [recoveryLegalSumWireGateOutput, recoveryLegalTermWireGateOutput_eq,
        if_neg hwire]
    by_cases hdescription :
        recoveryLegalTermDescriptionStageValue
          (recoveryLegalSumMassStageOutput inputLength handoff) = 0
    · have hdescriptionGate :
          recoveryLegalSumDescriptionGateOutput inputLength handoff = 0 := by
        rw [recoveryLegalSumDescriptionGateOutput, hwireGate,
          recoveryLegalTermDescriptionGateOutput_eq, if_pos hdescription]
      rw [recoveryLegalSumMassGateOutput, hdescriptionGate,
        recoveryLegalSumFlagGateOutput_zero,
        if_neg (fun haccepts => haccepts.2.1 hdescription)]
    · have hdescriptionGate :
          recoveryLegalSumDescriptionGateOutput inputLength handoff =
            recoveryLegalSumMassStageOutput inputLength handoff := by
        rw [recoveryLegalSumDescriptionGateOutput, hwireGate,
          recoveryLegalTermDescriptionGateOutput_eq, if_neg hdescription]
      rw [recoveryLegalSumMassGateOutput, hdescriptionGate]
      by_cases hmass :
          recoveryLegalTermMassAccepts inputLength
            (recoveryLegalTermBitCapStageOutput
              (recoveryLegalTermCircuitStageOutput inputLength handoff))
      · have hflag :
            recoveryLegalTermMassComparisonFlag inputLength
                (recoveryLegalTermBitCapStageOutput
                  (recoveryLegalTermCircuitStageOutput inputLength
                    handoff)) ≠ 0 :=
          (recoveryLegalTermMassComparisonFlag_ne_zero_iff inputLength
            (recoveryLegalTermBitCapStageOutput
              (recoveryLegalTermCircuitStageOutput inputLength handoff))).2
            hmass
        rw [if_pos ⟨hwire, hdescription, hmass⟩]
        simp [recoveryLegalSumMassStageOutput,
          recoveryLegalTermMassComparisonOutput,
          recoveryLegalSumFlagGateOutput_pair,
          recoveryLegalTermMassComparisonFinalContext_eq, hflag]
      · have hflag :
            recoveryLegalTermMassComparisonFlag inputLength
                (recoveryLegalTermBitCapStageOutput
                  (recoveryLegalTermCircuitStageOutput inputLength
                    handoff)) = 0 := by
          by_contra hne
          exact hmass ((recoveryLegalTermMassComparisonFlag_ne_zero_iff
            inputLength
            (recoveryLegalTermBitCapStageOutput
              (recoveryLegalTermCircuitStageOutput inputLength handoff))).1
            hne)
        rw [if_neg (fun haccepts => hmass haccepts.2.2)]
        simp [recoveryLegalSumMassStageOutput,
          recoveryLegalTermMassComparisonOutput,
          recoveryLegalSumFlagGateOutput_pair, hflag]

@[simp] theorem recoveryLegalSumHandoffProjectionOutput_zero :
    recoveryLegalSumHandoffProjectionOutput 0 = 0 := by
  simp [recoveryLegalSumHandoffProjectionOutput]

theorem recoveryLegalSumHandoffProjectionOutput_termsRest
    (handoff : ℕ) :
    recoveryLegalSumHandoffProjectionOutput
        (Nat.unpair
          (Nat.unpair (recoveryLegalSumContext handoff)).2).2 =
      handoff := by
  simp [recoveryLegalSumHandoffProjectionOutput,
    recoveryLegalSumContext]

theorem
    recoveryLegalSumEnvelopeOutput_eq_of_massBitCapAndCircuitValidation
    (inputLength handoff : ℕ)
    (hwire :
      recoveryLegalTermWireStageValue
        (recoveryLegalSumMassStageOutput inputLength handoff) ≠ 0)
    (hdescription :
      recoveryLegalTermDescriptionStageValue
        (recoveryLegalSumMassStageOutput inputLength handoff) ≠ 0)
    (hmass :
      recoveryLegalTermMassAccepts inputLength
        (recoveryLegalTermBitCapStageOutput
          (recoveryLegalTermCircuitStageOutput inputLength handoff)))
    (hbitCap :
      recoveryLegalTermCoefficientBitCapListOutput
          (recoveryLegalTermBitCapSelectedCap
            (recoveryLegalTermCircuitStageOutput inputLength handoff))
          (recoveryLegalTermBitCapMappedCode
            (recoveryLegalTermCircuitStageOutput inputLength handoff)) ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
          (recoveryLegalTermCircuitContext handoff)
          (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0) :
    recoveryLegalSumEnvelopeOutput inputLength handoff =
      if recoveryLegalTermCoefficientListOutput inputLength
            (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0 ∧
          recoveryLegalSumTermCount handoff ≤
            handoffSelectedTermCap handoff ∧
          recoveryLegalSumTermsFlag handoff ≠ 0 ∧
          recoveryLegalSumArityFlag handoff ≠ 0 ∧
          recoveryLegalSumQFlag handoff ≠ 0 ∧
          recoveryLegalSumTupleFlag handoff ≠ 0 ∧
          handoffLegalSumModeFlag handoff ≠ 0 then
        handoff
      else
        0 := by
  have hmassGate :
      recoveryLegalSumMassGateOutput inputLength handoff =
        Nat.pair
          (recoveryLegalTermCoefficientBitCapListOutput
            (recoveryLegalTermBitCapSelectedCap
              (recoveryLegalTermCircuitStageOutput inputLength handoff))
            (recoveryLegalTermBitCapMappedCode
              (recoveryLegalTermCircuitStageOutput inputLength handoff)))
          (recoveryLegalTermCircuitStageOutput inputLength handoff) := by
    rw [recoveryLegalSumMassGateOutput_eq,
      if_pos ⟨hwire, hdescription, hmass⟩,
      recoveryLegalTermMassFinalContext_bitCapStageOutput]
  have hbitCapGate :
      recoveryLegalSumBitCapGateOutput inputLength handoff =
        recoveryLegalTermCircuitStageOutput inputLength handoff := by
    simp [recoveryLegalSumBitCapGateOutput, hmassGate,
      recoveryLegalSumFlagGateOutput_pair, hbitCap]
  have hcircuitGate :
      recoveryLegalSumCircuitGateOutput inputLength handoff =
        recoveryLegalTermCoefficientStageOutput inputLength handoff := by
    simp [recoveryLegalSumCircuitGateOutput,
      recoveryLegalTermCircuitStageOutput,
      recoveryLegalSumFlagGateOutput_pair, hbitCapGate, hcircuit]
  by_cases hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) = 0
  · simp [recoveryLegalSumEnvelopeOutput,
      recoveryLegalSumModeGateOutput, recoveryLegalSumTupleGateOutput,
      recoveryLegalSumQGateOutput, recoveryLegalSumArityGateOutput,
      recoveryLegalSumTermsGateOutput, recoveryLegalSumCoefficientGateOutput,
      recoveryLegalTermCoefficientStageOutput,
      recoveryLegalSumFlagGateOutput_pair, hcircuitGate, hcoefficient]
  · by_cases hle :
        recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff
    · by_cases hterms : recoveryLegalSumTermsFlag handoff = 0
      · simp [recoveryLegalSumEnvelopeOutput,
          recoveryLegalSumModeGateOutput,
          recoveryLegalSumTupleGateOutput, recoveryLegalSumQGateOutput,
          recoveryLegalSumArityGateOutput,
          recoveryLegalSumTermsGateOutput,
          recoveryLegalSumCoefficientGateOutput,
          recoveryLegalTermCoefficientStageOutput,
          recoveryLegalSumBoundOutput,
          recoveryBoundedContextOutput, recoveryLegalSumLengthContext,
          recoveryLegalSumFlagGateOutput_pair, hcircuitGate, hcoefficient,
          hle, hterms]
      · by_cases harity : recoveryLegalSumArityFlag handoff = 0
        · simp [recoveryLegalSumEnvelopeOutput,
            recoveryLegalSumModeGateOutput,
            recoveryLegalSumTupleGateOutput, recoveryLegalSumQGateOutput,
            recoveryLegalSumArityGateOutput,
            recoveryLegalSumTermsGateOutput,
            recoveryLegalSumCoefficientGateOutput,
            recoveryLegalTermCoefficientStageOutput,
            recoveryLegalSumBoundOutput,
            recoveryBoundedContextOutput, recoveryLegalSumLengthContext,
            recoveryLegalSumArityStageOutput,
            recoveryLegalSumFlagGateOutput_pair, hcircuitGate, hcoefficient,
            hle, hterms, harity]
        · by_cases hq : recoveryLegalSumQFlag handoff = 0
          · simp [recoveryLegalSumEnvelopeOutput,
              recoveryLegalSumModeGateOutput,
              recoveryLegalSumTupleGateOutput, recoveryLegalSumQGateOutput,
              recoveryLegalSumArityGateOutput,
              recoveryLegalSumTermsGateOutput,
              recoveryLegalSumCoefficientGateOutput,
              recoveryLegalTermCoefficientStageOutput,
              recoveryLegalSumBoundOutput,
              recoveryBoundedContextOutput, recoveryLegalSumLengthContext,
              recoveryLegalSumArityStageOutput,
              recoveryLegalSumArityContext,
              recoveryLegalSumFlagGateOutput_pair, hcircuitGate,
              hcoefficient, hle, hterms, harity, hq]
          · by_cases htuple : recoveryLegalSumTupleFlag handoff = 0
            · simp [recoveryLegalSumEnvelopeOutput,
                recoveryLegalSumModeGateOutput,
                recoveryLegalSumTupleGateOutput,
                recoveryLegalSumQGateOutput,
                recoveryLegalSumArityGateOutput,
                recoveryLegalSumTermsGateOutput,
                recoveryLegalSumCoefficientGateOutput,
                recoveryLegalTermCoefficientStageOutput,
                recoveryLegalSumBoundOutput,
                recoveryBoundedContextOutput,
                recoveryLegalSumLengthContext,
                recoveryLegalSumArityStageOutput,
                recoveryLegalSumArityContext, recoveryLegalSumContext,
                recoveryLegalSumFlagGateOutput_pair, hcircuitGate,
                hcoefficient, hle, hterms, harity, hq, htuple]
            · by_cases hmode : handoffLegalSumModeFlag handoff = 0
              · simp [recoveryLegalSumEnvelopeOutput,
                  recoveryLegalSumModeGateOutput,
                  recoveryLegalSumTupleGateOutput,
                  recoveryLegalSumQGateOutput,
                  recoveryLegalSumArityGateOutput,
                  recoveryLegalSumTermsGateOutput,
                  recoveryLegalSumCoefficientGateOutput,
                  recoveryLegalTermCoefficientStageOutput,
                  recoveryLegalSumBoundOutput,
                  recoveryBoundedContextOutput,
                  recoveryLegalSumLengthContext,
                  recoveryLegalSumArityStageOutput,
                  recoveryLegalSumArityContext, recoveryLegalSumContext,
                  recoveryLegalSumFlagGateOutput_pair, hcircuitGate,
                  hcoefficient, hle, hterms, harity, hq, htuple, hmode]
              · simp [recoveryLegalSumEnvelopeOutput,
                  recoveryLegalSumModeGateOutput,
                  recoveryLegalSumTupleGateOutput,
                  recoveryLegalSumQGateOutput,
                  recoveryLegalSumArityGateOutput,
                  recoveryLegalSumTermsGateOutput,
                  recoveryLegalSumCoefficientGateOutput,
                  recoveryLegalTermCoefficientStageOutput,
                  recoveryLegalSumBoundOutput,
                  recoveryBoundedContextOutput,
                  recoveryLegalSumLengthContext,
                  recoveryLegalSumArityStageOutput,
                  recoveryLegalSumArityContext, recoveryLegalSumContext,
                  recoveryLegalSumFlagGateOutput_pair,
                  recoveryLegalSumHandoffProjectionOutput,
                  hcircuitGate, hcoefficient, hle, hterms, harity, hq,
                  htuple, hmode]
    · simp [recoveryLegalSumEnvelopeOutput,
        recoveryLegalSumModeGateOutput, recoveryLegalSumTupleGateOutput,
        recoveryLegalSumQGateOutput, recoveryLegalSumArityGateOutput,
        recoveryLegalSumTermsGateOutput,
        recoveryLegalSumCoefficientGateOutput,
        recoveryLegalTermCoefficientStageOutput,
        recoveryLegalSumBoundOutput, recoveryBoundedContextOutput,
        recoveryLegalSumFlagGateOutput_pair, hcircuitGate, hcoefficient, hle]

theorem recoveryLegalSumEnvelopeOutput_eq
    (inputLength handoff : ℕ) :
    recoveryLegalSumEnvelopeOutput inputLength handoff =
      if recoveryLegalTermCircuitListOutput
            (recoveryLegalTermCircuitContext handoff)
            (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0 ∧
          recoveryLegalTermCoefficientBitCapListOutput
            (recoveryLegalTermBitCapSelectedCap
              (recoveryLegalTermCircuitStageOutput inputLength handoff))
            (recoveryLegalTermBitCapMappedCode
              (recoveryLegalTermCircuitStageOutput inputLength handoff)) ≠ 0 ∧
          recoveryLegalTermMassAccepts inputLength
            (recoveryLegalTermBitCapStageOutput
              (recoveryLegalTermCircuitStageOutput inputLength handoff)) ∧
          recoveryLegalTermCoefficientListOutput inputLength
            (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0 ∧
          recoveryLegalSumTermCount handoff ≤
            handoffSelectedTermCap handoff ∧
          recoveryLegalSumTermsFlag handoff ≠ 0 ∧
          recoveryLegalSumArityFlag handoff ≠ 0 ∧
          recoveryLegalSumQFlag handoff ≠ 0 ∧
          recoveryLegalSumTupleFlag handoff ≠ 0 ∧
          handoffLegalSumModeFlag handoff ≠ 0 ∧
          recoveryLegalTermWireStageValue
            (recoveryLegalSumMassStageOutput inputLength handoff) ≠ 0 ∧
          recoveryLegalTermDescriptionStageValue
            (recoveryLegalSumMassStageOutput inputLength handoff) ≠ 0 then
        handoff
      else
        0 := by
  by_cases hwire :
      recoveryLegalTermWireStageValue
        (recoveryLegalSumMassStageOutput inputLength handoff) = 0
  · have hbitCapGate :
        recoveryLegalSumBitCapGateOutput inputLength handoff = 0 := by
      have hmassGate :
          recoveryLegalSumMassGateOutput inputLength handoff = 0 := by
        rw [recoveryLegalSumMassGateOutput_eq,
          if_neg (fun haccepts => haccepts.1 hwire)]
      simp [recoveryLegalSumBitCapGateOutput, hmassGate]
    simp [recoveryLegalSumEnvelopeOutput,
      recoveryLegalSumModeGateOutput, recoveryLegalSumTupleGateOutput,
      recoveryLegalSumQGateOutput, recoveryLegalSumArityGateOutput,
      recoveryLegalSumTermsGateOutput, recoveryLegalSumCoefficientGateOutput,
      recoveryLegalSumCircuitGateOutput, hbitCapGate, hwire]
  · by_cases hdescription :
        recoveryLegalTermDescriptionStageValue
          (recoveryLegalSumMassStageOutput inputLength handoff) = 0
    · have hbitCapGate :
          recoveryLegalSumBitCapGateOutput inputLength handoff = 0 := by
        have hmassGate :
            recoveryLegalSumMassGateOutput inputLength handoff = 0 := by
          rw [recoveryLegalSumMassGateOutput_eq,
            if_neg (fun haccepts => haccepts.2.1 hdescription)]
        simp [recoveryLegalSumBitCapGateOutput, hmassGate]
      simp [recoveryLegalSumEnvelopeOutput,
        recoveryLegalSumModeGateOutput, recoveryLegalSumTupleGateOutput,
        recoveryLegalSumQGateOutput, recoveryLegalSumArityGateOutput,
        recoveryLegalSumTermsGateOutput,
        recoveryLegalSumCoefficientGateOutput,
        recoveryLegalSumCircuitGateOutput, hbitCapGate, hdescription]
    · by_cases hmass :
          recoveryLegalTermMassAccepts inputLength
            (recoveryLegalTermBitCapStageOutput
              (recoveryLegalTermCircuitStageOutput inputLength handoff))
      · have hmassGate :
            recoveryLegalSumMassGateOutput inputLength handoff =
              Nat.pair
                (recoveryLegalTermCoefficientBitCapListOutput
                  (recoveryLegalTermBitCapSelectedCap
                    (recoveryLegalTermCircuitStageOutput inputLength handoff))
                  (recoveryLegalTermBitCapMappedCode
                    (recoveryLegalTermCircuitStageOutput inputLength
                      handoff)))
                (recoveryLegalTermCircuitStageOutput inputLength handoff) := by
          rw [recoveryLegalSumMassGateOutput_eq,
            if_pos ⟨hwire, hdescription, hmass⟩,
            recoveryLegalTermMassFinalContext_bitCapStageOutput]
        by_cases hbitCap :
            recoveryLegalTermCoefficientBitCapListOutput
                (recoveryLegalTermBitCapSelectedCap
                  (recoveryLegalTermCircuitStageOutput inputLength handoff))
                (recoveryLegalTermBitCapMappedCode
                  (recoveryLegalTermCircuitStageOutput inputLength
                    handoff)) = 0
        · have hbitCapGate :
              recoveryLegalSumBitCapGateOutput inputLength handoff = 0 := by
            simp [recoveryLegalSumBitCapGateOutput, hmassGate,
              recoveryLegalSumFlagGateOutput_pair, hbitCap]
          simp [recoveryLegalSumEnvelopeOutput,
            recoveryLegalSumModeGateOutput, recoveryLegalSumTupleGateOutput,
            recoveryLegalSumQGateOutput, recoveryLegalSumArityGateOutput,
            recoveryLegalSumTermsGateOutput,
            recoveryLegalSumCoefficientGateOutput,
            recoveryLegalSumCircuitGateOutput, hbitCapGate, hbitCap]
        · have hbitCapGate :
              recoveryLegalSumBitCapGateOutput inputLength handoff =
                recoveryLegalTermCircuitStageOutput inputLength handoff := by
            simp [recoveryLegalSumBitCapGateOutput, hmassGate,
              recoveryLegalSumFlagGateOutput_pair, hbitCap]
          by_cases hcircuit :
              recoveryLegalTermCircuitListOutput
                  (recoveryLegalTermCircuitContext handoff)
                  (recoveryLegalTermCoefficientMappedCode inputLength
                    handoff) = 0
          · simp [recoveryLegalSumEnvelopeOutput,
              recoveryLegalSumModeGateOutput,
              recoveryLegalSumTupleGateOutput,
              recoveryLegalSumQGateOutput, recoveryLegalSumArityGateOutput,
              recoveryLegalSumTermsGateOutput,
              recoveryLegalSumCoefficientGateOutput,
              recoveryLegalSumCircuitGateOutput, hbitCapGate,
              recoveryLegalTermCircuitStageOutput,
              recoveryLegalSumFlagGateOutput_pair, hcircuit]
          · rw
              [recoveryLegalSumEnvelopeOutput_eq_of_massBitCapAndCircuitValidation
                inputLength handoff hwire hdescription hmass hbitCap hcircuit]
            simp [hmass, hbitCap, hcircuit, hwire, hdescription]
      · have hbitCapGate :
            recoveryLegalSumBitCapGateOutput inputLength handoff = 0 := by
          have hmassGate :
              recoveryLegalSumMassGateOutput inputLength handoff = 0 := by
            rw [recoveryLegalSumMassGateOutput_eq,
              if_neg (fun haccepts => hmass haccepts.2.2)]
          simp [recoveryLegalSumBitCapGateOutput, hmassGate]
        simp [recoveryLegalSumEnvelopeOutput,
          recoveryLegalSumModeGateOutput, recoveryLegalSumTupleGateOutput,
          recoveryLegalSumQGateOutput, recoveryLegalSumArityGateOutput,
          recoveryLegalSumTermsGateOutput,
          recoveryLegalSumCoefficientGateOutput,
          recoveryLegalSumCircuitGateOutput, hbitCapGate, hmass]

theorem recoveryLegalSumEnvelopeOutput_ne_zero_internal_iff
    (inputLength handoff : ℕ) :
    recoveryLegalSumEnvelopeOutput inputLength handoff ≠ 0 ↔
      recoveryLegalTermCircuitListOutput
          (recoveryLegalTermCircuitContext handoff)
          (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0 ∧
        recoveryLegalTermCoefficientBitCapListOutput
          (recoveryLegalTermBitCapSelectedCap
            (recoveryLegalTermCircuitStageOutput inputLength handoff))
          (recoveryLegalTermBitCapMappedCode
            (recoveryLegalTermCircuitStageOutput inputLength handoff)) ≠ 0 ∧
        recoveryLegalTermMassAccepts inputLength
          (recoveryLegalTermBitCapStageOutput
            (recoveryLegalTermCircuitStageOutput inputLength handoff)) ∧
        recoveryLegalTermCoefficientListOutput inputLength
          (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0 ∧
        recoveryLegalSumTermCount handoff ≤
          handoffSelectedTermCap handoff ∧
        recoveryLegalSumTermsFlag handoff ≠ 0 ∧
        recoveryLegalSumArityFlag handoff ≠ 0 ∧
        recoveryLegalSumQFlag handoff ≠ 0 ∧
        recoveryLegalSumTupleFlag handoff ≠ 0 ∧
        handoffLegalSumModeFlag handoff ≠ 0 ∧
        recoveryLegalTermWireStageValue
          (recoveryLegalSumMassStageOutput inputLength handoff) ≠ 0 ∧
        recoveryLegalTermDescriptionStageValue
          (recoveryLegalSumMassStageOutput inputLength handoff) ≠ 0 := by
  rw [recoveryLegalSumEnvelopeOutput_eq]
  by_cases haccepts :
      recoveryLegalTermCircuitListOutput
          (recoveryLegalTermCircuitContext handoff)
          (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0 ∧
        recoveryLegalTermCoefficientBitCapListOutput
          (recoveryLegalTermBitCapSelectedCap
            (recoveryLegalTermCircuitStageOutput inputLength handoff))
          (recoveryLegalTermBitCapMappedCode
            (recoveryLegalTermCircuitStageOutput inputLength handoff)) ≠ 0 ∧
        recoveryLegalTermMassAccepts inputLength
          (recoveryLegalTermBitCapStageOutput
            (recoveryLegalTermCircuitStageOutput inputLength handoff)) ∧
        recoveryLegalTermCoefficientListOutput inputLength
          (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0 ∧
        recoveryLegalSumTermCount handoff ≤
          handoffSelectedTermCap handoff ∧
        recoveryLegalSumTermsFlag handoff ≠ 0 ∧
        recoveryLegalSumArityFlag handoff ≠ 0 ∧
        recoveryLegalSumQFlag handoff ≠ 0 ∧
        recoveryLegalSumTupleFlag handoff ≠ 0 ∧
        handoffLegalSumModeFlag handoff ≠ 0 ∧
        recoveryLegalTermWireStageValue
          (recoveryLegalSumMassStageOutput inputLength handoff) ≠ 0 ∧
        recoveryLegalTermDescriptionStageValue
          (recoveryLegalSumMassStageOutput inputLength handoff) ≠ 0
  · rw [if_pos haccepts]
    constructor
    · intro _
      exact haccepts
    · intro _ hzero
      subst handoff
      simp [handoffLegalSumModeFlag, handoffMode] at haccepts
  · rw [if_neg haccepts]
    constructor
    · intro hzero
      exact (hzero rfl).elim
    · intro haccepted
      exact (haccepts haccepted).elim

/-- The validated per-term summary tree retained by the circuit stage.  Both
new resource passes consume exactly this value; nothing re-parses a raw term. -/
def recoveryLegalTermValidatedSummaryTree (inputLength handoff : ℕ) : ℕ :=
  (Nat.unpair
    (Nat.unpair
      (recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff))).2).1

def recoveryLegalTermWireCapContext (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalTermBoundExpectedArity handoff)
    (handoffSelectedWireCap handoff)

def recoveryLegalTermDescriptionCapContext (handoff : ℕ) : ℕ :=
  Nat.pair (recoveryLegalTermBoundExpectedArity handoff)
    (handoffSelectedDescriptionCap handoff)

theorem recoveryLegalTermResourceStoredHandoff_massStage_of_le
    (inputLength handoff : ℕ)
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff) :
    recoveryLegalTermResourceStoredHandoff
        (recoveryLegalSumMassStageOutput inputLength handoff) = handoff := by
  simp [recoveryLegalTermResourceStoredHandoff,
    recoveryLegalTermResourceExpectedRest,
    recoveryLegalTermResourceCircuitStage_massStage,
    recoveryLegalTermCircuitStageOutput,
    recoveryLegalTermCoefficientStageOutput,
    recoveryLegalSumBoundOutput, recoveryBoundedContextOutput,
    recoveryLegalSumLengthContext, recoveryLegalSumArityStageOutput,
    recoveryLegalSumArityContext, recoveryLegalSumContext, hle]

theorem recoveryLegalTermResourceExpectedArity_massStage
    (inputLength handoff : ℕ) :
    recoveryLegalTermResourceExpectedArity
        (recoveryLegalSumMassStageOutput inputLength handoff) =
      recoveryLegalTermBoundExpectedArity handoff := by
  rw [recoveryLegalTermResourceExpectedArity_of_circuitStage
    (recoveryLegalTermResourceCircuitStage_massStage inputLength handoff)]
  simp [recoveryLegalTermCircuitArity, recoveryLegalTermCircuitContext]

theorem recoveryLegalTermResourceSummaryTree_massStage
    (inputLength handoff : ℕ) :
    recoveryLegalTermResourceSummaryTree
        (recoveryLegalSumMassStageOutput inputLength handoff) =
      recoveryLegalTermValidatedSummaryTree inputLength handoff :=
  recoveryLegalTermResourceSummaryTree_of_circuitStage
    (recoveryLegalTermResourceCircuitStage_massStage inputLength handoff)

theorem recoveryLegalTermWireStageValue_massStage_of_le
    (inputLength handoff : ℕ)
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff) :
    recoveryLegalTermWireStageValue
        (recoveryLegalSumMassStageOutput inputLength handoff) =
      recoveryLegalTermWireListOutput
        (recoveryLegalTermWireCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) := by
  simp only [recoveryLegalTermWireStageValue, recoveryLegalTermWireContext,
    recoveryLegalTermWireCapContext,
    recoveryLegalTermResourceExpectedArity_massStage,
    recoveryLegalTermResourceStoredHandoff_massStage_of_le inputLength
      handoff hle,
    recoveryLegalTermResourceSummaryTree_massStage]

theorem recoveryLegalTermDescriptionStageValue_massStage_of_le
    (inputLength handoff : ℕ)
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff) :
    recoveryLegalTermDescriptionStageValue
        (recoveryLegalSumMassStageOutput inputLength handoff) =
      recoveryLegalTermDescriptionListOutput
        (recoveryLegalTermDescriptionCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) := by
  simp only [recoveryLegalTermDescriptionStageValue,
    recoveryLegalTermDescriptionContext,
    recoveryLegalTermDescriptionCapContext,
    recoveryLegalTermResourceExpectedArity_massStage,
    recoveryLegalTermResourceStoredHandoff_massStage_of_le inputLength
      handoff hle,
    recoveryLegalTermResourceSummaryTree_massStage]

set_option maxHeartbeats 1200000 in
-- Twelve conjuncts are translated one at a time onto their public projections.
theorem recoveryLegalSumEnvelopeOutput_ne_zero_iff
    (inputLength handoff : ℕ) :
    recoveryLegalSumEnvelopeOutput inputLength handoff ≠ 0 ↔
      recoveryLegalTermCircuitListOutput
          (recoveryLegalTermCircuitContext handoff)
          (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0 ∧
        recoveryLegalTermCoefficientBitCapListOutput
          (handoffSelectedCoefficientBitCap handoff)
          (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0 ∧
        recoveryLegalTermCoefficientMassWithinCap inputLength handoff ∧
        recoveryLegalTermCoefficientListOutput inputLength
          (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0 ∧
        recoveryLegalSumTermCount handoff ≤
          handoffSelectedTermCap handoff ∧
        recoveryLegalSumTermsFlag handoff ≠ 0 ∧
        recoveryLegalSumArityFlag handoff ≠ 0 ∧
        recoveryLegalSumQFlag handoff ≠ 0 ∧
        recoveryLegalSumTupleFlag handoff ≠ 0 ∧
        handoffLegalSumModeFlag handoff ≠ 0 ∧
        recoveryLegalTermWireListOutput
          (recoveryLegalTermWireCapContext handoff)
          (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0 ∧
        recoveryLegalTermDescriptionListOutput
          (recoveryLegalTermDescriptionCapContext handoff)
          (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠
            0 := by
  rw [recoveryLegalSumEnvelopeOutput_ne_zero_internal_iff]
  constructor
  · rintro ⟨hcircuit, hbitCap, hmass, hcoefficient, hle, hterms, harity, hq,
      htuple, hmode, hwire, hdescription⟩
    have hselected :=
      recoveryLegalTermBitCapSelectedCap_circuitStage_of_le
        inputLength handoff hle
    have hbitCapSelected :
        recoveryLegalTermCoefficientBitCapListOutput
            (handoffSelectedCoefficientBitCap handoff)
            (recoveryLegalTermCoefficientMappedCode inputLength
              handoff) ≠ 0 := by
      simpa [hselected, recoveryLegalTermBitCapMappedCode_circuitStage]
        using hbitCap
    have hmassCap :
        recoveryLegalTermCoefficientMassWithinCap inputLength handoff :=
      (recoveryLegalTermMassAccepts_iff_coefficientMassWithinCap
        inputLength handoff).1 hmass
    have hwireList :
        recoveryLegalTermWireListOutput
            (recoveryLegalTermWireCapContext handoff)
            (recoveryLegalTermValidatedSummaryTree inputLength
              handoff) ≠ 0 := by
      rw [recoveryLegalTermWireStageValue_massStage_of_le inputLength
        handoff hle] at hwire
      exact hwire
    have hdescriptionList :
        recoveryLegalTermDescriptionListOutput
            (recoveryLegalTermDescriptionCapContext handoff)
            (recoveryLegalTermValidatedSummaryTree inputLength
              handoff) ≠ 0 := by
      rw [recoveryLegalTermDescriptionStageValue_massStage_of_le
        inputLength handoff hle] at hdescription
      exact hdescription
    exact ⟨hcircuit, hbitCapSelected, hmassCap, hcoefficient, hle, hterms,
      harity, hq, htuple, hmode, hwireList, hdescriptionList⟩
  · rintro ⟨hcircuit, hbitCap, hmass, hcoefficient, hle, hterms, harity, hq,
      htuple, hmode, hwire, hdescription⟩
    have hselected :=
      recoveryLegalTermBitCapSelectedCap_circuitStage_of_le
        inputLength handoff hle
    have hbitCapStage :
        recoveryLegalTermCoefficientBitCapListOutput
            (recoveryLegalTermBitCapSelectedCap
              (recoveryLegalTermCircuitStageOutput inputLength handoff))
            (recoveryLegalTermBitCapMappedCode
              (recoveryLegalTermCircuitStageOutput inputLength
                handoff)) ≠ 0 := by
      simpa [hselected, recoveryLegalTermBitCapMappedCode_circuitStage]
        using hbitCap
    have hmassAccepts :
        recoveryLegalTermMassAccepts inputLength
          (recoveryLegalTermBitCapStageOutput
            (recoveryLegalTermCircuitStageOutput inputLength handoff)) :=
      (recoveryLegalTermMassAccepts_iff_coefficientMassWithinCap
        inputLength handoff).2 hmass
    have hwireStage :
        recoveryLegalTermWireStageValue
          (recoveryLegalSumMassStageOutput inputLength handoff) ≠ 0 := by
      rw [recoveryLegalTermWireStageValue_massStage_of_le inputLength
        handoff hle]
      exact hwire
    have hdescriptionStage :
        recoveryLegalTermDescriptionStageValue
          (recoveryLegalSumMassStageOutput inputLength handoff) ≠ 0 := by
      rw [recoveryLegalTermDescriptionStageValue_massStage_of_le
        inputLength handoff hle]
      exact hdescription
    exact ⟨hcircuit, hbitCapStage, hmassAccepts, hcoefficient, hle, hterms,
      harity, hq, htuple, hmode, hwireStage, hdescriptionStage⟩

theorem recoveryValidatorLegalSumPrefixOutput_ne_zero_iff
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0 ↔
      let handoff := recoveryValidatorOraclePrefixOutput limits raw
      recoveryLegalTermCircuitListOutput
          (recoveryLegalTermCircuitContext handoff)
          (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0 ∧
        recoveryLegalTermCoefficientBitCapListOutput
          (handoffSelectedCoefficientBitCap handoff)
          (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0 ∧
        recoveryLegalTermCoefficientMassWithinCap inputLength handoff ∧
        recoveryLegalTermCoefficientListOutput inputLength
          (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0 ∧
        recoveryLegalSumTermCount handoff ≤
          handoffSelectedTermCap handoff ∧
        recoveryLegalSumTermsFlag handoff ≠ 0 ∧
        recoveryLegalSumArityFlag handoff ≠ 0 ∧
        recoveryLegalSumQFlag handoff ≠ 0 ∧
        recoveryLegalSumTupleFlag handoff ≠ 0 ∧
        handoffLegalSumModeFlag handoff ≠ 0 ∧
        recoveryLegalTermWireListOutput
          (recoveryLegalTermWireCapContext handoff)
          (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0 ∧
        recoveryLegalTermDescriptionListOutput
          (recoveryLegalTermDescriptionCapContext handoff)
          (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠
            0 := by
  exact recoveryLegalSumEnvelopeOutput_ne_zero_iff inputLength
    (recoveryValidatorOraclePrefixOutput limits raw)

/-! ## Fail-closed regressions for the staged validator

Every entry below is a kernel-checked minimal counterexample class for the
staged validator: each names one hostile coordinate and shows that the single
public output collapses to zero.  Rejection always happens at the owning gate,
so no later stage ever unpairs or projects a sentinel. -/

private theorem recoveryValidatorLegalSumPrefixOutput_eq_zero_of_reject
    {inputLength : ℕ} {limits : RecoveryWitnessLimits} {raw : ℕ}
    (hreject :
      ¬ (recoveryLegalSumEnvelopeOutput inputLength
        (recoveryValidatorOraclePrefixOutput limits raw) ≠ 0)) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0 :=
  not_not.mp hreject

/-- Malformed nested circuit syntax: the per-term circuit validator rejects,
so the whole legal sum is rejected. -/
theorem recoveryValidatorLegalSumPrefixOutput_eq_zero_of_malformed_circuit
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext
          (recoveryValidatorOraclePrefixOutput limits raw))
        (recoveryLegalTermCoefficientMappedCode inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) = 0) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0 :=
  recoveryValidatorLegalSumPrefixOutput_eq_zero_of_reject (fun hnonzero =>
    ((recoveryLegalSumEnvelopeOutput_ne_zero_iff inputLength
      (recoveryValidatorOraclePrefixOutput limits raw)).1 hnonzero).1 hcircuit)

/-- Coefficient-bit overflow: a coefficient wider than the schedule-selected
bit cap is rejected. -/
theorem
    recoveryValidatorLegalSumPrefixOutput_eq_zero_of_coefficientBitOverflow
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hbitCap :
      recoveryLegalTermCoefficientBitCapListOutput
        (handoffSelectedCoefficientBitCap
          (recoveryValidatorOraclePrefixOutput limits raw))
        (recoveryLegalTermCoefficientMappedCode inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) = 0) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0 :=
  recoveryValidatorLegalSumPrefixOutput_eq_zero_of_reject (fun hnonzero =>
    ((recoveryLegalSumEnvelopeOutput_ne_zero_iff inputLength
      (recoveryValidatorOraclePrefixOutput limits raw)).1 hnonzero).2.1
      hbitCap)

/-- Exact-mass overflow: an exact rational coefficient mass outside the
schedule-selected mass cap is rejected at the mass gate. -/
theorem recoveryValidatorLegalSumPrefixOutput_eq_zero_of_massOverflow
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hmass :
      ¬ recoveryLegalTermCoefficientMassWithinCap inputLength
        (recoveryValidatorOraclePrefixOutput limits raw)) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0 :=
  recoveryValidatorLegalSumPrefixOutput_eq_zero_of_reject (fun hnonzero =>
    hmass
      ((recoveryLegalSumEnvelopeOutput_ne_zero_iff inputLength
        (recoveryValidatorOraclePrefixOutput limits raw)).1 hnonzero).2.2.1)

/-- Zero denominator, or any other rejected canonical rational syntax, fails
the per-term coefficient validator. -/
theorem recoveryValidatorLegalSumPrefixOutput_eq_zero_of_rationalReject
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode
          (recoveryValidatorOraclePrefixOutput limits raw)) = 0) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0 :=
  recoveryValidatorLegalSumPrefixOutput_eq_zero_of_reject (fun hnonzero =>
    ((recoveryLegalSumEnvelopeOutput_ne_zero_iff inputLength
      (recoveryValidatorOraclePrefixOutput limits raw)).1
        hnonzero).2.2.2.1 hcoefficient)

/-- Term-count overflow at the smallest boundary value: one term beyond the
schedule-selected cap is rejected. -/
theorem recoveryValidatorLegalSumPrefixOutput_eq_zero_of_termCountOverflow
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hcount :
      handoffSelectedTermCap (recoveryValidatorOraclePrefixOutput limits raw)
        < recoveryLegalSumTermCount
          (recoveryValidatorOraclePrefixOutput limits raw)) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0 :=
  recoveryValidatorLegalSumPrefixOutput_eq_zero_of_reject (fun hnonzero =>
    absurd
      ((recoveryLegalSumEnvelopeOutput_ne_zero_iff inputLength
        (recoveryValidatorOraclePrefixOutput limits raw)).1
          hnonzero).2.2.2.2.1
      (Nat.not_le.mpr hcount))

/-- A wrong recovery mode is rejected by the mode gate. -/
theorem recoveryValidatorLegalSumPrefixOutput_eq_zero_of_wrongMode
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hmode :
      handoffLegalSumModeFlag
        (recoveryValidatorOraclePrefixOutput limits raw) = 0) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0 :=
  recoveryValidatorLegalSumPrefixOutput_eq_zero_of_reject (fun hnonzero =>
    ((recoveryLegalSumEnvelopeOutput_ne_zero_iff inputLength
      (recoveryValidatorOraclePrefixOutput limits raw)).1
        hnonzero).2.2.2.2.2.2.2.2.2.1 hmode)

@[simp] theorem recoveryLegalTermResourceArity_wireCapContext
    (handoff : ℕ) :
    recoveryLegalTermResourceArity
        (recoveryLegalTermWireCapContext handoff) =
      recoveryLegalTermBoundExpectedArity handoff := by
  simp [recoveryLegalTermResourceArity, recoveryLegalTermWireCapContext]

@[simp] theorem recoveryLegalTermResourceCap_wireCapContext (handoff : ℕ) :
    recoveryLegalTermResourceCap (recoveryLegalTermWireCapContext handoff) =
      handoffSelectedWireCap handoff := by
  simp [recoveryLegalTermResourceCap, recoveryLegalTermWireCapContext]

@[simp] theorem recoveryLegalTermResourceArity_descriptionCapContext
    (handoff : ℕ) :
    recoveryLegalTermResourceArity
        (recoveryLegalTermDescriptionCapContext handoff) =
      recoveryLegalTermBoundExpectedArity handoff := by
  simp [recoveryLegalTermResourceArity,
    recoveryLegalTermDescriptionCapContext]

@[simp] theorem recoveryLegalTermResourceCap_descriptionCapContext
    (handoff : ℕ) :
    recoveryLegalTermResourceCap
        (recoveryLegalTermDescriptionCapContext handoff) =
      handoffSelectedDescriptionCap handoff := by
  simp [recoveryLegalTermResourceCap,
    recoveryLegalTermDescriptionCapContext]

/-- Wire overflow: a validated term whose exact physical wire count exceeds the
schedule-selected wire cap is rejected at the wire gate. -/
theorem recoveryValidatorLegalSumPrefixOutput_eq_zero_of_wireOverflow
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hwire :
      recoveryLegalTermWireListOutput
        (recoveryLegalTermWireCapContext
          (recoveryValidatorOraclePrefixOutput limits raw))
        (recoveryLegalTermValidatedSummaryTree inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) = 0) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0 :=
  recoveryValidatorLegalSumPrefixOutput_eq_zero_of_reject (fun hnonzero =>
    ((recoveryLegalSumEnvelopeOutput_ne_zero_iff inputLength
      (recoveryValidatorOraclePrefixOutput limits raw)).1
        hnonzero).2.2.2.2.2.2.2.2.2.2.1 hwire)

/-- Description overflow: a validated term whose exact encoding length exceeds
the schedule-selected description cap is rejected at the description gate. -/
theorem recoveryValidatorLegalSumPrefixOutput_eq_zero_of_descriptionOverflow
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hdescription :
      recoveryLegalTermDescriptionListOutput
        (recoveryLegalTermDescriptionCapContext
          (recoveryValidatorOraclePrefixOutput limits raw))
        (recoveryLegalTermValidatedSummaryTree inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) = 0) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0 :=
  recoveryValidatorLegalSumPrefixOutput_eq_zero_of_reject (fun hnonzero =>
    ((recoveryLegalSumEnvelopeOutput_ne_zero_iff inputLength
      (recoveryValidatorOraclePrefixOutput limits raw)).1
        hnonzero).2.2.2.2.2.2.2.2.2.2.2 hdescription)

/-- Wire overflow at the smallest boundary value: one validated term whose
exact wire count is exactly one unit past the cap collapses the single public
output to zero. -/
theorem recoveryValidatorLegalSumPrefixOutput_eq_zero_of_wireBoundary
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    {summaries : List ℕ} {summary : ℕ}
    (hdecode :
      decodeBalancedList
          (recoveryLegalTermValidatedSummaryTree inputLength
            (recoveryValidatorOraclePrefixOutput limits raw)) =
        some summaries)
    (hsummary : summary ∈ summaries)
    (hoverflow :
      normalizedCircuitResourceMetric summary =
        handoffSelectedWireCap
            (recoveryValidatorOraclePrefixOutput limits raw) + 1) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0 :=
  recoveryValidatorLegalSumPrefixOutput_eq_zero_of_wireOverflow inputLength
    limits raw
    (recoveryLegalTermWireListOutput_eq_zero_of_wireOverflow
      (recoveryLegalTermWireCapContext
        (recoveryValidatorOraclePrefixOutput limits raw))
      (recoveryLegalTermValidatedSummaryTree inputLength
        (recoveryValidatorOraclePrefixOutput limits raw))
      hdecode hsummary (by simpa using hoverflow))

/-- Description overflow at the smallest boundary value. -/
theorem recoveryValidatorLegalSumPrefixOutput_eq_zero_of_descriptionBoundary
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    {summaries : List ℕ} {summary : ℕ}
    (hdecode :
      decodeBalancedList
          (recoveryLegalTermValidatedSummaryTree inputLength
            (recoveryValidatorOraclePrefixOutput limits raw)) =
        some summaries)
    (hsummary : summary ∈ summaries)
    (hoverflow :
      normalizedCircuitDescriptionMetric
          (recoveryLegalTermBoundExpectedArity
            (recoveryValidatorOraclePrefixOutput limits raw)) summary =
        handoffSelectedDescriptionCap
            (recoveryValidatorOraclePrefixOutput limits raw) + 1) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0 :=
  recoveryValidatorLegalSumPrefixOutput_eq_zero_of_descriptionOverflow
    inputLength limits raw
    (recoveryLegalTermDescriptionListOutput_eq_zero_of_descriptionOverflow
      (recoveryLegalTermDescriptionCapContext
        (recoveryValidatorOraclePrefixOutput limits raw))
      (recoveryLegalTermValidatedSummaryTree inputLength
        (recoveryValidatorOraclePrefixOutput limits raw))
      hdecode hsummary (by simpa using hoverflow))

/-- Acceptance of the staged validator forces the exact physical wire charge of
every validated term to lie within the schedule-selected wire cap. -/
theorem recoveryValidatorLegalSumPrefixOutput_wireBounds
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (haccepts :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0) :
    ∃ summaries,
      decodeBalancedList
          (recoveryLegalTermValidatedSummaryTree inputLength
            (recoveryValidatorOraclePrefixOutput limits raw)) =
        some summaries ∧
        ∀ summary ∈ summaries,
          normalizedCircuitResourceMetric summary ≤
            handoffSelectedWireCap
              (recoveryValidatorOraclePrefixOutput limits raw) := by
  have hwire :=
    ((recoveryLegalSumEnvelopeOutput_ne_zero_iff inputLength
      (recoveryValidatorOraclePrefixOutput limits raw)).1
        haccepts).2.2.2.2.2.2.2.2.2.2.1
  simpa using
    (recoveryLegalTermWireListOutput_ne_zero_iff
      (recoveryLegalTermWireCapContext
        (recoveryValidatorOraclePrefixOutput limits raw))
      (recoveryLegalTermValidatedSummaryTree inputLength
        (recoveryValidatorOraclePrefixOutput limits raw))).1 hwire

/-- Acceptance likewise forces the exact circuit-description charge of every
validated term to lie within the schedule-selected description cap.  The charge
is the description metric, not the wire metric. -/
theorem recoveryValidatorLegalSumPrefixOutput_descriptionBounds
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (haccepts :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0) :
    ∃ summaries,
      decodeBalancedList
          (recoveryLegalTermValidatedSummaryTree inputLength
            (recoveryValidatorOraclePrefixOutput limits raw)) =
        some summaries ∧
        ∀ summary ∈ summaries,
          normalizedCircuitDescriptionMetric
              (recoveryLegalTermBoundExpectedArity
                (recoveryValidatorOraclePrefixOutput limits raw))
              summary ≤
            handoffSelectedDescriptionCap
              (recoveryValidatorOraclePrefixOutput limits raw) := by
  have hdescription :=
    ((recoveryLegalSumEnvelopeOutput_ne_zero_iff inputLength
      (recoveryValidatorOraclePrefixOutput limits raw)).1
        haccepts).2.2.2.2.2.2.2.2.2.2.2
  simpa using
    (recoveryLegalTermDescriptionListOutput_ne_zero_iff
      (recoveryLegalTermDescriptionCapContext
        (recoveryValidatorOraclePrefixOutput limits raw))
      (recoveryLegalTermValidatedSummaryTree inputLength
        (recoveryValidatorOraclePrefixOutput limits raw))).1 hdescription

/-! ## Typed limits recovered from the accepted staged handoff

Every acceptance conjunct of the staged validator is stated against a
positional projection of one packed configuration word.  The lemmas below prove
that on the accepting path each projection is exactly the corresponding typed
field of the caller's `RecoveryWitnessLimits`, so no conjunct can ever be
discharged against a cap other than the configured one. -/

@[simp] private theorem recoveryOracleValidationOutput_zero :
    recoveryOracleValidationOutput 0 = 0 := by
  unfold recoveryOracleValidationOutput recoveryBoundedContextOutput
    recoveryOracleBoundContext
  split_ifs <;> rfl

private theorem recoveryOracleValidationOutput_eq_zero_or_self
    (handoff : ℕ) :
    recoveryOracleValidationOutput handoff = 0 ∨
      recoveryOracleValidationOutput handoff = handoff := by
  unfold recoveryOracleValidationOutput recoveryBoundedContextOutput
    recoveryOracleBoundContext
  split_ifs <;> simp

private theorem recoveryNestedPresenceOutput_eq_zero_or_self
    (handoff : ℕ) :
    recoveryNestedPresenceOutput handoff = 0 ∨
      recoveryNestedPresenceOutput handoff = handoff := by
  unfold recoveryNestedPresenceOutput
  split_ifs <;> simp

/-- The nested-presence stage is a pure guard: it never rewrites the handoff. -/
theorem recoveryValidatorStructuralPrefixOutput_eq_handoff
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorStructuralPrefixOutput limits raw ≠ 0) :
    recoveryValidatorStructuralPrefixOutput limits raw =
      recoveryValidatorHandoffOutput limits raw := by
  rw [recoveryValidatorStructuralPrefixOutput] at haccepts ⊢
  rcases recoveryNestedPresenceOutput_eq_zero_or_self
      (recoveryValidatorHandoffOutput limits raw) with hzero | hself
  · exact absurd hzero haccepts
  · exact hself

/-- The Boolean-DAG stage is likewise a pure guard on the same handoff. -/
theorem recoveryValidatorOraclePrefixOutput_eq_handoff
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    recoveryValidatorOraclePrefixOutput limits raw =
      recoveryValidatorHandoffOutput limits raw := by
  rw [recoveryValidatorOraclePrefixOutput] at haccepts ⊢
  rcases recoveryOracleValidationOutput_eq_zero_or_self
      (recoveryValidatorStructuralPrefixOutput limits raw) with hzero | hself
  · exact absurd hzero haccepts
  · rw [hself] at haccepts ⊢
    exact recoveryValidatorStructuralPrefixOutput_eq_handoff haccepts

private theorem recoveryValidatorHandoffOutput_ne_zero_of_prefix
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    recoveryValidatorHandoffOutput limits raw ≠ 0 := by
  rw [← recoveryValidatorOraclePrefixOutput_eq_handoff haccepts]
  exact haccepts

private theorem recoveryValidatorHandoffOutput_eq_pair
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorHandoffOutput limits raw ≠ 0) :
    recoveryValidatorHandoffOutput limits raw =
      Nat.pair (Nat.unpair (recoveryEnvelopeOutput raw)).1
        (Nat.pair raw
          (Nat.pair (recoveryEnvelopeOracleCode raw)
            (Nat.pair (recoveryEnvelopeSumCode raw)
              (encodeRecoveryWitnessLimits limits)))) := by
  by_cases hzero : recoveryEnvelopeOutput raw = 0
  · exact absurd (by simp [recoveryValidatorHandoffOutput, hzero]) haccepts
  · simp [recoveryValidatorHandoffOutput, hzero]

/-- The packed configuration word survives the whole staged prefix unchanged. -/
theorem handoffLimitsCode_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffLimitsCode (recoveryValidatorOraclePrefixOutput limits raw) =
      encodeRecoveryWitnessLimits limits := by
  rw [recoveryValidatorOraclePrefixOutput_eq_handoff haccepts,
    recoveryValidatorHandoffOutput_eq_pair
      (recoveryValidatorHandoffOutput_ne_zero_of_prefix haccepts)]
  simp [handoffLimitsCode]

theorem handoffMode_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffMode (recoveryValidatorOraclePrefixOutput limits raw) =
      (Nat.unpair (recoveryEnvelopeOutput raw)).1 := by
  rw [recoveryValidatorOraclePrefixOutput_eq_handoff haccepts,
    recoveryValidatorHandoffOutput_eq_pair
      (recoveryValidatorHandoffOutput_ne_zero_of_prefix haccepts)]
  simp [handoffMode]

theorem handoffOracleCode_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffOracleCode (recoveryValidatorOraclePrefixOutput limits raw) =
      recoveryEnvelopeOracleCode raw := by
  rw [recoveryValidatorOraclePrefixOutput_eq_handoff haccepts,
    recoveryValidatorHandoffOutput_eq_pair
      (recoveryValidatorHandoffOutput_ne_zero_of_prefix haccepts)]
  simp [handoffOracleCode]

theorem handoffSumCode_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffSumCode (recoveryValidatorOraclePrefixOutput limits raw) =
      recoveryEnvelopeSumCode raw := by
  rw [recoveryValidatorOraclePrefixOutput_eq_handoff haccepts,
    recoveryValidatorHandoffOutput_eq_pair
      (recoveryValidatorHandoffOutput_ne_zero_of_prefix haccepts)]
  simp [handoffSumCode]

/-! ### Positional projections of the packed configuration -/

theorem handoffOracleArity_of_limitsCode
    {handoff : ℕ} {limits : RecoveryWitnessLimits}
    (hcode : handoffLimitsCode handoff = encodeRecoveryWitnessLimits limits) :
    handoffOracleArity handoff = limits.oracleArity := by
  simp [handoffOracleArity, hcode, encodeRecoveryWitnessLimits]

theorem handoffOracleSizeCap_of_limitsCode
    {handoff : ℕ} {limits : RecoveryWitnessLimits}
    (hcode : handoffLimitsCode handoff = encodeRecoveryWitnessLimits limits) :
    handoffOracleSizeCap handoff = limits.oracleSizeCap := by
  simp [handoffOracleSizeCap, hcode, encodeRecoveryWitnessLimits]

theorem handoffSumArity_of_limitsCode
    {handoff : ℕ} {limits : RecoveryWitnessLimits}
    (hcode : handoffLimitsCode handoff = encodeRecoveryWitnessLimits limits) :
    handoffSumArity handoff = limits.sumArity := by
  simp [handoffSumArity, hcode, encodeRecoveryWitnessLimits]

private theorem handoffLegalLimitsPair_of_limitsCode
    {handoff : ℕ} {limits : RecoveryWitnessLimits}
    (hcode : handoffLimitsCode handoff = encodeRecoveryWitnessLimits limits) :
    handoffLegalLimitsPair handoff =
      Nat.pair (encodeLegalSumLimits limits.symmetric)
        (encodeLegalSumLimits limits.threshold) := by
  simp [handoffLegalLimitsPair, hcode, encodeRecoveryWitnessLimits]

theorem handoffSelectedLegalLimits_of_limitsCode_symmetric
    {handoff : ℕ} {limits : RecoveryWitnessLimits}
    (hcode : handoffLimitsCode handoff = encodeRecoveryWitnessLimits limits)
    (hmode : handoffMode handoff = 1) :
    handoffSelectedLegalLimits handoff =
      encodeLegalSumLimits limits.symmetric := by
  simp [handoffSelectedLegalLimits, hmode,
    handoffLegalLimitsPair_of_limitsCode hcode]

theorem handoffSelectedLegalLimits_of_limitsCode_threshold
    {handoff : ℕ} {limits : RecoveryWitnessLimits}
    (hcode : handoffLimitsCode handoff = encodeRecoveryWitnessLimits limits)
    (hmode : handoffMode handoff = 2) :
    handoffSelectedLegalLimits handoff =
      encodeLegalSumLimits limits.threshold := by
  simp [handoffSelectedLegalLimits, hmode,
    handoffLegalLimitsPair_of_limitsCode hcode]

theorem handoffSelectedExpectedArity_of_encode
    {handoff : ℕ} {policy : LegalSumLimits}
    (hselected :
      handoffSelectedLegalLimits handoff = encodeLegalSumLimits policy) :
    handoffSelectedExpectedArity handoff = policy.expectedArity := by
  simp [handoffSelectedExpectedArity, hselected, encodeLegalSumLimits]

theorem handoffSelectedTermCap_of_encode
    {handoff : ℕ} {policy : LegalSumLimits}
    (hselected :
      handoffSelectedLegalLimits handoff = encodeLegalSumLimits policy) :
    handoffSelectedTermCap handoff = policy.termCap := by
  simp [handoffSelectedTermCap, hselected, encodeLegalSumLimits]

theorem handoffSelectedCoefficientBitCap_of_encode
    {handoff : ℕ} {policy : LegalSumLimits}
    (hselected :
      handoffSelectedLegalLimits handoff = encodeLegalSumLimits policy) :
    handoffSelectedCoefficientBitCap handoff = policy.coefficientBitCap := by
  simp [handoffSelectedCoefficientBitCap, hselected, encodeLegalSumLimits]

theorem handoffSelectedCoefficientMassCapCode_of_encode
    {handoff : ℕ} {policy : LegalSumLimits}
    (hselected :
      handoffSelectedLegalLimits handoff = encodeLegalSumLimits policy) :
    handoffSelectedCoefficientMassCapCode handoff =
      encodeCanonicalRational policy.coefficientMassCap := by
  simp [handoffSelectedCoefficientMassCapCode, hselected,
    encodeLegalSumLimits]

theorem handoffSelectedWireCap_of_encode
    {handoff : ℕ} {policy : LegalSumLimits}
    (hselected :
      handoffSelectedLegalLimits handoff = encodeLegalSumLimits policy) :
    handoffSelectedWireCap handoff = policy.wireCap := by
  simp [handoffSelectedWireCap, hselected, encodeLegalSumLimits]

theorem handoffSelectedDescriptionCap_of_encode
    {handoff : ℕ} {policy : LegalSumLimits}
    (hselected :
      handoffSelectedLegalLimits handoff = encodeLegalSumLimits policy) :
    handoffSelectedDescriptionCap handoff = policy.descriptionCap := by
  simp [handoffSelectedDescriptionCap, hselected, encodeLegalSumLimits]

/-! ### Mode selection on the accepting path -/

private theorem recoveryEnvelopeOutput_eq_pair_of_decode
    {raw : ℕ} {envelope : RecoveryEnvelope}
    (hdecode : decodeRecoveryEnvelope raw = some envelope) :
    recoveryEnvelopeOutput raw =
      Nat.pair (RecoveryEnvelope.outputTag envelope.mode) raw := by
  unfold recoveryEnvelopeOutput
  rw [hdecode]

private theorem recoveryEnvelopeOutput_eq_zero_of_decode
    {raw : ℕ} (hdecode : decodeRecoveryEnvelope raw = none) :
    recoveryEnvelopeOutput raw = 0 := by
  unfold recoveryEnvelopeOutput
  rw [hdecode]

/-- Acceptance forces the outer envelope to decode; the executable mode tag is
then exactly the decoded envelope's tag. -/
theorem recoveryValidatorOraclePrefix_decodeRecoveryEnvelope
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    ∃ envelope, decodeRecoveryEnvelope raw = some envelope ∧
      handoffMode (recoveryValidatorOraclePrefixOutput limits raw) =
        RecoveryEnvelope.outputTag envelope.mode := by
  have hhandoff := recoveryValidatorHandoffOutput_ne_zero_of_prefix haccepts
  have hnonzero : recoveryEnvelopeOutput raw ≠ 0 := by
    intro hzero
    exact hhandoff (by simp [recoveryValidatorHandoffOutput, hzero])
  cases hdecode : decodeRecoveryEnvelope raw with
  | none =>
      exact
        absurd (recoveryEnvelopeOutput_eq_zero_of_decode hdecode) hnonzero
  | some envelope =>
      refine ⟨envelope, rfl, ?_⟩
      rw [handoffMode_oraclePrefixOutput haccepts,
        recoveryEnvelopeOutput_eq_pair_of_decode hdecode]
      simp

/-- On the accepting path the executable mode tag is one of the two configured
branch tags; there is no third accepted family. -/
theorem handoffMode_oraclePrefixOutput_cases
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffMode (recoveryValidatorOraclePrefixOutput limits raw) = 1 ∨
      handoffMode (recoveryValidatorOraclePrefixOutput limits raw) = 2 := by
  obtain ⟨envelope, _, hmode⟩ :=
    recoveryValidatorOraclePrefix_decodeRecoveryEnvelope haccepts
  cases hbranch : envelope.mode with
  | symmetric =>
      left
      rw [hmode, hbranch]
      rfl
  | threshold =>
      right
      rw [hmode, hbranch]
      rfl

/-- The mode-selected legal-sum policy read by the staged validator. -/
def recoveryValidatorSelectedPolicy
    (limits : RecoveryWitnessLimits) (raw : ℕ) : LegalSumLimits :=
  if handoffMode (recoveryValidatorOraclePrefixOutput limits raw) = 1 then
    limits.symmetric
  else
    limits.threshold

theorem recoveryValidatorSelectedPolicy_symmetric
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (hmode : handoffMode (recoveryValidatorOraclePrefixOutput limits raw) = 1) :
    recoveryValidatorSelectedPolicy limits raw = limits.symmetric := by
  simp [recoveryValidatorSelectedPolicy, hmode]

theorem recoveryValidatorSelectedPolicy_threshold
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (hmode : handoffMode (recoveryValidatorOraclePrefixOutput limits raw) = 2) :
    recoveryValidatorSelectedPolicy limits raw = limits.threshold := by
  simp [recoveryValidatorSelectedPolicy, hmode]

/-- Master limits-recovery statement: the mode-selected packed policy read by
every legal-sum conjunct is the encoding of a genuine typed branch policy. -/
theorem handoffSelectedLegalLimits_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffSelectedLegalLimits (recoveryValidatorOraclePrefixOutput limits raw) =
      encodeLegalSumLimits (recoveryValidatorSelectedPolicy limits raw) := by
  have hcode := handoffLimitsCode_oraclePrefixOutput haccepts
  rcases handoffMode_oraclePrefixOutput_cases haccepts with hmode | hmode
  · rw [recoveryValidatorSelectedPolicy_symmetric hmode]
    exact handoffSelectedLegalLimits_of_limitsCode_symmetric hcode hmode
  · rw [recoveryValidatorSelectedPolicy_threshold hmode]
    exact handoffSelectedLegalLimits_of_limitsCode_threshold hcode hmode

theorem handoffSelectedExpectedArity_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffSelectedExpectedArity
        (recoveryValidatorOraclePrefixOutput limits raw) =
      (recoveryValidatorSelectedPolicy limits raw).expectedArity :=
  handoffSelectedExpectedArity_of_encode
    (handoffSelectedLegalLimits_oraclePrefixOutput haccepts)

theorem handoffSelectedTermCap_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffSelectedTermCap (recoveryValidatorOraclePrefixOutput limits raw) =
      (recoveryValidatorSelectedPolicy limits raw).termCap :=
  handoffSelectedTermCap_of_encode
    (handoffSelectedLegalLimits_oraclePrefixOutput haccepts)

theorem handoffSelectedCoefficientBitCap_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffSelectedCoefficientBitCap
        (recoveryValidatorOraclePrefixOutput limits raw) =
      (recoveryValidatorSelectedPolicy limits raw).coefficientBitCap :=
  handoffSelectedCoefficientBitCap_of_encode
    (handoffSelectedLegalLimits_oraclePrefixOutput haccepts)

theorem handoffSelectedCoefficientMassCapCode_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffSelectedCoefficientMassCapCode
        (recoveryValidatorOraclePrefixOutput limits raw) =
      encodeCanonicalRational
        (recoveryValidatorSelectedPolicy limits raw).coefficientMassCap :=
  handoffSelectedCoefficientMassCapCode_of_encode
    (handoffSelectedLegalLimits_oraclePrefixOutput haccepts)

theorem handoffSelectedWireCap_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffSelectedWireCap (recoveryValidatorOraclePrefixOutput limits raw) =
      (recoveryValidatorSelectedPolicy limits raw).wireCap :=
  handoffSelectedWireCap_of_encode
    (handoffSelectedLegalLimits_oraclePrefixOutput haccepts)

theorem handoffSelectedDescriptionCap_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffSelectedDescriptionCap
        (recoveryValidatorOraclePrefixOutput limits raw) =
      (recoveryValidatorSelectedPolicy limits raw).descriptionCap :=
  handoffSelectedDescriptionCap_of_encode
    (handoffSelectedLegalLimits_oraclePrefixOutput haccepts)

theorem handoffOracleArity_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffOracleArity (recoveryValidatorOraclePrefixOutput limits raw) =
      limits.oracleArity :=
  handoffOracleArity_of_limitsCode
    (handoffLimitsCode_oraclePrefixOutput haccepts)

theorem handoffOracleSizeCap_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffOracleSizeCap (recoveryValidatorOraclePrefixOutput limits raw) =
      limits.oracleSizeCap :=
  handoffOracleSizeCap_of_limitsCode
    (handoffLimitsCode_oraclePrefixOutput haccepts)

theorem handoffSumArity_oraclePrefixOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    handoffSumArity (recoveryValidatorOraclePrefixOutput limits raw) =
      limits.sumArity :=
  handoffSumArity_of_limitsCode
    (handoffLimitsCode_oraclePrefixOutput haccepts)

/-! ## Acceptance criterion for the structural and Boolean-DAG prefix

The staged prefix composes the outer three-field envelope parser, the
nested-presence guard, and the complete Boolean-DAG validator.  The theorem
below records its exact acceptance condition against the pure canonical
decoders, leaving no intermediate register ABI in the statement. -/

private theorem recoveryNestedPresenceOutput_ne_zero_iff (handoff : ℕ) :
    recoveryNestedPresenceOutput handoff ≠ 0 ↔
      handoff ≠ 0 ∧ handoffOracleCode handoff ≠ 0 ∧
        handoffSumCode handoff ≠ 0 := by
  unfold recoveryNestedPresenceOutput
  split_ifs with hzero horacle hsum
  · simp [hzero]
  · simp [horacle]
  · simp [hsum]
  · simp [hzero, horacle, hsum]

private theorem recoveryValidatorHandoffOutput_eq_pair_of_envelope
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (henvelope : recoveryEnvelopeOutput raw ≠ 0) :
    recoveryValidatorHandoffOutput limits raw =
      Nat.pair (Nat.unpair (recoveryEnvelopeOutput raw)).1
        (Nat.pair raw
          (Nat.pair (recoveryEnvelopeOracleCode raw)
            (Nat.pair (recoveryEnvelopeSumCode raw)
              (encodeRecoveryWitnessLimits limits)))) := by
  simp [recoveryValidatorHandoffOutput, henvelope]

private theorem handoffOracleCode_handoffOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorHandoffOutput limits raw ≠ 0) :
    handoffOracleCode (recoveryValidatorHandoffOutput limits raw) =
      recoveryEnvelopeOracleCode raw := by
  rw [recoveryValidatorHandoffOutput_eq_pair haccepts]
  simp [handoffOracleCode]

private theorem handoffSumCode_handoffOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorHandoffOutput limits raw ≠ 0) :
    handoffSumCode (recoveryValidatorHandoffOutput limits raw) =
      recoveryEnvelopeSumCode raw := by
  rw [recoveryValidatorHandoffOutput_eq_pair haccepts]
  simp [handoffSumCode]

private theorem handoffLimitsCode_handoffOutput
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorHandoffOutput limits raw ≠ 0) :
    handoffLimitsCode (recoveryValidatorHandoffOutput limits raw) =
      encodeRecoveryWitnessLimits limits := by
  rw [recoveryValidatorHandoffOutput_eq_pair haccepts]
  simp [handoffLimitsCode]

private theorem recoveryValidatorHandoffOutput_ne_zero_iff
    (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryValidatorHandoffOutput limits raw ≠ 0 ↔
      ∃ envelope, decodeRecoveryEnvelope raw = some envelope := by
  cases hdecode : decodeRecoveryEnvelope raw with
  | none =>
      have hzero : recoveryEnvelopeOutput raw = 0 :=
        recoveryEnvelopeOutput_eq_zero_of_decode hdecode
      simp [recoveryValidatorHandoffOutput, hzero]
  | some envelope =>
      have htag : 0 < RecoveryEnvelope.outputTag envelope.mode := by
        cases envelope.mode <;> decide
      have henvelope : recoveryEnvelopeOutput raw ≠ 0 := by
        rw [recoveryEnvelopeOutput_eq_pair_of_decode hdecode]
        have hleft :=
          Nat.left_le_pair (RecoveryEnvelope.outputTag envelope.mode) raw
        omega
      have hmode :
          (Nat.unpair (recoveryEnvelopeOutput raw)).1 =
            RecoveryEnvelope.outputTag envelope.mode := by
        rw [recoveryEnvelopeOutput_eq_pair_of_decode hdecode]
        simp
      have hhandoff : recoveryValidatorHandoffOutput limits raw ≠ 0 := by
        rw [recoveryValidatorHandoffOutput_eq_pair_of_envelope henvelope]
        have hleft :=
          Nat.left_le_pair (Nat.unpair (recoveryEnvelopeOutput raw)).1
            (Nat.pair raw
              (Nat.pair (recoveryEnvelopeOracleCode raw)
                (Nat.pair (recoveryEnvelopeSumCode raw)
                  (encodeRecoveryWitnessLimits limits))))
        omega
      simp [hhandoff]

private theorem recoveryEnvelopeCodes_of_taggedList
    {raw modeCode oracleCode sumCode : ℕ}
    (hfields :
      decodeTaggedList raw = some [modeCode, oracleCode, sumCode]) :
    recoveryEnvelopeOracleCode raw = oracleCode ∧
      recoveryEnvelopeSumCode raw = sumCode := by
  have hraw : encodeTaggedList [modeCode, oracleCode, sumCode] = raw :=
    encodeTaggedList_of_decode hfields
  rw [← hraw]
  constructor
  · simp [recoveryEnvelopeOracleCode, taggedHeadCode, taggedTailCode,
      encodeTaggedList]
  · simp [recoveryEnvelopeSumCode, taggedHeadCode, taggedTailCode,
      encodeTaggedList]

private theorem decodeRecoveryEnvelope_isSome_iff (raw : ℕ) :
    (∃ envelope, decodeRecoveryEnvelope raw = some envelope) ↔
      ∃ modeCode oracleCode sumCode,
        decodeTaggedList raw = some [modeCode, oracleCode, sumCode] ∧
          (decodeNat modeCode = some 0 ∨ decodeNat modeCode = some 1) := by
  constructor
  · rintro ⟨envelope, hdecode⟩
    unfold decodeRecoveryEnvelope at hdecode
    cases hfields : decodeTaggedList raw with
    | none =>
        rw [hfields] at hdecode
        simp at hdecode
    | some fields =>
        rw [hfields] at hdecode
        rcases fields with _ | ⟨modeCode, rest⟩
        · simp at hdecode
        rcases rest with _ | ⟨oracleCode, rest⟩
        · simp at hdecode
        rcases rest with _ | ⟨sumCode, rest⟩
        · simp at hdecode
        rcases rest with _ | ⟨extra, rest⟩
        · refine ⟨modeCode, oracleCode, sumCode, rfl, ?_⟩
          cases hmode : decodeNat modeCode with
          | none => simp [hmode] at hdecode
          | some value =>
              cases value with
              | zero => exact Or.inl rfl
              | succ value =>
                  cases value with
                  | zero => exact Or.inr rfl
                  | succ value => simp [hmode] at hdecode
        · simp at hdecode
  · rintro ⟨modeCode, oracleCode, sumCode, hfields, hmode⟩
    rcases hmode with hmode | hmode
    · exact ⟨⟨.symmetric, oracleCode, sumCode⟩, by
        simp [decodeRecoveryEnvelope, hfields, hmode]⟩
    · exact ⟨⟨.threshold, oracleCode, sumCode⟩, by
        simp [decodeRecoveryEnvelope, hfields, hmode]⟩

/-- Exact acceptance criterion of the staged prefix: the outer envelope must be
canonical with an accepted mode tag, the nested legal-sum payload must be
present, and the Boolean oracle must decode within the configured size cap. -/
theorem recoveryValidatorOraclePrefixOutput_ne_zero_iff
    (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryValidatorOraclePrefixOutput limits raw ≠ 0 ↔
      ∃ modeCode oracleCode sumCode,
        decodeTaggedList raw = some [modeCode, oracleCode, sumCode] ∧
          (decodeNat modeCode = some 0 ∨ decodeNat modeCode = some 1) ∧
          sumCode ≠ 0 ∧
          ∃ circuit : BooleanCircuit limits.oracleArity,
            decodeBooleanCircuit limits.oracleArity oracleCode =
                some circuit ∧
              circuit.size ≤ limits.oracleSizeCap := by
  constructor
  · intro haccepts
    have hstructural :
        recoveryValidatorStructuralPrefixOutput limits raw ≠ 0 := by
      intro hzero
      apply haccepts
      simp [recoveryValidatorOraclePrefixOutput, hzero]
    have hpresence :
        recoveryNestedPresenceOutput
          (recoveryValidatorHandoffOutput limits raw) ≠ 0 := hstructural
    obtain ⟨hhandoff, horacleCode, hsumCode⟩ :=
      (recoveryNestedPresenceOutput_ne_zero_iff
        (recoveryValidatorHandoffOutput limits raw)).1 hpresence
    obtain ⟨envelope, hdecode⟩ :=
      (recoveryValidatorHandoffOutput_ne_zero_iff limits raw).1 hhandoff
    obtain ⟨modeCode, oracleCode, sumCode, hfields, hmode⟩ :=
      (decodeRecoveryEnvelope_isSome_iff raw).1 ⟨envelope, hdecode⟩
    obtain ⟨horacleEq, hsumEq⟩ := recoveryEnvelopeCodes_of_taggedList hfields
    have hstructuralEq :=
      recoveryValidatorStructuralPrefixOutput_eq_handoff hstructural
    have hiff :=
      recoveryOracleValidationOutput_ne_zero_iff
        (recoveryValidatorStructuralPrefixOutput limits raw)
    rw [hstructuralEq, handoffOracleCode_handoffOutput hhandoff, horacleEq,
      handoffOracleArity_of_limitsCode
        (handoffLimitsCode_handoffOutput hhandoff),
      handoffOracleSizeCap_of_limitsCode
        (handoffLimitsCode_handoffOutput hhandoff)] at hiff
    have houtput :
        recoveryOracleValidationOutput
          (recoveryValidatorHandoffOutput limits raw) ≠ 0 := by
      rw [← hstructuralEq]
      exact haccepts
    refine ⟨modeCode, oracleCode, sumCode, hfields, hmode, ?_, hiff.1 houtput⟩
    rw [handoffSumCode_handoffOutput hhandoff, hsumEq] at hsumCode
    exact hsumCode
  · rintro ⟨modeCode, oracleCode, sumCode, hfields, hmode, hsum,
      circuit, hcircuit, hsize⟩
    obtain ⟨horacleEq, hsumEq⟩ := recoveryEnvelopeCodes_of_taggedList hfields
    have hhandoff : recoveryValidatorHandoffOutput limits raw ≠ 0 :=
      (recoveryValidatorHandoffOutput_ne_zero_iff limits raw).2
        ((decodeRecoveryEnvelope_isSome_iff raw).2
          ⟨modeCode, oracleCode, sumCode, hfields, hmode⟩)
    have horacleNonzero : oracleCode ≠ 0 := by
      intro hzero
      rw [hzero, decodeBooleanCircuit_zero] at hcircuit
      exact absurd hcircuit (by simp)
    have hpresence :
        recoveryNestedPresenceOutput
          (recoveryValidatorHandoffOutput limits raw) ≠ 0 := by
      refine (recoveryNestedPresenceOutput_ne_zero_iff
        (recoveryValidatorHandoffOutput limits raw)).2 ⟨hhandoff, ?_, ?_⟩
      · rw [handoffOracleCode_handoffOutput hhandoff, horacleEq]
        exact horacleNonzero
      · rw [handoffSumCode_handoffOutput hhandoff, hsumEq]
        exact hsum
    have hstructural :
        recoveryValidatorStructuralPrefixOutput limits raw ≠ 0 := hpresence
    have hstructuralEq :=
      recoveryValidatorStructuralPrefixOutput_eq_handoff hstructural
    have hiff :=
      recoveryOracleValidationOutput_ne_zero_iff
        (recoveryValidatorStructuralPrefixOutput limits raw)
    rw [hstructuralEq, handoffOracleCode_handoffOutput hhandoff, horacleEq,
      handoffOracleArity_of_limitsCode
        (handoffLimitsCode_handoffOutput hhandoff),
      handoffOracleSizeCap_of_limitsCode
        (handoffLimitsCode_handoffOutput hhandoff)] at hiff
    change
      recoveryOracleValidationOutput
        (recoveryValidatorStructuralPrefixOutput limits raw) ≠ 0
    rw [hstructuralEq]
    exact hiff.2 ⟨circuit, hcircuit, hsize⟩

/-! ## Canonical round-trip from structural field checks

`decodeRecoveryWitness` and `decodeLegalCircuitSum` both end with an exact
re-encode guard.  The lemmas below show that guard is *implied* by the
component-level canonical decodes the executable stages already perform:
`decodeTaggedList`, `decodeNat`, `decodeBalancedList`, `decodeBooleanCircuit`
and `decodeLegalCircuitTerm` are each canonical, so re-encoding the decoded
fields reproduces the original code bit for bit.  Consequently no additional
executable canonicality check is required beyond the structural ones, and no
raw code can pass the structural checks while failing the round-trip. -/

/-- The legal-sum re-encode guard is discharged by the two field decodes. -/
theorem decodeLegalCircuitSum_of_canonical_fields
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily}
    (codec : CanonicalCircuitCodec Circuit)
    (wires description : {n : ℕ} → Circuit n → ℕ)
    (limits : LegalSumLimits)
    {code qCode termCodesCode : ℕ}
    (checked : CheckedLegalCircuitSum Circuit wires description limits)
    (hfields : decodeTaggedList code = some [qCode, termCodesCode])
    (hq : decodeNat qCode = some checked.value.q)
    (hcodes :
      decodeBalancedList termCodesCode =
        some (checked.value.terms.map (·.code codec))) :
    decodeLegalCircuitSum codec wires description limits code =
      some checked := by
  have hcode : checked.code codec = code := by
    change
      encodeTaggedList
        [encodeNat checked.value.q,
          encodeBalancedList
            (checked.value.terms.map (·.code codec))] = code
    rw [encodeNat_of_decode hq, encodeBalancedList_of_decode hcodes]
    exact encodeTaggedList_of_decode hfields
  rw [← hcode]
  exact decodeLegalCircuitSum_encode codec wires description limits checked

/-- The complete witness re-encode guard on the symmetric branch is discharged
by the outer tagged-tuple, mode, oracle and legal-sum canonical decodes. -/
theorem decodeRecoveryWitness_symmetric_of_canonical_fields
    {limits : RecoveryWitnessLimits} {code modeCode oracleCode sumCode : ℕ}
    {oracle : BooleanCircuit limits.oracleArity}
    (hsize : oracle.size ≤ limits.oracleSizeCap)
    {sum :
      CheckedLegalCircuitSum NormalizedSymmetricThresholdCircuit
        NormalizedSymmetricThresholdCircuit.wireCount
        NormalizedSymmetricThresholdCircuit.descriptionBits limits.symmetric}
    (hfields : decodeTaggedList code = some [modeCode, oracleCode, sumCode])
    (hmode : decodeNat modeCode = some 0)
    (horacle :
      decodeBooleanCircuit limits.oracleArity oracleCode = some oracle)
    (hsum : sum.code symmetricCircuitCodec = sumCode) :
    decodeRecoveryWitness limits code =
      some (.symmetric oracle hsize sum) := by
  have hcode :
      (CheckedRecoveryWitness.symmetric oracle hsize sum).code = code := by
    change
      encodeTaggedList
        [encodeNat 0, encodeBooleanCircuit oracle,
          sum.code symmetricCircuitCodec] = code
    rw [encodeNat_of_decode hmode, encodeBooleanCircuit_of_decode horacle,
      hsum]
    exact encodeTaggedList_of_decode hfields
  rw [← hcode]
  exact decodeRecoveryWitness_encode _

/-- The threshold twin of the previous round-trip lemma. -/
theorem decodeRecoveryWitness_threshold_of_canonical_fields
    {limits : RecoveryWitnessLimits} {code modeCode oracleCode sumCode : ℕ}
    {oracle : BooleanCircuit limits.oracleArity}
    (hsize : oracle.size ≤ limits.oracleSizeCap)
    {sum :
      CheckedLegalCircuitSum NormalizedThresholdThresholdCircuit
        NormalizedThresholdThresholdCircuit.wireCount
        NormalizedThresholdThresholdCircuit.descriptionBits limits.threshold}
    (hfields : decodeTaggedList code = some [modeCode, oracleCode, sumCode])
    (hmode : decodeNat modeCode = some 1)
    (horacle :
      decodeBooleanCircuit limits.oracleArity oracleCode = some oracle)
    (hsum : sum.code thresholdCircuitCodec = sumCode) :
    decodeRecoveryWitness limits code =
      some (.threshold oracle hsize sum) := by
  have hcode :
      (CheckedRecoveryWitness.threshold oracle hsize sum).code = code := by
    change
      encodeTaggedList
        [encodeNat 1, encodeBooleanCircuit oracle,
          sum.code thresholdCircuitCodec] = code
    rw [encodeNat_of_decode hmode, encodeBooleanCircuit_of_decode horacle,
      hsum]
    exact encodeTaggedList_of_decode hfields
  rw [← hcode]
  exact decodeRecoveryWitness_encode _

/-! ## Coefficient magnitude ABI of one validated term

The coefficient mapper stores the accepted rational as
`pair 1 (pair sign (pair magnitude denominator))`.  The two lemmas below prove
that the magnitude and denominator projections consumed by the coefficient
bit-cap stage are exactly the reduced numerator magnitude and denominator of
the typed rational, so the bit-cap conjunct is the typed `coefficient_bits_le`
condition and not a check on some other integer. -/

private theorem rationalTupleOutput_encodeCanonicalRational (value : ℚ) :
    rationalTupleOutput (encodeCanonicalRational value) =
      Nat.pair 1
        (Nat.pair (Nat.pair 0 (encodeInt value.num))
          (encodeNat value.den)) := by
  unfold rationalTupleOutput taggedTupleOutput encodeCanonicalRational
  rw [show (2 : ℕ) =
    [encodeInt value.num, encodeNat value.den].length by rfl]
  rw [decodeTaggedTuple_encode]
  rfl

theorem rationalMagnitudeValue_encodeCanonicalRational (value : ℚ) :
    rationalMagnitudeValue (encodeCanonicalRational value) =
      value.num.natAbs := by
  by_cases hnegative : value.num < 0
  · simp [rationalMagnitudeValue, rationalMagnitudeValidation,
      rationalMagnitudeCode, rationalNumeratorCode, rationalNumeratorFrame,
      rationalTupleFields, rationalTupleOutput_encodeCanonicalRational,
      encodeInt, hnegative]
  · simp [rationalMagnitudeValue, rationalMagnitudeValidation,
      rationalMagnitudeCode, rationalNumeratorCode, rationalNumeratorFrame,
      rationalTupleFields, rationalTupleOutput_encodeCanonicalRational,
      encodeInt, hnegative]

theorem rationalDenominatorValue_encodeCanonicalRational (value : ℚ) :
    rationalDenominatorValue (encodeCanonicalRational value) = value.den := by
  simp [rationalDenominatorValue, rationalDenominatorValidation,
    rationalDenominatorCode, rationalTupleFields,
    rationalTupleOutput_encodeCanonicalRational]

theorem rationalValidationOutput_encodeCanonicalRational (value : ℚ) :
    rationalValidationOutput (encodeCanonicalRational value) =
      Nat.pair 1
        (Nat.pair (rationalSign (encodeCanonicalRational value))
          (Nat.pair value.num.natAbs value.den)) := by
  rw [rationalValidationOutput,
    if_pos (rationalValidationAccepts_encodeCanonicalRational value),
    rationalMagnitudeValue_encodeCanonicalRational,
    rationalDenominatorValue_encodeCanonicalRational]

/-- The magnitude the bit-cap stage charges is the reduced numerator
magnitude of the typed coefficient. -/
theorem recoveryLegalTermValidatedMagnitude_termCode
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily} {n : ℕ}
    (codec : CanonicalCircuitCodec Circuit)
    (term : LegalCircuitTerm Circuit n) :
    recoveryLegalTermValidatedMagnitude
        (legalTermCoefficientValidationOutput (term.code codec)) =
      term.coefficient.num.natAbs := by
  rw [legalTermCoefficientValidationOutput_code codec term,
    rationalValidationOutput_encodeCanonicalRational]
  simp [recoveryLegalTermValidatedMagnitude,
    recoveryLegalTermValidatedRationalSummary]

/-- The denominator the bit-cap stage charges is the reduced denominator of
the typed coefficient. -/
theorem recoveryLegalTermValidatedDenominator_termCode
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily} {n : ℕ}
    (codec : CanonicalCircuitCodec Circuit)
    (term : LegalCircuitTerm Circuit n) :
    recoveryLegalTermValidatedDenominator
        (legalTermCoefficientValidationOutput (term.code codec)) =
      term.coefficient.den := by
  rw [legalTermCoefficientValidationOutput_code codec term,
    rationalValidationOutput_encodeCanonicalRational]
  simp [recoveryLegalTermValidatedDenominator,
    recoveryLegalTermValidatedRationalSummary]

/-! ## The public recovery-witness validator endpoint

The staged legal-sum prefix returns the complete accepted handoff, whose first
two components are the accepted mode tag and the original untrusted code.  The
final stage repackages exactly those two components.  On rejection the handoff
is zero and both projections are zero, so the same instructions preserve the
fail-closed sentinel; no second reject block is introduced. -/

theorem recoveryLegalSumEnvelopeOutput_eq_zero_or_self
    (inputLength handoff : ℕ) :
    recoveryLegalSumEnvelopeOutput inputLength handoff = 0 ∨
      recoveryLegalSumEnvelopeOutput inputLength handoff = handoff := by
  rw [recoveryLegalSumEnvelopeOutput_eq]
  split_ifs <;> simp

/-- The legal-sum stage is a pure guard on the staged handoff. -/
theorem recoveryValidatorLegalSumPrefixOutput_eq_oraclePrefixOutput
    {inputLength : ℕ} {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw =
      recoveryValidatorOraclePrefixOutput limits raw := by
  rw [recoveryValidatorLegalSumPrefixOutput] at haccepts ⊢
  rcases recoveryLegalSumEnvelopeOutput_eq_zero_or_self inputLength
      (recoveryValidatorOraclePrefixOutput limits raw) with hzero | hself
  · exact absurd hzero haccepts
  · exact hself

theorem recoveryValidatorOraclePrefixOutput_ne_zero_of_legalSum
    {inputLength : ℕ} {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0) :
    recoveryValidatorOraclePrefixOutput limits raw ≠ 0 := by
  rw [← recoveryValidatorLegalSumPrefixOutput_eq_oraclePrefixOutput haccepts]
  exact haccepts

/-- Repackaging semantics: the accepted mode tag paired with the original
untrusted code.  Both projections of the zero sentinel are zero. -/
def recoveryValidatorModeRawOutput (handoff : ℕ) : ℕ :=
  Nat.pair (Nat.unpair handoff).1 (Nat.unpair (Nat.unpair handoff).2).1

@[simp] theorem recoveryValidatorModeRawOutput_zero :
    recoveryValidatorModeRawOutput 0 = 0 := by
  simp [recoveryValidatorModeRawOutput, Nat.pair]

def recoveryValidatorModeRawProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .pair 2 4 0 4
  , .halt 0
  ]

@[simp] theorem recoveryValidatorModeRawProgram_oracleFree :
    OracleFree recoveryValidatorModeRawProgram := by
  rfl

def recoveryValidatorModeRawFuel : ℕ := 5

private def recoveryValidatorModeRawValues
    (inputLength handoff : ℕ) : List ℕ :=
  [ inputLength
  , handoff
  , (Nat.unpair handoff).1
  , (Nat.unpair handoff).2
  , (Nat.unpair (Nat.unpair handoff).2).1
  , recoveryValidatorModeRawOutput handoff
  ]

def recoveryValidatorModeRawBits (inputLength handoff : ℕ) : ℕ :=
  natBitLength <|
    (recoveryValidatorModeRawValues inputLength handoff).foldr max 0

private theorem recoveryValidatorModeRawValue_bits
    {inputLength handoff value : ℕ}
    (hvalue : value ∈ recoveryValidatorModeRawValues inputLength handoff) :
    natBitLength value ≤
      recoveryValidatorModeRawBits inputLength handoff := by
  apply natBitLength_mono
  exact member_le_foldr_max hvalue

-- The exact five-step trace peels the mode tag and the retained raw code.
theorem run_recoveryValidatorModeRawProgram
    (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryValidatorModeRawProgram
        (recoveryValidatorModeRawBits inputLength handoff)
        recoveryValidatorModeRawFuel
        (initialNPOracleState inputLength handoff) =
      some (recoveryValidatorModeRawOutput handoff) := by
  let mode := (Nat.unpair handoff).1
  let tail := (Nat.unpair handoff).2
  let rawCode := (Nat.unpair tail).1
  let output := recoveryValidatorModeRawOutput handoff
  have hmode :
      natBitLength mode ≤
        recoveryValidatorModeRawBits inputLength handoff := by
    apply recoveryValidatorModeRawValue_bits
    simp [recoveryValidatorModeRawValues, mode]
  have htail :
      natBitLength tail ≤
        recoveryValidatorModeRawBits inputLength handoff := by
    apply recoveryValidatorModeRawValue_bits
    simp [recoveryValidatorModeRawValues, tail]
  have hrawCode :
      natBitLength rawCode ≤
        recoveryValidatorModeRawBits inputLength handoff := by
    apply recoveryValidatorModeRawValue_bits
    simp [recoveryValidatorModeRawValues, tail, rawCode]
  have houtput :
      natBitLength output ≤
        recoveryValidatorModeRawBits inputLength handoff := by
    apply recoveryValidatorModeRawValue_bits
    simp [recoveryValidatorModeRawValues, output]
  rw [show recoveryValidatorModeRawFuel = 4 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := mode)
    (by rfl) rfl
    (by simp [initialNPOracleState, mode])
    hmode]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := tail)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      tail])
    htail]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := rawCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, tail, rawCode])
    hrawCode]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      recoveryValidatorModeRawOutput, mode, tail, rawCode, output])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-- Executable output of the complete recovery-witness validator. -/
def recoveryWitnessValidatorProgramOutput
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  recoveryValidatorModeRawOutput
    (recoveryValidatorLegalSumPrefixOutput inputLength limits raw)

/-- The single public register program for the complete recovery-witness
validator: staged canonical validation followed by mode/raw repackaging. -/
def recoveryWitnessValidatorProgram : NPOracleProgram :=
  linkPrograms recoveryValidatorLegalSumPrefixProgram
    recoveryValidatorModeRawProgram

@[simp] theorem recoveryWitnessValidatorProgram_oracleFree :
    OracleFree recoveryWitnessValidatorProgram :=
  oracleFree_linkPrograms recoveryValidatorLegalSumPrefixProgram_oracleFree
    recoveryValidatorModeRawProgram_oracleFree

def recoveryWitnessValidatorFuel
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  linkFuel recoveryValidatorModeRawProgram
    (recoveryValidatorLegalSumPrefixFuel inputLength limits raw)
    recoveryValidatorModeRawFuel

def recoveryWitnessValidatorBits
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryValidatorLegalSumPrefixBits inputLength limits raw)
      (recoveryValidatorModeRawBits inputLength
        (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))

theorem run_recoveryWitnessValidatorProgram
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryWitnessValidatorProgram
        (recoveryWitnessValidatorBits inputLength limits raw)
        (recoveryWitnessValidatorFuel inputLength limits raw)
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits raw)) =
      some
        (recoveryWitnessValidatorProgramOutput inputLength limits raw) := by
  let maximumBits := recoveryWitnessValidatorBits inputLength limits raw
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hprefixBits :
      recoveryValidatorLegalSumPrefixBits inputLength limits raw ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hmodeBits :
      recoveryValidatorModeRawBits inputLength
          (recoveryValidatorLegalSumPrefixOutput inputLength limits raw) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprefix :=
    run_bits_mono
      (run_recoveryValidatorLegalSumPrefixProgram inputLength limits raw)
      hprefixBits
  have hmode :=
    run_bits_mono
      (run_recoveryValidatorModeRawProgram inputLength
        (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))
      hmodeBits
  have hrun := run_linkPrograms hpositive hlength hprefix hmode
  rw [recoveryWitnessValidatorProgram, recoveryWitnessValidatorFuel]
  exact hrun

/-! ### Exact shape of the endpoint output -/

theorem recoveryWitnessValidatorProgramOutput_eq_zero_of_reject
    {inputLength : ℕ} {limits : RecoveryWitnessLimits} {raw : ℕ}
    (hreject :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw = 0 := by
  rw [recoveryWitnessValidatorProgramOutput, hreject,
    recoveryValidatorModeRawOutput_zero]

/-- On acceptance the endpoint returns the accepted mode tag paired with the
original untrusted code, exactly the shape of `recoveryWitnessValidatorOutput`. -/
theorem recoveryWitnessValidatorProgramOutput_eq_pair
    {inputLength : ℕ} {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw =
      Nat.pair
        (handoffMode (recoveryValidatorOraclePrefixOutput limits raw)) raw := by
  have horacle := recoveryValidatorOraclePrefixOutput_ne_zero_of_legalSum
    haccepts
  have hhandoff := recoveryValidatorHandoffOutput_ne_zero_of_prefix horacle
  rw [handoffMode_oraclePrefixOutput horacle,
    recoveryWitnessValidatorProgramOutput,
    recoveryValidatorLegalSumPrefixOutput_eq_oraclePrefixOutput haccepts,
    recoveryValidatorOraclePrefixOutput_eq_handoff horacle,
    recoveryValidatorHandoffOutput_eq_pair hhandoff]
  simp [recoveryValidatorModeRawOutput]

theorem recoveryWitnessValidatorProgramOutput_ne_zero_iff
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw ≠ 0 ↔
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0 := by
  constructor
  · intro hnonzero hreject
    exact hnonzero
      (recoveryWitnessValidatorProgramOutput_eq_zero_of_reject hreject)
  · intro haccepts
    rw [recoveryWitnessValidatorProgramOutput_eq_pair haccepts]
    have horacle :=
      recoveryValidatorOraclePrefixOutput_ne_zero_of_legalSum haccepts
    rcases handoffMode_oraclePrefixOutput_cases horacle with hmode | hmode
    · rw [hmode]
      have hleft := Nat.left_le_pair 1 raw
      omega
    · rw [hmode]
      have hleft := Nat.left_le_pair 2 raw
      omega

private theorem balancedValidationMapCodes_encode (codes : List ℕ) :
    balancedValidationMapCodes (encodeBalancedList codes) = codes := by
  rw [balancedValidationMapCodes, decodeBalancedList_encode, Option.getD_some]

/-- Accepted coefficient pass: the mapped payload is the balanced list of the
per-term coefficient-validator outputs. -/
theorem recoveryLegalTermCoefficientMappedCode_eq
    (inputLength handoff : ℕ)
    (haccepts :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0) :
    recoveryLegalTermCoefficientMappedCode inputLength handoff =
      encodeBalancedList
        ((balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff)).map
          legalTermCoefficientValidationOutput) := by
  have hpayload :
      (Nat.unpair
          (recoveryLegalTermCoefficientListOutput inputLength
            (recoveryLegalTermCoefficientTermsCode handoff))).2 =
        balancedValidationSummaryData inputLength
          (recoveryLegalTermCoefficientTermsCode handoff)
          recoveryLegalTermCoefficientRequestOutput :=
    balancedValidationSummaryOutput_payload inputLength
      (recoveryLegalTermCoefficientTermsCode handoff)
      recoveryLegalTermCoefficientRequestOutput haccepts
  simp [recoveryLegalTermCoefficientMappedCode, hpayload,
    balancedValidationSummaryData, balancedValidationMapOutputs,
    balancedValidationMapRequests, List.map_map, Function.comp_def,
    recoveryLegalTermCoefficientRequestOutput, nativeInputRequest]

/-- Accepted circuit pass: the validated summary tree is the balanced list of
the per-term normalized-circuit validator outputs. -/
theorem recoveryLegalTermValidatedSummaryTree_eq
    (inputLength handoff : ℕ)
    (haccepts :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0) :
    recoveryLegalTermValidatedSummaryTree inputLength handoff =
      encodeBalancedList
        ((balancedValidationMapCodes
            (recoveryLegalTermCoefficientMappedCode inputLength handoff)).map
          (recoveryLegalTermCircuitCallOutput
            (recoveryLegalTermCircuitContext handoff))) := by
  have hpayload :
      (Nat.unpair
          (recoveryLegalTermCircuitListOutput
            (recoveryLegalTermCircuitContext handoff)
            (recoveryLegalTermCoefficientMappedCode inputLength handoff))).2 =
        balancedValidationSummaryData
          (recoveryLegalTermCircuitContext handoff)
          (recoveryLegalTermCoefficientMappedCode inputLength handoff)
          recoveryLegalTermCircuitRequestOutput :=
    balancedValidationSummaryOutput_payload
      (recoveryLegalTermCircuitContext handoff)
      (recoveryLegalTermCoefficientMappedCode inputLength handoff)
      recoveryLegalTermCircuitRequestOutput haccepts
  simp [recoveryLegalTermValidatedSummaryTree, hpayload,
    balancedValidationSummaryData, balancedValidationMapOutputs,
    balancedValidationMapRequests, List.map_map, Function.comp_def,
    recoveryLegalTermCircuitRequestOutput, nativeInputRequest]

/-- Composite per-term ABI: the summaries charged by the wire and description
gates are exactly the normalized-circuit validator outputs of the per-term
coefficient-validator outputs of the decoded term codes. -/
theorem decodeBalancedList_recoveryLegalTermValidatedSummaryTree
    (inputLength handoff : ℕ)
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0) :
    decodeBalancedList
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) =
      some
        (((balancedValidationMapCodes
              (recoveryLegalTermCoefficientTermsCode handoff)).map
            legalTermCoefficientValidationOutput).map
          (recoveryLegalTermCircuitCallOutput
            (recoveryLegalTermCircuitContext handoff))) := by
  rw [recoveryLegalTermValidatedSummaryTree_eq inputLength handoff hcircuit,
    recoveryLegalTermCoefficientMappedCode_eq inputLength handoff hcoefficient,
    balancedValidationMapCodes_encode, decodeBalancedList_encode]

/-! ### Typed resource charges of one accepted per-term summary

The two refinements below turn the wire and description charges the executable
gates compare against their caps into the exact typed metrics of the decoded
normalized circuit, in whichever family the request selects. -/

private theorem normalizedCircuitHeaderTag_eq_one_of_family
    {arity request : ℕ}
    (hfamily : normalizedCircuitExpectedFamily request = 0)
    (hvalid : normalizedCircuitValidationOutput arity request ≠ 0) :
    normalizedCircuitHeaderTag arity request = 1 := by
  rcases (normalizedCircuitValidationOutput_ne_zero_iff_branches arity
      request).1 hvalid with ⟨htag, _⟩ | ⟨htag, _⟩
  · exact htag
  · have hother := ((normalizedCircuitHeaderTag_eq_two_iff arity request).1
      htag).1
    rw [hfamily] at hother
    exact absurd hother (by omega)

private theorem normalizedCircuitHeaderTag_eq_two_of_family
    {arity request : ℕ}
    (hfamily : normalizedCircuitExpectedFamily request = 1)
    (hvalid : normalizedCircuitValidationOutput arity request ≠ 0) :
    normalizedCircuitHeaderTag arity request = 2 := by
  rcases (normalizedCircuitValidationOutput_ne_zero_iff_branches arity
      request).1 hvalid with ⟨htag, _⟩ | ⟨htag, _⟩
  · have hother := ((normalizedCircuitHeaderTag_eq_one_iff arity request).1
      htag).1
    rw [hfamily] at hother
    exact absurd hother (by omega)
  · exact htag

theorem normalizedCircuitValidationOutput_wireCount_symmetric
    {arity request : ℕ}
    {circuit : NormalizedSymmetricThresholdCircuit arity}
    (hfamily : normalizedCircuitExpectedFamily request = 0)
    (hvalid : normalizedCircuitValidationOutput arity request ≠ 0)
    (hdecode :
      decodeNormalizedSymmetricThresholdCircuit arity
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitResourceMetric
        (normalizedCircuitValidationOutput arity request) =
      circuit.wireCount :=
  normalizedCircuitValidationOutput_resourceMetric_eq_symmetricWireCount
    (normalizedCircuitHeaderTag_eq_one_of_family hfamily hvalid) hvalid hdecode

theorem normalizedCircuitValidationOutput_wireCount_threshold
    {arity request : ℕ}
    {circuit : NormalizedThresholdThresholdCircuit arity}
    (hfamily : normalizedCircuitExpectedFamily request = 1)
    (hvalid : normalizedCircuitValidationOutput arity request ≠ 0)
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit arity
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitResourceMetric
        (normalizedCircuitValidationOutput arity request) =
      circuit.wireCount :=
  normalizedCircuitValidationOutput_resourceMetric_eq_thresholdWireCount
    (normalizedCircuitHeaderTag_eq_two_of_family hfamily hvalid) hvalid hdecode

theorem normalizedCircuitValidationOutput_descriptionBits_symmetric
    {arity request : ℕ}
    {circuit : NormalizedSymmetricThresholdCircuit arity}
    (hfamily : normalizedCircuitExpectedFamily request = 0)
    (hvalid : normalizedCircuitValidationOutput arity request ≠ 0)
    (hdecode :
      decodeNormalizedSymmetricThresholdCircuit arity
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitDescriptionMetric arity
        (normalizedCircuitValidationOutput arity request) =
      circuit.descriptionBits :=
  normalizedCircuitValidationOutput_descriptionMetric_eq_symmetric
    (normalizedCircuitHeaderTag_eq_one_of_family hfamily hvalid) hvalid hdecode

theorem normalizedCircuitValidationOutput_descriptionBits_threshold
    {arity request : ℕ}
    {circuit : NormalizedThresholdThresholdCircuit arity}
    (hfamily : normalizedCircuitExpectedFamily request = 1)
    (hvalid : normalizedCircuitValidationOutput arity request ≠ 0)
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit arity
        (normalizedCircuitRawCode request) = some circuit) :
    normalizedCircuitDescriptionMetric arity
        (normalizedCircuitValidationOutput arity request) =
      circuit.descriptionBits :=
  normalizedCircuitValidationOutput_descriptionMetric_eq_threshold
    (normalizedCircuitHeaderTag_eq_two_of_family hfamily hvalid) hvalid hdecode

@[simp] theorem normalizedCircuitExpectedFamily_circuitRequest
    (context validated : ℕ) :
    normalizedCircuitExpectedFamily
        (recoveryLegalTermCircuitRequest context validated) =
      recoveryLegalTermCircuitFamily context := by
  simp [normalizedCircuitExpectedFamily, recoveryLegalTermCircuitRequest]

@[simp] theorem normalizedCircuitRawCode_circuitRequest
    (context validated : ℕ) :
    normalizedCircuitRawCode
        (recoveryLegalTermCircuitRequest context validated) =
      (Nat.unpair (Nat.unpair validated).2).2 := by
  simp [normalizedCircuitRawCode, recoveryLegalTermCircuitRequest]

/-- Symmetric branch: the wire charge of one accepted per-term summary is the
typed physical wire count of that term's decoded circuit. -/
theorem recoveryLegalTermCircuitCallOutput_wireCount_symmetric
    {context validated : ℕ}
    {circuit :
      NormalizedSymmetricThresholdCircuit
        (recoveryLegalTermCircuitArity context)}
    (hfamily : recoveryLegalTermCircuitFamily context = 0)
    (hvalid : recoveryLegalTermCircuitCallOutput context validated ≠ 0)
    (hdecode :
      decodeNormalizedSymmetricThresholdCircuit
          (recoveryLegalTermCircuitArity context)
          (Nat.unpair (Nat.unpair validated).2).2 = some circuit) :
    normalizedCircuitResourceMetric
        (recoveryLegalTermCircuitCallOutput context validated) =
      circuit.wireCount := by
  refine normalizedCircuitValidationOutput_wireCount_symmetric ?_ hvalid ?_
  · rw [normalizedCircuitExpectedFamily_circuitRequest]
    exact hfamily
  · rw [normalizedCircuitRawCode_circuitRequest]
    exact hdecode

/-- Threshold branch of the previous refinement. -/
theorem recoveryLegalTermCircuitCallOutput_wireCount_threshold
    {context validated : ℕ}
    {circuit :
      NormalizedThresholdThresholdCircuit
        (recoveryLegalTermCircuitArity context)}
    (hfamily : recoveryLegalTermCircuitFamily context = 1)
    (hvalid : recoveryLegalTermCircuitCallOutput context validated ≠ 0)
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit
          (recoveryLegalTermCircuitArity context)
          (Nat.unpair (Nat.unpair validated).2).2 = some circuit) :
    normalizedCircuitResourceMetric
        (recoveryLegalTermCircuitCallOutput context validated) =
      circuit.wireCount := by
  refine normalizedCircuitValidationOutput_wireCount_threshold ?_ hvalid ?_
  · rw [normalizedCircuitExpectedFamily_circuitRequest]
    exact hfamily
  · rw [normalizedCircuitRawCode_circuitRequest]
    exact hdecode

/-- Symmetric branch: the description charge of one accepted per-term summary
is the typed description length of that term's decoded circuit. -/
theorem recoveryLegalTermCircuitCallOutput_descriptionBits_symmetric
    {context validated : ℕ}
    {circuit :
      NormalizedSymmetricThresholdCircuit
        (recoveryLegalTermCircuitArity context)}
    (hfamily : recoveryLegalTermCircuitFamily context = 0)
    (hvalid : recoveryLegalTermCircuitCallOutput context validated ≠ 0)
    (hdecode :
      decodeNormalizedSymmetricThresholdCircuit
          (recoveryLegalTermCircuitArity context)
          (Nat.unpair (Nat.unpair validated).2).2 = some circuit) :
    normalizedCircuitDescriptionMetric
        (recoveryLegalTermCircuitArity context)
        (recoveryLegalTermCircuitCallOutput context validated) =
      circuit.descriptionBits := by
  refine normalizedCircuitValidationOutput_descriptionBits_symmetric ?_ hvalid
    ?_
  · rw [normalizedCircuitExpectedFamily_circuitRequest]
    exact hfamily
  · rw [normalizedCircuitRawCode_circuitRequest]
    exact hdecode

/-- Threshold branch of the previous refinement. -/
theorem recoveryLegalTermCircuitCallOutput_descriptionBits_threshold
    {context validated : ℕ}
    {circuit :
      NormalizedThresholdThresholdCircuit
        (recoveryLegalTermCircuitArity context)}
    (hfamily : recoveryLegalTermCircuitFamily context = 1)
    (hvalid : recoveryLegalTermCircuitCallOutput context validated ≠ 0)
    (hdecode :
      decodeNormalizedThresholdThresholdCircuit
          (recoveryLegalTermCircuitArity context)
          (Nat.unpair (Nat.unpair validated).2).2 = some circuit) :
    normalizedCircuitDescriptionMetric
        (recoveryLegalTermCircuitArity context)
        (recoveryLegalTermCircuitCallOutput context validated) =
      circuit.descriptionBits := by
  refine normalizedCircuitValidationOutput_descriptionBits_threshold ?_ hvalid
    ?_
  · rw [normalizedCircuitExpectedFamily_circuitRequest]
    exact hfamily
  · rw [normalizedCircuitRawCode_circuitRequest]
    exact hdecode

/-! ### Reconstructing typed legal terms from accepted term codes

The executable per-term stages certify canonical field decodes for every term
code.  The two lemmas below turn those field decodes into a typed term whose
canonical code is the original one, and then assemble the whole accepted code
list into a typed term list with the exact same serialization.  Together with
`decodeLegalCircuitSum_of_canonical_fields` this is everything the pure
decoder needs beyond the field-level facts. -/

/-- One accepted term code is the canonical code of a typed legal term. -/
theorem legalCircuitTerm_code_of_canonical_fields
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily}
    (codec : CanonicalCircuitCodec Circuit)
    {q code coefficientCode circuitCode : ℕ}
    {coefficient : ℚ} {circuit : Circuit q}
    (hfields :
      decodeTaggedList code = some [coefficientCode, circuitCode])
    (hcoefficient :
      decodeCanonicalRational coefficientCode = some coefficient)
    (hcircuit : codec.decode q circuitCode = some circuit) :
    ({ coefficient := coefficient
       circuit := circuit } : LegalCircuitTerm Circuit q).code codec =
      code := by
  change
    encodeTaggedList
      [encodeCanonicalRational coefficient, codec.encode circuit] = code
  rw [encodeCanonicalRational_of_decode hcoefficient,
    codec.encode_decode hcircuit]
  exact encodeTaggedList_of_decode hfields

/-- Assemble a typed term list whose serialization is the accepted code list. -/
theorem exists_legalCircuitTerms_of_codes
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily}
    (codec : CanonicalCircuitCodec Circuit) (q : ℕ) {codes : List ℕ}
    (hterms :
      ∀ code ∈ codes,
        ∃ term : LegalCircuitTerm Circuit q, term.code codec = code) :
    ∃ terms : List (LegalCircuitTerm Circuit q),
      terms.map (·.code codec) = codes := by
  induction codes with
  | nil => exact ⟨[], rfl⟩
  | cons code rest inductionHypothesis =>
      obtain ⟨term, hterm⟩ := hterms code (by simp)
      obtain ⟨terms, hcodes⟩ :=
        inductionHypothesis fun next hnext =>
          hterms next (by simp [hnext])
      exact ⟨term :: terms, by simp [hterm, hcodes]⟩

/-! ### Field-level consequences of the accepted legal-sum flags

The four structural legal-sum conjuncts are executable flags on register
projections.  The lemmas below translate each of them onto the pure codecs the
canonical decoder itself runs, so `decodeLegalCircuitSum_of_canonical_fields`
can be applied without re-reading any register ABI.  The terms slot the later
per-term stages consume is the tuple's second field *only* on the accepting
side of the term-count gate, so that bound travels with the bundle. -/

theorem recoveryLegalSumTupleOutput_eq_of_decode
    {handoff qCode termsCode : ℕ}
    (hdecode :
      decodeTaggedList (handoffSumCode handoff) = some [qCode, termsCode]) :
    recoveryLegalSumTupleOutput handoff =
      Nat.pair 1 (Nat.pair (Nat.pair 0 qCode) termsCode) := by
  have hcode : encodeTaggedList [qCode, termsCode] = handoffSumCode handoff :=
    encodeTaggedList_of_decode hdecode
  rw [recoveryLegalSumTupleOutput, ← hcode]
  unfold taggedTupleOutput
  rw [show (2 : ℕ) = [qCode, termsCode].length from rfl,
    decodeTaggedTuple_encode]
  rfl

/-- The tuple flag certifies that the nested legal-sum payload is a canonical
two-field tagged list whose fields are exactly the recorded arity and terms
codes. -/
theorem recoveryLegalSumTuple_decodeTaggedList
    {handoff : ℕ} (htuple : recoveryLegalSumTupleFlag handoff ≠ 0) :
    decodeTaggedList (handoffSumCode handoff) =
      some
        [recoveryLegalSumQCode handoff, recoveryLegalSumTermsCode handoff] := by
  have houtput : recoveryLegalSumTupleOutput handoff ≠ 0 := by
    intro hzero
    apply htuple
    rw [recoveryLegalSumTupleFlag, hzero]
    simp
  obtain ⟨values, hvalues, hlength⟩ :=
    (taggedTupleOutput_ne_zero_iff_decodeTaggedList 2
      (handoffSumCode handoff)).1 houtput
  match values, hlength with
  | [qCode, termsCode], _ =>
      have hshape := recoveryLegalSumTupleOutput_eq_of_decode hvalues
      have hq : recoveryLegalSumQCode handoff = qCode := by
        rw [recoveryLegalSumQCode, recoveryLegalSumTupleFields, hshape]
        simp
      have hterms : recoveryLegalSumTermsCode handoff = termsCode := by
        rw [recoveryLegalSumTermsCode, recoveryLegalSumTupleFields, hshape]
        simp
      rw [hq, hterms]
      exact hvalues

/-- The arity flag certifies that the recorded arity code is a canonical
natural number, and names its value. -/
theorem recoveryLegalSumQCode_decodeNat
    {handoff : ℕ} (hq : recoveryLegalSumQFlag handoff ≠ 0) :
    decodeNat (recoveryLegalSumQCode handoff) =
      some (recoveryLegalSumArityValue handoff) := by
  have hvalidation : recoveryLegalSumQValidation handoff ≠ 0 := by
    intro hzero
    apply hq
    rw [recoveryLegalSumQFlag, hzero]
    simp
  obtain ⟨value, hvalue⟩ :=
    (canonicalNatValidationOutput_ne_zero_iff
      (recoveryLegalSumQCode handoff)).1 hvalidation
  have hpair : recoveryLegalSumQValidation handoff = Nat.pair 1 value :=
    canonicalNatValidationOutput_of_decode hvalue
  have harity : recoveryLegalSumArityValue handoff = value := by
    rw [recoveryLegalSumArityValue, hpair]
    simp
  rw [harity]
  exact hvalue

/-- The equality gate identifies the decoded arity with the schedule-selected
expected arity. -/
theorem recoveryLegalSumArityValue_eq_expectedArity
    {handoff : ℕ} (harity : recoveryLegalSumArityFlag handoff ≠ 0) :
    recoveryLegalSumArityValue handoff =
      handoffSelectedExpectedArity handoff := by
  simpa [recoveryLegalSumArityFlag] using harity

/-- The terms flag certifies that the recorded terms code is a canonical
balanced list, whose payload is the code list the per-term stages map over. -/
theorem recoveryLegalSumTermsCode_decodeBalancedList
    {handoff : ℕ} (hterms : recoveryLegalSumTermsFlag handoff ≠ 0) :
    decodeBalancedList (recoveryLegalSumTermsCode handoff) =
      some
        (balancedValidationMapCodes (recoveryLegalSumTermsCode handoff)) := by
  cases hdecode : decodeBalancedList (recoveryLegalSumTermsCode handoff) with
  | none =>
      exact absurd
        ((NearCubicWires.CanonicalBalancedValidationProgram.balancedCanonicalityOutput_eq_zero_iff
          (recoveryLegalSumTermsCode handoff)).2 hdecode) hterms
  | some codes =>
      rw [balancedValidationMapCodes, hdecode]
      rfl

/-- On the accepting side of the term-count gate the per-term stages read the
very terms code the tuple parser produced. -/
theorem recoveryLegalTermCoefficientTermsCode_eq
    {handoff : ℕ}
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff) :
    recoveryLegalTermCoefficientTermsCode handoff =
      recoveryLegalSumTermsCode handoff := by
  rw [recoveryLegalTermCoefficientTermsCode, recoveryLegalSumBoundOutput,
    recoveryBoundedContextOutput, if_pos hle]
  simp [recoveryLegalSumLengthContext, recoveryLegalSumArityStageOutput,
    recoveryLegalSumArityContext, recoveryLegalSumContext]

/-- Fail-closed twin of the previous identity: when the term-count gate
rejects, the terms slot the per-term stages read is the zero sentinel.  This is
why the term-count bound is a genuine hypothesis of the field bundle below and
not a derivable side condition. -/
theorem recoveryLegalTermCoefficientTermsCode_eq_zero_of_termCount_gt
    {handoff : ℕ}
    (hgt :
      ¬ recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff) :
    recoveryLegalTermCoefficientTermsCode handoff = 0 := by
  rw [recoveryLegalTermCoefficientTermsCode, recoveryLegalSumBoundOutput,
    recoveryBoundedContextOutput, if_neg hgt]
  simp

/-- Complete field bundle of the accepted legal sum, stated purely against the
canonical decoders: the nested payload is a canonical two-field tagged list,
its first field is the canonical code of the schedule-selected expected arity,
and its second field is the canonical balanced list of term codes the per-term
stages consume. -/
theorem recoveryLegalSumFields_of_accept (handoff : ℕ)
    (htuple : recoveryLegalSumTupleFlag handoff ≠ 0)
    (hq : recoveryLegalSumQFlag handoff ≠ 0)
    (harity : recoveryLegalSumArityFlag handoff ≠ 0)
    (hterms : recoveryLegalSumTermsFlag handoff ≠ 0)
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff) :
    decodeTaggedList (handoffSumCode handoff) =
        some
          [recoveryLegalSumQCode handoff,
            recoveryLegalTermCoefficientTermsCode handoff] ∧
      decodeNat (recoveryLegalSumQCode handoff) =
        some (handoffSelectedExpectedArity handoff) ∧
      decodeBalancedList (recoveryLegalTermCoefficientTermsCode handoff) =
        some
          (balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff)) := by
  have hbridge := recoveryLegalTermCoefficientTermsCode_eq hle
  refine ⟨?_, ?_, ?_⟩
  · rw [hbridge]
    exact recoveryLegalSumTuple_decodeTaggedList htuple
  · rw [recoveryLegalSumQCode_decodeNat hq,
      recoveryLegalSumArityValue_eq_expectedArity harity]
  · rw [hbridge]
    exact recoveryLegalSumTermsCode_decodeBalancedList hterms

/-! ### Canonical outer fields on the accepting path

`recoveryValidatorOraclePrefixOutput_ne_zero_iff` already states acceptance
against the pure decoders, but leaves the accepted mode tag and the nested
legal-sum code as anonymous existentials.  The lemmas below pin them to the
handoff projections the legal-sum stages actually read, which is what the
mode-specific round-trip lemmas require. -/

private theorem decodeRecoveryEnvelope_of_modeCode_zero
    {raw modeCode oracleCode sumCode : ℕ}
    (hfields : decodeTaggedList raw = some [modeCode, oracleCode, sumCode])
    (hmode : decodeNat modeCode = some 0) :
    decodeRecoveryEnvelope raw =
      some ⟨.symmetric, oracleCode, sumCode⟩ := by
  simp [decodeRecoveryEnvelope, hfields, hmode]

private theorem decodeRecoveryEnvelope_of_modeCode_one
    {raw modeCode oracleCode sumCode : ℕ}
    (hfields : decodeTaggedList raw = some [modeCode, oracleCode, sumCode])
    (hmode : decodeNat modeCode = some 1) :
    decodeRecoveryEnvelope raw =
      some ⟨.threshold, oracleCode, sumCode⟩ := by
  simp [decodeRecoveryEnvelope, hfields, hmode]

/-- The executable mode tag is the successor of the canonical mode code: the
symmetric branch is code `0`/tag `1`, the threshold branch is code `1`/tag `2`.
There is no third accepted pairing. -/
theorem handoffMode_oraclePrefixOutput_of_modeCode
    {limits : RecoveryWitnessLimits} {raw modeCode oracleCode sumCode : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0)
    (hfields : decodeTaggedList raw = some [modeCode, oracleCode, sumCode])
    (hmode : decodeNat modeCode = some 0 ∨ decodeNat modeCode = some 1) :
    (decodeNat modeCode = some 0 ∧
        handoffMode (recoveryValidatorOraclePrefixOutput limits raw) = 1) ∨
      (decodeNat modeCode = some 1 ∧
        handoffMode (recoveryValidatorOraclePrefixOutput limits raw) = 2) := by
  obtain ⟨envelope, hdecode, htag⟩ :=
    recoveryValidatorOraclePrefix_decodeRecoveryEnvelope haccepts
  rcases hmode with hzero | hone
  · refine Or.inl ⟨hzero, ?_⟩
    rw [decodeRecoveryEnvelope_of_modeCode_zero hfields hzero] at hdecode
    have henvelope :
        envelope = ⟨.symmetric, oracleCode, sumCode⟩ :=
      (Option.some.inj hdecode).symm
    rw [htag, henvelope]
    rfl
  · refine Or.inr ⟨hone, ?_⟩
    rw [decodeRecoveryEnvelope_of_modeCode_one hfields hone] at hdecode
    have henvelope :
        envelope = ⟨.threshold, oracleCode, sumCode⟩ :=
      (Option.some.inj hdecode).symm
    rw [htag, henvelope]
    rfl

/-- Complete outer-field bundle of the accepting Boolean-DAG prefix: the raw
code is a canonical three-field tagged list whose third field is exactly the
nested legal-sum code every later stage reads, whose second field is a
canonical Boolean circuit within the configured size cap, and whose mode code
selects the branch policy the legal-sum stages are configured with. -/
theorem recoveryValidatorOraclePrefix_canonicalOuterFields
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts : recoveryValidatorOraclePrefixOutput limits raw ≠ 0) :
    ∃ modeCode oracleCode : ℕ,
      ∃ oracle : BooleanCircuit limits.oracleArity,
      decodeTaggedList raw =
          some
            [modeCode, oracleCode,
              handoffSumCode
                (recoveryValidatorOraclePrefixOutput limits raw)] ∧
        decodeBooleanCircuit limits.oracleArity oracleCode = some oracle ∧
          oracle.size ≤ limits.oracleSizeCap ∧
          ((decodeNat modeCode = some 0 ∧
              handoffMode (recoveryValidatorOraclePrefixOutput limits raw) =
                1 ∧
              recoveryValidatorSelectedPolicy limits raw = limits.symmetric) ∨
            (decodeNat modeCode = some 1 ∧
              handoffMode (recoveryValidatorOraclePrefixOutput limits raw) =
                2 ∧
              recoveryValidatorSelectedPolicy limits raw =
                limits.threshold)) := by
  obtain ⟨modeCode, oracleCode, sumCode, hfields, hmodeCode, _,
    oracle, horacle, hsize⟩ :=
    (recoveryValidatorOraclePrefixOutput_ne_zero_iff limits raw).1 haccepts
  obtain ⟨_, hsumEq⟩ := recoveryEnvelopeCodes_of_taggedList hfields
  have hsumCode :
      handoffSumCode (recoveryValidatorOraclePrefixOutput limits raw) =
        sumCode := by
    rw [handoffSumCode_oraclePrefixOutput haccepts]
    exact hsumEq
  refine ⟨modeCode, oracleCode, oracle, ?_, horacle, hsize, ?_⟩
  · rw [hsumCode]
    exact hfields
  · rcases handoffMode_oraclePrefixOutput_of_modeCode haccepts hfields
      hmodeCode with ⟨hcode, hmode⟩ | ⟨hcode, hmode⟩
    · exact Or.inl ⟨hcode, hmode, recoveryValidatorSelectedPolicy_symmetric hmode⟩
    · exact Or.inr ⟨hcode, hmode, recoveryValidatorSelectedPolicy_threshold hmode⟩

/-! ### Canonical legal-sum fields on the accepting path

Instantiating the flag-level bundle at the staged handoff and rewriting the
schedule-selected arity through the limits-recovery statement turns the four
structural legal-sum conjuncts into exactly the three field decodes
`decodeLegalCircuitSum` performs. -/

/-- The term-count charged by the executable gate is the length of the code
list the per-term stages map over. -/
theorem recoveryLegalSumTermCount_eq_length
    {inputLength : ℕ} {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0) :
    recoveryLegalSumTermCount (recoveryValidatorOraclePrefixOutput limits raw) =
      (balancedValidationMapCodes
        (recoveryLegalTermCoefficientTermsCode
          (recoveryValidatorOraclePrefixOutput limits raw))).length := by
  obtain ⟨_, _, _, _, hle, _, _, _, _, _, _, _⟩ :=
    (recoveryValidatorLegalSumPrefixOutput_ne_zero_iff inputLength limits
      raw).1 haccepts
  rw [recoveryLegalTermCoefficientTermsCode_eq hle]
  rfl

/-- Complete legal-sum field bundle of the accepting staged validator, stated
against the pure decoders and the typed branch policy. -/
theorem recoveryValidatorLegalSumPrefix_canonicalSumFields
    {inputLength : ℕ} {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0) :
    decodeTaggedList
        (handoffSumCode (recoveryValidatorOraclePrefixOutput limits raw)) =
        some
          [recoveryLegalSumQCode
              (recoveryValidatorOraclePrefixOutput limits raw),
            recoveryLegalTermCoefficientTermsCode
              (recoveryValidatorOraclePrefixOutput limits raw)] ∧
      decodeNat
          (recoveryLegalSumQCode
            (recoveryValidatorOraclePrefixOutput limits raw)) =
        some (recoveryValidatorSelectedPolicy limits raw).expectedArity ∧
      decodeBalancedList
          (recoveryLegalTermCoefficientTermsCode
            (recoveryValidatorOraclePrefixOutput limits raw)) =
        some
          (balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode
              (recoveryValidatorOraclePrefixOutput limits raw))) := by
  have horacle :=
    recoveryValidatorOraclePrefixOutput_ne_zero_of_legalSum haccepts
  obtain ⟨_, _, _, _, hle, hterms, harity, hq, htuple, _, _, _⟩ :=
    (recoveryValidatorLegalSumPrefixOutput_ne_zero_iff inputLength limits
      raw).1 haccepts
  obtain ⟨hfields, hqDecode, hcodes⟩ :=
    recoveryLegalSumFields_of_accept
      (recoveryValidatorOraclePrefixOutput limits raw) htuple hq harity hterms
      hle
  refine ⟨hfields, ?_, hcodes⟩
  rw [hqDecode, handoffSelectedExpectedArity_oraclePrefixOutput horacle]

/-- The term-count conjunct in typed form: the accepted code list is no longer
than the schedule-selected term cap of the typed branch policy. -/
theorem recoveryValidatorLegalSumPrefix_termCount_le
    {inputLength : ℕ} {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0) :
    (balancedValidationMapCodes
        (recoveryLegalTermCoefficientTermsCode
          (recoveryValidatorOraclePrefixOutput limits raw))).length ≤
      (recoveryValidatorSelectedPolicy limits raw).termCap := by
  have horacle :=
    recoveryValidatorOraclePrefixOutput_ne_zero_of_legalSum haccepts
  obtain ⟨_, _, _, _, hle, _, _, _, _, _, _, _⟩ :=
    (recoveryValidatorLegalSumPrefixOutput_ne_zero_iff inputLength limits
      raw).1 haccepts
  rw [← recoveryLegalSumTermCount_eq_length haccepts,
    ← handoffSelectedTermCap_oraclePrefixOutput horacle]
  exact hle

theorem recoveryLegalTermBoundHandoff_eq
    {handoff : ℕ}
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff) :
    recoveryLegalTermBoundHandoff handoff = handoff := by
  rw [recoveryLegalTermBoundHandoff, recoveryLegalSumBoundOutput,
    recoveryBoundedContextOutput, if_pos hle]
  simp [recoveryLegalSumLengthContext, recoveryLegalSumArityStageOutput,
    recoveryLegalSumArityContext, recoveryLegalSumContext]

theorem recoveryLegalTermBoundExpectedArity_eq
    {handoff : ℕ}
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff) :
    recoveryLegalTermBoundExpectedArity handoff =
      handoffSelectedExpectedArity handoff := by
  rw [recoveryLegalTermBoundExpectedArity, recoveryLegalSumBoundOutput,
    recoveryBoundedContextOutput, if_pos hle]
  simp [recoveryLegalSumLengthContext, recoveryLegalSumArityStageOutput,
    recoveryLegalSumArityContext, recoveryLegalSumContext]

theorem recoveryLegalTermCircuitArity_circuitContext
    {handoff : ℕ}
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff) :
    recoveryLegalTermCircuitArity (recoveryLegalTermCircuitContext handoff) =
      handoffSelectedExpectedArity handoff := by
  have hcontext :
      recoveryLegalTermCircuitArity (recoveryLegalTermCircuitContext handoff) =
        recoveryLegalTermBoundExpectedArity handoff := by
    simp [recoveryLegalTermCircuitArity, recoveryLegalTermCircuitContext]
  rw [hcontext]
  exact recoveryLegalTermBoundExpectedArity_eq hle

theorem recoveryLegalTermCircuitFamily_circuitContext
    {handoff : ℕ}
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff) :
    recoveryLegalTermCircuitFamily (recoveryLegalTermCircuitContext handoff) =
      (handoffMode handoff).pred := by
  have hcontext :
      recoveryLegalTermCircuitFamily
          (recoveryLegalTermCircuitContext handoff) =
        (handoffMode (recoveryLegalTermBoundHandoff handoff)).pred := by
    simp [recoveryLegalTermCircuitFamily, recoveryLegalTermCircuitContext]
  rw [hcontext, recoveryLegalTermBoundHandoff_eq hle]

/-! ### Per-term canonical reconstruction

The coefficient pass certifies the two-field term syntax and the canonical
rational; the circuit pass certifies the normalized circuit in the selected
family.  Together they rebuild a typed `LegalCircuitTerm` whose canonical code
is bit-for-bit the accepted term code, which is what
`decodeLegalCircuitSum_of_canonical_fields` consumes. -/

/-- Accepted coefficient payload of one term code. -/
theorem legalTermCoefficientValidationOutput_eq_pair_of_ne_zero
    {code : ℕ} (haccepts : legalTermCoefficientValidationOutput code ≠ 0) :
    legalTermCoefficientValidationOutput code =
      Nat.pair 1
        (Nat.pair (rationalValidationOutput (legalTermCoefficientCode code))
          (legalTermCircuitCode code)) := by
  by_cases htuple : legalTermTupleFlag code = 0
  · exact absurd
      (by simp [legalTermCoefficientValidationOutput, htuple]) haccepts
  · by_cases hrational :
        rationalValidationOutput (legalTermCoefficientCode code) = 0
    · exact absurd
        (by simp [legalTermCoefficientValidationOutput, htuple, hrational])
        haccepts
    · simp [legalTermCoefficientValidationOutput, htuple, hrational]

/-- The circuit slot the circuit pass reads from an accepted coefficient
payload is the term code's own circuit field. -/
theorem recoveryLegalTermValidatedCircuitCode_eq
    {code coefficientCode circuitCode : ℕ}
    (haccepts : legalTermCoefficientValidationOutput code ≠ 0)
    (hfields :
      decodeTaggedList code = some [coefficientCode, circuitCode]) :
    (Nat.unpair
        (Nat.unpair (legalTermCoefficientValidationOutput code)).2).2 =
      circuitCode := by
  obtain ⟨_, hcircuitCode⟩ := legalTermCodes_of_decode hfields
  rw [legalTermCoefficientValidationOutput_eq_pair_of_ne_zero haccepts]
  simp [hcircuitCode]

/-- Exact acceptance criterion of the coefficient pass over the accepted terms
code, stated leafwise against the per-term coefficient validator. -/
theorem recoveryLegalTermCoefficientListOutput_ne_zero_iff
    (inputLength raw : ℕ) :
    recoveryLegalTermCoefficientListOutput inputLength raw ≠ 0 ↔
      ∃ codes,
        decodeBalancedList raw = some codes ∧
          ∀ code ∈ codes, legalTermCoefficientValidationOutput code ≠ 0 := by
  rw [recoveryLegalTermCoefficientListOutput,
    balancedValidationSummaryOutput_ne_zero_iff]
  simp only [recoveryLegalTermCoefficientRequestOutput, nativeInputRequest,
    Nat.unpair_pair]

/-- Symmetric branch: one accepted term code is the canonical code of a typed
`SYM ∘ THR` legal term at the selected arity. -/
theorem exists_symmetricLegalCircuitTerm_of_termCode
    {context code : ℕ}
    (hfamily : recoveryLegalTermCircuitFamily context = 0)
    (hcoefficient : legalTermCoefficientValidationOutput code ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitCallOutput context
        (legalTermCoefficientValidationOutput code) ≠ 0) :
    ∃ term :
        LegalCircuitTerm NormalizedSymmetricThresholdCircuit
          (recoveryLegalTermCircuitArity context),
      term.code symmetricCircuitCodec = code ∧
        decodeNormalizedSymmetricThresholdCircuit
            (recoveryLegalTermCircuitArity context)
            (Nat.unpair
              (Nat.unpair
                (legalTermCoefficientValidationOutput code)).2).2 =
          some term.circuit := by
  obtain ⟨coefficientCode, circuitCode, coefficient, hfields, hrational⟩ :=
    (legalTermCoefficientValidationOutput_ne_zero_iff code).1 hcoefficient
  have hproject :
      (Nat.unpair
          (Nat.unpair (legalTermCoefficientValidationOutput code)).2).2 =
        circuitCode :=
    recoveryLegalTermValidatedCircuitCode_eq hcoefficient hfields
  rcases (recoveryLegalTermCircuitCallOutput_ne_zero_iff context
      (legalTermCoefficientValidationOutput code)).1 hcircuit with
    ⟨_, hsome⟩ | ⟨hother, _⟩
  · rw [hproject] at hsome
    obtain ⟨circuit, hdecode⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨⟨coefficient, circuit⟩, ?_, ?_⟩
    · exact legalCircuitTerm_code_of_canonical_fields symmetricCircuitCodec
        hfields hrational hdecode
    · rw [hproject]
      exact hdecode
  · rw [hfamily] at hother
    exact absurd hother (by omega)

/-- Threshold twin of the previous reconstruction. -/
theorem exists_thresholdLegalCircuitTerm_of_termCode
    {context code : ℕ}
    (hfamily : recoveryLegalTermCircuitFamily context = 1)
    (hcoefficient : legalTermCoefficientValidationOutput code ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitCallOutput context
        (legalTermCoefficientValidationOutput code) ≠ 0) :
    ∃ term :
        LegalCircuitTerm NormalizedThresholdThresholdCircuit
          (recoveryLegalTermCircuitArity context),
      term.code thresholdCircuitCodec = code ∧
        decodeNormalizedThresholdThresholdCircuit
            (recoveryLegalTermCircuitArity context)
            (Nat.unpair
              (Nat.unpair
                (legalTermCoefficientValidationOutput code)).2).2 =
          some term.circuit := by
  obtain ⟨coefficientCode, circuitCode, coefficient, hfields, hrational⟩ :=
    (legalTermCoefficientValidationOutput_ne_zero_iff code).1 hcoefficient
  have hproject :
      (Nat.unpair
          (Nat.unpair (legalTermCoefficientValidationOutput code)).2).2 =
        circuitCode :=
    recoveryLegalTermValidatedCircuitCode_eq hcoefficient hfields
  rcases (recoveryLegalTermCircuitCallOutput_ne_zero_iff context
      (legalTermCoefficientValidationOutput code)).1 hcircuit with
    ⟨hother, _⟩ | ⟨_, hsome⟩
  · rw [hfamily] at hother
    exact absurd hother (by omega)
  · rw [hproject] at hsome
    obtain ⟨circuit, hdecode⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨⟨coefficient, circuit⟩, ?_, ?_⟩
    · exact legalCircuitTerm_code_of_canonical_fields thresholdCircuitCodec
        hfields hrational hdecode
    · rw [hproject]
      exact hdecode

/-! ### Whole-list typed reconstruction

Both per-term passes accept over the same accepted code list, so every term
code carries both certificates at once.  Feeding that through
`exists_legalCircuitTerms_of_codes` produces a typed term list whose
serialization is bit-for-bit the accepted balanced list. -/

/-- Both per-term certificates for every accepted term code. -/
theorem legalSumAccept_termCode_certificates
    {inputLength handoff : ℕ}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0) :
    ∀ code ∈
        balancedValidationMapCodes
          (recoveryLegalTermCoefficientTermsCode handoff),
      legalTermCoefficientValidationOutput code ≠ 0 ∧
        recoveryLegalTermCircuitCallOutput
            (recoveryLegalTermCircuitContext handoff)
            (legalTermCoefficientValidationOutput code) ≠ 0 := by
  obtain ⟨codes, hcodes, hallCoefficient⟩ :=
    (recoveryLegalTermCoefficientListOutput_ne_zero_iff inputLength
      (recoveryLegalTermCoefficientTermsCode handoff)).1 hcoefficient
  have hcodesEq :
      balancedValidationMapCodes
          (recoveryLegalTermCoefficientTermsCode handoff) = codes := by
    rw [balancedValidationMapCodes, hcodes]
    rfl
  obtain ⟨validatedCodes, hvalidated, hallCircuit⟩ :=
    (recoveryLegalTermCircuitListOutput_ne_zero_iff
      (recoveryLegalTermCircuitContext handoff)
      (recoveryLegalTermCoefficientMappedCode inputLength handoff)).1 hcircuit
  rw [recoveryLegalTermCoefficientMappedCode_eq inputLength handoff
      hcoefficient,
    decodeBalancedList_encode] at hvalidated
  have hvalidatedEq :
      (balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff)).map
          legalTermCoefficientValidationOutput = validatedCodes :=
    Option.some.inj hvalidated
  intro code hcode
  refine ⟨hallCoefficient code (hcodesEq ▸ hcode), ?_⟩
  refine hallCircuit (legalTermCoefficientValidationOutput code) ?_
  rw [← hvalidatedEq]
  exact List.mem_map.2 ⟨code, hcode, rfl⟩

/-- Symmetric branch: the accepted code list is the serialization of a typed
`SYM ∘ THR` term list at the schedule-selected arity. -/
theorem exists_symmetricLegalCircuitTerms_of_legalSumAccept
    {inputLength handoff q : ℕ}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff)
    (hmode : handoffMode handoff = 1)
    (harity : handoffSelectedExpectedArity handoff = q) :
    ∃ terms : List (LegalCircuitTerm NormalizedSymmetricThresholdCircuit q),
      terms.map (·.code symmetricCircuitCodec) =
        balancedValidationMapCodes
          (recoveryLegalTermCoefficientTermsCode handoff) := by
  subst harity
  have hfamily :
      recoveryLegalTermCircuitFamily
        (recoveryLegalTermCircuitContext handoff) = 0 := by
    rw [recoveryLegalTermCircuitFamily_circuitContext hle, hmode]
    rfl
  have hcertificates :=
    legalSumAccept_termCode_certificates hcoefficient hcircuit
  rw [← recoveryLegalTermCircuitArity_circuitContext hle]
  refine exists_legalCircuitTerms_of_codes symmetricCircuitCodec
    (recoveryLegalTermCircuitArity (recoveryLegalTermCircuitContext handoff))
    ?_
  intro code hcode
  obtain ⟨hcoefficientCode, hcircuitCode⟩ := hcertificates code hcode
  obtain ⟨term, hterm, _⟩ :=
    exists_symmetricLegalCircuitTerm_of_termCode hfamily hcoefficientCode
      hcircuitCode
  exact ⟨term, hterm⟩

/-- Threshold twin of the previous reconstruction. -/
theorem exists_thresholdLegalCircuitTerms_of_legalSumAccept
    {inputLength handoff q : ℕ}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff)
    (hmode : handoffMode handoff = 2)
    (harity : handoffSelectedExpectedArity handoff = q) :
    ∃ terms : List (LegalCircuitTerm NormalizedThresholdThresholdCircuit q),
      terms.map (·.code thresholdCircuitCodec) =
        balancedValidationMapCodes
          (recoveryLegalTermCoefficientTermsCode handoff) := by
  subst harity
  have hfamily :
      recoveryLegalTermCircuitFamily
        (recoveryLegalTermCircuitContext handoff) = 1 := by
    rw [recoveryLegalTermCircuitFamily_circuitContext hle, hmode]
    rfl
  have hcertificates :=
    legalSumAccept_termCode_certificates hcoefficient hcircuit
  rw [← recoveryLegalTermCircuitArity_circuitContext hle]
  refine exists_legalCircuitTerms_of_codes thresholdCircuitCodec
    (recoveryLegalTermCircuitArity (recoveryLegalTermCircuitContext handoff))
    ?_
  intro code hcode
  obtain ⟨hcoefficientCode, hcircuitCode⟩ := hcertificates code hcode
  obtain ⟨term, hterm, _⟩ :=
    exists_thresholdLegalCircuitTerm_of_termCode hfamily hcoefficientCode
      hcircuitCode
  exact ⟨term, hterm⟩

/-! ### Typed resource charges of one typed term

The metric refinements are stated against an anonymous validated payload.  The
lemmas below instantiate them at the payload the coefficient pass produces from
a typed term's own canonical code, which removes the last register projection
from the resource conjuncts. -/

theorem recoveryLegalTermValidatedCircuitCode_symmetric_term
    {n : ℕ} (term : LegalCircuitTerm NormalizedSymmetricThresholdCircuit n) :
    (Nat.unpair
        (Nat.unpair
          (legalTermCoefficientValidationOutput
            (term.code symmetricCircuitCodec))).2).2 =
      encodeNormalizedSymmetricThresholdCircuit term.circuit := by
  rw [legalTermCoefficientValidationOutput_code symmetricCircuitCodec term]
  simp [symmetricCircuitCodec]

theorem recoveryLegalTermValidatedCircuitCode_threshold_term
    {n : ℕ} (term : LegalCircuitTerm NormalizedThresholdThresholdCircuit n) :
    (Nat.unpair
        (Nat.unpair
          (legalTermCoefficientValidationOutput
            (term.code thresholdCircuitCodec))).2).2 =
      encodeNormalizedThresholdThresholdCircuit term.circuit := by
  rw [legalTermCoefficientValidationOutput_code thresholdCircuitCodec term]
  simp [thresholdCircuitCodec]

theorem recoveryLegalTermCircuitCallOutput_wireCount_symmetric_term
    {context : ℕ}
    {term :
      LegalCircuitTerm NormalizedSymmetricThresholdCircuit
        (recoveryLegalTermCircuitArity context)}
    (hfamily : recoveryLegalTermCircuitFamily context = 0)
    (hvalid :
      recoveryLegalTermCircuitCallOutput context
        (legalTermCoefficientValidationOutput
          (term.code symmetricCircuitCodec)) ≠ 0) :
    normalizedCircuitResourceMetric
        (recoveryLegalTermCircuitCallOutput context
          (legalTermCoefficientValidationOutput
            (term.code symmetricCircuitCodec))) =
      NormalizedSymmetricThresholdCircuit.wireCount term.circuit := by
  refine recoveryLegalTermCircuitCallOutput_wireCount_symmetric hfamily hvalid
    ?_
  rw [recoveryLegalTermValidatedCircuitCode_symmetric_term term]
  exact decodeNormalizedSymmetricThresholdCircuit_encode term.circuit

theorem recoveryLegalTermCircuitCallOutput_wireCount_threshold_term
    {context : ℕ}
    {term :
      LegalCircuitTerm NormalizedThresholdThresholdCircuit
        (recoveryLegalTermCircuitArity context)}
    (hfamily : recoveryLegalTermCircuitFamily context = 1)
    (hvalid :
      recoveryLegalTermCircuitCallOutput context
        (legalTermCoefficientValidationOutput
          (term.code thresholdCircuitCodec)) ≠ 0) :
    normalizedCircuitResourceMetric
        (recoveryLegalTermCircuitCallOutput context
          (legalTermCoefficientValidationOutput
            (term.code thresholdCircuitCodec))) =
      NormalizedThresholdThresholdCircuit.wireCount term.circuit := by
  refine recoveryLegalTermCircuitCallOutput_wireCount_threshold hfamily hvalid
    ?_
  rw [recoveryLegalTermValidatedCircuitCode_threshold_term term]
  exact decodeNormalizedThresholdThresholdCircuit_encode term.circuit

theorem recoveryLegalTermCircuitCallOutput_descriptionBits_symmetric_term
    {context : ℕ}
    {term :
      LegalCircuitTerm NormalizedSymmetricThresholdCircuit
        (recoveryLegalTermCircuitArity context)}
    (hfamily : recoveryLegalTermCircuitFamily context = 0)
    (hvalid :
      recoveryLegalTermCircuitCallOutput context
        (legalTermCoefficientValidationOutput
          (term.code symmetricCircuitCodec)) ≠ 0) :
    normalizedCircuitDescriptionMetric
        (recoveryLegalTermCircuitArity context)
        (recoveryLegalTermCircuitCallOutput context
          (legalTermCoefficientValidationOutput
            (term.code symmetricCircuitCodec))) =
      NormalizedSymmetricThresholdCircuit.descriptionBits term.circuit := by
  refine recoveryLegalTermCircuitCallOutput_descriptionBits_symmetric hfamily
    hvalid ?_
  rw [recoveryLegalTermValidatedCircuitCode_symmetric_term term]
  exact decodeNormalizedSymmetricThresholdCircuit_encode term.circuit

theorem recoveryLegalTermCircuitCallOutput_descriptionBits_threshold_term
    {context : ℕ}
    {term :
      LegalCircuitTerm NormalizedThresholdThresholdCircuit
        (recoveryLegalTermCircuitArity context)}
    (hfamily : recoveryLegalTermCircuitFamily context = 1)
    (hvalid :
      recoveryLegalTermCircuitCallOutput context
        (legalTermCoefficientValidationOutput
          (term.code thresholdCircuitCodec)) ≠ 0) :
    normalizedCircuitDescriptionMetric
        (recoveryLegalTermCircuitArity context)
        (recoveryLegalTermCircuitCallOutput context
          (legalTermCoefficientValidationOutput
            (term.code thresholdCircuitCodec))) =
      NormalizedThresholdThresholdCircuit.descriptionBits term.circuit := by
  refine recoveryLegalTermCircuitCallOutput_descriptionBits_threshold hfamily
    hvalid ?_
  rw [recoveryLegalTermValidatedCircuitCode_threshold_term term]
  exact decodeNormalizedThresholdThresholdCircuit_encode term.circuit

@[simp] theorem recoveryLegalTermCircuitArity_circuitContext_eq_bound
    (handoff : ℕ) :
    recoveryLegalTermCircuitArity (recoveryLegalTermCircuitContext handoff) =
      recoveryLegalTermBoundExpectedArity handoff := by
  simp [recoveryLegalTermCircuitArity, recoveryLegalTermCircuitContext]

/-! ### Per-code resource certificates of the accepting legal sum

The three resource passes accept over payloads derived from the same accepted
code list, so each accepted term code carries its own bit-width, wire and
description certificate.  Each lemma below is stated at one code, which keeps
the later whole-list assembly free of nested balanced-tree reasoning. -/

private theorem legalSumAccept_mappedCode_decode
    {inputLength handoff : ℕ}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0) :
    decodeBalancedList
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) =
      some
        ((balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff)).map
          legalTermCoefficientValidationOutput) := by
  rw [recoveryLegalTermCoefficientMappedCode_eq inputLength handoff
      hcoefficient,
    decodeBalancedList_encode]

/-- Bit-width certificate of one accepted term code. -/
theorem legalSumAccept_coefficientBits_le
    {inputLength handoff code : ℕ}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hbitCap :
      recoveryLegalTermCoefficientBitCapListOutput
        (handoffSelectedCoefficientBitCap handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hcode :
      code ∈
        balancedValidationMapCodes
          (recoveryLegalTermCoefficientTermsCode handoff)) :
    natBitLength
        (recoveryLegalTermValidatedMagnitude
          (legalTermCoefficientValidationOutput code)) ≤
        handoffSelectedCoefficientBitCap handoff ∧
      natBitLength
          (recoveryLegalTermValidatedDenominator
            (legalTermCoefficientValidationOutput code)) ≤
        handoffSelectedCoefficientBitCap handoff := by
  obtain ⟨validatedCodes, hvalidated, hall⟩ :=
    (recoveryLegalTermCoefficientBitCapListOutput_ne_zero_iff
      (handoffSelectedCoefficientBitCap handoff)
      (recoveryLegalTermCoefficientMappedCode inputLength handoff)).1 hbitCap
  rw [legalSumAccept_mappedCode_decode hcoefficient] at hvalidated
  have hmem : legalTermCoefficientValidationOutput code ∈ validatedCodes := by
    rw [← Option.some.inj hvalidated]
    exact List.mem_map.2 ⟨code, hcode, rfl⟩
  obtain ⟨_, hmagnitude, hdenominator⟩ :=
    hall (legalTermCoefficientValidationOutput code) hmem
  exact ⟨hmagnitude, hdenominator⟩

private theorem legalSumAccept_summaryTree_mem
    {inputLength handoff code : ℕ}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hcode :
      code ∈
        balancedValidationMapCodes
          (recoveryLegalTermCoefficientTermsCode handoff))
    {summaries : List ℕ}
    (hsummaries :
      decodeBalancedList
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) =
          some summaries) :
    recoveryLegalTermCircuitCallOutput
        (recoveryLegalTermCircuitContext handoff)
        (legalTermCoefficientValidationOutput code) ∈ summaries := by
  rw [decodeBalancedList_recoveryLegalTermValidatedSummaryTree inputLength
    handoff hcoefficient hcircuit] at hsummaries
  rw [← Option.some.inj hsummaries]
  exact List.mem_map.2
    ⟨legalTermCoefficientValidationOutput code,
      List.mem_map.2 ⟨code, hcode, rfl⟩, rfl⟩

/-- Wire certificate of one accepted term code. -/
theorem legalSumAccept_wireMetric_le
    {inputLength handoff code : ℕ}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hwire :
      recoveryLegalTermWireListOutput
        (recoveryLegalTermWireCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0)
    (hcode :
      code ∈
        balancedValidationMapCodes
          (recoveryLegalTermCoefficientTermsCode handoff)) :
    normalizedCircuitResourceMetric
        (recoveryLegalTermCircuitCallOutput
          (recoveryLegalTermCircuitContext handoff)
          (legalTermCoefficientValidationOutput code)) ≤
      handoffSelectedWireCap handoff := by
  obtain ⟨summaries, hsummaries, hall⟩ :=
    (recoveryLegalTermWireListOutput_ne_zero_iff
      (recoveryLegalTermWireCapContext handoff)
      (recoveryLegalTermValidatedSummaryTree inputLength handoff)).1 hwire
  have hbound :=
    hall
      (recoveryLegalTermCircuitCallOutput
        (recoveryLegalTermCircuitContext handoff)
        (legalTermCoefficientValidationOutput code))
      (legalSumAccept_summaryTree_mem hcoefficient hcircuit hcode hsummaries)
  rwa [recoveryLegalTermResourceCap_wireCapContext] at hbound

/-- Description certificate of one accepted term code. -/
theorem legalSumAccept_descriptionMetric_le
    {inputLength handoff code : ℕ}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hdescription :
      recoveryLegalTermDescriptionListOutput
        (recoveryLegalTermDescriptionCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0)
    (hcode :
      code ∈
        balancedValidationMapCodes
          (recoveryLegalTermCoefficientTermsCode handoff)) :
    normalizedCircuitDescriptionMetric
        (recoveryLegalTermCircuitArity
          (recoveryLegalTermCircuitContext handoff))
        (recoveryLegalTermCircuitCallOutput
          (recoveryLegalTermCircuitContext handoff)
          (legalTermCoefficientValidationOutput code)) ≤
      handoffSelectedDescriptionCap handoff := by
  obtain ⟨summaries, hsummaries, hall⟩ :=
    (recoveryLegalTermDescriptionListOutput_ne_zero_iff
      (recoveryLegalTermDescriptionCapContext handoff)
      (recoveryLegalTermValidatedSummaryTree inputLength handoff)).1
      hdescription
  have hbound :=
    hall
      (recoveryLegalTermCircuitCallOutput
        (recoveryLegalTermCircuitContext handoff)
        (legalTermCoefficientValidationOutput code))
      (legalSumAccept_summaryTree_mem hcoefficient hcircuit hcode hsummaries)
  rw [recoveryLegalTermResourceCap_descriptionCapContext,
    recoveryLegalTermResourceArity_descriptionCapContext] at hbound
  rwa [recoveryLegalTermCircuitArity_circuitContext_eq_bound]

/-! ### Whole-list typed reconstruction with resource bounds

Combining the per-code certificates with the typed reconstruction produces the
term list `decodeLegalCircuitSum` would build, already carrying its bit-width,
wire and description proof fields.  Only the exact coefficient-mass field of
`CheckedLegalCircuitSum` is not produced here. -/

/-- Symmetric branch: the accepted code list is the exact serialization of a
typed term list that already satisfies every per-term resource field of
`CheckedLegalCircuitSum` except the exact coefficient mass. -/
theorem exists_symmetricLegalCircuitTerms_bounded_of_legalSumAccept
    {inputLength handoff q : ℕ}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hbitCap :
      recoveryLegalTermCoefficientBitCapListOutput
        (handoffSelectedCoefficientBitCap handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hwire :
      recoveryLegalTermWireListOutput
        (recoveryLegalTermWireCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0)
    (hdescription :
      recoveryLegalTermDescriptionListOutput
        (recoveryLegalTermDescriptionCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0)
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff)
    (hmode : handoffMode handoff = 1)
    (harity : handoffSelectedExpectedArity handoff = q) :
    ∃ terms : List (LegalCircuitTerm NormalizedSymmetricThresholdCircuit q),
      terms.map (·.code symmetricCircuitCodec) =
          balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff) ∧
        (∀ term ∈ terms,
          natBitLength term.coefficient.num.natAbs ≤
              handoffSelectedCoefficientBitCap handoff ∧
            natBitLength term.coefficient.den ≤
              handoffSelectedCoefficientBitCap handoff) ∧
        (∀ term ∈ terms,
          NormalizedSymmetricThresholdCircuit.wireCount term.circuit ≤
            handoffSelectedWireCap handoff) ∧
        (∀ term ∈ terms,
          NormalizedSymmetricThresholdCircuit.descriptionBits term.circuit ≤
            handoffSelectedDescriptionCap handoff) := by
  subst harity
  have hfamily :
      recoveryLegalTermCircuitFamily
        (recoveryLegalTermCircuitContext handoff) = 0 := by
    rw [recoveryLegalTermCircuitFamily_circuitContext hle, hmode]
    rfl
  have hcertificates :=
    legalSumAccept_termCode_certificates hcoefficient hcircuit
  have hall :
      ∀ code ∈
          balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff),
        ∃ term :
            LegalCircuitTerm NormalizedSymmetricThresholdCircuit
              (recoveryLegalTermCircuitArity
                (recoveryLegalTermCircuitContext handoff)),
          term.code symmetricCircuitCodec = code := by
    intro code hcode
    obtain ⟨hcoefficientCode, hcircuitCode⟩ := hcertificates code hcode
    obtain ⟨term, hterm, _⟩ :=
      exists_symmetricLegalCircuitTerm_of_termCode hfamily hcoefficientCode
        hcircuitCode
    exact ⟨term, hterm⟩
  rw [← recoveryLegalTermCircuitArity_circuitContext hle]
  obtain ⟨terms, hterms⟩ :=
    exists_legalCircuitTerms_of_codes symmetricCircuitCodec
      (recoveryLegalTermCircuitArity (recoveryLegalTermCircuitContext handoff))
      hall
  refine ⟨terms, hterms, ?_, ?_, ?_⟩
  · intro term hterm
    have hcode :
        term.code symmetricCircuitCodec ∈
          balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff) := by
      rw [← hterms]
      exact List.mem_map.2 ⟨term, hterm, rfl⟩
    obtain ⟨hmagnitude, hdenominator⟩ :=
      legalSumAccept_coefficientBits_le hcoefficient hbitCap hcode
    rw [recoveryLegalTermValidatedMagnitude_termCode symmetricCircuitCodec term]
      at hmagnitude
    rw [recoveryLegalTermValidatedDenominator_termCode symmetricCircuitCodec term]
      at hdenominator
    exact ⟨hmagnitude, hdenominator⟩
  · intro term hterm
    have hcode :
        term.code symmetricCircuitCodec ∈
          balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff) := by
      rw [← hterms]
      exact List.mem_map.2 ⟨term, hterm, rfl⟩
    obtain ⟨_, hvalid⟩ := hcertificates (term.code symmetricCircuitCodec) hcode
    have hbound :=
      legalSumAccept_wireMetric_le hcoefficient hcircuit hwire hcode
    rwa [recoveryLegalTermCircuitCallOutput_wireCount_symmetric_term hfamily
      hvalid] at hbound
  · intro term hterm
    have hcode :
        term.code symmetricCircuitCodec ∈
          balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff) := by
      rw [← hterms]
      exact List.mem_map.2 ⟨term, hterm, rfl⟩
    obtain ⟨_, hvalid⟩ := hcertificates (term.code symmetricCircuitCodec) hcode
    have hbound :=
      legalSumAccept_descriptionMetric_le hcoefficient hcircuit hdescription
        hcode
    rwa [recoveryLegalTermCircuitCallOutput_descriptionBits_symmetric_term hfamily
      hvalid] at hbound

/-- Threshold branch: the accepted code list is the exact serialization of a
typed term list that already satisfies every per-term resource field of
`CheckedLegalCircuitSum` except the exact coefficient mass. -/
theorem exists_thresholdLegalCircuitTerms_bounded_of_legalSumAccept
    {inputLength handoff q : ℕ}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hbitCap :
      recoveryLegalTermCoefficientBitCapListOutput
        (handoffSelectedCoefficientBitCap handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hwire :
      recoveryLegalTermWireListOutput
        (recoveryLegalTermWireCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0)
    (hdescription :
      recoveryLegalTermDescriptionListOutput
        (recoveryLegalTermDescriptionCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0)
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff)
    (hmode : handoffMode handoff = 2)
    (harity : handoffSelectedExpectedArity handoff = q) :
    ∃ terms : List (LegalCircuitTerm NormalizedThresholdThresholdCircuit q),
      terms.map (·.code thresholdCircuitCodec) =
          balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff) ∧
        (∀ term ∈ terms,
          natBitLength term.coefficient.num.natAbs ≤
              handoffSelectedCoefficientBitCap handoff ∧
            natBitLength term.coefficient.den ≤
              handoffSelectedCoefficientBitCap handoff) ∧
        (∀ term ∈ terms,
          NormalizedThresholdThresholdCircuit.wireCount term.circuit ≤
            handoffSelectedWireCap handoff) ∧
        (∀ term ∈ terms,
          NormalizedThresholdThresholdCircuit.descriptionBits term.circuit ≤
            handoffSelectedDescriptionCap handoff) := by
  subst harity
  have hfamily :
      recoveryLegalTermCircuitFamily
        (recoveryLegalTermCircuitContext handoff) = 1 := by
    rw [recoveryLegalTermCircuitFamily_circuitContext hle, hmode]
    rfl
  have hcertificates :=
    legalSumAccept_termCode_certificates hcoefficient hcircuit
  have hall :
      ∀ code ∈
          balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff),
        ∃ term :
            LegalCircuitTerm NormalizedThresholdThresholdCircuit
              (recoveryLegalTermCircuitArity
                (recoveryLegalTermCircuitContext handoff)),
          term.code thresholdCircuitCodec = code := by
    intro code hcode
    obtain ⟨hcoefficientCode, hcircuitCode⟩ := hcertificates code hcode
    obtain ⟨term, hterm, _⟩ :=
      exists_thresholdLegalCircuitTerm_of_termCode hfamily hcoefficientCode
        hcircuitCode
    exact ⟨term, hterm⟩
  rw [← recoveryLegalTermCircuitArity_circuitContext hle]
  obtain ⟨terms, hterms⟩ :=
    exists_legalCircuitTerms_of_codes thresholdCircuitCodec
      (recoveryLegalTermCircuitArity (recoveryLegalTermCircuitContext handoff))
      hall
  refine ⟨terms, hterms, ?_, ?_, ?_⟩
  · intro term hterm
    have hcode :
        term.code thresholdCircuitCodec ∈
          balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff) := by
      rw [← hterms]
      exact List.mem_map.2 ⟨term, hterm, rfl⟩
    obtain ⟨hmagnitude, hdenominator⟩ :=
      legalSumAccept_coefficientBits_le hcoefficient hbitCap hcode
    rw [recoveryLegalTermValidatedMagnitude_termCode thresholdCircuitCodec term]
      at hmagnitude
    rw [recoveryLegalTermValidatedDenominator_termCode thresholdCircuitCodec term]
      at hdenominator
    exact ⟨hmagnitude, hdenominator⟩
  · intro term hterm
    have hcode :
        term.code thresholdCircuitCodec ∈
          balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff) := by
      rw [← hterms]
      exact List.mem_map.2 ⟨term, hterm, rfl⟩
    obtain ⟨_, hvalid⟩ := hcertificates (term.code thresholdCircuitCodec) hcode
    have hbound :=
      legalSumAccept_wireMetric_le hcoefficient hcircuit hwire hcode
    rwa [recoveryLegalTermCircuitCallOutput_wireCount_threshold_term hfamily
      hvalid] at hbound
  · intro term hterm
    have hcode :
        term.code thresholdCircuitCodec ∈
          balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff) := by
      rw [← hterms]
      exact List.mem_map.2 ⟨term, hterm, rfl⟩
    obtain ⟨_, hvalid⟩ := hcertificates (term.code thresholdCircuitCodec) hcode
    have hbound :=
      legalSumAccept_descriptionMetric_le hcoefficient hcircuit hdescription
        hcode
    rwa [recoveryLegalTermCircuitCallOutput_descriptionBits_threshold_term hfamily
      hvalid] at hbound

/-! ### The mass pass reads the coefficient pass's own summaries

`recoveryLegalTermCoefficientMass_eq_legalCircuitSum` is stated against the
named correspondence premise `recoveryLegalTermMassSummariesRepresent`.  The
lemmas below discharge that premise from the executable acceptance facts: the
mass pass maps over exactly the coefficient pass's mapped payload, and the
rational summary it projects from one accepted term code is precisely the
canonical summary of that term's typed coefficient. -/

theorem recoveryLegalTermMassMappedCode_eq
    (inputLength handoff : ℕ) :
    recoveryLegalTermMassMappedCode
        (recoveryLegalTermBitCapStageOutput
          (recoveryLegalTermCircuitStageOutput inputLength handoff)) =
      recoveryLegalTermCoefficientMappedCode inputLength handoff := by
  simp [recoveryLegalTermMassMappedCode,
    recoveryLegalTermMassLoweringContext,
    recoveryLegalTermBitCapStageOutput,
    recoveryLegalTermBitCapLoweringContext,
    recoveryLegalTermBitCapMappedCode,
    recoveryLegalTermBitCapCoefficientStage,
    recoveryLegalTermCircuitStageOutput,
    recoveryLegalTermCoefficientStageOutput,
    recoveryLegalTermCoefficientMappedCode]

private theorem balancedValidationAllOutput_ne_zero_of_massSummaryFlag
    {inputLength handoff : ℕ}
    (hsummaryFlag :
      recoveryLegalTermMassSummaryFlag inputLength
        (recoveryLegalTermBitCapStageOutput
          (recoveryLegalTermCircuitStageOutput inputLength handoff)) ≠ 0) :
    balancedValidationAllOutput inputLength
        (recoveryLegalTermCoefficientMappedCode inputLength handoff)
        recoveryLegalTermRationalSummaryProjectionOutput ≠ 0 := by
  intro hzero
  apply hsummaryFlag
  rw [recoveryLegalTermMassSummaryFlag, recoveryLegalTermMassSummaryOutput,
    recoveryLegalTermMassSummaryStageOutput, Nat.unpair_pair,
    recoveryLegalTermRationalSummaryListOutput,
    recoveryLegalTermMassMappedCode_eq, balancedValidationSummaryOutput,
    if_pos hzero]
  simp

theorem recoveryLegalTermMassSummaries_eq_map
    {inputLength handoff : ℕ}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hsummaryFlag :
      recoveryLegalTermMassSummaryFlag inputLength
        (recoveryLegalTermBitCapStageOutput
          (recoveryLegalTermCircuitStageOutput inputLength handoff)) ≠ 0) :
    recoveryLegalTermMassSummaries inputLength
        (recoveryLegalTermBitCapStageOutput
          (recoveryLegalTermCircuitStageOutput inputLength handoff)) =
      (balancedValidationMapCodes
          (recoveryLegalTermCoefficientTermsCode handoff)).map
        (fun code =>
          recoveryLegalTermValidatedRationalSummary
            (legalTermCoefficientValidationOutput code)) := by
  have hall :=
    balancedValidationAllOutput_ne_zero_of_massSummaryFlag hsummaryFlag
  rw [recoveryLegalTermMassSummaries, recoveryLegalTermMassMappedCode_eq,
    if_neg hall, balancedValidationMapOutputs, balancedValidationMapRequests,
    recoveryLegalTermCoefficientMappedCode_eq inputLength handoff hcoefficient,
    balancedValidationMapCodes_encode, List.map_map, List.map_map]
  refine List.map_congr_left ?_
  intro code _
  simp [Function.comp_def, recoveryLegalTermRationalSummaryProjectionOutput,
    nativeInputRequest]

theorem recoveryLegalTermValidatedRationalSummary_termCode
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily} {n : ℕ}
    (codec : CanonicalCircuitCodec Circuit)
    (term : LegalCircuitTerm Circuit n) :
    recoveryLegalTermValidatedRationalSummary
        (legalTermCoefficientValidationOutput (term.code codec)) =
      canonicalRationalSummary term.coefficient := by
  rw [legalTermCoefficientValidationOutput_code codec term]
  simp [recoveryLegalTermValidatedRationalSummary, canonicalRationalSummary]

/-- The typed correspondence premise of the exact mass bridge is discharged by
the executable acceptance facts: no separate assumption relates the folded
summaries to the typed coefficients. -/
theorem recoveryLegalTermMassSummariesRepresent_of_termCodes
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily}
    (codec : CanonicalCircuitCodec Circuit)
    {inputLength handoff : ℕ}
    {description : LegalCircuitSumDescription Circuit}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hsummaryFlag :
      recoveryLegalTermMassSummaryFlag inputLength
        (recoveryLegalTermBitCapStageOutput
          (recoveryLegalTermCircuitStageOutput inputLength handoff)) ≠ 0)
    (hcodes :
      description.terms.map (·.code codec) =
        balancedValidationMapCodes
          (recoveryLegalTermCoefficientTermsCode handoff)) :
    recoveryLegalTermMassSummariesRepresent inputLength handoff
      description := by
  change
    recoveryLegalTermMassSummaries inputLength
        (recoveryLegalTermBitCapStageOutput
          (recoveryLegalTermCircuitStageOutput inputLength handoff)) =
      description.terms.map fun term =>
        canonicalRationalSummary term.coefficient
  rw [recoveryLegalTermMassSummaries_eq_map hcoefficient hsummaryFlag,
    ← hcodes, List.map_map]
  refine List.map_congr_left ?_
  intro term _
  exact recoveryLegalTermValidatedRationalSummary_termCode codec term

/-! ### The cross-multiplied mass gate is the exact rational comparison

The executable gate compares integer cross-products of the folded accumulator
with the validated cap summary.  With a canonical, nonnegative cap and a
nonzero accumulator denominator that is exactly the rational inequality
`coefficientMass ≤ coefficientMassCap` of `CheckedLegalCircuitSum`. -/

theorem recoveryLegalTermMassCapSummary_eq
    (inputLength bitCapStage : ℕ) :
    recoveryLegalTermMassCapSummary inputLength bitCapStage =
      rationalValidationOutput
        (recoveryLegalTermMassStageCapCode bitCapStage) := by
  simp [recoveryLegalTermMassCapSummary,
    recoveryLegalTermMassCapStageOutput,
    recoveryLegalTermMassCapLoweringOutput,
    recoveryLegalTermMassFoldStageOutput,
    recoveryLegalTermMassFoldContext,
    recoveryLegalTermMassSummaryStageOutput]

theorem recoveryLegalTermBitCapStoredHandoff_eq
    {inputLength handoff : ℕ}
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff) :
    recoveryLegalTermBitCapStoredHandoff
        (recoveryLegalTermCircuitStageOutput inputLength handoff) =
      handoff := by
  rw [recoveryLegalTermBitCapStoredHandoff,
    recoveryLegalTermBitCapCoefficientStage,
    recoveryLegalTermCircuitStageOutput,
    recoveryLegalTermCoefficientStageOutput,
    recoveryLegalSumBoundOutput, recoveryBoundedContextOutput, if_pos hle]
  simp [recoveryLegalSumLengthContext, recoveryLegalSumArityStageOutput,
    recoveryLegalSumArityContext, recoveryLegalSumContext]

theorem recoveryLegalTermMassStageCapCode_eq
    {inputLength handoff : ℕ}
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff) :
    recoveryLegalTermMassStageCapCode
        (recoveryLegalTermBitCapStageOutput
          (recoveryLegalTermCircuitStageOutput inputLength handoff)) =
      handoffSelectedCoefficientMassCapCode handoff := by
  rw [recoveryLegalTermMassStageCapCode, recoveryLegalTermMassCapContext,
    recoveryLegalTermMassLoweringContext, recoveryLegalTermBitCapStageOutput,
    Nat.unpair_pair, recoveryLegalTermBitCapLoweringContext, Nat.unpair_pair]
  simp only [Nat.unpair_pair, recoveryLegalTermMassCapCode]
  rw [recoveryLegalTermBitCapStoredHandoff_eq hle]

private theorem rationalSummarySign_canonicalRationalSummary (value : ℚ) :
    rationalSummarySign (canonicalRationalSummary value) =
      if value.num < 0 then 1 else 0 := by
  rw [canonicalRationalSummary_eq]
  simp [rationalSummarySign]

/-- The exact mass gate implies the typed rational mass bound. -/
theorem recoveryLegalTermCoefficientMass_le_of_withinCap
    {inputLength handoff : ℕ} {policy : LegalSumLimits}
    (hmass : recoveryLegalTermCoefficientMassWithinCap inputLength handoff)
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff)
    (hcap :
      handoffSelectedCoefficientMassCapCode handoff =
        encodeCanonicalRational policy.coefficientMassCap) :
    recoveryLegalTermCoefficientMass inputLength handoff ≤
      policy.coefficientMassCap := by
  obtain ⟨hcross, _, hsign, hdenominator, _⟩ := hmass
  have hcapSummary :
      recoveryLegalTermMassCapSummary inputLength
          (recoveryLegalTermBitCapStageOutput
            (recoveryLegalTermCircuitStageOutput inputLength handoff)) =
        canonicalRationalSummary policy.coefficientMassCap := by
    rw [recoveryLegalTermMassCapSummary_eq,
      recoveryLegalTermMassStageCapCode_eq hle, hcap]
    rfl
  rw [hcapSummary, rationalSummaryDenominator_canonical,
    rationalSummaryMagnitude_canonical] at hcross
  rw [hcapSummary, rationalSummarySign_canonicalRationalSummary] at hsign
  have hnonneg : 0 ≤ policy.coefficientMassCap.num := by
    by_contra hnegative
    rw [if_pos (by omega : policy.coefficientMassCap.num < 0)] at hsign
    exact absurd hsign (by omega)
  have hfoldPositive :
      (0 : ℤ) <
        ((Nat.unpair
          (recoveryLegalTermMassFoldValue inputLength
            (recoveryLegalTermBitCapStageOutput
              (recoveryLegalTermCircuitStageOutput inputLength
                handoff)))).2 : ℤ) := by
    have hpositive := Nat.pos_of_ne_zero hdenominator
    exact_mod_cast hpositive
  have hcapPositive :
      (0 : ℤ) < (policy.coefficientMassCap.den : ℤ) := by
    have hpositive :=
      Nat.pos_of_ne_zero policy.coefficientMassCap.den_nz
    exact_mod_cast hpositive
  rw [recoveryLegalTermCoefficientMass, rationalMassValue,
    ← Rat.num_divInt_den policy.coefficientMassCap,
    Rat.divInt_le_divInt hfoldPositive hcapPositive,
    ← Int.natAbs_of_nonneg hnonneg]
  exact_mod_cast hcross

/-! ### The accepting legal-sum stage builds the typed checked sum

Every proof field of `CheckedLegalCircuitSum` is now discharged: arity and term
count from the structural gates, coefficient widths from the bit-cap gate, the
exact rational mass from the cross-multiplied mass gate, and the two physical
resource bounds from the wire and description gates. -/

/-- Symmetric branch: the accepting legal-sum stage produces the typed checked sum
`decodeLegalCircuitSum` would return, with every resource proof field
discharged from the executable conjuncts. -/
theorem exists_symmetricCheckedLegalCircuitSum_of_legalSumAccept
    {inputLength handoff : ℕ} {policy : LegalSumLimits}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hbitCap :
      recoveryLegalTermCoefficientBitCapListOutput
        (handoffSelectedCoefficientBitCap handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hmass : recoveryLegalTermCoefficientMassWithinCap inputLength handoff)
    (hwire :
      recoveryLegalTermWireListOutput
        (recoveryLegalTermWireCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0)
    (hdescription :
      recoveryLegalTermDescriptionListOutput
        (recoveryLegalTermDescriptionCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0)
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff)
    (hmode : handoffMode handoff = 1)
    (hlimits :
      handoffSelectedLegalLimits handoff = encodeLegalSumLimits policy) :
    ∃ sum :
        CheckedLegalCircuitSum NormalizedSymmetricThresholdCircuit
          NormalizedSymmetricThresholdCircuit.wireCount
          NormalizedSymmetricThresholdCircuit.descriptionBits policy,
      sum.value.q = policy.expectedArity ∧
        sum.value.terms.map (·.code symmetricCircuitCodec) =
          balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff) := by
  have harity : handoffSelectedExpectedArity handoff = policy.expectedArity :=
    handoffSelectedExpectedArity_of_encode hlimits
  obtain ⟨terms, hterms, hbits, hwires, hdescriptions⟩ :=
    exists_symmetricLegalCircuitTerms_bounded_of_legalSumAccept hcoefficient
      hcircuit hbitCap hwire hdescription hle hmode harity
  obtain ⟨_, _, _, _, hsummaryFlag⟩ := id hmass
  have hcount : terms.length = recoveryLegalSumTermCount handoff := by
    rw [recoveryLegalSumTermCount, recoveryLegalSumTermCodes,
      ← recoveryLegalTermCoefficientTermsCode_eq hle, ← hterms,
      List.length_map]
  have hlength : terms.length ≤ policy.termCap := by
    rw [hcount, ← handoffSelectedTermCap_of_encode hlimits]
    exact hle
  have hrepresent :
      recoveryLegalTermMassSummariesRepresent inputLength handoff
        ⟨policy.expectedArity, terms⟩ :=
    recoveryLegalTermMassSummariesRepresent_of_termCodes symmetricCircuitCodec
      hcoefficient hsummaryFlag hterms
  have hmassValue :
      recoveryLegalTermCoefficientMass inputLength handoff =
        LegalCircuitSumDescription.coefficientMass
          ⟨policy.expectedArity, terms⟩ :=
    recoveryLegalTermCoefficientMass_eq_legalCircuitSum inputLength handoff
      ⟨policy.expectedArity, terms⟩ hrepresent
  have hmassLe :
      LegalCircuitSumDescription.coefficientMass
          (⟨policy.expectedArity, terms⟩ :
            LegalCircuitSumDescription NormalizedSymmetricThresholdCircuit) ≤
        policy.coefficientMassCap := by
    rw [← hmassValue]
    exact recoveryLegalTermCoefficientMass_le_of_withinCap hmass hle
      (handoffSelectedCoefficientMassCapCode_of_encode hlimits)
  refine
    ⟨{ value := ⟨policy.expectedArity, terms⟩
       arity_eq := rfl
       terms_le := hlength
       coefficient_bits_le := ?_
       mass_le := hmassLe
       wires_le := ?_
       description_le := ?_ }, rfl, hterms⟩
  · intro term hterm
    obtain ⟨hmagnitude, hdenominator⟩ := hbits term hterm
    rw [handoffSelectedCoefficientBitCap_of_encode hlimits] at hmagnitude
    rw [handoffSelectedCoefficientBitCap_of_encode hlimits] at hdenominator
    exact ⟨hmagnitude, hdenominator⟩
  · intro term hterm
    have hbound := hwires term hterm
    rwa [handoffSelectedWireCap_of_encode hlimits] at hbound
  · intro term hterm
    have hbound := hdescriptions term hterm
    rwa [handoffSelectedDescriptionCap_of_encode hlimits] at hbound

/-- Threshold branch: the accepting legal-sum stage produces the typed checked sum
`decodeLegalCircuitSum` would return, with every resource proof field
discharged from the executable conjuncts. -/
theorem exists_thresholdCheckedLegalCircuitSum_of_legalSumAccept
    {inputLength handoff : ℕ} {policy : LegalSumLimits}
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hbitCap :
      recoveryLegalTermCoefficientBitCapListOutput
        (handoffSelectedCoefficientBitCap handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0)
    (hmass : recoveryLegalTermCoefficientMassWithinCap inputLength handoff)
    (hwire :
      recoveryLegalTermWireListOutput
        (recoveryLegalTermWireCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0)
    (hdescription :
      recoveryLegalTermDescriptionListOutput
        (recoveryLegalTermDescriptionCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0)
    (hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff)
    (hmode : handoffMode handoff = 2)
    (hlimits :
      handoffSelectedLegalLimits handoff = encodeLegalSumLimits policy) :
    ∃ sum :
        CheckedLegalCircuitSum NormalizedThresholdThresholdCircuit
          NormalizedThresholdThresholdCircuit.wireCount
          NormalizedThresholdThresholdCircuit.descriptionBits policy,
      sum.value.q = policy.expectedArity ∧
        sum.value.terms.map (·.code thresholdCircuitCodec) =
          balancedValidationMapCodes
            (recoveryLegalTermCoefficientTermsCode handoff) := by
  have harity : handoffSelectedExpectedArity handoff = policy.expectedArity :=
    handoffSelectedExpectedArity_of_encode hlimits
  obtain ⟨terms, hterms, hbits, hwires, hdescriptions⟩ :=
    exists_thresholdLegalCircuitTerms_bounded_of_legalSumAccept hcoefficient
      hcircuit hbitCap hwire hdescription hle hmode harity
  obtain ⟨_, _, _, _, hsummaryFlag⟩ := id hmass
  have hcount : terms.length = recoveryLegalSumTermCount handoff := by
    rw [recoveryLegalSumTermCount, recoveryLegalSumTermCodes,
      ← recoveryLegalTermCoefficientTermsCode_eq hle, ← hterms,
      List.length_map]
  have hlength : terms.length ≤ policy.termCap := by
    rw [hcount, ← handoffSelectedTermCap_of_encode hlimits]
    exact hle
  have hrepresent :
      recoveryLegalTermMassSummariesRepresent inputLength handoff
        ⟨policy.expectedArity, terms⟩ :=
    recoveryLegalTermMassSummariesRepresent_of_termCodes thresholdCircuitCodec
      hcoefficient hsummaryFlag hterms
  have hmassValue :
      recoveryLegalTermCoefficientMass inputLength handoff =
        LegalCircuitSumDescription.coefficientMass
          ⟨policy.expectedArity, terms⟩ :=
    recoveryLegalTermCoefficientMass_eq_legalCircuitSum inputLength handoff
      ⟨policy.expectedArity, terms⟩ hrepresent
  have hmassLe :
      LegalCircuitSumDescription.coefficientMass
          (⟨policy.expectedArity, terms⟩ :
            LegalCircuitSumDescription NormalizedThresholdThresholdCircuit) ≤
        policy.coefficientMassCap := by
    rw [← hmassValue]
    exact recoveryLegalTermCoefficientMass_le_of_withinCap hmass hle
      (handoffSelectedCoefficientMassCapCode_of_encode hlimits)
  refine
    ⟨{ value := ⟨policy.expectedArity, terms⟩
       arity_eq := rfl
       terms_le := hlength
       coefficient_bits_le := ?_
       mass_le := hmassLe
       wires_le := ?_
       description_le := ?_ }, rfl, hterms⟩
  · intro term hterm
    obtain ⟨hmagnitude, hdenominator⟩ := hbits term hterm
    rw [handoffSelectedCoefficientBitCap_of_encode hlimits] at hmagnitude
    rw [handoffSelectedCoefficientBitCap_of_encode hlimits] at hdenominator
    exact ⟨hmagnitude, hdenominator⟩
  · intro term hterm
    have hbound := hwires term hterm
    rwa [handoffSelectedWireCap_of_encode hlimits] at hbound
  · intro term hterm
    have hbound := hdescriptions term hterm
    rwa [handoffSelectedDescriptionCap_of_encode hlimits] at hbound

/-! ## Soundness half of the decode equivalence

Assembling the outer-field bundle, the legal-sum field bundle and the typed
checked sum discharges every field of `decodeRecoveryWitness`: an accepting
staged validator run certifies a genuine typed recovery witness for the very
code it was handed.  No conjunct of the executable acceptance criterion is
unused, and no additional canonicality check is required. -/

theorem exists_decodeRecoveryWitness_of_legalSumAccept
    {inputLength : ℕ} {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0) :
    ∃ witness : CheckedRecoveryWitness limits,
      decodeRecoveryWitness limits raw = some witness := by
  have horacle :=
    recoveryValidatorOraclePrefixOutput_ne_zero_of_legalSum haccepts
  obtain ⟨modeCode, oracleCode, oracle, hfields, horacleDecode, hsize,
    hbranch⟩ :=
    recoveryValidatorOraclePrefix_canonicalOuterFields horacle
  obtain ⟨hsumFields, hqDecode, hcodes⟩ :=
    recoveryValidatorLegalSumPrefix_canonicalSumFields haccepts
  obtain ⟨hcircuit, hbitCap, hmass, hcoefficient, hle, _, _, _, _, _, hwire,
    hdescription⟩ :=
    (recoveryValidatorLegalSumPrefixOutput_ne_zero_iff inputLength limits
      raw).1 haccepts
  have hlimits := handoffSelectedLegalLimits_oraclePrefixOutput horacle
  rcases hbranch with ⟨hmodeCode, hmode, hpolicy⟩ | ⟨hmodeCode, hmode, hpolicy⟩
  · rw [hpolicy] at hlimits hqDecode
    obtain ⟨sum, hq, htermCodes⟩ :=
      exists_symmetricCheckedLegalCircuitSum_of_legalSumAccept hcoefficient
        hcircuit hbitCap hmass hwire hdescription hle hmode hlimits
    have hdecodeSum :=
      decodeLegalCircuitSum_of_canonical_fields symmetricCircuitCodec
        NormalizedSymmetricThresholdCircuit.wireCount
        NormalizedSymmetricThresholdCircuit.descriptionBits limits.symmetric
        sum hsumFields (by rw [hq]; exact hqDecode)
        (by rw [htermCodes]; exact hcodes)
    exact
      ⟨.symmetric oracle hsize sum,
        decodeRecoveryWitness_symmetric_of_canonical_fields hsize hfields
          hmodeCode horacleDecode
          (CheckedLegalCircuitSum.code_of_decode hdecodeSum)⟩
  · rw [hpolicy] at hlimits hqDecode
    obtain ⟨sum, hq, htermCodes⟩ :=
      exists_thresholdCheckedLegalCircuitSum_of_legalSumAccept hcoefficient
        hcircuit hbitCap hmass hwire hdescription hle hmode hlimits
    have hdecodeSum :=
      decodeLegalCircuitSum_of_canonical_fields thresholdCircuitCodec
        NormalizedThresholdThresholdCircuit.wireCount
        NormalizedThresholdThresholdCircuit.descriptionBits limits.threshold
        sum hsumFields (by rw [hq]; exact hqDecode)
        (by rw [htermCodes]; exact hcodes)
    exact
      ⟨.threshold oracle hsize sum,
        decodeRecoveryWitness_threshold_of_canonical_fields hsize hfields
          hmodeCode horacleDecode
          (CheckedLegalCircuitSum.code_of_decode hdecodeSum)⟩

/-- Soundness of the complete executable endpoint against the pure validator:
an accepting run identifies the pure output exactly. -/
theorem recoveryWitnessValidatorProgramOutput_eq_of_accept
    {inputLength : ℕ} {limits : RecoveryWitnessLimits} {raw : ℕ}
    (haccepts :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw =
      recoveryWitnessValidatorOutput limits raw := by
  obtain ⟨witness, hdecode⟩ :=
    exists_decodeRecoveryWitness_of_legalSumAccept haccepts
  have horacle :=
    recoveryValidatorOraclePrefixOutput_ne_zero_of_legalSum haccepts
  obtain ⟨modeCode, oracleCode, _, hfields, _, _, hbranch⟩ :=
    recoveryValidatorOraclePrefix_canonicalOuterFields horacle
  rw [recoveryWitnessValidatorProgramOutput_eq_pair haccepts,
    recoveryWitnessValidatorOutput_of_decode hdecode]
  have hmodeTag :
      handoffMode (recoveryValidatorOraclePrefixOutput limits raw) =
        checkedRecoveryWitnessModeTag witness := by
    rcases hbranch with ⟨hmodeCode, hmode, _⟩ | ⟨hmodeCode, hmode, _⟩
    · rw [hmode]
      cases witness with
      | symmetric _ _ _ => rfl
      | threshold oracle horacleSize sum =>
          exfalso
          have hcode :
              (CheckedRecoveryWitness.threshold oracle horacleSize sum).code =
                raw :=
            CheckedRecoveryWitness.code_of_decode hdecode
          have hthreshold :
              decodeTaggedList raw =
                some
                  [encodeNat 1, encodeBooleanCircuit oracle,
                    sum.code thresholdCircuitCodec] := by
            rw [← hcode]
            exact decodeTaggedList_encode _
          rw [hthreshold] at hfields
          obtain ⟨hmodeEq, _⟩ := List.cons.inj (Option.some.inj hfields)
          rw [← hmodeEq, decodeNat_encode] at hmodeCode
          exact absurd hmodeCode (by simp)
    · rw [hmode]
      cases witness with
      | threshold _ _ _ => rfl
      | symmetric oracle horacleSize sum =>
          exfalso
          have hcode :
              (CheckedRecoveryWitness.symmetric oracle horacleSize sum).code =
                raw :=
            CheckedRecoveryWitness.code_of_decode hdecode
          have hsymmetric :
              decodeTaggedList raw =
                some
                  [encodeNat 0, encodeBooleanCircuit oracle,
                    sum.code symmetricCircuitCodec] := by
            rw [← hcode]
            exact decodeTaggedList_encode _
          rw [hsymmetric] at hfields
          obtain ⟨hmodeEq, _⟩ := List.cons.inj (Option.some.inj hfields)
          rw [← hmodeEq, decodeNat_encode] at hmodeCode
          exact absurd hmodeCode (by simp)
  rw [hmodeTag]

/-! ## Completeness of the structural and Boolean-DAG prefix

The converse of the soundness statement above starts here: a code the pure
decoder accepts already satisfies the exact acceptance criterion of the staged
structural and Boolean-DAG prefix, and the executable mode tag it produces is
the typed witness's own mode tag. -/

private theorem legalCircuitSum_code_ne_zero
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily}
    {wires description : {n : ℕ} → Circuit n → ℕ}
    {policy : LegalSumLimits}
    (codec : CanonicalCircuitCodec Circuit)
    (checked : CheckedLegalCircuitSum Circuit wires description policy) :
    checked.code codec ≠ 0 := by
  have hshape :
      checked.code codec =
        Nat.pair 1
          (Nat.pair (encodeNat checked.value.q)
            (encodeTaggedList
              [encodeBalancedList
                (checked.value.terms.map (·.code codec))])) := rfl
  have hpositive :=
    Nat.left_le_pair 1
      (Nat.pair (encodeNat checked.value.q)
        (encodeTaggedList
          [encodeBalancedList
            (checked.value.terms.map (·.code codec))]))
  rw [hshape]
  omega

/-- A code the pure decoder accepts passes the whole staged prefix. -/
theorem recoveryValidatorOraclePrefixOutput_ne_zero_of_decode
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    {witness : CheckedRecoveryWitness limits}
    (hdecode : decodeRecoveryWitness limits raw = some witness) :
    recoveryValidatorOraclePrefixOutput limits raw ≠ 0 := by
  have hcode : witness.code = raw :=
    CheckedRecoveryWitness.code_of_decode hdecode
  refine (recoveryValidatorOraclePrefixOutput_ne_zero_iff limits raw).2 ?_
  cases witness with
  | symmetric oracle horacle sum =>
      refine
        ⟨encodeNat 0, encodeBooleanCircuit oracle,
          sum.code symmetricCircuitCodec, ?_, Or.inl (decodeNat_encode 0), ?_,
          oracle, decodeBooleanCircuit_encode oracle, horacle⟩
      · rw [← hcode]
        exact decodeTaggedList_encode _
      · exact legalCircuitSum_code_ne_zero symmetricCircuitCodec sum
  | threshold oracle horacle sum =>
      refine
        ⟨encodeNat 1, encodeBooleanCircuit oracle,
          sum.code thresholdCircuitCodec, ?_, Or.inr (decodeNat_encode 1), ?_,
          oracle, decodeBooleanCircuit_encode oracle, horacle⟩
      · rw [← hcode]
        exact decodeTaggedList_encode _
      · exact legalCircuitSum_code_ne_zero thresholdCircuitCodec sum

/-- On that path the executable mode tag is the typed witness's mode tag. -/
theorem handoffMode_oraclePrefixOutput_of_decode
    {limits : RecoveryWitnessLimits} {raw : ℕ}
    {witness : CheckedRecoveryWitness limits}
    (hdecode : decodeRecoveryWitness limits raw = some witness) :
    handoffMode (recoveryValidatorOraclePrefixOutput limits raw) =
      checkedRecoveryWitnessModeTag witness := by
  have haccepts := recoveryValidatorOraclePrefixOutput_ne_zero_of_decode hdecode
  have hcode : witness.code = raw :=
    CheckedRecoveryWitness.code_of_decode hdecode
  rw [handoffMode_oraclePrefixOutput haccepts]
  cases witness with
  | symmetric oracle horacle sum =>
      have henvelope :
          decodeRecoveryEnvelope raw =
            some
              ⟨.symmetric, encodeBooleanCircuit oracle,
                sum.code symmetricCircuitCodec⟩ := by
        refine decodeRecoveryEnvelope_of_modeCode_zero ?_ (decodeNat_encode 0)
        rw [← hcode]
        exact decodeTaggedList_encode _
      rw [recoveryEnvelopeOutput, henvelope]
      simp [RecoveryEnvelope.outputTag, checkedRecoveryWitnessModeTag,
        CheckedRecoveryWitness.mode, recoveryWitnessModeTag]
  | threshold oracle horacle sum =>
      have henvelope :
          decodeRecoveryEnvelope raw =
            some
              ⟨.threshold, encodeBooleanCircuit oracle,
                sum.code thresholdCircuitCodec⟩ := by
        refine decodeRecoveryEnvelope_of_modeCode_one ?_ (decodeNat_encode 1)
        rw [← hcode]
        exact decodeTaggedList_encode _
      rw [recoveryEnvelopeOutput, henvelope]
      simp [RecoveryEnvelope.outputTag, checkedRecoveryWitnessModeTag,
        CheckedRecoveryWitness.mode, recoveryWitnessModeTag]

/-! ## Completeness of the staged legal-sum envelope

The converse of the soundness chain.  Decode success pins `raw = witness.code`,
so every projection the staged validator reads is a canonical encoding, and each
of the twelve conjuncts of `recoveryValidatorLegalSumPrefixOutput_ne_zero_iff`
is discharged from a proof field the typed checked witness already carries.  No
conjunct needs a hypothesis beyond `CheckedLegalCircuitSum`. -/

private theorem legalTermCoefficientValidationOutput_termCode_ne_zero
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily} {n : ℕ}
    (codec : CanonicalCircuitCodec Circuit)
    (term : LegalCircuitTerm Circuit n) :
    legalTermCoefficientValidationOutput (term.code codec) ≠ 0 := by
  rw [legalTermCoefficientValidationOutput_code codec term]
  have hleft :=
    Nat.left_le_pair 1
      (Nat.pair
        (rationalValidationOutput
          (encodeCanonicalRational term.coefficient))
        (codec.encode term.circuit))
  omega

private theorem canonicalRationalSummary_ne_zero (coefficient : ℚ) :
    canonicalRationalSummary coefficient ≠ 0 := by
  rw [canonicalRationalSummary_eq]
  have hleft :=
    Nat.left_le_pair 1
      (Nat.pair (if coefficient.num < 0 then 1 else 0)
        (Nat.pair coefficient.num.natAbs coefficient.den))
  omega

/-- Structural half of the completeness argument: the four legal-sum flags, the
term-count bound and the terms slot the per-term stages read are all fixed by
the canonical code of a typed checked sum. -/
theorem recoveryLegalSumStructuralFields_of_checkedSum
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily}
    {wires description : {n : ℕ} → Circuit n → ℕ}
    (codec : CanonicalCircuitCodec Circuit) (handoff : ℕ)
    (policy : LegalSumLimits)
    (sum : CheckedLegalCircuitSum Circuit wires description policy)
    (hsumCode : handoffSumCode handoff = sum.code codec)
    (hlimits :
      handoffSelectedLegalLimits handoff = encodeLegalSumLimits policy) :
    recoveryLegalSumTupleFlag handoff ≠ 0 ∧
      recoveryLegalSumQFlag handoff ≠ 0 ∧
      recoveryLegalSumArityFlag handoff ≠ 0 ∧
      recoveryLegalSumTermsFlag handoff ≠ 0 ∧
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff ∧
      recoveryLegalTermCoefficientTermsCode handoff =
        encodeBalancedList (sum.value.terms.map (·.code codec)) := by
  have hcodeShape :
      sum.code codec =
        encodeTaggedList
          [encodeNat sum.value.q,
            encodeBalancedList (sum.value.terms.map (·.code codec))] := rfl
  have htagged :
      decodeTaggedList (handoffSumCode handoff) =
        some
          [encodeNat sum.value.q,
            encodeBalancedList (sum.value.terms.map (·.code codec))] := by
    rw [hsumCode, hcodeShape]
    exact decodeTaggedList_encode _
  have htupleOutput :
      recoveryLegalSumTupleOutput handoff =
        Nat.pair 1
          (Nat.pair (Nat.pair 0 (encodeNat sum.value.q))
            (encodeBalancedList (sum.value.terms.map (·.code codec)))) :=
    recoveryLegalSumTupleOutput_eq_of_decode htagged
  have htupleFlag : recoveryLegalSumTupleFlag handoff ≠ 0 := by
    rw [recoveryLegalSumTupleFlag, htupleOutput]
    simp
  have hqCode : recoveryLegalSumQCode handoff = encodeNat sum.value.q := by
    rw [recoveryLegalSumQCode, recoveryLegalSumTupleFields, htupleOutput]
    simp
  have htermsCode :
      recoveryLegalSumTermsCode handoff =
        encodeBalancedList (sum.value.terms.map (·.code codec)) := by
    rw [recoveryLegalSumTermsCode, recoveryLegalSumTupleFields, htupleOutput]
    simp
  have hqValidation :
      recoveryLegalSumQValidation handoff = Nat.pair 1 sum.value.q := by
    rw [recoveryLegalSumQValidation, hqCode]
    exact canonicalNatValidationOutput_of_decode (decodeNat_encode sum.value.q)
  have hqFlag : recoveryLegalSumQFlag handoff ≠ 0 := by
    rw [recoveryLegalSumQFlag, hqValidation]
    simp
  have harityValue : recoveryLegalSumArityValue handoff = sum.value.q := by
    rw [recoveryLegalSumArityValue, hqValidation]
    simp
  have harityFlag : recoveryLegalSumArityFlag handoff ≠ 0 := by
    rw [recoveryLegalSumArityFlag]
    refine (nativeNatEqOutput_ne_zero_iff _ _).2 ?_
    rw [harityValue, handoffSelectedExpectedArity_of_encode hlimits]
    exact sum.arity_eq
  have htermsFlag : recoveryLegalSumTermsFlag handoff ≠ 0 := by
    rw [recoveryLegalSumTermsFlag, balancedValidationMapFlag, htermsCode,
      (NearCubicWires.CanonicalBalancedValidationProgram.balancedCanonicalityOutput_eq_one_iff
        (encodeBalancedList (sum.value.terms.map (·.code codec)))).2
        (by simp)]
    exact one_ne_zero
  have hcount :
      recoveryLegalSumTermCount handoff = sum.value.terms.length := by
    rw [recoveryLegalSumTermCount, recoveryLegalSumTermCodes, htermsCode,
      balancedValidationMapCodes_encode, List.length_map]
  have hle :
      recoveryLegalSumTermCount handoff ≤ handoffSelectedTermCap handoff := by
    rw [hcount, handoffSelectedTermCap_of_encode hlimits]
    exact sum.terms_le
  refine ⟨htupleFlag, hqFlag, harityFlag, htermsFlag, hle, ?_⟩
  rw [recoveryLegalTermCoefficientTermsCode_eq hle, htermsCode]

/-- Complete completeness engine: a typed checked sum whose canonical code is
the nested legal-sum payload of the staged handoff satisfies every conjunct of
the executable legal-sum envelope.  The three per-term hypotheses are the only
family-specific inputs; everything else is a proof field of the checked sum. -/
theorem recoveryLegalSumEnvelopeOutput_ne_zero_of_checkedSum
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily}
    {wires description : {n : ℕ} → Circuit n → ℕ}
    (codec : CanonicalCircuitCodec Circuit) (inputLength handoff : ℕ)
    (policy : LegalSumLimits)
    (sum : CheckedLegalCircuitSum Circuit wires description policy)
    (hsumCode : handoffSumCode handoff = sum.code codec)
    (hlimits :
      handoffSelectedLegalLimits handoff = encodeLegalSumLimits policy)
    (hmode : handoffMode handoff = 1 ∨ handoffMode handoff = 2)
    (hcircuitValid :
      ∀ term ∈ sum.value.terms,
        recoveryLegalTermCircuitCallOutput
            (recoveryLegalTermCircuitContext handoff)
            (legalTermCoefficientValidationOutput (term.code codec)) ≠ 0)
    (hwireMetric :
      ∀ term ∈ sum.value.terms,
        normalizedCircuitResourceMetric
            (recoveryLegalTermCircuitCallOutput
              (recoveryLegalTermCircuitContext handoff)
              (legalTermCoefficientValidationOutput (term.code codec))) =
          wires term.circuit)
    (hdescriptionMetric :
      ∀ term ∈ sum.value.terms,
        normalizedCircuitDescriptionMetric
            (recoveryLegalTermBoundExpectedArity handoff)
            (recoveryLegalTermCircuitCallOutput
              (recoveryLegalTermCircuitContext handoff)
              (legalTermCoefficientValidationOutput (term.code codec))) =
          description term.circuit) :
    recoveryLegalSumEnvelopeOutput inputLength handoff ≠ 0 := by
  obtain ⟨htupleFlag, hqFlag, harityFlag, htermsFlag, hle, hbridge⟩ :=
    recoveryLegalSumStructuralFields_of_checkedSum codec handoff policy sum
      hsumCode hlimits
  have hmapCodes :
      balancedValidationMapCodes
          (recoveryLegalTermCoefficientTermsCode handoff) =
        sum.value.terms.map (·.code codec) := by
    rw [hbridge, balancedValidationMapCodes_encode]
  have hmodeFlag : handoffLegalSumModeFlag handoff ≠ 0 := by
    rcases hmode with hbranch | hbranch <;>
      simp [handoffLegalSumModeFlag, hbranch]
  have hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode handoff) ≠ 0 := by
    refine (recoveryLegalTermCoefficientListOutput_ne_zero_iff inputLength
      (recoveryLegalTermCoefficientTermsCode handoff)).2
      ⟨sum.value.terms.map (·.code codec), ?_, ?_⟩
    · rw [hbridge]
      exact decodeBalancedList_encode _
    · intro code hcode
      obtain ⟨term, _, htermCode⟩ := List.mem_map.1 hcode
      rw [← htermCode]
      exact legalTermCoefficientValidationOutput_termCode_ne_zero codec term
  have hmapped :
      decodeBalancedList
          (recoveryLegalTermCoefficientMappedCode inputLength handoff) =
        some
          (sum.value.terms.map fun term =>
            legalTermCoefficientValidationOutput (term.code codec)) := by
    rw [recoveryLegalTermCoefficientMappedCode_eq inputLength handoff
        hcoefficient,
      decodeBalancedList_encode, hmapCodes]
    simp [List.map_map, Function.comp_def]
  have hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0 := by
    refine (recoveryLegalTermCircuitListOutput_ne_zero_iff
      (recoveryLegalTermCircuitContext handoff)
      (recoveryLegalTermCoefficientMappedCode inputLength handoff)).2
      ⟨_, hmapped, ?_⟩
    intro validated hvalidated
    obtain ⟨term, hterm, hvalidatedCode⟩ := List.mem_map.1 hvalidated
    rw [← hvalidatedCode]
    exact hcircuitValid term hterm
  have hbitCap :
      recoveryLegalTermCoefficientBitCapListOutput
        (handoffSelectedCoefficientBitCap handoff)
        (recoveryLegalTermCoefficientMappedCode inputLength handoff) ≠ 0 := by
    refine (recoveryLegalTermCoefficientBitCapListOutput_ne_zero_iff
      (handoffSelectedCoefficientBitCap handoff)
      (recoveryLegalTermCoefficientMappedCode inputLength handoff)).2
      ⟨_, hmapped, ?_⟩
    intro validated hvalidated
    obtain ⟨term, hterm, hvalidatedCode⟩ := List.mem_map.1 hvalidated
    obtain ⟨hmagnitude, hdenominator⟩ := sum.coefficient_bits_le term hterm
    rw [← hvalidatedCode]
    refine
      ⟨legalTermCoefficientValidationOutput_termCode_ne_zero codec term, ?_, ?_⟩
    · rw [recoveryLegalTermValidatedMagnitude_termCode codec term,
        handoffSelectedCoefficientBitCap_of_encode hlimits]
      exact hmagnitude
    · rw [recoveryLegalTermValidatedDenominator_termCode codec term,
        handoffSelectedCoefficientBitCap_of_encode hlimits]
      exact hdenominator
  have hsummaryTree :
      decodeBalancedList
          (recoveryLegalTermValidatedSummaryTree inputLength handoff) =
        some
          (sum.value.terms.map fun term =>
            recoveryLegalTermCircuitCallOutput
              (recoveryLegalTermCircuitContext handoff)
              (legalTermCoefficientValidationOutput (term.code codec))) := by
    rw [decodeBalancedList_recoveryLegalTermValidatedSummaryTree inputLength
        handoff hcoefficient hcircuit,
      hmapCodes]
    simp [List.map_map, Function.comp_def]
  have hwire :
      recoveryLegalTermWireListOutput
        (recoveryLegalTermWireCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0 := by
    refine (recoveryLegalTermWireListOutput_ne_zero_iff
      (recoveryLegalTermWireCapContext handoff)
      (recoveryLegalTermValidatedSummaryTree inputLength handoff)).2
      ⟨_, hsummaryTree, ?_⟩
    intro summary hsummary
    obtain ⟨term, hterm, hsummaryCode⟩ := List.mem_map.1 hsummary
    rw [← hsummaryCode, recoveryLegalTermResourceCap_wireCapContext,
      hwireMetric term hterm, handoffSelectedWireCap_of_encode hlimits]
    exact sum.wires_le term hterm
  have hdescription :
      recoveryLegalTermDescriptionListOutput
        (recoveryLegalTermDescriptionCapContext handoff)
        (recoveryLegalTermValidatedSummaryTree inputLength handoff) ≠ 0 := by
    refine (recoveryLegalTermDescriptionListOutput_ne_zero_iff
      (recoveryLegalTermDescriptionCapContext handoff)
      (recoveryLegalTermValidatedSummaryTree inputLength handoff)).2
      ⟨_, hsummaryTree, ?_⟩
    intro summary hsummary
    obtain ⟨term, hterm, hsummaryCode⟩ := List.mem_map.1 hsummary
    rw [← hsummaryCode, recoveryLegalTermResourceCap_descriptionCapContext,
      recoveryLegalTermResourceArity_descriptionCapContext,
      hdescriptionMetric term hterm,
      handoffSelectedDescriptionCap_of_encode hlimits]
    exact sum.description_le term hterm
  have hall :
      balancedValidationAllOutput inputLength
        (recoveryLegalTermCoefficientMappedCode inputLength handoff)
        recoveryLegalTermRationalSummaryProjectionOutput ≠ 0 := by
    refine (balancedValidationAllOutput_ne_zero_iff inputLength
      (recoveryLegalTermCoefficientMappedCode inputLength handoff)
      recoveryLegalTermRationalSummaryProjectionOutput).2 ⟨_, hmapped, ?_⟩
    intro validated hvalidated
    obtain ⟨term, _, hvalidatedCode⟩ := List.mem_map.1 hvalidated
    rw [recoveryLegalTermRationalSummaryProjectionOutput, nativeInputRequest,
      Nat.unpair_pair, ← hvalidatedCode,
      recoveryLegalTermValidatedRationalSummary_termCode codec term]
    exact canonicalRationalSummary_ne_zero term.coefficient
  have hmassSummaryFlag :
      recoveryLegalTermMassSummaryFlag inputLength
        (recoveryLegalTermBitCapStageOutput
          (recoveryLegalTermCircuitStageOutput inputLength handoff)) ≠ 0 := by
    rw [recoveryLegalTermMassSummaryFlag, recoveryLegalTermMassSummaryOutput,
      recoveryLegalTermMassSummaryStageOutput, Nat.unpair_pair,
      recoveryLegalTermRationalSummaryListOutput,
      recoveryLegalTermMassMappedCode_eq, balancedValidationSummaryOutput,
      if_neg hall]
    simp
  have hrepresent :
      recoveryLegalTermMassSummariesRepresent inputLength handoff sum.value :=
    recoveryLegalTermMassSummariesRepresent_of_termCodes codec hcoefficient
      hmassSummaryFlag hmapCodes.symm
  have hsummariesEq :
      recoveryLegalTermMassSummaries inputLength
          (recoveryLegalTermBitCapStageOutput
            (recoveryLegalTermCircuitStageOutput inputLength handoff)) =
        sum.value.terms.map fun term =>
          canonicalRationalSummary term.coefficient := hrepresent
  have hfoldEq :
      recoveryLegalTermMassFoldValue inputLength
          (recoveryLegalTermBitCapStageOutput
            (recoveryLegalTermCircuitStageOutput inputLength handoff)) =
        rationalMassFold
          (recoveryLegalTermMassSummaries inputLength
            (recoveryLegalTermBitCapStageOutput
              (recoveryLegalTermCircuitStageOutput inputLength handoff))) := by
    simp [recoveryLegalTermMassFoldValue,
      recoveryLegalTermMassCapStageOutput,
      recoveryLegalTermMassCapLoweringOutput,
      recoveryLegalTermMassCapValidationContext,
      recoveryLegalTermMassFoldStageOutput]
  have hdenominator :
      (Nat.unpair
        (recoveryLegalTermMassFoldValue inputLength
          (recoveryLegalTermBitCapStageOutput
            (recoveryLegalTermCircuitStageOutput inputLength
              handoff)))).2 ≠ 0 := by
    have hvalid :=
      rationalMassFold_canonical_valid
        (sum.value.terms.map fun term => term.coefficient)
    rw [hfoldEq, hsummariesEq,
      show
        (sum.value.terms.map fun term =>
            canonicalRationalSummary term.coefficient) =
          (sum.value.terms.map fun term => term.coefficient).map
            canonicalRationalSummary by
        simp [List.map_map, Function.comp_def]]
    exact hvalid
  have hcapSummary :
      recoveryLegalTermMassCapSummary inputLength
          (recoveryLegalTermBitCapStageOutput
            (recoveryLegalTermCircuitStageOutput inputLength handoff)) =
        canonicalRationalSummary policy.coefficientMassCap := by
    rw [recoveryLegalTermMassCapSummary_eq,
      recoveryLegalTermMassStageCapCode_eq hle,
      handoffSelectedCoefficientMassCapCode_of_encode hlimits]
    rfl
  have hmassNonneg : (0 : ℚ) ≤ sum.value.coefficientMass := by
    have hfoldNonneg :
        ∀ (terms : List (LegalCircuitTerm Circuit sum.value.q)) (initial : ℚ),
          0 ≤ initial →
            0 ≤
              terms.foldl (fun total term => total + |term.coefficient|)
                initial := by
      intro terms
      induction terms with
      | nil =>
          intro initial hinitial
          simpa using hinitial
      | cons term terms ih =>
          intro initial hinitial
          exact ih (initial + |term.coefficient|)
            (add_nonneg hinitial (abs_nonneg _))
    exact hfoldNonneg sum.value.terms 0 le_rfl
  have hcapNonneg : (0 : ℚ) ≤ policy.coefficientMassCap :=
    hmassNonneg.trans sum.mass_le
  have hcapNumNonneg : 0 ≤ policy.coefficientMassCap.num :=
    Rat.num_nonneg.mpr hcapNonneg
  have hmassValue :
      recoveryLegalTermCoefficientMass inputLength handoff =
        sum.value.coefficientMass :=
    recoveryLegalTermCoefficientMass_eq_legalCircuitSum inputLength handoff
      sum.value hrepresent
  have hmass : recoveryLegalTermCoefficientMassWithinCap inputLength handoff := by
    refine ⟨?_, ?_, ?_, hdenominator, hmassSummaryFlag⟩
    · rw [hcapSummary, rationalSummaryDenominator_canonical,
        rationalSummaryMagnitude_canonical]
      have hfoldPositive :
          (0 : ℤ) <
            ((Nat.unpair
              (recoveryLegalTermMassFoldValue inputLength
                (recoveryLegalTermBitCapStageOutput
                  (recoveryLegalTermCircuitStageOutput inputLength
                    handoff)))).2 : ℤ) := by
        have hpositive := Nat.pos_of_ne_zero hdenominator
        exact_mod_cast hpositive
      have hcapPositive : (0 : ℤ) < (policy.coefficientMassCap.den : ℤ) := by
        have hpositive := Nat.pos_of_ne_zero policy.coefficientMassCap.den_nz
        exact_mod_cast hpositive
      have hrational :
          Rat.divInt
              ((Nat.unpair
                (recoveryLegalTermMassFoldValue inputLength
                  (recoveryLegalTermBitCapStageOutput
                    (recoveryLegalTermCircuitStageOutput inputLength
                      handoff)))).1 : ℤ)
              ((Nat.unpair
                (recoveryLegalTermMassFoldValue inputLength
                  (recoveryLegalTermBitCapStageOutput
                    (recoveryLegalTermCircuitStageOutput inputLength
                      handoff)))).2 : ℤ) ≤
            Rat.divInt policy.coefficientMassCap.num
              (policy.coefficientMassCap.den : ℤ) := by
        rw [Rat.num_divInt_den]
        rw [show
          Rat.divInt
              ((Nat.unpair
                (recoveryLegalTermMassFoldValue inputLength
                  (recoveryLegalTermBitCapStageOutput
                    (recoveryLegalTermCircuitStageOutput inputLength
                      handoff)))).1 : ℤ)
              ((Nat.unpair
                (recoveryLegalTermMassFoldValue inputLength
                  (recoveryLegalTermBitCapStageOutput
                    (recoveryLegalTermCircuitStageOutput inputLength
                      handoff)))).2 : ℤ) =
            recoveryLegalTermCoefficientMass inputLength handoff from rfl,
          hmassValue]
        exact sum.mass_le
      have hcross :=
        (Rat.divInt_le_divInt hfoldPositive hcapPositive).1 hrational
      rw [← Int.natAbs_of_nonneg hcapNumNonneg] at hcross
      exact_mod_cast hcross
    · rw [hcapSummary, rationalSummaryFlag_canonical]
      exact one_ne_zero
    · rw [hcapSummary, rationalSummarySign_canonicalRationalSummary,
        if_neg (by omega : ¬ policy.coefficientMassCap.num < 0)]
  exact (recoveryLegalSumEnvelopeOutput_ne_zero_iff inputLength handoff).2
    ⟨hcircuit, hbitCap, hmass, hcoefficient, hle, htermsFlag, harityFlag,
      hqFlag, htupleFlag, hmodeFlag, hwire, hdescription⟩

/-! ### Per-term certificates of one canonically encoded typed term

The circuit pass accepts the payload the coefficient pass builds from a typed
term's own canonical code, and the two resource metrics it reports are the
typed wire count and description length of that term's circuit. -/

private theorem symmetricLegalCircuitTerm_circuitCertificates
    {context n : ℕ}
    (hfamily : recoveryLegalTermCircuitFamily context = 0)
    (harity : recoveryLegalTermCircuitArity context = n)
    (term : LegalCircuitTerm NormalizedSymmetricThresholdCircuit n) :
    recoveryLegalTermCircuitCallOutput context
          (legalTermCoefficientValidationOutput
            (term.code symmetricCircuitCodec)) ≠ 0 ∧
      normalizedCircuitResourceMetric
          (recoveryLegalTermCircuitCallOutput context
            (legalTermCoefficientValidationOutput
              (term.code symmetricCircuitCodec))) =
        NormalizedSymmetricThresholdCircuit.wireCount term.circuit ∧
      normalizedCircuitDescriptionMetric
          (recoveryLegalTermCircuitArity context)
          (recoveryLegalTermCircuitCallOutput context
            (legalTermCoefficientValidationOutput
              (term.code symmetricCircuitCodec))) =
        NormalizedSymmetricThresholdCircuit.descriptionBits term.circuit := by
  subst harity
  have hvalid :
      recoveryLegalTermCircuitCallOutput context
        (legalTermCoefficientValidationOutput
          (term.code symmetricCircuitCodec)) ≠ 0 := by
    refine (recoveryLegalTermCircuitCallOutput_ne_zero_iff context
      (legalTermCoefficientValidationOutput
        (term.code symmetricCircuitCodec))).2 (Or.inl ⟨hfamily, ?_⟩)
    rw [recoveryLegalTermValidatedCircuitCode_symmetric_term term,
      decodeNormalizedSymmetricThresholdCircuit_encode term.circuit]
    rfl
  exact
    ⟨hvalid,
      recoveryLegalTermCircuitCallOutput_wireCount_symmetric_term hfamily
        hvalid,
      recoveryLegalTermCircuitCallOutput_descriptionBits_symmetric_term hfamily
        hvalid⟩

private theorem thresholdLegalCircuitTerm_circuitCertificates
    {context n : ℕ}
    (hfamily : recoveryLegalTermCircuitFamily context = 1)
    (harity : recoveryLegalTermCircuitArity context = n)
    (term : LegalCircuitTerm NormalizedThresholdThresholdCircuit n) :
    recoveryLegalTermCircuitCallOutput context
          (legalTermCoefficientValidationOutput
            (term.code thresholdCircuitCodec)) ≠ 0 ∧
      normalizedCircuitResourceMetric
          (recoveryLegalTermCircuitCallOutput context
            (legalTermCoefficientValidationOutput
              (term.code thresholdCircuitCodec))) =
        NormalizedThresholdThresholdCircuit.wireCount term.circuit ∧
      normalizedCircuitDescriptionMetric
          (recoveryLegalTermCircuitArity context)
          (recoveryLegalTermCircuitCallOutput context
            (legalTermCoefficientValidationOutput
              (term.code thresholdCircuitCodec))) =
        NormalizedThresholdThresholdCircuit.descriptionBits term.circuit := by
  subst harity
  have hvalid :
      recoveryLegalTermCircuitCallOutput context
        (legalTermCoefficientValidationOutput
          (term.code thresholdCircuitCodec)) ≠ 0 := by
    refine (recoveryLegalTermCircuitCallOutput_ne_zero_iff context
      (legalTermCoefficientValidationOutput
        (term.code thresholdCircuitCodec))).2 (Or.inr ⟨hfamily, ?_⟩)
    rw [recoveryLegalTermValidatedCircuitCode_threshold_term term,
      decodeNormalizedThresholdThresholdCircuit_encode term.circuit]
    rfl
  exact
    ⟨hvalid,
      recoveryLegalTermCircuitCallOutput_wireCount_threshold_term hfamily
        hvalid,
      recoveryLegalTermCircuitCallOutput_descriptionBits_threshold_term hfamily
        hvalid⟩

/-- Completeness of the staged validator: every code the pure canonical decoder
accepts is accepted by the executable staged legal-sum prefix. -/
theorem recoveryValidatorLegalSumPrefixOutput_ne_zero_of_decode
    {inputLength : ℕ} {limits : RecoveryWitnessLimits} {raw : ℕ}
    {witness : CheckedRecoveryWitness limits}
    (hdecode : decodeRecoveryWitness limits raw = some witness) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0 := by
  have hcode : witness.code = raw :=
    CheckedRecoveryWitness.code_of_decode hdecode
  have horacle := recoveryValidatorOraclePrefixOutput_ne_zero_of_decode hdecode
  have hmodeTag := handoffMode_oraclePrefixOutput_of_decode hdecode
  have hlimits := handoffSelectedLegalLimits_oraclePrefixOutput horacle
  rw [recoveryValidatorLegalSumPrefixOutput]
  cases witness with
  | symmetric oracle horacleSize sum =>
      have hmode :
          handoffMode (recoveryValidatorOraclePrefixOutput limits raw) = 1 := by
        rw [hmodeTag]
        rfl
      have hfields :
          decodeTaggedList raw =
            some
              [encodeNat 0, encodeBooleanCircuit oracle,
                sum.code symmetricCircuitCodec] := by
        rw [← hcode]
        exact decodeTaggedList_encode _
      have hsumCode :
          handoffSumCode (recoveryValidatorOraclePrefixOutput limits raw) =
            sum.code symmetricCircuitCodec := by
        rw [handoffSumCode_oraclePrefixOutput horacle]
        exact (recoveryEnvelopeCodes_of_taggedList hfields).2
      have hpolicy :
          handoffSelectedLegalLimits
              (recoveryValidatorOraclePrefixOutput limits raw) =
            encodeLegalSumLimits limits.symmetric := by
        rw [hlimits, recoveryValidatorSelectedPolicy_symmetric hmode]
      obtain ⟨_, _, _, _, hle, _⟩ :=
        recoveryLegalSumStructuralFields_of_checkedSum symmetricCircuitCodec
          (recoveryValidatorOraclePrefixOutput limits raw) limits.symmetric sum
          hsumCode hpolicy
      have hfamily :
          recoveryLegalTermCircuitFamily
            (recoveryLegalTermCircuitContext
              (recoveryValidatorOraclePrefixOutput limits raw)) = 0 := by
        rw [recoveryLegalTermCircuitFamily_circuitContext hle, hmode]
        rfl
      have harity :
          recoveryLegalTermCircuitArity
              (recoveryLegalTermCircuitContext
                (recoveryValidatorOraclePrefixOutput limits raw)) =
            sum.value.q := by
        rw [recoveryLegalTermCircuitArity_circuitContext hle,
          handoffSelectedExpectedArity_of_encode hpolicy]
        exact sum.arity_eq.symm
      refine recoveryLegalSumEnvelopeOutput_ne_zero_of_checkedSum
        symmetricCircuitCodec inputLength
        (recoveryValidatorOraclePrefixOutput limits raw) limits.symmetric sum
        hsumCode hpolicy (Or.inl hmode) ?_ ?_ ?_
      · intro term hterm
        exact (symmetricLegalCircuitTerm_circuitCertificates hfamily harity
          term).1
      · intro term hterm
        exact (symmetricLegalCircuitTerm_circuitCertificates hfamily harity
          term).2.1
      · intro term hterm
        have hmetric :=
          (symmetricLegalCircuitTerm_circuitCertificates hfamily harity term).2.2
        rwa [recoveryLegalTermCircuitArity_circuitContext_eq_bound] at hmetric
  | threshold oracle horacleSize sum =>
      have hmode :
          handoffMode (recoveryValidatorOraclePrefixOutput limits raw) = 2 := by
        rw [hmodeTag]
        rfl
      have hfields :
          decodeTaggedList raw =
            some
              [encodeNat 1, encodeBooleanCircuit oracle,
                sum.code thresholdCircuitCodec] := by
        rw [← hcode]
        exact decodeTaggedList_encode _
      have hsumCode :
          handoffSumCode (recoveryValidatorOraclePrefixOutput limits raw) =
            sum.code thresholdCircuitCodec := by
        rw [handoffSumCode_oraclePrefixOutput horacle]
        exact (recoveryEnvelopeCodes_of_taggedList hfields).2
      have hpolicy :
          handoffSelectedLegalLimits
              (recoveryValidatorOraclePrefixOutput limits raw) =
            encodeLegalSumLimits limits.threshold := by
        rw [hlimits, recoveryValidatorSelectedPolicy_threshold hmode]
      obtain ⟨_, _, _, _, hle, _⟩ :=
        recoveryLegalSumStructuralFields_of_checkedSum thresholdCircuitCodec
          (recoveryValidatorOraclePrefixOutput limits raw) limits.threshold sum
          hsumCode hpolicy
      have hfamily :
          recoveryLegalTermCircuitFamily
            (recoveryLegalTermCircuitContext
              (recoveryValidatorOraclePrefixOutput limits raw)) = 1 := by
        rw [recoveryLegalTermCircuitFamily_circuitContext hle, hmode]
        rfl
      have harity :
          recoveryLegalTermCircuitArity
              (recoveryLegalTermCircuitContext
                (recoveryValidatorOraclePrefixOutput limits raw)) =
            sum.value.q := by
        rw [recoveryLegalTermCircuitArity_circuitContext hle,
          handoffSelectedExpectedArity_of_encode hpolicy]
        exact sum.arity_eq.symm
      refine recoveryLegalSumEnvelopeOutput_ne_zero_of_checkedSum
        thresholdCircuitCodec inputLength
        (recoveryValidatorOraclePrefixOutput limits raw) limits.threshold sum
        hsumCode hpolicy (Or.inr hmode) ?_ ?_ ?_
      · intro term hterm
        exact (thresholdLegalCircuitTerm_circuitCertificates hfamily harity
          term).1
      · intro term hterm
        exact (thresholdLegalCircuitTerm_circuitCertificates hfamily harity
          term).2.1
      · intro term hterm
        have hmetric :=
          (thresholdLegalCircuitTerm_circuitCertificates hfamily harity term).2.2
        rwa [recoveryLegalTermCircuitArity_circuitContext_eq_bound] at hmetric

/-! ## The decode equivalence

Soundness and completeness together: the staged validator accepts exactly the
codes the pure canonical decoder accepts. -/

theorem recoveryValidatorLegalSumPrefixOutput_ne_zero_iff_decode
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryValidatorLegalSumPrefixOutput inputLength limits raw ≠ 0 ↔
      ∃ witness : CheckedRecoveryWitness limits,
        decodeRecoveryWitness limits raw = some witness := by
  constructor
  · intro haccepts
    exact exists_decodeRecoveryWitness_of_legalSumAccept haccepts
  · rintro ⟨witness, hdecode⟩
    exact recoveryValidatorLegalSumPrefixOutput_ne_zero_of_decode hdecode

/-! ## The unconditional endpoint identification

The executable endpoint agrees with the pure validator at every input, not just
on the accepting path: rejection is now known to be exactly decode failure. -/

theorem recoveryWitnessValidatorProgramOutput_eq
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw =
      recoveryWitnessValidatorOutput limits raw := by
  by_cases haccepts :
      recoveryValidatorLegalSumPrefixOutput inputLength limits raw = 0
  · rw [recoveryWitnessValidatorProgramOutput_eq_zero_of_reject haccepts]
    refine (recoveryWitnessValidatorOutput_eq_zero_iff.2 ?_).symm
    cases hdecode : decodeRecoveryWitness limits raw with
    | none => rfl
    | some witness =>
        exact absurd haccepts
          (recoveryValidatorLegalSumPrefixOutput_ne_zero_of_decode hdecode)
  · exact recoveryWitnessValidatorProgramOutput_eq_of_accept haccepts

/-- Exact-shape run theorem for the handoff: the single public register program
returns the pure validator's own output at every input. -/
theorem run_recoveryWitnessValidatorProgram_eq_validatorOutput
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryWitnessValidatorProgram
        (recoveryWitnessValidatorBits inputLength limits raw)
        (recoveryWitnessValidatorFuel inputLength limits raw)
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits raw)) =
      some (recoveryWitnessValidatorOutput limits raw) := by
  rw [run_recoveryWitnessValidatorProgram inputLength limits raw,
    recoveryWitnessValidatorProgramOutput_eq inputLength limits raw]

/-- The pure resource ledger transfers verbatim to the executable endpoint. -/
theorem recoveryWitnessValidatorProgram_accepts_with_resources_iff
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw ≠ 0 ↔
      ∃ witness : CheckedRecoveryWitness limits,
        decodeRecoveryWitness limits raw = some witness ∧
          RecoveryWitnessResourceChecks witness := by
  rw [recoveryWitnessValidatorProgramOutput_eq inputLength limits raw]
  exact recoveryWitnessValidator_accepts_with_resources_iff

/-! ## Endpoint-level fail-closed regressions

Every hostile class of the staged validator is now a statement about the single
public endpoint output, obtained through the unconditional identification. -/

theorem recoveryWitnessValidatorProgramOutput_eq_zero_of_malformed_circuit
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hcircuit :
      recoveryLegalTermCircuitListOutput
        (recoveryLegalTermCircuitContext
          (recoveryValidatorOraclePrefixOutput limits raw))
        (recoveryLegalTermCoefficientMappedCode inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) = 0) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw = 0 :=
  recoveryWitnessValidatorProgramOutput_eq_zero_of_reject
    (recoveryValidatorLegalSumPrefixOutput_eq_zero_of_malformed_circuit
      inputLength limits raw hcircuit)

theorem
    recoveryWitnessValidatorProgramOutput_eq_zero_of_coefficientBitOverflow
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hbitCap :
      recoveryLegalTermCoefficientBitCapListOutput
        (handoffSelectedCoefficientBitCap
          (recoveryValidatorOraclePrefixOutput limits raw))
        (recoveryLegalTermCoefficientMappedCode inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) = 0) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw = 0 :=
  recoveryWitnessValidatorProgramOutput_eq_zero_of_reject
    (recoveryValidatorLegalSumPrefixOutput_eq_zero_of_coefficientBitOverflow
      inputLength limits raw hbitCap)

theorem recoveryWitnessValidatorProgramOutput_eq_zero_of_massOverflow
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hmass :
      ¬ recoveryLegalTermCoefficientMassWithinCap inputLength
        (recoveryValidatorOraclePrefixOutput limits raw)) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw = 0 :=
  recoveryWitnessValidatorProgramOutput_eq_zero_of_reject
    (recoveryValidatorLegalSumPrefixOutput_eq_zero_of_massOverflow inputLength
      limits raw hmass)

theorem recoveryWitnessValidatorProgramOutput_eq_zero_of_rationalReject
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hcoefficient :
      recoveryLegalTermCoefficientListOutput inputLength
        (recoveryLegalTermCoefficientTermsCode
          (recoveryValidatorOraclePrefixOutput limits raw)) = 0) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw = 0 :=
  recoveryWitnessValidatorProgramOutput_eq_zero_of_reject
    (recoveryValidatorLegalSumPrefixOutput_eq_zero_of_rationalReject
      inputLength limits raw hcoefficient)

theorem recoveryWitnessValidatorProgramOutput_eq_zero_of_termCountOverflow
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hcount :
      handoffSelectedTermCap (recoveryValidatorOraclePrefixOutput limits raw)
        < recoveryLegalSumTermCount
          (recoveryValidatorOraclePrefixOutput limits raw)) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw = 0 :=
  recoveryWitnessValidatorProgramOutput_eq_zero_of_reject
    (recoveryValidatorLegalSumPrefixOutput_eq_zero_of_termCountOverflow
      inputLength limits raw hcount)

theorem recoveryWitnessValidatorProgramOutput_eq_zero_of_wrongMode
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hmode :
      handoffLegalSumModeFlag
        (recoveryValidatorOraclePrefixOutput limits raw) = 0) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw = 0 :=
  recoveryWitnessValidatorProgramOutput_eq_zero_of_reject
    (recoveryValidatorLegalSumPrefixOutput_eq_zero_of_wrongMode inputLength
      limits raw hmode)

theorem recoveryWitnessValidatorProgramOutput_eq_zero_of_wireOverflow
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hwire :
      recoveryLegalTermWireListOutput
        (recoveryLegalTermWireCapContext
          (recoveryValidatorOraclePrefixOutput limits raw))
        (recoveryLegalTermValidatedSummaryTree inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) = 0) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw = 0 :=
  recoveryWitnessValidatorProgramOutput_eq_zero_of_reject
    (recoveryValidatorLegalSumPrefixOutput_eq_zero_of_wireOverflow inputLength
      limits raw hwire)

theorem recoveryWitnessValidatorProgramOutput_eq_zero_of_descriptionOverflow
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hdescription :
      recoveryLegalTermDescriptionListOutput
        (recoveryLegalTermDescriptionCapContext
          (recoveryValidatorOraclePrefixOutput limits raw))
        (recoveryLegalTermValidatedSummaryTree inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) = 0) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw = 0 :=
  recoveryWitnessValidatorProgramOutput_eq_zero_of_reject
    (recoveryValidatorLegalSumPrefixOutput_eq_zero_of_descriptionOverflow
      inputLength limits raw hdescription)

/-! ## Gap 1 closed

The executable recovery-witness validator and the pure canonical decoder are
now identified unconditionally.  The chain is:

* `recoveryValidatorOraclePrefixOutput_ne_zero_iff` — the staged structural and
  Boolean-DAG prefix accepts exactly the canonical three-field envelopes with a
  decodable in-cap oracle;
* `recoveryValidatorLegalSumPrefixOutput_ne_zero_iff` — the twelve executable
  conjuncts of the legal-sum envelope;
* `exists_decodeRecoveryWitness_of_legalSumAccept` (soundness) and
  `recoveryValidatorLegalSumPrefixOutput_ne_zero_of_decode` (completeness),
  combined in `recoveryValidatorLegalSumPrefixOutput_ne_zero_iff_decode`;
* `recoveryWitnessValidatorProgramOutput_eq` — the endpoint output equals
  `recoveryWitnessValidatorOutput` at every input, so
  `run_recoveryWitnessValidatorProgram_eq_validatorOutput` states the register
  program's run in the pure validator's own vocabulary, and
  `recoveryWitnessValidatorProgram_accepts_with_resources_iff` transfers the
  full typed resource ledger `RecoveryWitnessResourceChecks` verbatim.

Completeness consumes no conjunct-specific side condition: the term count, the
coefficient widths, the exact rational mass, the wire charge and the description
charge are all read off the proof fields of `CheckedLegalCircuitSum`, and the
fold denominator is nonzero by `rationalMassFold_canonical_valid`. -/

end NearCubicWires.CanonicalRecoveryValidatorProgram
