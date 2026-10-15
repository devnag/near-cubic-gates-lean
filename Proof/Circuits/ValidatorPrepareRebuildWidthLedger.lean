import Batteries.Tactic.OpenPrivate
import Proof.MachineModel.CanonicalBooleanNodePrepareRebuildProgram
import Proof.Circuits.ValidatorDescriptionLeafClosure
import Proof.Circuits.ValidatorRebuiltWidthCertificates
import Proof.Circuits.ValidatorTaggedIntermediateVerdict

namespace NearCubicWires.ValidatorPrepareRebuildWidthLedger

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedMidpointRebuildProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalBooleanNodeListRebuildProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodePrepareRebuildProgram
open NearCubicWires.CanonicalBooleanNodeValidationProgram
open NearCubicWires.CanonicalGateAtomHeadListProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedNatListRebuildProgram
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.CanonicalTaggedSpineIndexProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorCanonicalizerRebuildLedger
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorRebuildWidthLedger
open NearCubicWires.ValidatorTaggedIntermediateVerdict
open NearCubicWires.ValidatorTraversalWidthLedger
open NearCubicWires.ValidatorWidthCombinatorLedger
open NearCubicWires.VerifiedLinker

open private taggedListRetainBits taggedNatOutputTree taggedNatSingletonTree
  taggedNatCalleeBits from
  Proof.MachineModel.CanonicalTaggedNatListValidationProgram

open private booleanNodeStructuralDescriptorBits from
  Proof.MachineModel.CanonicalBooleanNodeValidationProgram

private theorem le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} {base : ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hmem
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmem).trans (Nat.le_max_right _ _)

private theorem foldr_max_le
    {values : List ℕ} {base bound : ℕ} (hbase : base ≤ bound)
    (hvalues : ∀ value ∈ values, value ≤ bound) :
    values.foldr max base ≤ bound := by
  induction values with
  | nil => simpa using hbase
  | cons head tail inductionHypothesis =>
      simp only [List.foldr]
      exact max_le (hvalues head (by simp))
        (inductionHypothesis fun value hvalue => hvalues value (by simp [hvalue]))

theorem taggedNatFieldValidateBits_le {index bound : ℕ} {fields : List ℕ}
    (hpositive : 1 ≤ bound) (hindex : natBitLength index ≤ bound)
    (hselect : taggedSpineSelectBits index fields ≤ bound)
    (hvalidate :
      canonicalNatValidationRebuildBits index (fields.getD index 0) ≤ bound) :
    taggedNatFieldValidateBits index fields ≤ bound := by
  simp only [taggedNatFieldValidateBits]
  omega

theorem taggedNatFieldValidateMaximumBits_le {raw bound : ℕ}
    (hpositive : 1 ≤ bound)
    (hleaf : ∀ index, index < (taggedNatFieldCodes raw).length →
      taggedNatFieldValidateBits index (taggedNatFieldCodes raw) ≤ bound) :
    taggedNatFieldValidateMaximumBits raw ≤ bound := by
  refine foldr_max_le hpositive ?_
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨index, hindexMem, rfl⟩
  exact hleaf index (List.mem_range.mp hindexMem)

/-! ## §2 The rebuilt tagged-nat list validator's width -/

/-- **The rebuilt tagged-nat charge, at its named stages.**  Ten entries, of
which two are the cone and eight are named residuals. -/
theorem taggedNatListValidationRebuildBits_le_of_stages_le
    {inputLength raw bound stageBound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hretain : taggedListRetainBits inputLength raw ≤ stageBound)
    (hcount :
      taggedSpineLengthBits (encodeTaggedList (taggedNatFieldCodes raw)) ≤
        stageBound)
    (hlist :
      indexedAtomListBits inputLength (taggedNatFieldCodes raw).length
        (encodeTaggedList (taggedNatFieldCodes raw))
        (fun index =>
          Nat.pair index (encodeTaggedList (taggedNatFieldCodes raw))) ≤
        stageBound)
    (hrequests : taggedNatIndexRequestBits raw ≤ stageBound)
    (hcall :
      balancedCallRequiredBits (taggedNatIndexOutput raw)
        (taggedNatIndexRequests raw) ≤ stageBound)
    (hleaf : taggedNatFieldValidateMaximumBits raw ≤ stageBound)
    (hsingleton :
      balancedBitSingletonTreeBits (taggedNatOutputTree raw) ≤ stageBound)
    (hflatten :
      balancedTreeStreamFlattenMaximumBits (taggedNatSingletonTree raw) ≤
        stageBound) :
    taggedNatListValidationRebuildBits inputLength raw ≤ max stageBound bound := by
  simp only [taggedNatListValidationRebuildBits,
    taggedNatListValidationRebuildStageBits, List.foldr]
  omega

/-! ## §3 The rebuilt node validator's width -/

/-- **The structural postprocessor's width.**  A fixed depth-`3` self-pairing
clock over the public length and the stage's own output, so it costs one
constant factor and no degree. -/
theorem booleanNodeStructuralDescriptorBits_le {inputLength value bound : ℕ}
    (hpositive : 1 ≤ bound) (hlength : natBitLength inputLength ≤ bound)
    (hvalue : natBitLength value ≤ bound) :
    booleanNodeStructuralDescriptorBits inputLength value ≤ 8 * bound := by
  have hclock :=
    natBitLength_pairIter_le 3 (max 1 (max inputLength value))
  have height : (2 : ℕ) ^ 3 = 8 := by norm_num
  have hone : natBitLength 1 = 1 := natBitLength_one
  have hinner :
      natBitLength (max 1 (max inputLength value)) ≤ bound := by
    have hright := natBitLength_max_le inputLength value
    have houter := natBitLength_max_le 1 (max inputLength value)
    omega
  have hscale :
      8 * natBitLength (max 1 (max inputLength value)) ≤ 8 * bound :=
    Nat.mul_le_mul_left _ hinner
  rw [height] at hclock
  simp only [booleanNodeStructuralDescriptorBits]
  omega

/-- **The rebuilt node validator's width.**  The tagged-nat stage plus the
postprocessor's constant factor; the postprocessor's input is the tagged-nat
stage's own returned value, so
`ValidatorTaggedIntermediateVerdict.natBitLength_le_of_run` pays for it. -/
theorem booleanNodeValidationRebuildBits_le_of_stage_le
    {inputLength raw bound stageBound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hstage : taggedNatListValidationRebuildBits inputLength raw ≤ stageBound) :
    booleanNodeValidationRebuildBits inputLength raw ≤
      8 * max stageBound bound := by
  have houtput :
      natBitLength (taggedNatListValidationOutput raw) ≤
        taggedNatListValidationRebuildBits inputLength raw :=
    natBitLength_le_of_run
      (run_taggedNatListValidationRebuildProgram inputLength raw)
  have hdescriptor :=
    booleanNodeStructuralDescriptorBits_le
      (inputLength := inputLength) (value := taggedNatListValidationOutput raw)
      (bound := max stageBound bound) (by omega) (by omega) (by omega)
  simp only [booleanNodeValidationRebuildBits]
  omega

/-! ## §4 The rebuilt batch and the rebuilt preparation fork -/

/-- **The counted call over the descriptors.** -/
theorem booleanNodeCallRebuildMaximumBits_le
    {inputLength bound stageBound : ℕ} {rawNodes : List ℕ}
    (hlength : natBitLength inputLength ≤ bound)
    (hcall :
      balancedCallRequiredBits booleanNodeCallOutput
        (booleanNodeRequests inputLength rawNodes) ≤ stageBound)
    (hpositive : 1 ≤ stageBound)
    (hnode : ∀ node ∈ rawNodes,
      booleanNodeValidationRebuildBits inputLength node ≤ stageBound) :
    booleanNodeCallRebuildMaximumBits inputLength rawNodes ≤
      max stageBound bound := by
  have hfold :
      ((booleanNodeRequests inputLength rawNodes).map
        booleanNodeCallRebuildBits).foldr max 1 ≤ stageBound := by
    refine foldr_max_le hpositive ?_
    intro value hvalue
    rcases List.mem_map.mp hvalue with ⟨request, hrequest, rfl⟩
    rcases List.mem_map.mp hrequest with ⟨node, hnodeMem, rfl⟩
    have hproject :
        booleanNodeCallRebuildBits (nativeInputRequest inputLength node) =
          booleanNodeValidationRebuildBits inputLength node := by
      rw [booleanNodeCallRebuildBits, nativeInputRequest, Nat.unpair_pair]
    rw [hproject]
    exact hnode node hnodeMem
  simp only [booleanNodeCallRebuildMaximumBits]
  omega

/-- **The rebuilt batch's width.** -/
theorem booleanNodeBatchRebuildBits_le
    {inputLength bound stageBound : ℕ} {rawNodes : List ℕ}
    (hlength : natBitLength inputLength ≤ bound)
    (hframing :
      nativeInputRequestTreeBits inputLength rawNodes ≤ stageBound)
    (hcall :
      balancedCallRequiredBits booleanNodeCallOutput
        (booleanNodeRequests inputLength rawNodes) ≤ stageBound)
    (hpositive : 1 ≤ stageBound)
    (hnode : ∀ node ∈ rawNodes,
      booleanNodeValidationRebuildBits inputLength node ≤ stageBound) :
    booleanNodeBatchRebuildBits inputLength rawNodes ≤
      max stageBound bound := by
  have hcalls :=
    booleanNodeCallRebuildMaximumBits_le (inputLength := inputLength)
      (bound := bound) (stageBound := stageBound) (rawNodes := rawNodes)
      hlength hcall hpositive hnode
  simp only [booleanNodeBatchRebuildBits]
  omega

/-- **The rebuilt preparation fork's width.** -/
theorem booleanCircuitPreparationRebuildBits_le
    {inputLength bound stageBound : ℕ} {rawNodes : List ℕ}
    (hpositive : 1 ≤ bound) (hlength : natBitLength inputLength ≤ bound)
    (hcode : natBitLength (encodeBalancedList rawNodes) ≤ bound)
    (hcount : natBitLength rawNodes.length ≤ bound)
    (houtputs :
      natBitLength (encodeBalancedList (booleanNodeOutputs rawNodes)) ≤ bound)
    (hlengthStage : balancedLengthBits inputLength rawNodes ≤ stageBound)
    (hbatch : booleanNodeBatchRebuildBits inputLength rawNodes ≤ stageBound) :
    booleanCircuitPreparationRebuildBits inputLength rawNodes ≤
      max stageBound (4 * bound) := by
  have hfork :=
    forkCallBits_le (inputLength := inputLength)
      (raw := encodeBalancedList rawNodes)
      (firstBits := balancedLengthBits inputLength rawNodes)
      (secondBits := booleanNodeBatchRebuildBits inputLength rawNodes)
      (firstOutput := rawNodes.length)
      (secondOutput := encodeBalancedList (booleanNodeOutputs rawNodes))
      (bound := bound) hpositive hlength hcode hcount houtputs
  simp only [booleanCircuitPreparationRebuildBits]
  omega

/-! ## §5 The rebuilt node-list preparation stage -/

/-- **The rebuilt preparation stage's width, at its one residual fork.**  This
is the drop-in replacement for `booleanNodeListPrepareBits` in
`ValidatorRebuildWidthLedger` §5. -/
theorem booleanNodeListPrepareRebuildBits_le
    {inputLength raw bound stageBound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hflag : natBitLength (balancedCanonicalityOutput raw) ≤ bound)
    (hnormalized :
      natBitLength (booleanNodeListNormalizedCode raw) ≤ bound)
    (hprepared :
      natBitLength (booleanNodeListPreparationOutput raw) ≤ bound)
    (hfork :
      booleanCircuitPreparationRebuildBits inputLength
        (booleanNodeListAtoms raw) ≤ stageBound) :
    booleanNodeListPrepareRebuildBits inputLength raw ≤
      max stageBound (2 * bound) := by
  have hswap :=
    swapPairBits_le (left := balancedCanonicalityOutput raw)
      (right := booleanNodeListNormalizedCode raw) (bound := bound) hflag
      hnormalized
  have hpreserve :=
    preserveRightBits_le
      (sourceBits :=
        booleanCircuitPreparationRebuildBits inputLength
          (booleanNodeListAtoms raw))
      (left := booleanNodeListNormalizedCode raw)
      (right := balancedCanonicalityOutput raw)
      (output := booleanNodeListPreparationOutput raw) (bound := bound)
      hnormalized hflag hprepared
  simp only [booleanNodeListPrepareRebuildBits]
  omega

theorem booleanNodeListPrepareRebuildBits_le_of_stages_le
    {inputLength raw bound stageBound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hflag : natBitLength (balancedCanonicalityOutput raw) ≤ bound)
    (hnormalized :
      natBitLength (booleanNodeListNormalizedCode raw) ≤ bound)
    (hprepared :
      natBitLength (booleanNodeListPreparationOutput raw) ≤ bound)
    (hcount : natBitLength (booleanNodeListAtoms raw).length ≤ bound)
    (houtputs :
      natBitLength
        (encodeBalancedList
          (booleanNodeOutputs (booleanNodeListAtoms raw))) ≤ bound)
    (hstagePositive : 1 ≤ stageBound)
    (hlengthStage :
      balancedLengthBits inputLength (booleanNodeListAtoms raw) ≤ stageBound)
    (hframing :
      nativeInputRequestTreeBits inputLength (booleanNodeListAtoms raw) ≤
        stageBound)
    (hcall :
      balancedCallRequiredBits booleanNodeCallOutput
        (booleanNodeRequests inputLength (booleanNodeListAtoms raw)) ≤
        stageBound)
    (hnode : ∀ node ∈ booleanNodeListAtoms raw,
      booleanNodeValidationRebuildBits inputLength node ≤ stageBound) :
    booleanNodeListPrepareRebuildBits inputLength raw ≤
      max stageBound (4 * bound) := by
  have hcodeEq :
      encodeBalancedList (booleanNodeListAtoms raw) =
        booleanNodeListNormalizedCode raw := rfl
  have hbatch :=
    booleanNodeBatchRebuildBits_le (inputLength := inputLength) (bound := bound)
      (stageBound := stageBound) (rawNodes := booleanNodeListAtoms raw) hlength
      hframing hcall hstagePositive hnode
  have hfork :=
    booleanCircuitPreparationRebuildBits_le (inputLength := inputLength)
      (bound := bound) (stageBound := max stageBound bound)
      (rawNodes := booleanNodeListAtoms raw) hpositive hlength
      (by rw [hcodeEq]; exact hnormalized) hcount houtputs
      (by omega) hbatch
  have hstage :=
    booleanNodeListPrepareRebuildBits_le (inputLength := inputLength) (raw := raw)
      (bound := bound) (stageBound := max (max stageBound bound) (4 * bound))
      hpositive hlength hflag hnormalized hprepared hfork
  omega

/-! ## §6 The doubly rebuilt node-list validator, and the `hnode` socket -/

set_option maxHeartbeats 1600000 in
-- One `omega` closes an eight-way maximum against the fork's own reduction.
/-- **The doubly rebuilt node-list validator's width.**
`ValidatorRebuildWidthLedger` §3 verbatim, with the preparation entry named at
the rebuilt stage. -/
theorem booleanNodeListValidationPrepareRebuildBits_le
    {inputLength raw bound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound)
    (hnormalized :
      natBitLength (booleanNodeListNormalizedCode raw) ≤ bound) :
    booleanNodeListValidationPrepareRebuildBits inputLength raw ≤
      max
        (balancedRawCanonicalizeFoldBits inputLength
          (rawBalancedTraversalTree raw))
        (max (booleanNodeListPrepareRebuildBits inputLength raw)
          (max (booleanNodeListRangeLoweringBits inputLength raw)
            (max (booleanNodeListTopologyBits inputLength raw)
              (max
                (booleanNodeListTopologyEqualityLoweringBits inputLength raw)
                (max (booleanNodeListTopologyEqualityBits inputLength raw)
                  (max (booleanNodeListValidationGateBits inputLength raw)
                    (8 * bound))))))) := by
  have hnormalize :=
    booleanNodeListNormalizeRebuildBits_le (inputLength := inputLength)
      (raw := raw) (bound := bound) hpositive hlength hraw hnormalized
  simp only [booleanNodeListValidationPrepareRebuildBits]
  omega

/-- **The doubly rebuilt node-list validator, at its one residual stage.**  The
generation-two analogue of
`ValidatorRebuildWidthLedger`'s
`booleanNodeListValidationRebuildBits_le_of_prepare_le`: the preparation entry
now names a stage whose cone contains no clock and no tagged public list. -/
theorem booleanNodeListValidationPrepareRebuildBits_le_of_prepare_le
    {inputLength raw bound stageBound : ℕ} (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound)
    (hnormalized : natBitLength (booleanNodeListNormalizedCode raw) ≤ bound)
    (hcanonicalize :
      balancedRawCanonicalizeFoldBits inputLength
        (rawBalancedTraversalTree raw) ≤ stageBound)
    (hscalars :
      max (booleanNodeListRangeLoweringBits inputLength raw)
          (max (booleanNodeListTopologyBits inputLength raw)
            (max
              (booleanNodeListTopologyEqualityLoweringBits inputLength raw)
              (max (booleanNodeListTopologyEqualityBits inputLength raw)
                (booleanNodeListValidationGateBits inputLength raw)))) ≤
        stageBound)
    (hprepare :
      booleanNodeListPrepareRebuildBits inputLength raw ≤ stageBound) :
    booleanNodeListValidationPrepareRebuildBits inputLength raw ≤
      max stageBound (8 * bound) := by
  have hstage :=
    booleanNodeListValidationPrepareRebuildBits_le (inputLength := inputLength)
      (raw := raw) (bound := bound) hpositive hlength hraw hnormalized
  omega

/-- **`hnode` at the doubly rebuilt name, as a domination judgement.**  The
generation-two analogue of
`ValidatorRebuiltWidthCertificates.booleanNodeListValidationRebuildBits_polyBounded`:
the preparation residual is the *rebuilt* fork, so no premise of this theorem
mentions a `pairIter` clock or the frozen natural validator. -/
theorem booleanNodeListValidationPrepareRebuildBits_polyBounded
    {inputLength raw measure lengthCoefficient rawCoefficient
      normalizedCoefficient canonicalizeCoefficient prepareCoefficient
      rangeCoefficient topologyCoefficient equalityLoweringCoefficient
      equalityCoefficient gateCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hraw : PolyBounded (natBitLength raw) measure rawCoefficient degree)
    (hnormalized :
      PolyBounded (natBitLength (booleanNodeListNormalizedCode raw)) measure
        normalizedCoefficient degree)
    (hcanonicalize :
      PolyBounded
        (balancedRawCanonicalizeFoldBits inputLength
          (rawBalancedTraversalTree raw)) measure canonicalizeCoefficient
        degree)
    (hprepare :
      PolyBounded (booleanNodeListPrepareRebuildBits inputLength raw) measure
        prepareCoefficient degree)
    (hrange :
      PolyBounded (booleanNodeListRangeLoweringBits inputLength raw) measure
        rangeCoefficient degree)
    (htopology :
      PolyBounded (booleanNodeListTopologyBits inputLength raw) measure
        topologyCoefficient degree)
    (hequalityLowering :
      PolyBounded (booleanNodeListTopologyEqualityLoweringBits inputLength raw)
        measure equalityLoweringCoefficient degree)
    (hequality :
      PolyBounded (booleanNodeListTopologyEqualityBits inputLength raw) measure
        equalityCoefficient degree)
    (hgate :
      PolyBounded (booleanNodeListValidationGateBits inputLength raw) measure
        gateCoefficient degree) :
    PolyBounded (booleanNodeListValidationPrepareRebuildBits inputLength raw)
      measure
      (max canonicalizeCoefficient
        (max prepareCoefficient
          (max rangeCoefficient
            (max topologyCoefficient
              (max equalityLoweringCoefficient
                (max equalityCoefficient
                  (max gateCoefficient
                    (8 *
                      max lengthCoefficient
                        (max rawCoefficient
                          (max normalizedCoefficient 1)))))))))) degree := by
  have hcone :
      PolyBounded
        (max (natBitLength inputLength)
          (max (natBitLength raw)
            (max (natBitLength (booleanNodeListNormalizedCode raw)) 1)))
        measure
        (max lengthCoefficient
          (max rawCoefficient (max normalizedCoefficient 1))) degree :=
    hlength.max (hraw.max (hnormalized.max (polyBounded_const 1 measure degree)))
  refine (hcanonicalize.max (hprepare.max (hrange.max (htopology.max
    (hequalityLowering.max (hequality.max (hgate.max
      (hcone.const_mul 8)))))))).mono ?_
  exact booleanNodeListValidationPrepareRebuildBits_le
    (bound :=
      max (natBitLength inputLength)
        (max (natBitLength raw)
          (max (natBitLength (booleanNodeListNormalizedCode raw)) 1)))
    (by omega) (by omega) (by omega) (by omega)

/-! ## §7 The verdict on the first-generation `hnode`

`ValidatorRebuiltCircuitFuelLedger.executableRecoveryMachineOfRebuiltValidatorAtCircuitFrontier`
states `hnode` at `booleanNodeListValidationRebuildBits`, whose preparation
entry is the **frozen** `booleanNodeListPrepareBits`.  §7 records why that
premise cannot be discharged, by exhibiting the frozen natural validator's
charge *inside* it at every field of every descriptor: composed with
`ValidatorTaggedIntermediateVerdict`'s
`two_pow_le_canonicalNatValidationBits_canonicalAtomFamily_of_run`, which
floors that charge at `2 ^ n` on the canonical atom family, the frozen
preparation charge is geometric wherever a descriptor carries such a field.
The repair is not an accounting change: it is §5's stage, and the machine has
to be relinked on `booleanNodeListValidationPrepareRebuildProgram`. -/

/-- The frozen tagged-nat charge contains the frozen natural validator's charge
at every field. -/
theorem canonicalNatValidationBits_le_taggedNatListValidationBits
    {inputLength raw field : ℕ} (hfield : field ∈ taggedNatFieldCodes raw) :
    canonicalNatValidationBits inputLength field ≤
      taggedNatListValidationBits inputLength raw := by
  have hmember :
      canonicalNatValidationBits inputLength field ∈
        (taggedNatFieldCodes raw).map fun value =>
          canonicalNatValidationBits inputLength value :=
    List.mem_map.mpr ⟨field, hfield, rfl⟩
  have hfold :
      canonicalNatValidationBits inputLength field ≤
        taggedNatCalleeBits inputLength raw := by
    simp only [taggedNatCalleeBits]
    exact le_foldr_max_of_mem hmember
  simp only [taggedNatListValidationBits]
  omega

/-- The frozen node validator's charge contains the frozen tagged-nat charge. -/
theorem taggedNatListValidationBits_le_booleanNodeValidationBits
    (inputLength raw : ℕ) :
    taggedNatListValidationBits inputLength raw ≤
      booleanNodeValidationBits inputLength raw :=
  Nat.le_max_left _ _

/-- The frozen batch's charge contains the frozen node validator's charge at
every descriptor. -/
theorem booleanNodeValidationBits_le_booleanNodeBatchBits
    {inputLength node : ℕ} {rawNodes : List ℕ} (hnode : node ∈ rawNodes) :
    booleanNodeValidationBits inputLength node ≤
      booleanNodeBatchBits inputLength rawNodes := by
  have hmember :
      booleanNodeCallBits (nativeInputRequest inputLength node) ∈
        (booleanNodeRequests inputLength rawNodes).map booleanNodeCallBits :=
    List.mem_map.mpr ⟨nativeInputRequest inputLength node,
      List.mem_map.mpr ⟨node, hnode, rfl⟩, rfl⟩
  have hproject :
      booleanNodeCallBits (nativeInputRequest inputLength node) =
        booleanNodeValidationBits inputLength node := by
    rw [booleanNodeCallBits, nativeInputRequest, Nat.unpair_pair]
  have hfold :
      booleanNodeValidationBits inputLength node ≤
        ((booleanNodeRequests inputLength rawNodes).map
          booleanNodeCallBits).foldr max 1 := by
    rw [← hproject]
    exact le_foldr_max_of_mem hmember
  simp only [booleanNodeBatchBits, booleanNodeCallMaximumBits]
  omega

/-- **The frozen preparation stage carries the frozen natural validator's
charge.**  Every field of every structural descriptor of the node-list code is
validated by the frozen `canonicalNatValidationProgram`, and the whole chain
from that charge up to `booleanNodeListPrepareBits` is a chain of maxima. -/
theorem canonicalNatValidationBits_le_booleanNodeListPrepareBits
    {inputLength raw node field : ℕ}
    (hnode : node ∈ booleanNodeListAtoms raw)
    (hfield : field ∈ taggedNatFieldCodes node) :
    canonicalNatValidationBits inputLength field ≤
      booleanNodeListPrepareBits inputLength raw := by
  have hfieldStage :=
    canonicalNatValidationBits_le_taggedNatListValidationBits
      (inputLength := inputLength) (raw := node) hfield
  have hnodeStage :=
    taggedNatListValidationBits_le_booleanNodeValidationBits inputLength node
  have hbatch :=
    booleanNodeValidationBits_le_booleanNodeBatchBits
      (inputLength := inputLength) (node := node)
      (rawNodes := booleanNodeListAtoms raw) hnode
  have hfork :=
    le_forkCallBits_second inputLength
      (encodeBalancedList (booleanNodeListAtoms raw))
      (balancedLengthBits inputLength (booleanNodeListAtoms raw))
      (booleanNodeBatchBits inputLength (booleanNodeListAtoms raw))
      (booleanNodeListAtoms raw).length
      (encodeBalancedList (booleanNodeOutputs (booleanNodeListAtoms raw)))
  have hpreserve :=
    le_preserveRightBits
      (booleanCircuitPreparationBits inputLength (booleanNodeListAtoms raw))
      (booleanNodeListNormalizedCode raw) (balancedCanonicalityOutput raw)
      (booleanNodeListPreparationOutput raw)
  simp only [booleanNodeListPrepareBits, booleanCircuitPreparationBits] at *
  omega

end NearCubicWires.ValidatorPrepareRebuildWidthLedger
