import Proof.Circuits.ValidatorTopologyRangeLedger

/-!
# `hcircuit`, closed

`ValidatorSweptLeafClosure` §3 lists `hcircuit` first: the Boolean circuit
validator's fuel charge at the oracle handoff.  `ValidatorCircuitStageWidths` §3
reduced it to two charges; `ValidatorNodePreparationLedger` §3 closed the first
and `ValidatorTopologyRangeLedger` §3 the second.  This module assembles them.

The one fact the assembly needs that no published module states is the *degree
anchor*: the oracle code the Boolean circuit validator runs on is a projection
of the **witness**, not of the serialized policy record.  So its width sits at
degree `1` — and that is what makes room for the preparation fork's degree-`3`
unit budget inside the published slot of `4`.  The projection is `private` to
`CanonicalRecoveryValidatorProgram`; `open private` reads it with no edit.

* §1 the degree anchor: `handoffOracleCode` of the structural prefix's output
  never exceeds the raw witness code.

* §2 the descriptor ledger: one structural node descriptor is linear in the
  atom it was parsed from, so the topology range's width hypothesis is paid
  from the node-list code's own width.

* §3 the node-list validator, assembled at degree `3`.

* §4 the Boolean circuit validator, assembled at degree `3`, and `hcircuit`
  itself at the machine's request family.
-/

namespace NearCubicWires.ValidatorCircuitLeafClosure

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalBooleanNodeValidationProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.RecoveryVerifierResourceEnvelope
open NearCubicWires.ValidatorCircuitStageWidths
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorDescriptionLeafClosure
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorLeafFuelBounds
open NearCubicWires.ValidatorLeafPremiseSweep
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorNodePreparationLedger
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorResidualLeafBudget
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.ValidatorTaggedSpineLedger
open NearCubicWires.ValidatorTopologyRangeLedger

open private recoveryEnvelopeOracleCode taggedHeadCode taggedTailCode from
  Proof.MachineModel.CanonicalRecoveryValidatorProgram

open private validatedNatValue from
  Proof.MachineModel.CanonicalBooleanNodeValidationProgram

/-! ## §1 The degree anchor -/

/-- The validator's nested handoff never invents an oracle code: the field it
publishes is the witness's own second nested component. -/
theorem handoffOracleCode_recoveryValidatorHandoffOutput_le
    (limits : RecoveryWitnessLimits) (raw : ℕ) :
    handoffOracleCode (recoveryValidatorHandoffOutput limits raw) ≤ raw := by
  have hzero : handoffOracleCode 0 = 0 := by
    simp [handoffOracleCode]
  have henvelope : recoveryEnvelopeOracleCode raw ≤ raw := by
    simp only [recoveryEnvelopeOracleCode, taggedHeadCode, taggedTailCode]
    exact (Nat.unpair_left_le _).trans
      ((Nat.unpair_right_le _).trans
        ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _)))
  simp only [recoveryValidatorHandoffOutput]
  split
  · rw [hzero]
    exact Nat.zero_le _
  · simp only [handoffOracleCode, Nat.unpair_pair]
    exact henvelope

/-- **The degree anchor.**  The Boolean circuit validator runs on a projection
of the raw witness code, so its input's width is charged at the *witness*
anchor's degree — one — and not at the serialized policy record's two. -/
theorem handoffOracleCode_structuralPrefixOutput_le
    (limits : RecoveryWitnessLimits) (raw : ℕ) :
    handoffOracleCode (recoveryValidatorStructuralPrefixOutput limits raw) ≤
      raw := by
  have hzero : handoffOracleCode 0 = 0 := by
    simp [handoffOracleCode]
  have hhandoff := handoffOracleCode_recoveryValidatorHandoffOutput_le limits raw
  simp only [recoveryValidatorStructuralPrefixOutput,
    recoveryNestedPresenceOutput]
  split
  · rw [hzero]
    exact Nat.zero_le _
  · split
    · rw [hzero]
      exact Nat.zero_le _
    · split
      · rw [hzero]
        exact Nat.zero_le _
      · exact hhandoff

/-- The anchor, in the domination judgement. -/
theorem polyBounded_handoffOracleCode_structuralPrefixOutput
    {limits : RecoveryWitnessLimits} {raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded
      (natBitLength
        (handoffOracleCode
          (recoveryValidatorStructuralPrefixOutput limits raw)))
      measure coefficient degree :=
  hraw.mono
    (natBitLength_mono (handoffOracleCode_structuralPrefixOutput_le limits raw))

/-! ## §2 The descriptor ledger -/

private theorem validatedNatValue_le {output value : ℕ}
    (hvalue : validatedNatValue output = some value) : value ≤ output := by
  unfold validatedNatValue at hvalue
  split at hvalue
  · exact absurd hvalue (by simp)
  · have hproject : value = (Nat.unpair output).2 := by
      injection hvalue with hvalue
      exact hvalue.symm
    rw [hproject]
    exact Nat.unpair_right_le output

/-- A validated natural field is at most four times as wide as its code: the
decoded candidate's width is capped by the code's atom count. -/
theorem natBitLength_canonicalNatValidationOutput_le (field : ℕ) :
    natBitLength (canonicalNatValidationOutput field) ≤ 4 * natBitLength field := by
  have hpositive := one_le_natBitLength field
  have hcandidate := natBitLength_canonicalNatCandidate_le field
  have hatoms := rawBalancedTraversalTree_atoms_length_succ_le field
  have hzero : natBitLength 0 = 1 := natBitLength_zero
  have hone : natBitLength 1 = 1 := natBitLength_one
  have hpair := pairCodeBits_le 1 (canonicalNatCandidate field)
  simp only [canonicalNatValidationOutput]
  split
  · omega
  · omega

/-- Every validated field output of a tagged record is linear in the record's
own width. -/
theorem natBitLength_le_of_mem_taggedNatFieldOutputs {raw output : ℕ}
    (houtput : output ∈ taggedNatFieldOutputs raw) :
    natBitLength output ≤ 4 * natBitLength raw := by
  rw [taggedNatFieldOutputs, List.mem_map] at houtput
  obtain ⟨field, hfield, rfl⟩ := houtput
  have hfieldWidth := natBitLength_le_of_mem_taggedNatFieldCodes hfield
  have hleaf := natBitLength_canonicalNatValidationOutput_le field
  omega

/-- Three nested pairings above a validated field: one structural descriptor is
linear in the widest field it names. -/
private theorem natBitLength_booleanNodeStructuralDescriptor_le
    (values : List ℕ) (bound : ℕ) (hone : 1 ≤ bound)
    (hvalues : ∀ value ∈ values, natBitLength value ≤ bound) :
    natBitLength (booleanNodeStructuralDescriptor values) ≤ 8 * (bound + 3) := by
  have hpair : ∀ left right cap : ℕ, natBitLength left ≤ cap →
      natBitLength right ≤ cap → natBitLength (Nat.pair left right) ≤ 2 * cap := by
    intro left right cap hleft hright
    have hbound := pairCodeBits_le left right
    omega
  have hzero : natBitLength 0 = 1 := natBitLength_zero
  have hunit : natBitLength 1 = 1 := natBitLength_one
  have hsmall : ∀ tag : ℕ, tag ≤ 4 → natBitLength tag ≤ bound + 3 := by
    intro tag htag
    have hlog : Nat.log 2 4 < 3 := Nat.log_lt_of_lt_pow (by omega) (by norm_num)
    have hfour : natBitLength 4 ≤ 3 := by
      unfold natBitLength
      omega
    have hmono := natBitLength_mono htag
    omega
  have hreject : natBitLength 0 ≤ 8 * (bound + 3) := by omega
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  · simpa only [booleanNodeStructuralDescriptor] using hreject
  · simpa only [booleanNodeStructuralDescriptor] using hreject
  · have hfirst : natBitLength first ≤ bound := hvalues first (by simp)
    have hsecond : natBitLength second ≤ bound := hvalues second (by simp)
    have hbody : ∀ tag payload : ℕ, tag ≤ 4 →
        validatedNatValue second = some payload →
        natBitLength (Nat.pair 1 (Nat.pair tag payload)) ≤ 8 * (bound + 3) := by
      intro tag payload htag hpayload
      have hwidth : natBitLength payload ≤ bound + 3 := by
        have hle := validatedNatValue_le hpayload
        have hmono := natBitLength_mono hle
        omega
      have hinner := hpair tag payload (bound + 3) (hsmall tag htag) hwidth
      have houter :=
        hpair 1 (Nat.pair tag payload) (2 * (bound + 3)) (by omega) hinner
      omega
    simp only [booleanNodeStructuralDescriptor]
    split
    · rename_i payload hfirstEq hsecondEq
      split
      · exact hbody 0 payload (by omega) hsecondEq
      · exact hreject
    · rename_i payload hfirstEq hsecondEq
      exact hbody 1 payload (by omega) hsecondEq
    · rename_i payload hfirstEq hsecondEq
      exact hbody 2 payload (by omega) hsecondEq
    · exact hreject
  · rcases rest with _ | ⟨fourth, tail⟩
    · have hfirst : natBitLength first ≤ bound := hvalues first (by simp)
      have hsecond : natBitLength second ≤ bound := hvalues second (by simp)
      have hthird : natBitLength third ≤ bound := hvalues third (by simp)
      have hbody : ∀ tag left right : ℕ, tag ≤ 4 →
          validatedNatValue second = some left →
          validatedNatValue third = some right →
          natBitLength (Nat.pair 1 (Nat.pair tag (Nat.pair left right))) ≤
            8 * (bound + 3) := by
        intro tag left right htag hleft hright
        have hleftWidth : natBitLength left ≤ bound + 3 := by
          have hle := validatedNatValue_le hleft
          have hmono := natBitLength_mono hle
          omega
        have hrightWidth : natBitLength right ≤ bound + 3 := by
          have hle := validatedNatValue_le hright
          have hmono := natBitLength_mono hle
          omega
        have hleaf := hpair left right (bound + 3) hleftWidth hrightWidth
        have hmiddle :=
          hpair tag (Nat.pair left right) (2 * (bound + 3))
            (by have := hsmall tag htag; omega) hleaf
        have houter :=
          hpair 1 (Nat.pair tag (Nat.pair left right)) (2 * (2 * (bound + 3)))
            (by omega) hmiddle
        omega
      simp only [booleanNodeStructuralDescriptor]
      split
      · rename_i left right hfirstEq hsecondEq hthirdEq
        exact hbody 3 left right (by omega) hsecondEq hthirdEq
      · rename_i left right hfirstEq hsecondEq hthirdEq
        exact hbody 4 left right (by omega) hsecondEq hthirdEq
      · exact hreject
    · simpa only [booleanNodeStructuralDescriptor] using hreject

/-- **The descriptor ledger.**  Every descriptor the topology pass reads is
linear in the node-list code's own width. -/
theorem natBitLength_le_of_mem_booleanNodeListDescriptors {raw code : ℕ}
    (hcode : code ∈ booleanNodeListDescriptors raw) :
    natBitLength code ≤ 96 * natBitLength raw + 24 := by
  rw [booleanNodeListDescriptors, booleanNodeOutputs, List.mem_map] at hcode
  obtain ⟨atom, hatom, rfl⟩ := hcode
  have hatomWidth : natBitLength atom ≤ 3 * natBitLength raw := by
    rw [booleanNodeListAtoms] at hatom
    exact natBitLength_le_of_mem_atoms hatom
  have hpositive := one_le_natBitLength atom
  have hfields :
      ∀ value ∈ taggedNatFieldOutputs atom,
        natBitLength value ≤ 4 * natBitLength atom := by
    intro value hvalue
    exact natBitLength_le_of_mem_taggedNatFieldOutputs hvalue
  have hdescriptor :=
    natBitLength_booleanNodeStructuralDescriptor_le (taggedNatFieldOutputs atom)
      (4 * natBitLength atom) (by omega) hfields
  rw [booleanNodeStructuralOutput]
  omega

/-- **The node-list normalizer, at a request-independent coefficient.** -/
theorem exists_booleanNodeListNormalizeFuel_polyBounded (rawCoefficient : ℕ) :
    ∃ normalizeCoefficient : ℕ, ∀ raw measure : ℕ,
      PolyBounded (natBitLength raw) measure rawCoefficient 1 →
      PolyBounded (booleanNodeListNormalizeFuel raw) measure
        normalizeCoefficient 2 := by
  exact ⟨_, fun raw measure hraw => by
  have hcanonicality :=
    balancedCanonicalityFuel_polyBounded
      (hraw.degree_mono (show (1 : ℕ) ≤ 2 by omega))
      ((polyBounded_natBitLength_encodeBalancedList_atoms hraw).degree_mono
        (show 1 + 1 ≤ 2 by omega))
  have hnodes :=
    (polyBounded_rawBalancedTraversalTree_nodeCount hraw).degree_mono
      (show (1 : ℕ) ≤ 2 by omega)
  exact forkCallFuel_polyBounded (first := balancedCanonicalityProgram)
    (second := balancedRawCanonicalizeProgram) hcanonicality
    (balancedRawCanonicalizeFuel_polyBounded hnodes)⟩

/-- **The node-list validator, at a request-independent coefficient.** -/
theorem exists_booleanNodeListValidationFuel_polyBounded
    (rawCoefficient arityCoefficient : ℕ) :
    ∃ nodeCoefficient : ℕ, ∀ inputLength raw measure : ℕ,
      PolyBounded (natBitLength raw) measure rawCoefficient 1 →
      PolyBounded (natBitLength inputLength) measure arityCoefficient 2 →
      PolyBounded (booleanNodeListValidationFuel inputLength raw) measure
        nodeCoefficient 3 := by
  obtain ⟨normalizeBudget, hnormalizeBudget⟩ :=
    exists_booleanNodeListNormalizeFuel_polyBounded rawCoefficient
  obtain ⟨preparationBudget, hpreparationBudget⟩ :=
    exists_booleanCircuitPreparationFuel_polyBounded
  obtain ⟨rangeBudget, hrangeBudget⟩ :=
    exists_booleanNodeTopologyRangeFuel_polyBounded (2 * rawCoefficient)
      (96 * rawCoefficient + 24 + arityCoefficient) 1 2 (by omega)
  obtain ⟨normalize, hnormalize⟩ :
      ∃ value : ℕ, ∀ raw measure : ℕ,
        PolyBounded (natBitLength raw) measure rawCoefficient 1 →
        PolyBounded (booleanNodeListNormalizeFuel raw) measure value 3 :=
    ⟨_, fun raw measure hraw =>
      (hnormalizeBudget raw measure hraw).degree_mono (by omega)⟩
  obtain ⟨prepare, hprepare⟩ :
      ∃ value : ℕ, ∀ inputLength raw measure : ℕ,
        PolyBounded (natBitLength raw) measure rawCoefficient 1 →
        PolyBounded (booleanNodeListPrepareFuel inputLength raw) measure value
          3 :=
    ⟨_, fun inputLength raw measure hraw =>
      booleanNodeListPrepareFuel_polyBounded
        ((polyBounded_of_unitBudget preparationBudget 3 hraw
          (hpreparationBudget inputLength raw)).degree_mono (by omega))⟩
  obtain ⟨topology, htopology⟩ :
      ∃ value : ℕ, ∀ inputLength raw measure : ℕ,
        PolyBounded (natBitLength raw) measure rawCoefficient 1 →
        PolyBounded (natBitLength inputLength) measure arityCoefficient 2 →
        PolyBounded (booleanNodeListTopologyFuel inputLength raw) measure value
          3 :=
    ⟨_, fun inputLength raw measure hraw harity =>
      booleanNodeListTopologyFuel_polyBounded
        ((hrangeBudget inputLength (booleanNodeListDescriptors raw)
            (96 * natBitLength raw + 24 + natBitLength inputLength) measure
            (by omega)
            (by
              intro code hcode
              have hwidth :=
                natBitLength_le_of_mem_booleanNodeListDescriptors hcode
              omega)
            (by omega)
            (by
              have hsucc :=
                natBitLength_le_succ (booleanNodeListDescriptors raw).length
              have hatoms := rawBalancedTraversalTree_atoms_length_succ_le raw
              have hlength :
                  (booleanNodeListDescriptors raw).length =
                    (rawBalancedTraversalTree raw).atoms.length := by
                simp only [booleanNodeListDescriptors, booleanNodeOutputs,
                  List.length_map, booleanNodeListAtoms]
              omega)
            (by
              refine (hraw.const_mul 2).mono ?_
              have hatoms := rawBalancedTraversalTree_atoms_length_succ_le raw
              have hlength :
                  (booleanNodeListDescriptors raw).length =
                    (rawBalancedTraversalTree raw).atoms.length := by
                simp only [booleanNodeListDescriptors, booleanNodeOutputs,
                  List.length_map, booleanNodeListAtoms]
              omega)
            ((((hraw.degree_mono (by omega)).const_mul 96).add
              (polyBounded_const 24 measure 2)).add harity)).degree_mono
          (by omega))⟩
  obtain ⟨equality, hequality⟩ :
      ∃ value : ℕ, ∀ inputLength raw measure : ℕ,
        PolyBounded (natBitLength raw) measure rawCoefficient 1 →
        PolyBounded (booleanNodeListTopologyEqualityFuel inputLength raw) measure
          value 3 :=
    ⟨_, fun inputLength raw measure hraw =>
      (booleanNodeListTopologyEqualityFuel_polyBounded_of_width
        hraw).degree_mono (by omega)⟩
  obtain ⟨stage, hstage⟩ :
      ∃ value : ℕ,
        max (max normalize prepare) (max (max topology equality) 10) = value :=
    ⟨_, rfl⟩
  exact ⟨_, fun inputLength raw measure hraw harity => by
  have hgate :
      PolyBounded booleanNodeListValidationGateFuel measure stage 3 :=
    PolyBounded.of_le_coefficient
      (by simp only [booleanNodeListValidationGateFuel]; omega)
  have h₇ : PolyBounded 7 measure stage 3 :=
    PolyBounded.of_le_coefficient (by omega)
  have node₆ :=
    linkFuel_polyBounded (second := nodeChainTail₆)
      ((hequality inputLength raw measure hraw).coefficient_mono
        (show equality ≤ stage by omega)) hgate
  have node₅ := linkFuel_polyBounded (second := nodeChainTail₅) h₇ node₆
  have node₄ :=
    linkFuel_polyBounded (second := nodeChainTail₄)
      ((htopology inputLength raw measure hraw harity).coefficient_mono
        (show topology ≤ stage by omega)) node₅
  have node₃ := linkFuel_polyBounded (second := nodeChainTail₃) h₇ node₄
  have node₂ :=
    linkFuel_polyBounded (second := nodeChainTail₂)
      ((hprepare inputLength raw measure hraw).coefficient_mono
        (show prepare ≤ stage by omega)) node₃
  exact linkFuel_polyBounded (second := nodeChainTail₁)
    ((hnormalize raw measure hraw).coefficient_mono
      (show normalize ≤ stage by omega)) node₂⟩

/-! ## §4 The Boolean circuit validator, and `hcircuit`

`booleanCircuitValidationFuel` is §3's charge under a wrapper, plus the
canonical natural stage and the comparison stage, both of which sit at the raw
code's own degree.  The whole charge lands at degree `3` — one inside the
published slot of `4`. -/

/-- **The Boolean circuit validator, at a request-independent coefficient.** -/
theorem exists_booleanCircuitValidationFuel_polyBounded
    (rawCoefficient arityCoefficient : ℕ) :
    ∃ circuitCoefficient : ℕ, ∀ inputLength raw measure : ℕ,
      PolyBounded (natBitLength raw) measure rawCoefficient 1 →
      PolyBounded (natBitLength inputLength) measure arityCoefficient 2 →
      PolyBounded (booleanCircuitValidationFuel inputLength raw) measure
        circuitCoefficient 3 := by
  obtain ⟨nodeListBudget, hnodeListBudget⟩ :=
    exists_booleanNodeListValidationFuel_polyBounded (8 * rawCoefficient)
      arityCoefficient
  obtain ⟨node, hnode⟩ :
      ∃ value : ℕ, ∀ inputLength raw measure : ℕ,
        PolyBounded (natBitLength raw) measure rawCoefficient 1 →
        PolyBounded (natBitLength inputLength) measure arityCoefficient 2 →
        PolyBounded (booleanCircuitNodeStageFuel inputLength raw) measure value
          3 :=
    ⟨_, fun inputLength raw measure hraw harity =>
      preserveRightFuel_polyBounded
        (hnodeListBudget inputLength (booleanCircuitNodesCode raw) measure
          ((hraw.const_mul 8).mono
            (natBitLength_booleanCircuitNodesCode_le raw))
          harity)⟩
  obtain ⟨nat, hnat⟩ :
      ∃ value : ℕ, ∀ raw measure : ℕ,
        PolyBounded (natBitLength raw) measure rawCoefficient 1 →
        PolyBounded (booleanCircuitNatStageFuel raw) measure value 3 :=
    ⟨_, fun raw measure hraw =>
      (booleanCircuitNatStageFuel_polyBounded
        ((hraw.const_mul 8).mono
          (natBitLength_booleanCircuitOutputCode_le raw))).degree_mono
        (by omega)⟩
  obtain ⟨comparison, hcomparison⟩ :
      ∃ value : ℕ, ∀ inputLength raw measure : ℕ,
        PolyBounded (natBitLength raw) measure rawCoefficient 1 →
        PolyBounded (booleanCircuitLtStageFuel inputLength raw) measure value
          3 :=
    ⟨_, fun inputLength raw measure hraw =>
      (booleanCircuitLtStageFuel_polyBounded hraw).degree_mono (by omega)⟩
  obtain ⟨tuple, htuple⟩ : ∃ value : ℕ, booleanCircuitTupleFuel = value :=
    ⟨_, rfl⟩
  obtain ⟨stage, hstage⟩ :
      ∃ value : ℕ,
        max (max node nat) (max (max comparison tuple) 15) = value := ⟨_, rfl⟩
  exact ⟨_, fun inputLength raw measure hraw harity => by
  have hgate : PolyBounded 15 measure stage 3 :=
    PolyBounded.of_le_coefficient (by omega)
  have h₈ : PolyBounded 8 measure stage 3 :=
    PolyBounded.of_le_coefficient (by omega)
  have h₇ : PolyBounded 7 measure stage 3 :=
    PolyBounded.of_le_coefficient (by omega)
  have htupleStage : PolyBounded booleanCircuitTupleFuel measure stage 3 :=
    PolyBounded.of_le_coefficient (by omega)
  have node₇ :=
    linkFuel_polyBounded (second := circuitChainTail₇)
      ((hcomparison inputLength raw measure hraw).coefficient_mono
        (show comparison ≤ stage by omega)) hgate
  have node₆ := linkFuel_polyBounded (second := circuitChainTail₆) h₈ node₇
  have node₅ :=
    linkFuel_polyBounded (second := circuitChainTail₅)
      ((hnat raw measure hraw).coefficient_mono
        (show nat ≤ stage by omega)) node₆
  have node₄ := linkFuel_polyBounded (second := circuitChainTail₄) h₇ node₅
  have node₃ :=
    linkFuel_polyBounded (second := circuitChainTail₃)
      ((hnode inputLength raw measure hraw harity).coefficient_mono
        (show node ≤ stage by omega)) node₄
  have node₂ := linkFuel_polyBounded (second := circuitChainTail₂) h₈ node₃
  exact linkFuel_polyBounded (second := circuitChainTail₁) htupleStage node₂⟩

theorem exists_hcircuit_at_computableLimits
    (profile : XorNumeralProfile)
    (copyBound oracleArity oracleSizeCap sumArity symmetricWireCap
      thresholdWireCap : ℕ → ℕ)
    (parameterCoefficient : ℕ)
    (hparameter : ∀ request : WeakVerifierRequest,
      PolyBounded
        (computableLimitsWidthParameter profile copyBound oracleArity
          oracleSizeCap sumArity symmetricWireCap thresholdWireCap
          request.inputArity)
        request.measure parameterCoefficient 1) :
    ∃ circuitCoefficient : ℕ, ∀ request : WeakVerifierRequest,
      PolyBounded
        (booleanCircuitValidationFuel
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness)))
          (handoffOracleCode
            (recoveryValidatorStructuralPrefixOutput
              (computableLimitsOf profile copyBound oracleArity oracleSizeCap
                sumArity symmetricWireCap thresholdWireCap request.inputArity)
              (encodeBitInput request.witness))))
        request.measure circuitCoefficient recoveryVerifierDegree := by
  obtain ⟨circuitBudget, hcircuitBudget⟩ :=
    exists_booleanCircuitValidationFuel_polyBounded 4
      (16 * max 4 (204800 * (parameterCoefficient + 1) ^ 2))
  exact ⟨circuitBudget, fun request => by
  have hprefix :=
    polyBounded_computableLimits_prefixWidth_of_parameter profile copyBound
      oracleArity oracleSizeCap sumArity symmetricWireCap thresholdWireCap
      (by omega : (1 : ℕ) ≤ 2) (by omega : 2 * 1 ≤ 2) hparameter request
  have hcode :=
    polyBounded_handoffOracleCode_structuralPrefixOutput
      (limits :=
        computableLimitsOf profile copyBound oracleArity oracleSizeCap sumArity
          symmetricWireCap thresholdWireCap request.inputArity)
      (polyBounded_witnessWidth request)
  have harity :=
    polyBounded_natBitLength_of_le (polyBounded_structuralPrefixOutput hprefix)
      ((Nat.unpair_left_le _).trans
        ((Nat.unpair_right_le _).trans
          ((Nat.unpair_right_le _).trans
            ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _)))))
  exact (hcircuitBudget _ _ request.measure hcode harity).degree_mono
    (by norm_num [recoveryVerifierDegree])⟩

end NearCubicWires.ValidatorCircuitLeafClosure
