import Proof.Circuits.ValidatorCompositeLeafBounds

namespace NearCubicWires.ValidatorResidualLeafBudget

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalNormalizedCircuitResourceProgram
open NearCubicWires.CanonicalRationalMassProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafFuelBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorLegalSumWalk
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

/-! ## §1 The canonical rank selector's counting ledger

The selector walks the same pending-subtree stack the nonzero counter walks,
and charges a constant per decoded node.  The requested rank is carried along
and only ever *decremented*, so it never enters the charge: the bound below is
uniform in `rank`, which is exactly what §2 needs to charge the counted call
without a per-request certificate. -/

/-- The rank selector's traversal, charged by node count — uniformly in the
requested rank. -/
theorem supplierSupportRankSelectorWorkFuel_le
    (forest : List BalancedTraversalTree) (rank : ℕ) :
    supplierSupportRankSelectorWorkFuel forest rank ≤
      15 * (forest.map BalancedTraversalTree.nodeCount).sum + 15 := by
  induction forest, rank using supplierSupportRankSelectorWorkFuel.induct with
  | case1 => simp [supplierSupportRankSelectorWorkFuel]
  | case2 rest rank inductionHypothesis =>
      simp only [supplierSupportRankSelectorWorkFuel, List.map_cons,
        List.sum_cons, BalancedTraversalTree.nodeCount]
        at inductionHypothesis ⊢
      omega
  | case3 rest rank inductionHypothesis =>
      have hstep :
          supplierSupportRankSelectorWorkFuel
              (BalancedTraversalTree.leaf 0 :: rest) rank =
            12 + supplierSupportRankSelectorWorkFuel rest rank := by
        conv_lhs => rw [supplierSupportRankSelectorWorkFuel.eq_def]
        simp
      simp only [List.map_cons, List.sum_cons,
        BalancedTraversalTree.nodeCount] at inductionHypothesis ⊢
      omega
  | case4 atom rest hatom =>
      simp only [supplierSupportRankSelectorWorkFuel, List.map_cons,
        List.sum_cons, BalancedTraversalTree.nodeCount, if_neg hatom]
      omega
  | case5 atom rest hatom nextRank inductionHypothesis =>
      simp only [supplierSupportRankSelectorWorkFuel, List.map_cons,
        List.sum_cons, BalancedTraversalTree.nodeCount, if_neg hatom]
        at inductionHypothesis ⊢
      omega
  | case6 left right rest rank inductionHypothesis =>
      simp only [supplierSupportRankSelectorWorkFuel, List.map_cons,
        List.sum_cons, BalancedTraversalTree.nodeCount]
        at inductionHypothesis ⊢
      omega

/-- **The rank selector's public charge, rank-uniformly.** -/
theorem supplierSupportRankSelectorFuel_le (support : List Bool) (rank : ℕ) :
    supplierSupportRankSelectorFuel support rank ≤ 30 * support.length + 40 := by
  have hwork :=
    supplierSupportRankSelectorWorkFuel_le
      [balancedTraversalTree (support.map boolCode)] rank
  have hnodes := balancedTraversalTree_nodeCount_le (support.map boolCode)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_map] at hwork hnodes
  unfold supplierSupportRankSelectorFuel
  omega

/-- Nonzero support indices are indices *into the support*.  Restated here as a
private counting fact: the module's own version is not exported. -/
private theorem nonzeroAtomIndicesFrom_mem_lt
    {first value : ℕ} {atoms : List ℕ}
    (hvalue : value ∈ nonzeroAtomIndicesFrom first atoms) :
    value < first + atoms.length := by
  induction atoms generalizing first with
  | nil => simp [nonzeroAtomIndicesFrom] at hvalue
  | cons atom rest inductionHypothesis =>
      by_cases hatom : atom = 0
      · have htail : value ∈ nonzeroAtomIndicesFrom (first + 1) rest := by
          simpa [nonzeroAtomIndicesFrom, hatom] using hvalue
        have := inductionHypothesis htail
        simp only [List.length_cons]
        omega
      · have hcases :
            value = first ∨ value ∈ nonzeroAtomIndicesFrom (first + 1) rest := by
          simpa [nonzeroAtomIndicesFrom, hatom] using hvalue
        rcases hcases with rfl | htail
        · simp
        · have := inductionHypothesis htail
          simp only [List.length_cons]
          omega

private theorem nonzeroAtomIndicesFrom_length_le
    (first : ℕ) (atoms : List ℕ) :
    (nonzeroAtomIndicesFrom first atoms).length ≤ atoms.length := by
  induction atoms generalizing first with
  | nil => simp [nonzeroAtomIndicesFrom]
  | cons atom rest inductionHypothesis =>
      by_cases hatom : atom = 0
      · have := inductionHypothesis (first + 1)
        simp only [nonzeroAtomIndicesFrom, if_pos hatom, List.length_cons]
        omega
      · have := inductionHypothesis (first + 1)
        simp only [nonzeroAtomIndicesFrom, if_neg hatom, List.length_cons]
        omega

/-- Every requested support index is an index into the support. -/
theorem nonzeroSupportIndices_mem_lt
    {support : List Bool} {index : ℕ}
    (hindex : index ∈ nonzeroSupportIndices support) :
    index < support.length := by
  have hmem :
      index ∈ nonzeroAtomIndicesFrom 0 (support.map boolCode) := by
    simpa only [nonzeroSupportIndices] using hindex
  have hbound :=
    nonzeroAtomIndicesFrom_mem_lt (first := 0)
      (atoms := support.map boolCode) hmem
  simpa only [Nat.zero_add, List.length_map] using hbound

theorem nonzeroSupportIndices_length_le (support : List Bool) :
    (nonzeroSupportIndices support).length ≤ support.length := by
  have hbound := nonzeroAtomIndicesFrom_length_le 0 (support.map boolCode)
  simpa only [nonzeroSupportIndices, List.length_map] using hbound

theorem nonzeroSupportCount_le_length (support : List Bool) :
    nonzeroSupportCount support ≤ support.length := by
  induction support with
  | nil => simp [nonzeroSupportCount]
  | cons bit rest inductionHypothesis =>
      have hstep : (if bit then 1 else 0) ≤ 1 := by split <;> omega
      simp only [nonzeroSupportCount, List.length_cons]
      omega

/-- The selector call's request list is counted by the support's own length. -/
theorem supplierSupportSelectorRequests_length_le
    (weights : List ℕ) (support : List Bool) :
    (supplierSupportSelectorRequests weights support).length ≤
      support.length := by
  rw [supplierSupportSelectorRequests, balancedRangeRequestAtoms_length]
  exact nonzeroSupportCount_le_length support

theorem supplierSupportSelectorCallFuelBound_polyBounded
    {weights : List ℕ} {support : List Bool}
    {measure coefficient degree : ℕ}
    (hsupport : PolyBounded support.length measure coefficient degree) :
    PolyBounded (supplierSupportSelectorCallFuelBound weights support) measure
      (37 + coefficient *
        ((balancedCallLayout supplierSupportRankSelectorProgram).calleeSpan +
          73 + (30 * coefficient + 40)))
      (degree + degree) := by
  have hcount :
      PolyBounded (supplierSupportSelectorRequests weights support).length
        measure coefficient degree :=
    hsupport.mono (supplierSupportSelectorRequests_length_le weights support)
  have hcallee :
      PolyBounded (30 * support.length + 40) measure (30 * coefficient + 40)
        degree :=
    (hsupport.const_mul 30).add (polyBounded_const 40 measure degree)
  refine balancedCallFuel_polyBounded hcount hcallee ?_
  intro request _
  rw [supplierSupportSelectorCallFuel]
  exact supplierSupportRankSelectorFuel_le support _

/-- The lookup call's request list is the nonzero support index list. -/
theorem supplierSupportLookupRequests_length_le
    (weights : List ℕ) (support : List Bool) :
    (supplierSupportLookupRequests weights support).length ≤
      support.length := by
  rw [supplierSupportLookupRequests, List.length_map]
  exact nonzeroSupportIndices_length_le support

/-- The lookup request's index projection, restated: both the projection and
the request constructor are public, so this is a definitional unfolding. -/
private theorem supplierSupportLookupRequestIndex_request'
    (inputLength weightsCode index : ℕ) :
    supplierSupportLookupRequestIndex
        (supplierSupportLookupRequest inputLength weightsCode index) =
      index := by
  simp only [supplierSupportLookupRequestIndex, supplierSupportLookupRequest,
    nativeInputRequest, Nat.unpair_pair]

theorem supplierSupportLookupCallFuelBound_polyBounded
    {weights : List ℕ} {support : List Bool}
    {measure coefficient degree : ℕ}
    (hsupport : PolyBounded support.length measure coefficient degree)
    (hweights : PolyBounded weights.length measure coefficient degree)
    (hlength : weights.length = support.length) :
    PolyBounded (supplierSupportLookupCallFuelBound weights support) measure
      (37 + coefficient *
        ((balancedCallLayout canonicalBalancedLookupProgram).calleeSpan + 73 +
          (27 * coefficient + 27)))
      (degree + degree) := by
  have hcount :
      PolyBounded (supplierSupportLookupRequests weights support).length
        measure coefficient degree :=
    hsupport.mono (supplierSupportLookupRequests_length_le weights support)
  have hcallee :
      PolyBounded (27 * (weights.length + 1)) measure (27 * coefficient + 27)
        degree := by
    refine ((hweights.const_mul 27).add
      (polyBounded_const 27 measure degree)).mono ?_
    omega
  refine balancedCallFuel_polyBounded hcount hcallee ?_
  intro request hrequest
  rw [supplierSupportLookupRequests, List.mem_map] at hrequest
  obtain ⟨index, hindex, rfl⟩ := hrequest
  have hlt : index < weights.length := by
    have := nonzeroSupportIndices_mem_lt hindex
    omega
  rw [supplierSupportLookupCallFuel, supplierSupportLookupRequestIndex_request']
  exact balancedLookupFuel_le weights index hlt

/-! ### The compression pipeline

Five nodes: the shared count preparation, the generated range builder, the two
counted calls above under their context-preserving wrappers, and one closed
numeral.  Only the two counted calls raise the degree, and each raises it by
exactly the support-count's degree. -/

/-- The count preparation's charge, as an ordinary linear function of the
support's length. -/
theorem supplierSupportCountPrepareFuel_le (support : List Bool) :
    supplierSupportCountPrepareFuel support ≤ 30 * support.length + 27 := by
  have hforest :=
    supplierSupportCountWorkFuel_le
      [balancedTraversalTree (support.map boolCode)]
  have hnodes := balancedTraversalTree_nodeCount_le (support.map boolCode)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_map] at hforest hnodes
  unfold supplierSupportCountPrepareFuel
  omega

/-- **The support-compression pipeline, dominated at degree `2d`.** -/
theorem supplierSupportCompressionFuel_polyBounded
    {weights : List ℕ} {support : List Bool}
    {measure coefficient degree : ℕ}
    (hsupport : PolyBounded support.length measure coefficient degree)
    (hweights : PolyBounded weights.length measure coefficient degree)
    (hlength : weights.length = support.length) :
    ∃ compressionCoefficient : ℕ,
      PolyBounded (supplierSupportCompressionFuel weights support) measure
        compressionCoefficient (degree + degree) := by
  have hraise : degree ≤ degree + degree := by omega
  have hprepare :
      PolyBounded (supplierSupportCountPrepareFuel support) measure
        (30 * coefficient + 27) (degree + degree) :=
    (((hsupport.const_mul 30).add
      (polyBounded_const 27 measure degree)).mono
      (supplierSupportCountPrepareFuel_le support)).degree_mono hraise
  have hrange :
      PolyBounded
        (generatedBalancedRangeFuel weights.length
          (nonzeroSupportCount support)
          (supplierSupportRangeContext weights support)) measure
        (42 * coefficient + 42) (degree + degree) := by
    refine ((((hsupport.const_mul 42).add
      (polyBounded_const 42 measure degree)).degree_mono hraise)).mono ?_
    have hcount := nonzeroSupportCount_le_length support
    have hbound :=
      generatedBalancedRangeFuel_le_linear weights.length
        (nonzeroSupportCount support)
        (supplierSupportRangeContext weights support)
    omega
  have hselector :=
    preserveRightFuel_polyBounded
      (supplierSupportSelectorCallFuelBound_polyBounded
        (weights := weights) hsupport)
  have hlookup :=
    preserveRightFuel_polyBounded
      (supplierSupportLookupCallFuelBound_polyBounded hsupport hweights hlength)
  have hnode₁ :=
    linkFuel_polyBounded (second := generatedBalancedRangeProgram) hprepare
      hrange
  have hnode₂ :=
    linkFuel_polyBounded
      (second :=
        preserveRightProgram
          (balancedCallProgram supplierSupportRankSelectorProgram))
      hnode₁ hselector
  have hnode₃ :=
    linkFuel_polyBounded
      (second :=
        preserveRightProgram
          (balancedCallProgram canonicalBalancedLookupProgram))
      hnode₂ hlookup
  exact ⟨_,
    linkFuel_polyBounded (second := supplierSupportProjectionProgram) hnode₃
      (polyBounded_const 5 measure (degree + degree))⟩

/-- The compressed weight vector is no longer than the weight vector. -/
theorem supportedWeights_length_le (weights : List ℕ) (support : List Bool) :
    (supportedWeights weights support).length ≤ weights.length := by
  induction weights generalizing support with
  | nil => cases support <;> simp [supportedWeights]
  | cons weight rest inductionHypothesis =>
      cases support with
      | nil => simp [supportedWeights]
      | cons bit tail =>
          have := inductionHypothesis (support := tail)
          by_cases hbit : bit
          · simp only [supportedWeights, if_pos hbit, List.length_cons]
            omega
          · simp only [supportedWeights, if_neg hbit, List.length_cons]
            omega

@[simp] theorem normalizedGateWireMetrics_length (summaries : List ℕ) :
    (normalizedGateWireMetrics summaries).length = summaries.length := by
  simp [normalizedGateWireMetrics]

/-- **The threshold wire metric, dominated at the guard's degree.** -/
theorem normalizedCircuitThresholdWireFuel_polyBounded
    {inputLength : ℕ} {summaries : List ℕ} {membership : List Bool}
    {measure coefficient guardCoefficient degree : ℕ}
    (hraw :
      PolyBounded (natBitLength (encodeBalancedList summaries)) measure
        coefficient degree)
    (hguard :
      PolyBounded
        (balancedValidationMapGuardFuel (encodeBalancedList summaries)) measure
        guardCoefficient (degree + degree))
    (hlength : summaries.length = membership.length) :
    ∃ thresholdCoefficient : ℕ,
      PolyBounded
        (normalizedCircuitThresholdWireFuel inputLength summaries membership)
        measure thresholdCoefficient (degree + degree) := by
  have hraise : degree ≤ degree + degree := by omega
  have hsummaries :
      PolyBounded summaries.length measure (2 * coefficient) degree :=
    polyBounded_length_of_encodeBalancedList_width hraw
  have hmembership :
      PolyBounded membership.length measure (2 * coefficient) degree := by
    rw [← hlength]
    exact hsummaries
  have hweights :
      PolyBounded (normalizedGateWireMetrics summaries).length measure
        (2 * coefficient) degree := by
    rw [normalizedGateWireMetrics_length]
    exact hsummaries
  have hmapEq :
      normalizedCircuitThresholdMapFuel inputLength summaries =
        preserveRightFuel
          (normalizedGateWireMetricMapFuel inputLength summaries) := rfl
  have hmap :=
    (preserveRightFuel_polyBounded
      (normalizedGateWireMetricMapFuel_polyBounded
        (inputLength := inputLength) hraw hguard)).mono (le_of_eq hmapEq)
  obtain ⟨compressionCoefficient, hcompression⟩ :=
    supplierSupportCompressionFuel_polyBounded (support := membership)
      hmembership hweights (by rw [normalizedGateWireMetrics_length, hlength])
  have hcall :
      PolyBounded
        (normalizedCircuitThresholdCompressionFuel summaries membership) measure
        (nativeCallOverhead supplierSupportCompressionProgram +
          compressionCoefficient) (degree + degree) := by
    rw [normalizedCircuitThresholdCompressionFuel]
    exact ((polyBounded_const
      (nativeCallOverhead supplierSupportCompressionProgram) measure
      (degree + degree)).add hcompression).mono (nativeCallFuel_le _ _ _ _)
  have hsum :
      PolyBounded
        (balancedNatSumFuel
          (supportedWeights (normalizedGateWireMetrics summaries) membership))
        measure (71 * (2 * coefficient) + 37) (degree + degree) := by
    refine ((((hweights.const_mul 71).add
      (polyBounded_const 37 measure degree)).degree_mono hraise)).mono ?_
    have hlengths :=
      supportedWeights_length_le (normalizedGateWireMetrics summaries)
        membership
    have hbound :=
      balancedNatSumFuel_le_linear
        (supportedWeights (normalizedGateWireMetrics summaries) membership)
    omega
  have hnode₁ :=
    linkFuel_polyBounded
      (second := normalizedCircuitThresholdCompressionPrepareProgram) hmap
      (polyBounded_const normalizedCircuitThresholdCompressionPrepareFuel
        measure (degree + degree))
  have hnode₂ :=
    linkFuel_polyBounded
      (second := normalizedCircuitThresholdCompressionProgram) hnode₁ hcall
  have hnode₃ :=
    linkFuel_polyBounded
      (second := normalizedCircuitThresholdProjectionProgram) hnode₂
      (polyBounded_const normalizedCircuitThresholdProjectionFuel measure
        (degree + degree))
  exact ⟨_,
    linkFuel_polyBounded (second := balancedNatSumProgram) hnode₃ hsum⟩

/-- **The threshold resource metric, dominated.**  The mirror of
`normalizedCircuitResourceFuel_polyBounded_symmetric`: a width certificate for
the bottom summary code, plus the decoded-length agreement the branch's own run
theorem already requires. -/
theorem normalizedCircuitResourceFuel_polyBounded_threshold
    {inputLength summary measure coefficient degree : ℕ}
    (htag : normalizedCircuitResourceBranchTag summary ≠ 0)
    (hcode :
      PolyBounded
        (natBitLength (normalizedCircuitResourceBottomSummariesCode summary))
        measure coefficient degree)
    (hlength :
      (normalizedCircuitResourceSummaries summary).length =
        (normalizedCircuitResourceMembership summary).length) :
    ∃ resourceCoefficient : ℕ,
      PolyBounded (normalizedCircuitResourceFuel inputLength summary) measure
        resourceCoefficient (degree + degree) := by
  have hraw :
      PolyBounded
        (natBitLength
          (encodeBalancedList (normalizedCircuitResourceSummaries summary)))
        measure coefficient degree :=
    hcode.mono
      (natBitLength_mono
        (encodeBalancedList_getD_le
          (normalizedCircuitResourceBottomSummariesCode summary)))
  obtain ⟨guardCoefficient, hguard⟩ :=
    balancedValidationMapGuardFuel_degree hraw
  obtain ⟨thresholdCoefficient, hbranch⟩ :=
    normalizedCircuitThresholdWireFuel_polyBounded (inputLength := inputLength)
      hraw hguard hlength
  have hfamilyEq :
      normalizedCircuitResourceFamilyFuel inputLength summary =
        taggedProgramChoiceFuel
          (normalizedCircuitThresholdWireFuel inputLength
            (normalizedCircuitResourceSummaries summary)
            (normalizedCircuitResourceMembership summary)) := by
    unfold normalizedCircuitResourceFamilyFuel
    rw [if_neg htag]
  have hfamily :=
    (taggedProgramChoiceFuel_polyBounded hbranch).mono (le_of_eq hfamilyEq)
  exact ⟨_,
    linkFuel_polyBounded (second := normalizedCircuitResourceFamilyProgram)
      (polyBounded_const normalizedCircuitResourcePrepareFuel measure
        (degree + degree))
      hfamily⟩

theorem normalizedCircuitResourceFuel_polyBounded
    {inputLength summary measure coefficient degree : ℕ}
    (hcode :
      PolyBounded
        (natBitLength (normalizedCircuitResourceBottomSummariesCode summary))
        measure coefficient degree)
    (hlength :
      (normalizedCircuitResourceSummaries summary).length =
        (normalizedCircuitResourceMembership summary).length) :
    ∃ resourceCoefficient : ℕ,
      PolyBounded (normalizedCircuitResourceFuel inputLength summary) measure
        resourceCoefficient (degree + degree) := by
  by_cases htag : normalizedCircuitResourceBranchTag summary = 0
  · exact normalizedCircuitResourceFuel_polyBounded_symmetric htag hcode
  · exact normalizedCircuitResourceFuel_polyBounded_threshold htag hcode hlength

/-- **The accumulation lemma.**  One fold step widens the accumulator's
denominator by at most the summary's denominator width: the step multiplies the
two denominators, and a product's width is subadditive.  On the rejecting branch
the accumulator collapses to `0`, whose width is minimal. -/
theorem rationalMassStep_denominator_natBitLength_le
    (accumulator summary : ℕ) :
    natBitLength (Nat.unpair (rationalMassStep accumulator summary)).2 ≤
      natBitLength (Nat.unpair accumulator).2 +
        natBitLength (rationalSummaryDenominator summary) := by
  unfold rationalMassStep
  split
  · simp only [Nat.unpair_pair]
    exact natBitLength_mul_le _ _
  · have haccumulator := one_le_natBitLength (Nat.unpair accumulator).2
    have hsummary := one_le_natBitLength (rationalSummaryDenominator summary)
    have hzero : natBitLength (Nat.unpair 0).2 = 1 := by
      simp only [Nat.unpair_zero]
      exact natBitLength_zero
    omega

theorem rationalMassFoldLeafSteps_le_of_denominatorCaps
    {cap bound leafCap : ℕ}
    (hleaf : ∀ accumulator summary,
      natBitLength (Nat.unpair accumulator).2 ≤ bound →
      natBitLength (rationalSummaryDenominator summary) ≤ cap →
      rationalMassFoldLeafBudget accumulator summary ≤ leafCap) :
    ∀ (summaries : List ℕ) (accumulator : ℕ),
      (∀ summary ∈ summaries,
        natBitLength (rationalSummaryDenominator summary) ≤ cap) →
      natBitLength (Nat.unpair accumulator).2 + summaries.length * cap ≤
        bound →
      balancedFoldLeafSteps rationalMassStep rationalMassFoldLeafBudget
          accumulator summaries ≤ summaries.length * leafCap := by
  intro summaries
  induction summaries with
  | nil =>
      intro accumulator _ _
      simp [balancedFoldLeafSteps]
  | cons summary rest inductionHypothesis =>
      intro accumulator hcaps hbound
      have hexpandCap : (rest.length + 1) * cap = rest.length * cap + cap := by
        ring
      have hexpandLeaf :
          (rest.length + 1) * leafCap = rest.length * leafCap + leafCap := by
        ring
      simp only [List.length_cons] at hbound
      have hhead : natBitLength (rationalSummaryDenominator summary) ≤ cap :=
        hcaps summary List.mem_cons_self
      have haccumulator : natBitLength (Nat.unpair accumulator).2 ≤ bound := by
        omega
      have hcharge := hleaf accumulator summary haccumulator hhead
      have hgrow :=
        rationalMassStep_denominator_natBitLength_le accumulator summary
      have htail :
          natBitLength
              (Nat.unpair (rationalMassStep accumulator summary)).2 +
            rest.length * cap ≤ bound := by
        omega
      have hrest :=
        inductionHypothesis (rationalMassStep accumulator summary)
          (fun value hvalue => hcaps value (List.mem_cons_of_mem _ hvalue))
          htail
      simp only [balancedFoldLeafSteps, List.length_cons]
      omega

theorem rationalMassFoldFuel_le_of_denominatorCaps
    {summaries : List ℕ} {cap bound leafCap : ℕ}
    (hleaf : ∀ accumulator summary,
      natBitLength (Nat.unpair accumulator).2 ≤ bound →
      natBitLength (rationalSummaryDenominator summary) ≤ cap →
      rationalMassFoldLeafBudget accumulator summary ≤ leafCap)
    (hcaps : ∀ summary ∈ summaries,
      natBitLength (rationalSummaryDenominator summary) ≤ cap)
    (hbudget : 1 + summaries.length * cap ≤ bound) :
    rationalMassFoldFuel summaries ≤
      70 * summaries.length + 37 + summaries.length * leafCap := by
  have hinitial :
      natBitLength (Nat.unpair rationalMassInitialAccumulator).2 = 1 := by
    simp only [rationalMassInitialAccumulator, Nat.unpair_pair]
    exact natBitLength_one
  have hstructural := balancedTraversalStructuralSteps_le_linear summaries
  have hleaves :=
    rationalMassFoldLeafSteps_le_of_denominatorCaps hleaf summaries
      rationalMassInitialAccumulator hcaps (by omega)
  unfold rationalMassFoldFuel
  omega

theorem rationalMassFoldFuel_polyBounded_of_denominatorCaps
    {summaries : List ℕ}
    {measure cap bound leafCap countCoefficient leafCoefficient countDegree
      leafDegree : ℕ}
    (hleaf : ∀ accumulator summary,
      natBitLength (Nat.unpair accumulator).2 ≤ bound →
      natBitLength (rationalSummaryDenominator summary) ≤ cap →
      rationalMassFoldLeafBudget accumulator summary ≤ leafCap)
    (hcaps : ∀ summary ∈ summaries,
      natBitLength (rationalSummaryDenominator summary) ≤ cap)
    (hbudget : 1 + summaries.length * cap ≤ bound)
    (hcount : PolyBounded summaries.length measure countCoefficient countDegree)
    (hleafCap : PolyBounded leafCap measure leafCoefficient leafDegree) :
    PolyBounded (rationalMassFoldFuel summaries) measure
      (70 * countCoefficient + 37 + countCoefficient * leafCoefficient)
      (countDegree + leafDegree) := by
  have hstructural :
      PolyBounded (70 * summaries.length + 37) measure
        (70 * countCoefficient + 37) (countDegree + leafDegree) :=
    ((hcount.const_mul 70).add
      (polyBounded_const 37 measure countDegree)).degree_mono (by omega)
  have hproduct := hcount.mul hleafCap
  exact (hstructural.add hproduct).mono
    (rationalMassFoldFuel_le_of_denominatorCaps hleaf hcaps hbudget)

def massLeafChainTail₇ : NPOracleProgram := rationalMassLeafFinalProgram

def massLeafChainTail₆ : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitSerialMulProgram) massLeafChainTail₇

def massLeafChainTail₅ : NPOracleProgram :=
  linkPrograms rationalMassDenominatorLoweringProgram massLeafChainTail₆

def massLeafChainTail₄ : NPOracleProgram :=
  linkPrograms rationalMassNumeratorProgram massLeafChainTail₅

def massLeafChainTail₃ : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitSerialMulProgram) massLeafChainTail₄

def massLeafChainTail₂ : NPOracleProgram :=
  linkPrograms rationalMassSecondLoweringProgram massLeafChainTail₃

def massLeafChainTail₁ : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitSerialMulProgram) massLeafChainTail₂

def massLeafCoefficient (accumulatorCoefficient summaryCoefficient : ℕ) : ℕ :=
  programRegisterSpan massLeafChainTail₁ + 5 + 16 +
    (programRegisterSpan massLeafChainTail₂ + 5 +
        (8 * summaryCoefficient + 5 + 4) +
      (programRegisterSpan massLeafChainTail₃ + 5 + 9 +
        (programRegisterSpan massLeafChainTail₄ + 5 +
            (8 * accumulatorCoefficient + 5 + 4) +
          (programRegisterSpan massLeafChainTail₅ + 5 + 7 +
            (programRegisterSpan massLeafChainTail₆ + 5 + 8 +
              (programRegisterSpan massLeafChainTail₇ + 5 +
                  (8 * summaryCoefficient + 5 + 4) + 12))))))

theorem rationalMassLeafFuel_polyBounded
    {accumulator summary measure accumulatorCoefficient summaryCoefficient
      degree : ℕ}
    (haccumulator :
      PolyBounded (natBitLength (Nat.unpair accumulator).2) measure
        accumulatorCoefficient degree)
    (hsummary :
      PolyBounded (natBitLength (rationalSummaryDenominator summary)) measure
        summaryCoefficient degree) :
    PolyBounded (rationalMassLeafFuel accumulator summary) measure
      (massLeafCoefficient accumulatorCoefficient summaryCoefficient) degree := by
  have hfinalBound : rationalMassLeafFinalFuel summary ≤ 12 := by
    unfold rationalMassLeafFinalFuel
    split
    · omega
    · split <;> omega
  have hfinal : PolyBounded (rationalMassLeafFinalFuel summary) measure 12 degree :=
    (polyBounded_const 12 measure degree).mono hfinalBound
  have hdenominator :=
    preserveRightFuel_polyBounded (bitSerialMulFuel_polyBounded hsummary)
  have haccumulatorMul :=
    preserveRightFuel_polyBounded (bitSerialMulFuel_polyBounded haccumulator)
  have node₇ :=
    linkFuel_polyBounded (second := massLeafChainTail₇) hdenominator hfinal
  have node₆ :=
    linkFuel_polyBounded (second := massLeafChainTail₆)
      (polyBounded_const 8 measure degree) node₇
  have node₅ :=
    linkFuel_polyBounded (second := massLeafChainTail₅)
      (polyBounded_const 7 measure degree) node₆
  have node₄ :=
    linkFuel_polyBounded (second := massLeafChainTail₄) haccumulatorMul node₅
  have node₃ :=
    linkFuel_polyBounded (second := massLeafChainTail₃)
      (polyBounded_const 9 measure degree) node₄
  have node₂ :=
    linkFuel_polyBounded (second := massLeafChainTail₂) hdenominator node₃
  exact linkFuel_polyBounded (second := massLeafChainTail₁)
    (polyBounded_const 16 measure degree) node₂

theorem rationalMassLeafFuel_le_of_widths
    {accumulator summary bound cap : ℕ}
    (haccumulator : natBitLength (Nat.unpair accumulator).2 ≤ bound)
    (hsummary : natBitLength (rationalSummaryDenominator summary) ≤ cap) :
    rationalMassLeafFuel accumulator summary ≤ massLeafCoefficient bound cap := by
  have hbounded :=
    rationalMassLeafFuel_polyBounded (measure := 0) (degree := 0)
      (PolyBounded.of_le_coefficient haccumulator)
      (PolyBounded.of_le_coefficient hsummary)
  unfold PolyBounded at hbounded
  rw [pow_zero, Nat.mul_one] at hbounded
  exact hbounded

private theorem le_massLeafBudgetLedger
    (calleeSpan leafFuel leafBound : ℕ) (hleaf : leafFuel ≤ leafBound) :
    calleeSpan + 2 + leafFuel + 1 ≤ calleeSpan + 3 + leafBound := by
  omega

def massLeafBudgetCap (bound cap : ℕ) : ℕ :=
  rationalMassFoldLayout.calleeSpan + 3 + massLeafCoefficient bound cap

theorem rationalMassFoldLeafBudget_le_of_widths
    {accumulator summary bound cap : ℕ}
    (haccumulator : natBitLength (Nat.unpair accumulator).2 ≤ bound)
    (hsummary : natBitLength (rationalSummaryDenominator summary) ≤ cap) :
    rationalMassFoldLeafBudget accumulator summary ≤
      massLeafBudgetCap bound cap :=
  le_massLeafBudgetLedger _ _ _
    (rationalMassLeafFuel_le_of_widths haccumulator hsummary)

theorem rationalMassFoldFuel_le_of_summaryCaps
    {summaries : List ℕ} {cap : ℕ}
    (hcaps : ∀ summary ∈ summaries,
      natBitLength (rationalSummaryDenominator summary) ≤ cap) :
    rationalMassFoldFuel summaries ≤
      70 * summaries.length + 37 +
        summaries.length *
          massLeafBudgetCap (1 + summaries.length * cap) cap :=
  rationalMassFoldFuel_le_of_denominatorCaps
    (fun _ _ haccumulator hsummary =>
      rationalMassFoldLeafBudget_le_of_widths haccumulator hsummary)
    hcaps le_rfl

/-- **The rational mass fold, dominated from the caps alone.** -/
theorem rationalMassFoldFuel_polyBounded_of_summaryCaps
    {summaries : List ℕ}
    {measure cap countCoefficient leafCoefficient countDegree leafDegree : ℕ}
    (hcaps : ∀ summary ∈ summaries,
      natBitLength (rationalSummaryDenominator summary) ≤ cap)
    (hcount : PolyBounded summaries.length measure countCoefficient countDegree)
    (hleafCap :
      PolyBounded (massLeafBudgetCap (1 + summaries.length * cap) cap) measure
        leafCoefficient leafDegree) :
    PolyBounded (rationalMassFoldFuel summaries) measure
      (70 * countCoefficient + 37 + countCoefficient * leafCoefficient)
      (countDegree + leafDegree) :=
  rationalMassFoldFuel_polyBounded_of_denominatorCaps
    (fun _ _ haccumulator hsummary =>
      rationalMassFoldLeafBudget_le_of_widths haccumulator hsummary)
    hcaps le_rfl hcount hleafCap

/-! ### The mass stage's own charge

`initializedRationalMassFoldFuel` is the fold's charge one step past the
accumulator installation, and `recoveryLegalTermMassFoldStageFuel` is that under
a context-preserving wrapper.  With the fold's budget derived, the validator's
mass fold stage closes from the summaries' denominator caps alone. -/

/-- **The validator's mass fold stage, dominated.** -/
theorem recoveryLegalTermMassFoldStageFuel_polyBounded_of_denominatorCaps
    {inputLength bitCapStage : ℕ}
    {measure cap bound leafCap countCoefficient leafCoefficient countDegree
      leafDegree : ℕ}
    (hleaf : ∀ accumulator summary,
      natBitLength (Nat.unpair accumulator).2 ≤ bound →
      natBitLength (rationalSummaryDenominator summary) ≤ cap →
      rationalMassFoldLeafBudget accumulator summary ≤ leafCap)
    (hcaps : ∀ summary ∈
        recoveryLegalTermMassSummaries inputLength bitCapStage,
      natBitLength (rationalSummaryDenominator summary) ≤ cap)
    (hbudget :
      1 + (recoveryLegalTermMassSummaries inputLength bitCapStage).length *
        cap ≤ bound)
    (hcount :
      PolyBounded
        (recoveryLegalTermMassSummaries inputLength bitCapStage).length measure
        countCoefficient countDegree)
    (hleafCap : PolyBounded leafCap measure leafCoefficient leafDegree) :
    PolyBounded
      (recoveryLegalTermMassFoldStageFuel inputLength bitCapStage) measure
      (70 * countCoefficient + 37 + countCoefficient * leafCoefficient + 1 + 4)
      (countDegree + leafDegree) := by
  have hfold :=
    rationalMassFoldFuel_polyBounded_of_denominatorCaps hleaf hcaps hbudget
      hcount hleafCap
  have hinitialized :
      PolyBounded
        (initializedRationalMassFoldFuel
          (recoveryLegalTermMassSummaries inputLength bitCapStage)) measure
        (70 * countCoefficient + 37 + countCoefficient * leafCoefficient + 1)
        (countDegree + leafDegree) := by
    rw [initializedRationalMassFoldFuel]
    exact hfold.add (polyBounded_const 1 measure (countDegree + leafDegree))
  exact preserveRightFuel_polyBounded hinitialized

/-- The innermost linked tail of the circuit validator's chain. -/
def circuitChainTail₇ : NPOracleProgram := booleanCircuitValidationGateProgram

def circuitChainTail₆ : NPOracleProgram :=
  linkPrograms booleanCircuitLtStageProgram circuitChainTail₇

def circuitChainTail₅ : NPOracleProgram :=
  linkPrograms booleanCircuitLtLoweringProgram circuitChainTail₆

def circuitChainTail₄ : NPOracleProgram :=
  linkPrograms booleanCircuitNatStageProgram circuitChainTail₅

def circuitChainTail₃ : NPOracleProgram :=
  linkPrograms booleanCircuitNatLoweringProgram circuitChainTail₄

def circuitChainTail₂ : NPOracleProgram :=
  linkPrograms booleanCircuitNodeStageProgram circuitChainTail₃

/-- The outermost linked tail of the circuit validator's chain. -/
def circuitChainTail₁ : NPOracleProgram :=
  linkPrograms booleanCircuitFieldProjectionProgram circuitChainTail₂

/-- **The canonical natural stage, closed.**  This is the one charge of the
circuit validator that `ValidatorCompositeLeafBounds` already discharged: it is
one `canonicalNatValidationFuel` under a context-preserving wrapper, so it sits
at the width anchor's own degree. -/
theorem booleanCircuitNatStageFuel_polyBounded
    {raw measure coefficient degree : ℕ}
    (hcode :
      PolyBounded (natBitLength (booleanCircuitOutputCode raw)) measure
        coefficient degree) :
    PolyBounded (booleanCircuitNatStageFuel raw) measure
      (canonicalNatValidationCoefficient coefficient + 4) degree :=
  preserveRightFuel_polyBounded (canonicalNatValidationFuel_polyBounded hcode)

/-- **The circuit validator's chain, dominated.**  Four of its eight charges are
closed numerals absorbed by the stage coefficient; the natural stage is closed
above; the node stage and the comparison stage are the walk's residue. -/
theorem booleanCircuitValidationFuel_polyBounded
    {inputLength raw measure stage degree : ℕ}
    (hnumerals : max (taggedTupleFuel 2) 15 ≤ stage)
    (hnode :
      PolyBounded (booleanCircuitNodeStageFuel inputLength raw) measure stage
        degree)
    (hnat : PolyBounded (booleanCircuitNatStageFuel raw) measure stage degree)
    (hlt :
      PolyBounded (booleanCircuitLtStageFuel inputLength raw) measure stage
        degree) :
    ∃ circuitCoefficient : ℕ,
      PolyBounded (booleanCircuitValidationFuel inputLength raw) measure
        circuitCoefficient degree := by
  have htuple : PolyBounded (taggedTupleFuel 2) measure stage degree :=
    PolyBounded.of_le_coefficient (le_trans (le_max_left _ _) hnumerals)
  have hgate : PolyBounded 15 measure stage degree :=
    PolyBounded.of_le_coefficient (le_trans (le_max_right _ _) hnumerals)
  have hfifteen : (15 : ℕ) ≤ stage := le_trans (le_max_right _ _) hnumerals
  have h₈ : PolyBounded 8 measure stage degree :=
    PolyBounded.of_le_coefficient (by omega)
  have h₇ : PolyBounded 7 measure stage degree :=
    PolyBounded.of_le_coefficient (by omega)
  have node₇ :=
    linkFuel_polyBounded (second := circuitChainTail₇) hlt hgate
  have node₆ :=
    linkFuel_polyBounded (second := circuitChainTail₆) h₈ node₇
  have node₅ :=
    linkFuel_polyBounded (second := circuitChainTail₅) hnat node₆
  have node₄ :=
    linkFuel_polyBounded (second := circuitChainTail₄) h₇ node₅
  have node₃ :=
    linkFuel_polyBounded (second := circuitChainTail₃) hnode node₄
  have node₂ :=
    linkFuel_polyBounded (second := circuitChainTail₂) h₈ node₃
  exact ⟨_,
    linkFuel_polyBounded (second := circuitChainTail₁) htuple node₂⟩

def nodeChainTail₆ : NPOracleProgram := booleanNodeListValidationGateProgram

def nodeChainTail₅ : NPOracleProgram :=
  linkPrograms booleanNodeListTopologyEqualityProgram nodeChainTail₆

def nodeChainTail₄ : NPOracleProgram :=
  linkPrograms booleanNodeListTopologyEqualityLoweringProgram nodeChainTail₅

def nodeChainTail₃ : NPOracleProgram :=
  linkPrograms booleanNodeListTopologyProgram nodeChainTail₄

def nodeChainTail₂ : NPOracleProgram :=
  linkPrograms booleanNodeListRangeLoweringProgram nodeChainTail₃

def nodeChainTail₁ : NPOracleProgram :=
  linkPrograms booleanNodeListPrepareProgram nodeChainTail₂

theorem booleanNodeListNormalizeFuel_polyBounded
    {raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    ∃ normalizeCoefficient : ℕ,
      PolyBounded (booleanNodeListNormalizeFuel raw) measure
        normalizeCoefficient (degree + degree) := by
  obtain ⟨canonicalityCoefficient, hcanonicality⟩ :=
    balancedCanonicalityFuel_degree hraw
  have hnodes :=
    (polyBounded_rawBalancedTraversalTree_nodeCount hraw).degree_mono
      (by omega : degree ≤ degree + degree)
  exact ⟨_,
    forkCallFuel_polyBounded (first := balancedCanonicalityProgram)
      (second := balancedRawCanonicalizeProgram) hcanonicality
      (balancedRawCanonicalizeFuel_polyBounded hnodes)⟩

/-- **The node list validator's chain, dominated.**  The walk's residue is two
named charges — the preparation fork and the topology range aggregation — plus
the two width certificates the native equality consumes. -/
theorem booleanNodeListValidationFuel_polyBounded
    {inputLength raw measure stage degree : ℕ}
    (hnumerals : 10 ≤ stage)
    (hnormalize :
      PolyBounded (booleanNodeListNormalizeFuel raw) measure stage degree)
    (hprepare :
      PolyBounded (booleanNodeListPrepareFuel inputLength raw) measure stage
        degree)
    (htopology :
      PolyBounded (booleanNodeListTopologyFuel inputLength raw) measure stage
        degree)
    (hequality :
      PolyBounded (booleanNodeListTopologyEqualityFuel inputLength raw) measure
        stage degree) :
    ∃ nodeCoefficient : ℕ,
      PolyBounded (booleanNodeListValidationFuel inputLength raw) measure
        nodeCoefficient degree := by
  have hgate : PolyBounded booleanNodeListValidationGateFuel measure stage
      degree := PolyBounded.of_le_coefficient hnumerals
  have h₇ : PolyBounded 7 measure stage degree :=
    PolyBounded.of_le_coefficient (by omega)
  have node₆ :=
    linkFuel_polyBounded (second := nodeChainTail₆) hequality hgate
  have node₅ :=
    linkFuel_polyBounded (second := nodeChainTail₅) h₇ node₆
  have node₄ :=
    linkFuel_polyBounded (second := nodeChainTail₄) htopology node₅
  have node₃ :=
    linkFuel_polyBounded (second := nodeChainTail₃) h₇ node₄
  have node₂ :=
    linkFuel_polyBounded (second := nodeChainTail₂) hprepare node₃
  exact ⟨_,
    linkFuel_polyBounded (second := nodeChainTail₁) hnormalize node₂⟩

/-- **The node list validator's two remaining charges, named.**  Both are one
wrapper away from a charge not stated as a published bound: the preparation fork over
`booleanCircuitPreparationFuel`, and the topology stage over
`booleanNodeTopologyRangeFuel`.  Everything else on the Boolean circuit
validator's path is closed. -/
theorem booleanNodeListPrepareFuel_polyBounded
    {inputLength raw measure coefficient degree : ℕ}
    (hpreparation :
      PolyBounded
        (booleanCircuitPreparationFuel inputLength (booleanNodeListAtoms raw))
        measure coefficient degree) :
    PolyBounded (booleanNodeListPrepareFuel inputLength raw) measure
      (programRegisterSpan
          (preserveRightProgram booleanCircuitPreparationProgram) + 5 + 4 +
        (coefficient + 4)) degree :=
  linkFuel_polyBounded
    (second := preserveRightProgram booleanCircuitPreparationProgram)
    (polyBounded_const 4 measure degree)
    (preserveRightFuel_polyBounded hpreparation)

theorem booleanNodeListTopologyFuel_polyBounded
    {inputLength raw measure coefficient degree : ℕ}
    (hrange :
      PolyBounded
        (booleanNodeTopologyRangeFuel inputLength
          (booleanNodeListDescriptors raw)) measure coefficient degree) :
    PolyBounded (booleanNodeListTopologyFuel inputLength raw) measure
      (coefficient + 4) degree :=
  preserveRightFuel_polyBounded hrange

theorem booleanNodeListTopologyEqualityFuel_polyBounded
    {inputLength raw measure topologyCoefficient nodeCoefficient degree : ℕ}
    (htopology :
      PolyBounded
        (natBitLength (booleanNodeListTopologyCount inputLength raw)) measure
        topologyCoefficient degree)
    (hnodes :
      PolyBounded (natBitLength (booleanNodeListNodeCount raw)) measure
        nodeCoefficient degree) :
    PolyBounded (booleanNodeListTopologyEqualityFuel inputLength raw) measure
      (nativeNatEqCoefficient topologyCoefficient nodeCoefficient + 4) degree :=
  preserveRightFuel_polyBounded (nativeNatEqFuel_polyBounded' htopology hnodes)

end NearCubicWires.ValidatorResidualLeafBudget
