import Proof.CaseAnalysis.WitnessFamily
import Proof.Hierarchy.CompetitorSourceCompleteness

/-! The paper's common table stores the named proof-variable bit, before
literal negation. Its occurrence averages feed the existing aggregate test
without changing the approximation radius or coefficient mass. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness
open SourceInterfaces ComponentwiseBranchExtraction ComponentwiseTransfer
open OccurrenceSliceTransport OuterPCPRecovery VerifierThresholdSeam
open PCPPClausePadding ProjectionPCPPadding RepairRepresentation
open SupplierEstimator
open CanonicalWitnessCodec SupplierPipeline LocalBitMultitape RecoveryRootRound
open RecoveryExecution RadixSemantics ExecutableInterfaces
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def unsignedHonest {n : ℕ} {c : BooleanCircuit n} (pcpp : PointwisePCPP c) :
    BoolFunction (n + pcpp.clauseBits + 1) := fun address =>
  pcpp.assignment (occurrenceInput address) (pcpp.honestAuxiliary (occurrenceInput address))
    (occurrenceVariable pcpp
      (binaryAddress (occurrenceClauseAddress address), occurrencePosition address))

theorem unsignedHonest_address {n : ℕ} {c : BooleanCircuit n} (pcpp : PointwisePCPP c)
    (u : BitInput n) (clause : BitInput pcpp.clauseBits) (position : Bool) :
    unsignedHonest pcpp (occurrenceAddress u clause position) =
      pcpp.assignment u (pcpp.honestAuxiliary u)
        (occurrenceVariable pcpp (binaryAddress clause, position)) := by
  simp [unsignedHonest]

theorem signedHonest_eq {n : ℕ} {c : BooleanCircuit n} (pcpp : PointwisePCPP c)
    (u : BitInput n) (clause : BitInput pcpp.clauseBits) (position : Bool) :
    honestOccurrenceFunction pcpp (occurrenceAddress u clause position) =
      xor (literalNegated (occurrenceLiteral pcpp (binaryAddress clause, position)))
        (unsignedHonest pcpp (occurrenceAddress u clause position)) := by
  rw [honestOccurrenceFunction_occurrenceAddress, literal_eval_eq_xor, unsignedHonest_address]
  rfl

noncomputable def averagedValue {n : ℕ} {c : BooleanCircuit n} (pcpp : PointwisePCPP c)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ) (u : BitInput n) :=
  occurrenceAverage (occurrenceVariable pcpp) (sliceGuess pcpp guess u)

theorem aliases {n : ℕ} {c : BooleanCircuit n} (pcpp : PointwisePCPP c)
    (values : BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (u : BitInput n) (i j : Fin (2 ^ pcpp.clauseBits) × Bool)
    (h : occurrenceVariable pcpp i = occurrenceVariable pcpp j) :
    values u (occurrenceVariable pcpp i) = values u (occurrenceVariable pcpp j) :=
  congrArg (values u) h

theorem averagedValue_unit {n : ℕ} {c : BooleanCircuit n} (pcpp : PointwisePCPP c)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ)
    (h0 : ∀ address, 0 ≤ guess address) (h1 : ∀ address, guess address ≤ 1)
    (u : BitInput n) (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    0 ≤ averagedValue pcpp guess u j ∧ averagedValue pcpp guess u j ≤ 1 := by
  classical
  by_cases hf : (occurrenceFiber (occurrenceVariable pcpp) j).Nonempty
  · exact occurrenceAverage_mem_unitInterval _ _ _ hf (fun _ => ⟨h0 _, h1 _⟩)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hf
    simp [averagedValue, occurrenceAverage, meanOn, he]

theorem averaged_error {n : ℕ} {c : BooleanCircuit n} (pcpp : PointwisePCPP c)
    (assignment : BitInput (pcpp.systematicBits + pcpp.auxiliaryBits))
    (guess : Fin (2 ^ pcpp.clauseBits) × Bool → ℝ)
    (h : ∀ slot, 0 ≤ guess slot ∧ guess slot ≤ 1) :
    clauseOccurrenceErrorMean pcpp (occurrenceAverage (occurrenceVariable pcpp) guess)
      (fun j => bitAsReal (assignment j)) =
      𝔼 slot : Fin (2 ^ pcpp.clauseBits) × Bool,
        |guess slot - bitAsReal (assignment (occurrenceVariable pcpp slot))| := by
  classical
  rw [clauseOccurrenceErrorMean_eq_expect_slot, Finset.expect_eq_sum_div_card,
    Finset.expect_eq_sum_div_card]
  congr 1
  exact occurrenceAveraging_preserves_distance (occurrenceVariable pcpp) guess assignment h

theorem unsigned_slice_error {n : ℕ} {c : BooleanCircuit n} (pcpp : PointwisePCPP c)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ) (u : BitInput n) :
    occurrenceSliceDistance (unsignedHonest pcpp) guess u =
      𝔼 slot : Fin (2 ^ pcpp.clauseBits) × Bool,
        |sliceGuess pcpp guess u slot -
          bitAsReal (pcpp.assignment u (pcpp.honestAuxiliary u) (occurrenceVariable pcpp slot))| := by
  classical
  have hcards : Fintype.card (BitInput pcpp.clauseBits × Bool) =
      Fintype.card (Fin (2 ^ pcpp.clauseBits) × Bool) := by simp [Fintype.card_prod]
  rw [occurrenceSliceDistance, Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
    ← (Equiv.prodCongr (bitInputIndexEquiv pcpp.clauseBits) (Equiv.refl Bool)).sum_comp
      (fun slot : BitInput pcpp.clauseBits × Bool =>
        |guess (occurrenceAddress u slot.1 slot.2) -
          bitAsReal (unsignedHonest pcpp (occurrenceAddress u slot.1 slot.2))|)]
  simp only [Finset.card_univ, hcards]
  congr 1
  exact Finset.sum_congr rfl fun slot _ => by
    change |guess (occurrenceAddress u (bitInputIndexEquiv pcpp.clauseBits slot.1) slot.2) -
      bitAsReal (unsignedHonest pcpp
        (occurrenceAddress u (bitInputIndexEquiv pcpp.clauseBits slot.1) slot.2))| = _
    rw [unsignedHonest_address]
    rw [show binaryAddress ((bitInputIndexEquiv pcpp.clauseBits) slot.1) = slot.1 from
      (bitInputIndexEquiv pcpp.clauseBits).left_inv slot.1]
    rfl

theorem honestError_eq_distance (source : PointwisePCPPAlgorithm)
    (r : PCPPRequest source.minimumArity)
    (guess : BitInput (r.arity + (source.output r).clauseBits + 1) → ℝ)
    (h0 : ∀ address, 0 ≤ guess address) (h1 : ∀ address, guess address ≤ 1) :
    CompetitorSourceAverage.honestError source r (averagedValue (source.output r) guess) =
      l1DistanceFromBoolean (unsignedHonest (source.output r)) guess := by
  rw [l1DistanceFromBoolean_eq_expect_slice]
  apply Finset.expect_congr rfl
  intro u _
  rw [unsigned_slice_error]
  exact averaged_error (source.output r) _ _ (fun _ => ⟨h0 _, h1 _⟩)

theorem family_header_run {limits : RecoveryWitnessLimits}
    {variableCount : BooleanCircuit limits.oracleArity → ℕ}
    (w : FamilyWitness limits variableCount) (x bits : List Bool) (h : value bits = w.code) :
    ∃ r : ExecutionReceipt 148 _,
      run CompetitorWitnessHeader.machine (CompetitorWitnessHeader.budget bits)
        (CompetitorWitnessHeader.input x bits) = some r ∧
      r.steps ≤ CompetitorWitnessHeader.budget bits ∧ (∀ i, r.final.heads i = 0) ∧
      readTapeBit (r.final.tapes 147) 0 = true ∧
      r.final.tapes 78 = frame (SignedSortKey.binary bits.length (encodeBooleanCircuit w.oracle)) ∧
      r.final.tapes 118 = frame (SignedSortKey.binary bits.length w.payload) := by
  obtain ⟨r, hr, hs, hh, ht⟩ := CompetitorWitnessHeader.header_output x bits
  obtain ⟨hv, ho, hp⟩ := w.header_fields bits h
  refine ⟨r, hr, hs, hh, ?_, ?_, ?_⟩
  · rw [ht]
    exact (CompetitorWitnessHeader.output_passes x bits).mpr hv
  · rw [ht, CompetitorWitnessHeader.output_oracle, CompetitorWitnessHeader.field_word, ho]
  · rw [ht, CompetitorWitnessHeader.output_sum, CompetitorWitnessHeader.field_word, hp]

end NearCubicWires.RepairOrdinary.CloseoutWitness
