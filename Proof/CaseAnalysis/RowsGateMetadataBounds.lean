import Proof.CaseAnalysis.RowsGateMetadata

/-! The metadata scans use only actual raw-width bounds of the same accepted
gate. No wire cap, description cap, source child count or numeric-magnitude
driver is assumed at this preprocessing boundary. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateMetadata
open LocalBitMultitape RadixSemantics CanonicalWitnessCodec SupplierPipeline CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem actual_bounds {n : ℕ} (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : decodeSupportedNormalizedGate n (value bits)=some g) :
    n ≤ bits.length+1 ∧ natBitLength g.gate.threshold.natAbs ≤ bits.length+2 ∧
      ∀ field∈gateFields g.gate,field.2.length ≤ bits.length+2 := by
  have hc := CloseoutRowsGateGuard.typed_components g bits h
  refine ⟨?_,?_,?_⟩
  · simpa only [CloseoutRowsGateFields.field_length,List.length_ofFn] using
      CloseoutRowsGateRawBounds.list_count _ _ hc.2.1
  · have hb := CloseoutRowsGateRawBounds.integer_bits _ _ hc.2.2.1
    rw [CloseoutRowsGateFields.field_length] at hb
    have hv := PCPSerializerMass.value_width g.gate.threshold.natAbs.bits
    rw [CanonicalPositiveOutput.nat_bits_value] at hv
    omega
  · have hb := CloseoutRowsGateRawBounds.fields_bound _ _ hc.2.1
    have he : CloseoutRowsGateDecisionMeaning.fields (List.ofFn g.gate.weight)=gateFields g.gate := by
      simp only [CloseoutRowsGateDecisionMeaning.fields,gateFields,List.map_ofFn,Function.comp_def]
    simpa only [he,CloseoutRowsGateFields.field_length] using hb

theorem budget_bound (B n m z : ℕ) (hn : n ≤ B+1) (hm : m ≤ B+1)
    (hz : natBitLength z ≤ B+2) : budget (B+2) n z m ≤ 64*(B+2)^2 := by
  have hmul := Nat.mul_le_mul_right (2*(B+2)+7) hn
  unfold budget CloseoutRowsGateWeightLength.budget preparedBudget loopBudget
  nlinarith

theorem gate_run {n : ℕ} (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : decodeSupportedNormalizedGate n (value bits)=some g) : ∃ out,
    ClockJoin.ReadyRun machine (64*(bits.length+2)^2)
      (input (gateFields g.gate) (gateMembers g.support) g.gate.threshold.natAbs) out ∧
      out 6=List.replicate ((List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord).length true ∧
      out 11=List.replicate (RepairRepresentation.natWord g.gate.threshold.natAbs).length true ∧
      out 13=List.replicate g.wireCount true := by
  obtain ⟨hn,hz,hw⟩ := actual_bounds g bits h
  obtain ⟨out,hr,hwgt,hthr,hs⟩ := metadata_run (gateFields g.gate) (gateMembers g.support)
    g.gate.threshold.natAbs (bits.length+2) hw
  have hb := budget_bound bits.length n n g.gate.threshold.natAbs hn hn hz
  have hl : (gateFields g.gate).length=n := List.length_ofFn
  have hm : (gateMembers g.support).length=n := List.length_ofFn
  rw [hl,hm] at hr
  refine ⟨out,ClockJoin.enlarge machine _ _ _ _ hr hb,?_,hthr,?_⟩
  · simpa only [gateFields_word] using hwgt
  · simpa only [CloseoutRowsSupportCount.support_card,SupportedNormalizedGate.wireCount] using hs

end NearCubicWires.RepairOrdinary.CloseoutRowsGateMetadata
