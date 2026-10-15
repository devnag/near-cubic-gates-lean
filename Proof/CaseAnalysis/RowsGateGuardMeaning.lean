import Proof.CaseAnalysis.RowsGateGuardLayout

/-! A successful public gate decode identifies the SAME component tuple
and framed request already retained by the physical all-raw worker. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateGuard
open LocalBitMultitape CanonicalBinary CanonicalWitnessCodec SupplierPipeline RadixSemantics
open CloseoutRowsGateRawRun CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem typed_components {core : ℕ} (g : SupportedNormalizedGate core) (bits : List Bool)
    (h : decodeSupportedNormalizedGate core (value bits)=some g) :
    Components bits (List.ofFn g.gate.weight) g.gate.threshold (gateMembers g.support) := by
  obtain ⟨hs,hcodes⟩ := CloseoutRowsGateFieldsMeaning.field_codes g bits
    (encodeSupportedNormalizedGate_of_decode h).symm
  refine ⟨hs,?_,?_,?_⟩
  · rw [hcodes 0]
    exact decodeIntList_encode _
  · rw [hcodes 1]
    exact decodeInt_encode _
  · rw [hcodes 2]
    exact decodeBoolList_encode _

theorem decoded_exists (core : ℕ) (bits : List Bool)
    (h : (decodeSupportedNormalizedGate core (value bits)).isSome) : ExistsComponents bits := by
  obtain ⟨g,hg⟩ := Option.isSome_iff_exists.mp h
  exact ⟨_,_,_,typed_components g bits hg⟩

theorem native_of_components {core : ℕ} (compressed : Bool) (g : SupportedNormalizedGate core)
    (bits : List Bool) (weights : List ℤ) (threshold : ℤ) (members : List Bool)
    (old : Fin 1035 → List Bool) (h : decodeSupportedNormalizedGate core (value bits)=some g)
    (hc : Components bits weights threshold members) (hp : Produced compressed bits weights threshold members old) :
    old 1033=frame (CloseoutRowsGateNative.word compressed (gateFields g.gate) (gateMembers g.support)
      (CloseoutRowsGateCold.signSource bits) g.gate.threshold.natAbs) := by
  have hg := typed_components g bits h
  have hw := Option.some.inj (hc.2.1.symm.trans hg.2.1)
  have ht := Option.some.inj (hc.2.2.1.symm.trans hg.2.2.1)
  have hm := Option.some.inj (hc.2.2.2.symm.trans hg.2.2.2)
  subst weights
  subst threshold
  subst members
  have fields : CloseoutRowsGateDecisionMeaning.fields (List.ofFn g.gate.weight)=gateFields g.gate := by
    simp [CloseoutRowsGateDecisionMeaning.fields,gateFields,List.map_ofFn,Function.comp_def]
  simpa only [fields] using hp.1

theorem sign_of_gate {core : ℕ} (g : SupportedNormalizedGate core) (bits : List Bool)
    (h : decodeSupportedNormalizedGate core (value bits)=some g) :
    readTapeBit (CloseoutRowsGateCold.signSource bits) 1=decide (g.gate.threshold<0) :=
  CloseoutRowsSignedAppend.sign_of_decode _ _ (typed_components g bits h).2.2.1

end NearCubicWires.RepairOrdinary.CloseoutRowsGateGuard
