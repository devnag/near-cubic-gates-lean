import Proof.CaseAnalysis.RowsGateFieldsMeaning

/-! The exact remaining gate verdict uses the SAME decoded component
fields, two arity comparisons and the executed zero-outside-support fold. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateDecisionMeaning
open LocalBitMultitape CanonicalBinary CanonicalWitnessCodec RadixSemantics
open CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (weights : List ℤ) := weights.map intField

theorem field_get (weights : List ℤ) (i : ℕ) (hi : i < weights.length) :
    value ((fields weights).getD i (false,[])).2=(weights.get ⟨i,hi⟩).natAbs := by
  rw [List.getD_eq_getElem _ _ (by simpa [fields] using hi)]
  simp only [fields,List.getElem_map,intField_value,List.get_eq_getElem]

theorem zero_iff (weights : List ℤ) (members : List Bool) (hl : weights.length=members.length) :
    validity (fields weights) members true weights.length=true ↔
      List.Forall₂ (fun weight bit => bit=false → weight=0) weights members := by
  rw [validity_iff,List.forall₂_iff_get]
  simp only [true_and]
  constructor
  · intro h
    refine ⟨hl,?_⟩
    intro i hi hm hb
    have hv := h i hi (by simpa only [List.getD_eq_getElem _ _ hm,List.get_eq_getElem] using hb)
    rw [field_get _ _ hi] at hv
    exact Int.natAbs_eq_zero.mp hv
  · rintro ⟨_,h⟩ i hi hb
    have hm : i < members.length := by omega
    rw [field_get _ _ hi]
    have hz := h i hi hm (by simpa only [List.getD_eq_getElem _ _ hm,List.get_eq_getElem] using hb)
    rw [hz]
    rfl

theorem tagged (bits : List Bool) (h : CompetitorWitnessTriple.structural bits) :
    decodeTaggedList (value bits)=some
      [value (CloseoutRowsGateHeader.codeWord bits 0),value (CloseoutRowsGateHeader.codeWord bits 1),
        value (CloseoutRowsGateHeader.codeWord bits 2)] := by
  rw [(CompetitorWitnessTriple.structural_iff bits).mp h,decodeTaggedList_encode]
  rfl

theorem decision_exact (n : ℕ) (bits : List Bool) (weights : List ℤ) (threshold : ℤ) (members : List Bool)
    (hs : CompetitorWitnessTriple.structural bits)
    (hw : decodeIntList (value (CloseoutRowsGateHeader.codeWord bits 0))=some weights)
    (ht : decodeInt (value (CloseoutRowsGateHeader.codeWord bits 1))=some threshold)
    (hm : decodeBoolList (value (CloseoutRowsGateHeader.codeWord bits 2))=some members) :
    (decodeSupportedNormalizedGate n (value bits)).isSome ↔
      weights.length=n ∧ members.length=n ∧ validity (fields weights) members true weights.length=true := by
  rw [decodeSupportedNormalizedGate_isSome_iff_fields]
  constructor
  · rintro ⟨wc,tc,mc,ws,z,ms,hcode,hws,hz,hms,hnw,hnm,hzero⟩
    rw [tagged bits hs] at hcode
    have codes := Option.some.inj hcode
    have hc : value (CloseoutRowsGateHeader.codeWord bits 0)=wc ∧
        value (CloseoutRowsGateHeader.codeWord bits 1)=tc ∧
        value (CloseoutRowsGateHeader.codeWord bits 2)=mc := by simpa only [List.cons.injEq,and_true] using codes
    rw [←hc.1,hw] at hws
    rw [←hc.2.2,hm] at hms
    cases Option.some.inj hws
    cases Option.some.inj hms
    exact ⟨hnw,hnm,(zero_iff weights members (hnw.trans hnm.symm)).mpr hzero⟩
  · rintro ⟨hwlen,hmLen,hzero⟩
    exact ⟨_,_,_,weights,threshold,members,tagged bits hs,hw,ht,hm,hwlen,hmLen,
      (zero_iff weights members (hwlen.trans hmLen.symm)).mp hzero⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsGateDecisionMeaning
