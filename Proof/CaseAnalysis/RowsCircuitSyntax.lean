import Proof.CaseAnalysis.RowsCircuitCanonicalFields

/-! The complete physical syntax predicates are exactly the two original
public circuit decoders, using their existing field characterizations. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSyntax
open LocalBitMultitape RadixSemantics CanonicalBinary CanonicalWitnessCodec SupplierPipeline
open CloseoutRowsCircuitHeader CloseoutRowsCircuitWords CloseoutRowsCircuitBottomLoop
open CloseoutRowsCircuitCanonicalFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem typed_validity {core n : ℕ} (g : Fin n → SupportedNormalizedGate core) (ws : List (List Bool))
    (hn : ws.length=n)
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (ws.getD i.val []))=some (g i)) :
    validity core true ws ws.length=true:=by
  apply (validity_true core ws).mpr
  intro b hb
  obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.mp hb
  have hj:i<n:=by rw [←hn];exact hi
  have h:=Option.isSome_iff_exists.mpr ⟨g ⟨i,hj⟩,hd ⟨i,hj⟩⟩
  simpa only [List.getD_eq_getElem ws [] hi] using h

theorem actual_bottoms (core : ℕ) (bits : List Bool) (codes : List ℕ)
    (hlist : decodeBalancedList (value (codeWord bits 2))=some codes)
    (good : validity core true (words bits) (words bits).length=true) :
    codes.length=(words bits).length ∧
      ∀ c∈codes,(decodeSupportedNormalizedGate core c).isSome:=by
  have vals:=word_values bits codes hlist
  have count:codes.length=(words bits).length:=by
    have h:=congrArg List.length vals
    simpa only [PCPSerializerMass.values,List.length_map] using h.symm
  refine ⟨count,?_⟩
  intro c hc
  rw [←vals] at hc
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hc
  exact (validity_true core (words bits)).mp good b hb

theorem symmetric (core : ℕ) (bits : List Bool) :
    (decodeNormalizedSymmetricThresholdCircuit core (value bits)).isSome ↔
      CloseoutRowsCircuitPrefix.valid false bits ∧
      CloseoutRowsCircuitSymTop.valid (words bits).length (codeWord bits 3) ∧
      validity core true (words bits) (words bits).length=true:=by
  constructor
  · intro h
    obtain ⟨c,hc⟩:=Option.isSome_iff_exists.mp h
    obtain ⟨hp,hn,hd,_ht,validTop⟩:=symmetric_fields c bits hc
    exact ⟨hp,validTop,typed_validity c.bottom (words bits) hn hd⟩
  · rintro ⟨⟨hs,hmode,codes,hcodes,hcount⟩,⟨top,htop,topCount⟩,bottoms⟩
    obtain ⟨count,allBottoms⟩:=actual_bottoms core bits codes hcodes bottoms
    apply (decodeNormalizedSymmetricThresholdCircuit_isSome_iff_fields core (value bits)).mpr
    refine ⟨value (codeWord bits 0),value (codeWord bits 1),value (codeWord bits 2),value (codeWord bits 3),
      (words bits).length,codes,top,?_,hmode,?_,hcodes,allBottoms,htop,count,topCount⟩
    · rw [(structural_iff bits).mp hs];exact decodeTaggedList_encode _
    · rw [←count];exact hcount

theorem threshold (core : ℕ) (bits : List Bool) :
    (decodeNormalizedThresholdThresholdCircuit core (value bits)).isSome ↔
      CloseoutRowsCircuitPrefix.valid true bits ∧
      (CloseoutRowsCircuitThresholdRun.decoded bits).isSome ∧
      validity core true (words bits) (words bits).length=true:=by
  constructor
  · intro h
    obtain ⟨c,hc⟩:=Option.isSome_iff_exists.mp h
    obtain ⟨hp,hn,hd,ht⟩:=threshold_fields c bits hc
    refine ⟨hp,?_,typed_validity c.bottom (words bits) hn hd⟩
    · unfold CloseoutRowsCircuitThresholdRun.decoded
      rw [hn,ht,decodeSupportedNormalizedGate_encode]
      rfl
  · rintro ⟨⟨hs,hmode,codes,hcodes,hcount⟩,htop,bottoms⟩
    obtain ⟨count,allBottoms⟩:=actual_bottoms core bits codes hcodes bottoms
    apply (decodeNormalizedThresholdThresholdCircuit_isSome_iff_fields core (value bits)).mpr
    refine ⟨value (codeWord bits 0),value (codeWord bits 1),value (codeWord bits 2),value (codeWord bits 3),
      (words bits).length,codes,?_,hmode,?_,hcodes,allBottoms,htop,count⟩
    · rw [(structural_iff bits).mp hs];exact decodeTaggedList_encode _
    · rw [←count];exact hcount

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSyntax
