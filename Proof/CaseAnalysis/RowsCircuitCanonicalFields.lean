import Proof.CaseAnalysis.RowsCircuitThresholdProgram

/-! The original public decoder identifies the same ordered fields read
by the cold worker. These are proof projections, without a new traversal. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCanonicalFields
open LocalBitMultitape RadixSemantics CanonicalBinary CanonicalWitnessCodec SupplierPipeline
open CloseoutRowsCircuitHeader CloseoutRowsCircuitWords CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem word_values (bits : List Bool) (codes : List ℕ)
    (h : decodeBalancedList (value (codeWord bits 2))=some codes) :
    PCPSerializerMass.values (words bits)=codes:=by
  rw [CloseoutRowsCircuitWords.values,←encodeBalancedList_of_decode h,PCPPNativeCanonicalTree.tree_atoms]

theorem typed_bottoms {core n : ℕ} (g : Fin n → SupportedNormalizedGate core)
    (bits : List Bool)
    (h : PCPSerializerMass.values (words bits)=List.ofFn (fun i=>encodeSupportedNormalizedGate (g i))) :
    (words bits).length=n ∧
      ∀ i,decodeSupportedNormalizedGate core (value ((words bits).getD i.val []))=some (g i):=by
  have hn:(words bits).length=n:=by
    have hl:=congrArg List.length h
    simpa only [PCPSerializerMass.values,List.length_map,List.length_ofFn] using hl
  refine ⟨hn,?_⟩
  intro i
  have he:=congrArg (fun xs : List ℕ=>xs.getD i.val 0) h
  have hi:i.val < (words bits).length:=by rw [hn];exact i.isLt
  have hj:i.val < (List.ofFn (fun j=>encodeSupportedNormalizedGate (g j))).length:=by
    simpa only [List.length_ofFn] using i.isLt
  rw [List.getD_eq_getElem _ _ (by simpa only [PCPSerializerMass.values,List.length_map] using hi),
    List.getD_eq_getElem _ _ hj] at he
  simp only [PCPSerializerMass.values,List.getElem_map,List.getElem_ofFn] at he
  rw [List.getD_eq_getElem _ _ hi,he]
  exact decodeSupportedNormalizedGate_encode (g i)

theorem symmetric_fields {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core) (bits : List Bool)
    (hd : decodeNormalizedSymmetricThresholdCircuit core (value bits)=some c) :
    CloseoutRowsCircuitPrefix.valid false bits ∧ (words bits).length=c.bottomCount ∧
      (∀ i,decodeSupportedNormalizedGate core (value ((words bits).getD i.val []))=some (c.bottom i)) ∧
      value (codeWord bits 3)=encodeBoolList (List.ofFn c.top) ∧
      CloseoutRowsCircuitSymTop.valid (words bits).length (codeWord bits 3):=by
  have encoded: value bits=encodeTaggedList [encodeNat symmetricCircuitFamilyTag,encodeNat c.bottomCount,
      encodeBalancedList (List.ofFn (fun i=>encodeSupportedNormalizedGate (c.bottom i))),
      encodeBoolList (List.ofFn c.top)]:=(encodeNormalizedSymmetricThresholdCircuit_of_decode hd).symm
  have fields:=code_values _ _ _ _ bits encoded
  have f0:value (codeWord bits 0)=encodeNat symmetricCircuitFamilyTag:=fields 0
  have f1:value (codeWord bits 1)=encodeNat c.bottomCount:=fields 1
  have f2:value (codeWord bits 2)=encodeBalancedList (List.ofFn (fun i=>encodeSupportedNormalizedGate (c.bottom i))):=fields 2
  have f3:value (codeWord bits 3)=encodeBoolList (List.ofFn c.top):=fields 3
  have listDecode:decodeBalancedList (value (codeWord bits 2))=
      some (List.ofFn (fun i=>encodeSupportedNormalizedGate (c.bottom i))):=by rw [f2];simp
  have typed:=typed_bottoms c.bottom bits (word_values bits _ listDecode)
  refine ⟨?_,typed.1,typed.2,f3,?_⟩
  · refine ⟨(structural_iff bits).mpr ?_,?_,_,listDecode,?_⟩
    · rw [f0,f1,f2,f3];exact encoded
    · rw [f0,decodeNat_encode];rfl
    · rw [f1,List.length_ofFn];exact decodeNat_encode _
  · refine ⟨List.ofFn c.top,?_,?_⟩
    · rw [f3];exact decodeBoolList_encode _
    · rw [List.length_ofFn,typed.1]

theorem threshold_fields {core : ℕ} (c : NormalizedThresholdThresholdCircuit core) (bits : List Bool)
    (hd : decodeNormalizedThresholdThresholdCircuit core (value bits)=some c) :
    CloseoutRowsCircuitPrefix.valid true bits ∧ (words bits).length=c.bottomCount ∧
      (∀ i,decodeSupportedNormalizedGate core (value ((words bits).getD i.val []))=some (c.bottom i)) ∧
      value (codeWord bits 3)=encodeSupportedNormalizedGate c.top:=by
  have encoded:value bits=encodeTaggedList [encodeNat thresholdCircuitFamilyTag,encodeNat c.bottomCount,
      encodeBalancedList (List.ofFn (fun i=>encodeSupportedNormalizedGate (c.bottom i))),
      encodeSupportedNormalizedGate c.top]:=(encodeNormalizedThresholdThresholdCircuit_of_decode hd).symm
  have fields:=code_values _ _ _ _ bits encoded
  have f0:value (codeWord bits 0)=encodeNat thresholdCircuitFamilyTag:=fields 0
  have f1:value (codeWord bits 1)=encodeNat c.bottomCount:=fields 1
  have f2:value (codeWord bits 2)=encodeBalancedList (List.ofFn (fun i=>encodeSupportedNormalizedGate (c.bottom i))):=fields 2
  have f3:value (codeWord bits 3)=encodeSupportedNormalizedGate c.top:=fields 3
  have listDecode:decodeBalancedList (value (codeWord bits 2))=
      some (List.ofFn (fun i=>encodeSupportedNormalizedGate (c.bottom i))):=by rw [f2];simp
  have typed:=typed_bottoms c.bottom bits (word_values bits _ listDecode)
  refine ⟨?_,typed.1,typed.2,f3⟩
  refine ⟨(structural_iff bits).mpr ?_,?_,_,listDecode,?_⟩
  · rw [f0,f1,f2,f3];exact encoded
  · rw [f0,decodeNat_encode];rfl
  · rw [f1,List.length_ofFn];exact decodeNat_encode _

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCanonicalFields
