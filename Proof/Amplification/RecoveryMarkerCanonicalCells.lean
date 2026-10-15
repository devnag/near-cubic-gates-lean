import Proof.Amplification.RecoveryMarkerMeaning

/-! Canonical literal and clause-load equations for the same executed
marker machine. These use encoded natural values, allowing the actual
retained binary words to remain padded to the original input width. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryMarkerClause RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem singleton_check (which : Fin 3) (flat : Bool) (index : Nat) :
    RecoveryMarkerAtom.codeCheck which (Encodable.encode [(flat,index)])=RecoveryMarkerAtom.tagOK which flat := by
  cases flat
  · change RecoveryMarkerAtom.codeCheck which (Nat.pair (Nat.pair 0 index) 0+1)=_
    simp [RecoveryMarkerAtom.codeCheck,Nat.unpair_pair]
  · change RecoveryMarkerAtom.codeCheck which (Nat.pair (Nat.pair 1 index) 0+1)=_
    simp [RecoveryMarkerAtom.codeCheck,Nat.unpair_pair]

theorem committed_check (committed count : Nat) :
    RecoveryMarkerAtom.codeCheck 1 (Encodable.encode [(false,committed),(true,count)])=true := by
  change RecoveryMarkerAtom.codeCheck 1
    (Nat.pair (Nat.pair 0 committed) (Encodable.encode [(true,count)])+1)=true
  simp [RecoveryMarkerAtom.codeCheck,RecoveryMarkerAtom.tagOK,Nat.unpair_pair]

theorem load_cons (x : State) (clause : List (Bool×Nat)) (rest : EncodedCNF)
    (hc : outerCode x=Encodable.encode (clause::rest)) :
    (loaded x).outer.flag=true ∧ RecoveryMarkerAtom.inputCode (loaded x)=Encodable.encode clause ∧
      outerCode (loaded x)=Encodable.encode rest := by
  have hp : (loaded x).outer.flag=true := by
    rw [load_flag,hc,Encodable.encode_list_cons]
    simp
  have hs := load_codes x hp
  rw [hc,Encodable.encode_list_cons,Nat.succ_sub_one,Nat.unpair_pair] at hs
  exact ⟨hp,hs⟩

theorem outer_zero (x : State) (hz : outerCode x=0) : (outerStep x).outer.flag=false := by
  rw [show (outerStep x).outer.flag=decide (outerCode x≠0) from RecoveryThreeCellReader.after_flag x.outer 0,hz]
  rfl

theorem empty_zero (x : State) (hz : RecoveryMarkerAtom.inputCode x=0) : (emptyStep x).inner.data.flag=false := by
  rw [empty_flag,hz]
  rfl

theorem canonical_prefix (x : State) (committed count : Nat)
    (hc : RecoveryMarkerAtom.inputCode x=Encodable.encode [(false,committed),(true,count)])
    (hz : outerCode x=0) : (prefixOutput x).inner.present=true := by
  have ha1 : RecoveryMarkerAtom.answer 1 x=true := by
    rw [RecoveryMarkerAtom.answer_eq_codeCheck]
    change RecoveryMarkerAtom.codeCheck 1 (RecoveryMarkerAtom.inputCode x)=true
    rw [hc,committed_check]
  have hc2 : RecoveryMarkerAtom.inputCode (RecoveryMarkerAtom.output 1 x)=Encodable.encode [(true,count)] := by
    rw [RecoveryMarkerAtom.committed_tail x ha1]
    unfold RecoveryMarkerAtom.literalTail
    rw [hc,Encodable.encode_list_cons,Nat.succ_sub_one,Nat.unpair_pair]
  have ha2 : RecoveryMarkerAtom.answer 2 (RecoveryMarkerAtom.output 1 x)=true := by
    rw [RecoveryMarkerAtom.answer_eq_codeCheck]
    change RecoveryMarkerAtom.codeCheck 2 (RecoveryMarkerAtom.inputCode (RecoveryMarkerAtom.output 1 x))=true
    rw [hc2,singleton_check]
    rfl
  have hp1 := (RecoveryMarkerAtom.output_answer 1 x).trans ha1
  have hp2 := (RecoveryMarkerAtom.output_answer 2 (RecoveryMarkerAtom.output 1 x)).trans ha2
  have ht : (outerStep (RecoveryMarkerAtom.output 2 (RecoveryMarkerAtom.output 1 x))).outer.flag=false := by
    apply outer_zero
    change value (RecoveryMarkerAtom.output 2 (RecoveryMarkerAtom.output 1 x)).outer.bits=0
    rw [RecoveryMarkerAtom.output_outer_bits,RecoveryMarkerAtom.output_outer_bits]
    exact hz
  simp only [prefixOutput,hp1,hp2,ite_true,ht,Bool.not_false]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryMarker
