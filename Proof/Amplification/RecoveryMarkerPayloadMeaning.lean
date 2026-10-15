import Proof.Amplification.RecoveryMarkerThirdMeaning

/-! Accepting the payload branch reconstructs its exact singleton and
optional prefix clauses, using the physically saved payload/polarity. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryMarkerClause RadixSemantics RecoveryMarkerMetadata
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem payload_accepted (x : State) (hx : x.Valid) (ha : (payloadOutput x).inner.present=true) :
    ∃ flat : Bool,∃ payload : List Bool,∃ tail : TailWords,
      payload.length=x.width ∧ TailFits x.width tail ∧
      outerCode x=Encodable.encode ([(flat,value payload)]::tailClauses tail) ∧
      read (payloadOutput x)=installTail {read x with payload:=frame payload,flat:=flat} tail := by
  cases hp : (loaded x).outer.flag
  · simp only [payloadOutput,hp,Bool.false_eq_true,ite_false] at ha
    contradiction
  · cases hq : (RecoveryMarkerAtom.output 0 (loaded x)).inner.present
    · simp only [payloadOutput,hp,hq,ite_true,Bool.false_eq_true,ite_false] at ha
      contradiction
    · have hqa : RecoveryMarkerAtom.answer 0 (loaded x)=true := (RecoveryMarkerAtom.output_answer 0 _).symm.trans hq
      have ho : payloadOutput x=thirdOutput (RecoveryMarkerAtom.output 0 (loaded x)) := by
        simp only [payloadOutput,hp,hq,ite_true]
      rw [ho] at ha ⊢
      have hy := loaded_valid x hx
      have hz := RecoveryMarkerAtom.output_valid 0 _ hy
      obtain ⟨tail,htfit,htcode,htfields⟩ := third_accepted (RecoveryMarkerAtom.output 0 (loaded x)) hz ha
      have hw1 := loaded_width x hx
      have hw2 := (RecoveryMarkerAtom.output_width 0 (loaded x)).trans hw1
      have hhead := atom_singleton 0 (loaded x) hqa (by decide)
      have hv := RecoveryMarkerAtom.accepted_variable 0 (loaded x) hqa
      rw [←hv] at hhead
      have htail : outerCode (loaded x)=Encodable.encode (tailClauses tail) := by
        change value (loaded x).outer.bits=_
        change value (RecoveryMarkerAtom.output 0 (loaded x)).outer.bits=_ at htcode
        rw [RecoveryMarkerAtom.output_outer_bits] at htcode
        exact htcode
      have hcode := load_rebuild x hp
      rw [hhead,htail] at hcode
      have hm := RecoveryMarkerAtom.accepted_metadata 0 (loaded x) hqa
      change read (RecoveryMarkerAtom.output 0 (loaded x))=
        {read (loaded x) with payload:=frame (RecoveryMarkerAtom.variableWord (loaded x)),flat:=decide (RecoveryMarkerAtom.literalTag (loaded x)≠0)} at hm
      refine ⟨decide (RecoveryMarkerAtom.literalTag (loaded x)≠0),RecoveryMarkerAtom.variableWord (loaded x),tail,
        (variable_width _).trans hw1,?_,?_,?_⟩
      · rw [hw2] at htfit
        exact htfit
      · rw [←hcode,Encodable.encode_list_cons]
        rfl
      · rw [htfields,hm,read_loaded]

end NearCubicWires.RepairOrdinary.RecoveryMarker
