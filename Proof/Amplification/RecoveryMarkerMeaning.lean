import Proof.Amplification.RecoveryMarkerPayloadMeaning

/-! Every accepted marker replay reconstructs one of the exact legacy
four marker forms and the actual saved field words. No supplied marker
classification or scalar-value oracle occurs in this bridge. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryMarkerClause RadixSemantics RecoveryMarkerMetadata
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def formula (flat : Bool) (payload : List Bool) (tail : TailWords) : EncodedCNF :=
  []::[(flat,value payload)]::tailClauses tail

theorem accepted_marker (x : State) (hx : x.Valid) (ha : (output x).inner.present=true) :
    ∃ flat : Bool,∃ payload : List Bool,∃ tail : TailWords,
      payload.length=x.width ∧ TailFits x.width tail ∧
      outerCode x=Encodable.encode (formula flat payload tail) ∧
      read (output x)=installTail {read x with payload:=frame payload,flat:=flat} tail := by
  cases hp : (loaded (RecoveryMarkerFlags.answered x false)).outer.flag
  · simp only [output,hp,Bool.false_eq_true,ite_false] at ha
    contradiction
  · cases he : (emptyStep (loaded (RecoveryMarkerFlags.answered x false))).inner.data.flag
    · have ho : output x=payloadOutput (emptyStep (loaded (RecoveryMarkerFlags.answered x false))) := by
        simp only [output,hp,he,ite_true,Bool.false_eq_true,ite_false]
      rw [ho] at ha ⊢
      have hy := loaded_valid (RecoveryMarkerFlags.answered x false) hx
      have hz := empty_valid _ hy
      obtain ⟨flat,payload,tail,hplen,htfit,hcode,hfields⟩ := payload_accepted _ hz ha
      have hw : (emptyStep (loaded (RecoveryMarkerFlags.answered x false))).width=x.width :=
        (RecoveryClauseState.after_length _ 0).trans (loaded_width _ hx)
      have hempty : RecoveryMarkerAtom.inputCode (loaded (RecoveryMarkerFlags.answered x false))=0 := by
        rw [empty_flag] at he
        by_cases hn : RecoveryMarkerAtom.inputCode (loaded (RecoveryMarkerFlags.answered x false))=0
        · exact hn
        · simp [hn] at he
      have hrebuild := load_rebuild (RecoveryMarkerFlags.answered x false) hp
      rw [hempty] at hrebuild
      have htail : outerCode (loaded (RecoveryMarkerFlags.answered x false))=
          Encodable.encode ([(flat,value payload)]::tailClauses tail) := hcode
      rw [htail] at hrebuild
      refine ⟨flat,payload,tail,hplen.trans hw,?_,?_,?_⟩
      · rw [hw] at htfit
        exact htfit
      · change outerCode (RecoveryMarkerFlags.answered x false)=_
        rw [←hrebuild]
        unfold formula
        rw [Encodable.encode_list_cons]
        rfl
      · rw [hfields,read_empty,read_loaded,read_answered]
    · simp only [output,hp,he,ite_true] at ha
      contradiction

theorem accepted_decode (x : State) (hx : x.Valid) (ha : (output x).inner.present=true) :
    ∃ flat : Bool,∃ payload : List Bool,∃ tail : TailWords,
      payload.length=x.width ∧ TailFits x.width tail ∧
      decodeCNF (outerCode x)=formula flat payload tail ∧
      read (output x)=installTail {read x with payload:=frame payload,flat:=flat} tail := by
  obtain ⟨flat,payload,tail,hp,ht,hcode,hfields⟩ := accepted_marker x hx ha
  refine ⟨flat,payload,tail,hp,ht,?_,hfields⟩
  unfold decodeCNF
  rw [hcode,Encodable.encodek]

end NearCubicWires.RepairOrdinary.RecoveryMarker
