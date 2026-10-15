import Proof.Amplification.RecoveryMarkerHandoffCalls

/-! Accepted marker metadata has three actual width-bounded framed words.
Absent prefix fields are the physically initialized zero words. These are
the exact words consumed by the three paid handoff copies. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryMarkerClause RadixSemantics RecoveryMarkerMetadata
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem accepted_fields (x : State) (hx : x.Valid)
    (hc0 : (read x).committed=frame (List.replicate x.width false))
    (hn0 : (read x).count=frame (List.replicate x.width false))
    (ha : (output x).inner.present=true) :
    ∃ flat : Bool,∃ payload committed count : List Bool,∃ tail : TailWords,
      payload.length=x.width ∧ committed.length=x.width ∧ count.length=x.width ∧
      decodeCNF (outerCode x)=formula flat payload tail ∧
      value committed=tailCommitted tail ∧ value count=tailCount tail ∧
      read (output x)=⟨frame payload,frame committed,frame count,flat⟩ := by
  obtain ⟨flat,payload,tail,hp,ht,hcode,hfields⟩ := accepted_decode x hx ha
  cases tail with
  | none=>
    refine ⟨flat,payload,List.replicate x.width false,List.replicate x.width false,none,
      hp,by simp,by simp,hcode,RecoveryRootIteration.zeros_value _,RecoveryRootIteration.zeros_value _,?_⟩
    rw [hfields]
    change {read x with payload:=frame payload,flat:=flat}=_
    cases he : read x with
    | mk p c n f=>
      rw [he] at hc0 hn0
      change c=_ at hc0
      change n=_ at hn0
      simp only [hc0,hn0]
  | some words=>
    refine ⟨flat,payload,words.1,words.2,some words,hp,ht.1,ht.2,hcode,rfl,rfl,?_⟩
    rw [hfields]
    rfl

theorem field_sources (x : State) (flat : Bool) (payload committed count : List Bool)
    (hf : read x=⟨frame payload,frame committed,frame count,flat⟩) :
    ∀ which : Fin 3,x.tapes (RecoveryMarkerSave.target which)=frame (![payload,committed,count] which) := by
  intro which
  fin_cases which
  · exact congrArg Fields.payload hf
  · exact congrArg Fields.committed hf
  · exact congrArg Fields.count hf

end NearCubicWires.RepairOrdinary.RecoveryMarker
