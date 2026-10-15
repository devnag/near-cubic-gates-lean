import Proof.Amplification.RecoveryCompactBranchWhole

/-! Canonical marker input determines the numeric values of the actual
saved words. Padded words need no extra canonical binary reencoding. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryMarkerClause RadixSemantics RecoveryMarkerMetadata
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem formula_values (flat flat' : Bool) (payload payload' : List Bool) (tail tail' : TailWords)
    (h : formula flat payload tail=formula flat' payload' tail') :
    flat=flat' ∧ value payload=value payload' ∧
      tailCommitted tail=tailCommitted tail' ∧ tailCount tail=tailCount tail' := by
  cases tail <;> cases tail' <;>
    simp_all [formula,tailClauses,tailCommitted,tailCount]

theorem canonical_fields (x : State) (hx : x.Valid)
    (hc0 : (read x).committed=frame (List.replicate x.width false))
    (hn0 : (read x).count=frame (List.replicate x.width false))
    (flat : Bool) (payload : List Bool) (tail : TailWords)
    (hc : outerCode x=Encodable.encode (formula flat payload tail)) :
    ∃ p c n : List Bool,p.length=x.width ∧ c.length=x.width ∧ n.length=x.width ∧
      value p=value payload ∧ value c=tailCommitted tail ∧ value n=tailCount tail ∧
      read (output x)=⟨frame p,frame c,frame n,flat⟩ := by
  have ha := canonical_marker x flat payload tail hc
  obtain ⟨f,p,c,n,t,hp,hc',hn,hdecode,hcv,hnv,hfields⟩ := accepted_fields x hx hc0 hn0 ha
  have hdecode' : decodeCNF (outerCode x)=formula flat payload tail := by
    unfold decodeCNF
    rw [hc,Encodable.encodek]
  obtain ⟨hflat,hpayload,hcomm,hcount⟩ := formula_values f flat p payload t tail (hdecode.symm.trans hdecode')
  refine ⟨p,c,n,hp,hc',hn,hpayload,hcv.trans hcomm,hnv.trans hcount,?_⟩
  rw [←hflat]
  exact hfields

end NearCubicWires.RepairOrdinary.RecoveryMarker
