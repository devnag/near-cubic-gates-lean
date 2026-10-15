import Proof.CaseAnalysis.CaseTwoOccurrencePorts

/-! One complete occurrence from the retained original request/cache and
final address. All address preparation and both assignment branches execute. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Occurrence
open LocalBitMultitape SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem run (D block : ℕ) (hD : 1 ≤ D) (a : PointwisePCPPAlgorithm)
    (r : PCPPRequest a.minimumArity) (u : BitInput r.arity)
    (clause : BitInput (a.output r).clauseBits) (pad pre tail : List Bool) (position : Bool)
    (hpad : (a.output r).clauseBits+pad.length=RepairSource.CloseoutLanguage.clauseWidth D r.arity)
    (hpre : pre.length=block*(r.arity+RepairSource.CloseoutLanguage.clauseWidth D r.arity+1)) :
    let address:=pre++AddressFields.word u clause pad position++tail
    ∃ out,runFrom (machine D block a) (budget D block a r u clause position pad.length)
      ⟨(machine D block a).start,heads D a,input D a r address⟩=some out ∧
      out.steps ≤ budget D block a r u clause position pad.length ∧
      out.final.tapes (outputSlot D a)=
        [(a.output r).assignment u ((a.output r).honestAuxiliary u)
          (OccurrenceBit.named a r (binaryAddress clause) position)] ∧
      out.final.tapes (old D a (OccurrenceAddress.base D 57))=frame address:=by
  dsimp only
  let address:=pre++AddressFields.word u clause pad position++tail
  obtain ⟨ar,har,as_,ah,arData⟩:=OccurrenceAddress.address_run D block hD a r u clause pad pre tail position hpad hpre
  obtain ⟨p,hp,_,ps,ph,pt,pkeep⟩:=RecoveryFocus.dock (old D a) (old_injective D a)
    (OccurrenceAddress.machine D block) _ (heads D a) (input D a r address) _
    (by intro j;exact Fin.addCases_left j) (by intro j;exact Fin.addCases_left j) ar har
  have fresh (j : Fin (OccurrenceBit.tapes a)) :
      p.final.heads (j.natAdd (OccurrenceAddress.tapes D))=0 ∧
      p.final.tapes (j.natAdd (OccurrenceAddress.tapes D))=[]:=by
    have outside : ∀ i,old D a i≠j.natAdd (OccurrenceAddress.tapes D):=by
      intro i he
      have h:=congrArg Fin.val he
      have hi:=i.isLt
      simp only [old,Fin.val_castAdd,Fin.val_natAdd] at h
      omega
    have keep:=pkeep _ outside
    simpa only [heads,input,Fin.addCases_right] using keep
  obtain ⟨b,hb,bs,bit⟩:=OccurrenceBit.bit_run a r u (binaryAddress clause) position
  obtain ⟨lastReceipt,hl,_,ls,_,lt,keep⟩:=RecoveryFocus.dock (bitSlots D a) (bit_injective D a)
    (OccurrenceBit.machine a) _ p.final.heads p.final.tapes _
    (by intro j
        change p.final.heads (bitSlots D a j)=OccurrenceBit.heads a j
        by_cases hj : j.val<25
        · let k : Fin 25:=⟨j.val,hj⟩
          have he : j=OccurrenceBit.base a k:=Fin.ext rfl
          rw [he]
          simp only [bitSlots,OccurrenceBit.base,OccurrenceBit.old,Fin.val_castAdd,dif_pos k.isLt]
          exact (ph (inputPort D k)).trans ((congrFun ah _).trans (port_heads D a k))
        · rw [bitSlots,dif_neg hj,(fresh j).1]
          simp only [OccurrenceBit.heads,show j.val≠13 by omega,show j.val≠14 by omega,or_self,if_false])
    (by intro j
        change p.final.tapes (bitSlots D a j)=OccurrenceBit.input a r u (binaryAddress clause).val position j
        by_cases hj : j.val<25
        · let k : Fin 25:=⟨j.val,hj⟩
          have he : j=OccurrenceBit.base a k:=Fin.ext rfl
          rw [he]
          simp only [bitSlots,OccurrenceBit.base,OccurrenceBit.old,Fin.val_castAdd,dif_pos k.isLt]
          exact (pt (inputPort D k)).trans (port_data D a r u clause position address ar.final.tapes arData k)
        · rw [bitSlots,dif_neg hj,(fresh j).2]
          exact (OccurrenceBit.high_input a r u (binaryAddress clause).val position j (by omega)).symm) b hb
  have whole:=Composition.run_join (first D block a) (last D a) _ _ _ p lastReceipt hp hl
  refine ⟨_,whole,?_,(lt (OccurrenceBit.outputSlot a)).trans bit,?_⟩
  · change p.steps+1+lastReceipt.steps ≤ _
    rw [ps,ls]
    unfold budget
    omega
  · exact (keep _ (address_outside D a)).2.trans ((pt _).trans arData.address)

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Occurrence
