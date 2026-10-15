import Proof.Hierarchy.HierarchyClauseLayout

/-! The same hierarchy/source prefix physically supplies the query and
clause encodings and retains the two original width/query scalar fields. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyClauses
open LocalBitMultitape RepairOrdinary PCPSerializerMass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem clause_run (k CH Cpad : ℕ) (code x bound : List Bool) (hpad : k+3 ≤ Cpad) :
    ∃ r,runFrom (machine source k CH Cpad code) (budget source k CH Cpad code x)
      (entry source k CH Cpad code x bound)=some r ∧
      (∀ i : Fin 4,r.final.tapes (fieldSlots source k i)=
        frame (words source k CH Cpad code x i)++suffixes source k CH Cpad code x i) ∧
      (∀ i : Fin 4,r.final.heads (fieldSlots source k i)=0) ∧
      r.steps ≤ budget source k CH Cpad code x := by
  obtain ⟨q,p,hq,_hp,pf,q77,_q78,qh77,_qh78,qt,qh,_qs⟩ :=
    HierarchyQuery.query_run source k CH Cpad code x bound hpad
  have h38 : HierarchyStreams.slots source k 38≠HierarchyQuery.sourceSlot source k := by
    intro h
    have he := HierarchyStreams.slots_injective source k h
    exact (by decide : (38 : Fin 48)≠29) he
  have h46 : HierarchyStreams.slots source k 46≠HierarchyQuery.sourceSlot source k := by
    intro h
    have he := HierarchyStreams.slots_injective source k h
    exact (by decide : (46 : Fin 48)≠29) he
  have hsource : q.final.tapes (sourceSlot source k)=PCPTripleLoop.stream (groups source k CH Cpad code x) := by
    exact ((qt _).trans pf.clauseStream).trans (PCPTripleNative.group_stream _).symm
  have hcount : q.final.tapes (countSlot source k)=VerifierDecoding.CompareMachine.word
      (groups source k CH Cpad code x).length := by
    exact ((qt _).trans pf.clauseCount).trans
      (congrArg VerifierDecoding.CompareMachine.word (PCPTripleNative.group_count _).symm)
  have hs : q.final.heads (sourceSlot source k)=0 := (qh _ h38).trans pf.clauseStreamHead
  have hc : q.final.heads (countSlot source k)=1 := (qh _ h46).trans pf.clauseCountHead
  obtain ⟨r,hr,r258,_r259,rh258,_rh259,ret,rs⟩ := PCPClauseBank.producer_run
    (sourceSlot source k) (countSlot source k) (slots_ne source k)
    (HierarchyQuery.machine source k CH Cpad code) _ _ q hq (groups source k CH Cpad code x)
    (PCPTripleNative.group_three _) hs hc hsource hcount
  have old_ne (i : Fin (HierarchyStreams.base source k)) (j : Fin 48)
      (h0 : j≠0) (h13 : j≠13) (h14 : j≠14) :
      (HierarchyStreams.old source k i).castAdd 128≠(HierarchyStreams.slots source k j).castAdd 128 := by
    intro he
    have hv := congrArg (fun z : Fin (base source k) => z.val) he
    exact old_not_slot source k i j h0 h13 h14 (Fin.ext hv)
  have widthRet := ret ((HierarchyStreams.old source k (HierarchyStreams.bitsR source k)).castAdd 128)
    (old_ne _ 38 (by decide) (by decide) (by decide))
    (old_ne _ 46 (by decide) (by decide) (by decide))
  have queriesRet := ret ((HierarchyStreams.old source k (HierarchyStreams.bitsQ source k)).castAdd 128)
    (old_ne _ 38 (by decide) (by decide) (by decide))
    (old_ne _ 46 (by decide) (by decide) (by decide))
  have queryNe (i : Fin (HierarchyStreams.tapes source k)) :
      (77 : Fin 128).natAdd (HierarchyStreams.tapes source k)≠i.castAdd 128 := by
    intro he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  have queryRet := ret ((77 : Fin 128).natAdd (HierarchyStreams.tapes source k)) (queryNe _) (queryNe _)
  refine ⟨r,hr,?_,?_,rs⟩
  · intro i
    fin_cases i
    · change r.final.tapes (widthSlot source k)=frame (HierarchyStreams.R source k CH Cpad code x).bits++[]
      exact ((widthRet.1.trans (qt _)).trans pf.width).trans (List.append_nil _).symm
    · change r.final.tapes (queriesSlot source k)=frame (HierarchyStreams.Q source k CH Cpad code x).bits++[]
      exact ((queriesRet.1.trans (qt _)).trans pf.queries).trans (List.append_nil _).symm
    · exact queryRet.1.trans q77
    · exact r258
  · intro i
    fin_cases i
    · change r.final.heads (widthSlot source k)=0
      exact (widthRet.2.trans (qh _ (old_not_slot source k _ 29 (by decide) (by decide) (by decide)))).trans pf.widthHead
    · change r.final.heads (queriesSlot source k)=0
      exact (queriesRet.2.trans (qh _ (old_not_slot source k _ 29 (by decide) (by decide) (by decide)))).trans pf.queriesHead
    · exact queryRet.2.trans qh77
    · exact rh258

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyClauses
