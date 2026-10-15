import Proof.CaseAnalysis.RecoveryHierarchyDockCountLayout

/-! Actual final count copy at the normalizer's head-one counter, retaining
all other source/stream tapes and every unrelated physical cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdHierarchyDock.Count
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem tail_run {k s : ℕ} (c : Configuration (RecoveryBoundedColdHierarchyDock.tapes source k) s)
    (n : ℕ) (hcount : c.tapes (clauseCountPort source k)=CompareMachine.word n)
    (hc : c.heads (clauseCountPort source k)=1)
    (hout : c.tapes (RecoveryBoundedColdHierarchyDock.old source k 157)=[])
    (ho : c.heads (RecoveryBoundedColdHierarchyDock.old source k 157)=0) :
    ∃ r,runFrom (last source k) (RecoveryBoundedColdClauseCount.budget n)
      ⟨(last source k).start,Fin.addCases c.heads (fun _=>0),Fin.addCases c.tapes (fun _=>[])⟩=some r ∧
      r.steps≤RecoveryBoundedColdClauseCount.budget n ∧
      r.final.tapes (old source k 157)=List.replicate n true ∧
      r.final.heads (old source k 157)=0 ∧ r.final.heads (counter source k)=0 ∧
      (∀ i,i≠RecoveryBoundedColdHierarchyDock.old source k 157→
        r.final.tapes (prior source k i)=c.tapes i) ∧
      (∀ i,i≠RecoveryBoundedColdHierarchyDock.old source k 157→i≠clauseCountPort source k→
        r.final.heads (prior source k i)=c.heads i):=by
  obtain ⟨countRun,hr,hs,hh,ht⟩:=RecoveryBoundedColdClauseCount.count_run n
  obtain ⟨result,hresult,_hcontrol,hsteps,hheads,htapes,hother⟩:=RecoveryFocus.dock
    (slots source k) (slots_injective source k) RecoveryBoundedColdClauseCount.machine
    (RecoveryBoundedColdClauseCount.budget n) (Fin.addCases c.heads (fun _=>0))
    (Fin.addCases c.tapes (fun _=>[])) _ (by
      intro j
      fin_cases j
      · exact (Fin.addCases_left (clauseCountPort source k)).trans hc
      · exact (Fin.addCases_left (RecoveryBoundedColdHierarchyDock.old source k 157)).trans ho
      · exact Fin.addCases_right (0 : Fin 1)) (by
      intro j
      fin_cases j
      · exact (Fin.addCases_left (clauseCountPort source k)).trans hcount
      · exact (Fin.addCases_left (RecoveryBoundedColdHierarchyDock.old source k 157)).trans hout
      · exact Fin.addCases_right (0 : Fin 1)) countRun hr
  refine ⟨result,hresult,hsteps.trans_le hs,(htapes 1).trans (congrFun ht 1),
    (hheads 1).trans (congrFun hh 1),(hheads 0).trans (congrFun hh 0),?_,?_⟩
  · intro i hi
    by_cases hic : i=clauseCountPort source k
    · subst i
      exact ((htapes 0).trans (congrFun ht 0)).trans hcount.symm
    · exact (hother (prior source k i) (slots_away source k i hi hic)).2.trans
        (Fin.addCases_left i)
  · intro i hi hic
    exact (hother (prior source k i) (slots_away source k i hi hic)).1.trans
      (Fin.addCases_left i)

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdHierarchyDock.Count
