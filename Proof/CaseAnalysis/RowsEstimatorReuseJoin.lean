import Proof.CaseAnalysis.RowsEstimatorReuseAfter

/-! The enclosing estimator composition is proved with a symbolic state
count. Its native source and native capacity survive the paid append/sweep. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape RepairRepresentation RecoveryRootRound CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem join_run (p : Program) {s : ℕ} (first : Machine (tapes p) s)
    (entry : Configuration (tapes p) s) (fuel b D : ℕ)
    (q : CompetitorValidity.Estimate) (count denominator : ℕ) (out : List Bool)
    (before : ExecutionReceipt (tapes p) s)
    (hr : runFrom first fuel entry=some before) (hb : 20*b+27≤D+1)
    (bh : ∀ i,i≠output p → before.final.heads i=0)
    (bo : before.final.heads (output p)=out.length)
    (bword : before.final.tapes (old p (Whole.recordSlot p))=
      ZeroPadding.pad D (Stream.recordWord b q count denominator))
    (bout : before.final.tapes (output p)=out)
    (blog : before.final.tapes (log p)=List.replicate (D+1) false)
    (bdriver : before.final.tapes (driver p)=List.replicate D true)
    (bsize : ∀ i,(before.final.tapes (work p i)).length≤D) :
    ∃ r,runFrom (Composition.machine first (after p)) (fuel+1+afterBudget b D)
        (Composition.leftConfig _ entry)=some r ∧
      r.steps≤before.steps+1+afterBudget b D ∧
      r.final.heads=(fun i=>if i=output p then (out++Stream.recordWord b q count denominator).length else 0) ∧
      r.final.tapes (output p)=out++Stream.recordWord b q count denominator ∧
      (∀ i,r.final.tapes (work p i)=List.replicate D false) ∧
      r.final.tapes (driver p)=List.replicate D true ∧
      r.final.tapes (log p)=List.replicate (D+1) false ∧
      (∀ i,i.val=52 ∨ i.val=68 → r.final.tapes i=before.final.tapes i) := by
  obtain ⟨tail,ht,ts,th,tt⟩:=after_run p b q count denominator D out
    before.final.heads before.final.tapes hb bword bout blog bdriver bh bo bsize
  have htail : runFrom (after p) (afterBudget b D)
      (Composition.restart before.final (after p).start)=some tail:=ht
  have whole:=Composition.run_join first (after p) fuel (afterBudget b D) entry before tail hr htail
  refine ⟨Composition.joinedReceipt before tail,whole,?_,?_,?_,?_,?_,?_,?_⟩
  · change before.steps+1+tail.steps≤_
    omega
  · change tail.final.heads=_
    exact th.trans (by
      funext i
      by_cases he:i=output p
      · subst i
        simp only [Function.update_self,ite_true]
      · exact (Function.update_of_ne he _ _).trans ((bh i he).trans (if_neg he).symm))
  · change tail.final.tapes (output p)=_
    have h:=congrFun tt (output p)
    exact h.trans ((install_other _ _ _ _ (erase_avoids p (output p) (Or.inr (Or.inr rfl)))).trans
      (Function.update_self _ _ _))
  · intro i
    change tail.final.tapes (work p i)=_
    have h:=congrFun tt (eraseSlots p ((i.castAdd 1).castAdd 1))
    rw [install_slot _ (erase_injective p)] at h
    simpa only [erase_work,erased,Fin.addCases_left] using h
  · change tail.final.tapes (driver p)=_
    have h:=congrFun tt (eraseSlots p ((((0 : Fin 1).natAdd (WholePrefix.tapes p-2)).castAdd 1)))
    rw [install_slot _ (erase_injective p)] at h
    simpa only [eraseSlots,erased,Fin.addCases_left,Fin.addCases_right] using h
  · change tail.final.tapes (log p)=_
    have h:=congrFun tt (eraseSlots p ((0 : Fin 1).natAdd (WholePrefix.tapes p-2+1)))
    rw [install_slot _ (erase_injective p)] at h
    simpa only [eraseSlots,erased,Fin.addCases_right] using h
  · intro i hi
    change tail.final.tapes i=_
    have hn : i≠output p := by
      intro he
      have hv:=congrArg Fin.val he
      have ht : 70≤WholePrefix.tapes p:=by unfold WholePrefix.tapes;omega
      simp only [output,Fin.val_natAdd] at hv
      rcases hi with hi|hi <;> omega
    exact (congrFun tt i).trans ((install_other (eraseSlots p) _ _ i
      (erase_avoids p i (hi.elim (fun h=>Or.inl (Fin.ext h)) (fun h=>Or.inr (Or.inl (Fin.ext h)))))).trans
      (Function.update_of_ne hn _ _))

theorem join_run_bounded (p : Program) {s : ℕ} (first : Machine (tapes p) s)
    (entry : Configuration (tapes p) s) (fuel b D : ℕ)
    (q : CompetitorValidity.Estimate) (count denominator : ℕ) (out : List Bool)
    (before : ExecutionReceipt (tapes p) s)
    (hr : runFrom first fuel entry=some before) (hb : 20*b+27≤D+1) (hs : before.steps≤2*D+2)
    (bh : ∀ i,i≠output p → before.final.heads i=0)
    (bo : before.final.heads (output p)=out.length)
    (bword : before.final.tapes (old p (Whole.recordSlot p))=
      ZeroPadding.pad D (Stream.recordWord b q count denominator))
    (bout : before.final.tapes (output p)=out)
    (blog : before.final.tapes (log p)=List.replicate (D+1) false)
    (bdriver : before.final.tapes (driver p)=List.replicate D true)
    (bsize : ∀ i,(before.final.tapes (work p i)).length≤D) :
    ∃ r,runFrom (Composition.machine first (after p)) (fuel+1+afterBudget b D)
        (Composition.leftConfig _ entry)=some r ∧
      r.steps≤4*D+40*b+64 ∧
      r.final.heads=(fun i=>if i=output p then (out++Stream.recordWord b q count denominator).length else 0) ∧
      r.final.tapes (output p)=out++Stream.recordWord b q count denominator ∧
      (∀ i,r.final.tapes (work p i)=List.replicate D false) ∧
      r.final.tapes (driver p)=List.replicate D true ∧
      r.final.tapes (log p)=List.replicate (D+1) false := by
  obtain ⟨r,hrun,hsteps,hh,ho,hw,hd,hl,_hk⟩:=join_run p first entry fuel b D q count denominator
    out before hr hb bh bo bword bout blog bdriver bsize
  refine ⟨r,hrun,?_,hh,ho,hw,hd,hl⟩
  unfold afterBudget at hsteps
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
