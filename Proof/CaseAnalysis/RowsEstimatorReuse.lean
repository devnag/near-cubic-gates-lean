import Proof.CaseAnalysis.CloseoutRowsEstimatorWarm
import Proof.CaseAnalysis.RowsEstimatorReuseRun
import Proof.CaseAnalysis.RowsEstimatorDriverBounds

/-! The same append/sweep bank after the scanner interposition. The warm
callee starts with every head zero, so the original complete rewind suffices;
no special native-cursor reset premise is needed. D backing is supplied by
the checked physical pad-in-place pass. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmReuse
open LocalBitMultitape RepairRepresentation RecoveryRootRound CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s):=
  TapeEmbedding.machine 2 (Rewind.machine worker)
noncomputable def machine {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s):=
  Composition.machine (first p worker) (Reuse.after p)
def padded (p : Program) (D : ℕ) (A : Fin (WholePrefix.tapes p)→List Bool) :=
  fun i=>ZeroPadding.pad (Reset.caps p D i) (A i)
noncomputable def entry {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (D : ℕ) (A : Fin (WholePrefix.tapes p)→List Bool) (out : List Bool) :=
  Composition.leftConfig 24 (TapeEmbedding.config (![out.length,0] : Fin 2→ℕ)
    (![out,List.replicate D true] : Fin 2→List Bool)
    (initialConfiguration (Rewind.machine worker)
      (Fin.addCases (padded p D A) (fun _ : Fin 1=>List.replicate (D+1) false))))

private theorem embedded_steps {t e s : ℕ} (H : Fin e→ℕ) (A : Fin e→List Bool)
    (r : ExecutionReceipt t s) : (TapeEmbedding.receipt H A r).steps=r.steps:=rfl

theorem run {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (A : Fin (WholePrefix.tapes p)→List Bool) (fuel b D : ℕ)
    (q : CompetitorValidity.Estimate) (count denominator : ℕ) (out : List Bool)
    (source : ExecutionReceipt (WholePrefix.tapes p) s)
    (hr : LocalBitMultitape.run worker fuel A=some source)
    (hrecord : source.final.tapes (Whole.recordSlot p)=Stream.recordWord b q count denominator)
    (hD : source.steps+1≤D) (hb : 20*b+27≤D+1)
    (hsize : ∀ i,(A i).length≤D) : ∃ r,
    runFrom (machine p worker) (Reuse.budget fuel b D) (entry p worker D A out)=some r ∧
      r.steps≤4*D+40*b+64 ∧
      r.final.heads=(fun i=>if i=Reuse.output p then (out++Stream.recordWord b q count denominator).length else 0) ∧
      r.final.tapes (Reuse.output p)=out++Stream.recordWord b q count denominator ∧
      (∀ i,r.final.tapes (Reuse.work p i)=List.replicate D false) ∧
      r.final.tapes (Reuse.driver p)=List.replicate D true ∧
      r.final.tapes (Reuse.log p)=List.replicate (D+1) false := by
  obtain ⟨pad,hp,pf,ps,_⟩:=ZeroPadding.run_config worker (Reset.caps p D) _ _ source hr
  have hp' : LocalBitMultitape.run worker fuel (padded p D A)=some pad:=hp
  obtain ⟨reset,rr,rt,rl,rh,rs,_⟩:=Rewind.Workspace.reset_workspace worker fuel _ pad hp' (D+1)
  have rsteps : reset.steps=2*source.steps+2:=by rw [rs,ps]
  rw [ps] at rr
  have htime:=runFrom_steps_le worker _ _ _ hr
  have rr' : LocalBitMultitape.run (Rewind.machine worker) (2*fuel+2)
      (Fin.addCases (padded p D A) (fun _ : Fin 1=>List.replicate (D+1) false))=some reset := by
    have hm:=run_moreFuel (Rewind.machine worker) (2*source.steps+2)
      (2*fuel+2-(2*source.steps+2)) _ reset rr
    rw [Nat.add_sub_of_le (by omega : 2*source.steps+2≤2*fuel+2)] at hm
    exact hm
  have resetT (i : Fin (WholePrefix.tapes p)) :
      reset.final.tapes (i.castAdd 1)=ZeroPadding.pad (Reset.caps p D i) (source.final.tapes i) :=
    (rt i).trans (congrArg (fun c=>c.tapes i) pf)
  have resetLog : reset.final.tapes ((0 : Fin 1).natAdd (WholePrefix.tapes p))=
      List.replicate (D+1) false := by
    rw [rl,ps,Nat.max_eq_left (by omega : source.steps≤D+1)]
  let before:=TapeEmbedding.receipt (![out.length,0] : Fin 2→ℕ)
    (![out,List.replicate D true] : Fin 2→List Bool) reset
  have hfirst:=TapeEmbedding.run_embed (Rewind.machine worker) (![out.length,0] : Fin 2→ℕ)
    (![out,List.replicate D true] : Fin 2→List Bool) _ _ reset rr'
  have bh : ∀ i,i≠Reuse.output p → before.final.heads i=0 := by
    intro i
    refine Fin.addCases (fun j _=>?_) (fun j hj=>?_) i
    · exact (TapeEmbedding.receipt_heads_old _ _ reset j).trans (rh j)
    · fin_cases j
      · exact False.elim (hj rfl)
      · exact TapeEmbedding.receipt_heads_new _ _ reset 1
  have bword : before.final.tapes (Reuse.old p (Whole.recordSlot p))=
      ZeroPadding.pad D (Stream.recordWord b q count denominator) := by
    have h:=(TapeEmbedding.receipt_tapes_old (![out.length,0] : Fin 2→ℕ)
      (![out,List.replicate D true] : Fin 2→List Bool) reset ((Whole.recordSlot p).castAdd 1)).trans
      (resetT (Whole.recordSlot p))
    rw [Reuse.record_caps,hrecord] at h
    exact h
  have bsize : ∀ i,(before.final.tapes (Reuse.work p i)).length≤D := by
    intro i
    let j : Fin (WholePrefix.tapes p):=⟨(Reuse.work p i).val,(Reuse.work_bounds p i).1⟩
    have hj : Reuse.work p i=Reuse.old p j:=Reuse.work_old p i
    rw [hj]
    have ht:=(TapeEmbedding.receipt_tapes_old (![out.length,0] : Fin 2→ℕ)
      (![out,List.replicate D true] : Fin 2→List Bool) reset (j.castAdd 1)).trans (resetT j)
    change before.final.tapes (Reuse.old p j)=ZeroPadding.pad (Reset.caps p D j) (source.final.tapes j) at ht
    rw [ht,ZeroPadding.pad_length]
    have hs:=CloseoutRowsProjectionReset.scratch_support worker fuel D _ source hr j rfl (hsize j) hD
    have hc : Reset.caps p D j≤D := by unfold Reset.caps;split_ifs <;>omega
    omega
  have beforeSteps : before.steps≤2*D+2 := by
    rw [embedded_steps,rsteps]
    omega
  exact Reuse.join_run_bounded p (first p worker) _ (2*fuel+2) b D q count denominator out before hfirst hb
    beforeSteps bh (TapeEmbedding.receipt_heads_new _ _ reset 0) bword
    (TapeEmbedding.receipt_tapes_new _ _ reset 0)
    ((TapeEmbedding.receipt_tapes_old (![out.length,0] : Fin 2→ℕ)
      (![out,List.replicate D true] : Fin 2→List Bool) reset ((0 : Fin 1).natAdd (WholePrefix.tapes p))).trans resetLog)
    (TapeEmbedding.receipt_tapes_new _ _ reset 1) bsize

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmReuse
