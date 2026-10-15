import Proof.CaseAnalysis.RowsEstimatorPrepareLive

/-! The prepared bank is the original reusable Warm entry with seven retained sources. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound WarmPrepare
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem spare_val (p : Program) : (spare p).val=WholePrefix.tapes p+1 := rfl
theorem old_ne (p : Program) (i : Fin (WholePrefix.tapes p)) : old p i≠spare p := by
  intro he
  have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
  rw [old_val,spare_val] at hv
  have hi:=i.isLt
  omega
theorem log_ne (p : Program) : log p≠spare p := by
  intro he
  have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
  rw [log_val,spare_val] at hv
  omega
theorem driver_ne (p : Program) : driver p≠spare p := by
  intro he
  have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
  rw [driver_val,spare_val] at hv
  omega
theorem source_ne (p : Program) (i : Fin 7) : source p i≠spare p := by
  intro he
  have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
  rw [source_val,spare_val] at hv
  unfold Reuse.tapes at hv
  omega

theorem live_data (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) :
    Fin.addCases (Fin.addCases (Fin.addCases A (fun _ : Fin 1=>List.replicate L false))
      (![out,List.replicate D true] : Fin 2 → List Bool)) fields=live p (data p A D L fields) out := by
  apply data_ext p
  · intro i
    rw [live,Function.update_of_ne (old_ne p i),at_old]
    simp only [old,Reuse.old,Fin.addCases_left]
  · rw [live,Function.update_of_ne (log_ne p),at_log]
    simp only [log,Reuse.log,Fin.addCases_left,Fin.addCases_right]
  · rw [live,Function.update_self]
    simp only [spare,Reuse.output,Fin.addCases_left,Fin.addCases_right,Matrix.cons_val_zero]
  · rw [live,Function.update_of_ne (driver_ne p),at_driver]
    simp only [driver,Reuse.driver,Fin.addCases_left,Fin.addCases_right,Matrix.cons_val_one,Matrix.cons_val_zero]
  · intro i
    rw [live,Function.update_of_ne (source_ne p i),at_source]
    simp only [source,Fin.addCases_right]

theorem live_heads (p : Program) (out : List Bool) :
    Fin.addCases (Fin.addCases (fun _ : Fin (WholePrefix.tapes p+1)=>0)
      (![out.length,0] : Fin 2 → ℕ)) (fun _ : Fin 7=>0)=heads p out := by
  funext i
  refine Fin.addCases (m:=Reuse.tapes p) (n:=7) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=WholePrefix.tapes p+1) (n:=2) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=WholePrefix.tapes p) (n:=1) (fun l=>?_) (fun l=>?_) k
      · simp only [Fin.addCases_left]
        change 0=heads p out (old p l)
        simp only [heads,old_ne p l,ite_false]
      · have he : l=0:=Subsingleton.elim _ _
        subst l
        simp only [Fin.addCases_left]
        change 0=heads p out (log p)
        simp only [heads,log_ne p,ite_false]
    · fin_cases k
      · simp only [Fin.addCases_left,Fin.addCases_right]
        change out.length=heads p out (spare p)
        simp only [heads,ite_true]
      · simp only [Fin.addCases_left,Fin.addCases_right]
        change 0=heads p out (driver p)
        simp only [heads,driver_ne p,ite_false]
  · simp only [Fin.addCases_right]
    change 0=heads p out (source p j)
    simp only [heads,source_ne p j,ite_false]

theorem warm_entry {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (A : Fin (WholePrefix.tapes p) → List Bool) (D : ℕ) (fields : Fin 7 → List Bool) (out : List Bool) :
    TapeEmbedding.config (fun _ : Fin 7=>0) fields (WarmReuse.entry p worker D A out)=
      (⟨(TapeEmbedding.machine 7 (WarmReuse.machine p worker)).start,heads p out,
        live p (data p (WarmReuse.padded p D A) D (D+1) fields) out⟩ : Configuration (tapes p) _) := by
  apply configuration_ext
  · rfl
  · dsimp only [TapeEmbedding.config,WarmReuse.entry,Composition.leftConfig,initialConfiguration]
    exact live_heads p out
  · dsimp only [TapeEmbedding.config,WarmReuse.entry,Composition.leftConfig,initialConfiguration]
    exact live_data p (WarmReuse.padded p D A) D (D+1) fields out

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared
