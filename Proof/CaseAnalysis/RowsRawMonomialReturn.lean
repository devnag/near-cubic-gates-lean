import Proof.CaseAnalysis.RowsRawMonomialCopy

/-! Multiplication reuses the SAME left monomial without a copied cache.
The existing selective rewind returns its arbitrary starting cursor because
the actual body copier advances that cursor exactly once per instruction. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawMonomialReturn
open LocalBitMultitape CloseoutRowsRawMonomialCopy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=SelectiveReset.machine CloseoutRowsRawMonomialCopy.machine 0
def budget (m : List ℕ):=2*(m.flatMap ExtIncidence.block).length+4
noncomputable def input (C : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool):=
  ZeroPadding.config (Rewind.Workspace.capacities 2 C) (Rewind.recording (cfg 0 source pos out) 0)

theorem returned_run (C : ℕ) (m : List ℕ) (pre tail out : List Bool)
    (hc : (m.flatMap ExtIncidence.block).length+1≤C) :
    ∃ r,runFrom machine (budget m)
      (input C (pre++m.flatMap ExtIncidence.block++false::tail) pre.length out)=some r ∧
      r.final.heads=![pre.length,(out++m.flatMap ExtIncidence.block).length,0] ∧
      r.final.tapes=![pre++m.flatMap ExtIncidence.block++false::tail,
        out++m.flatMap ExtIncidence.block,List.replicate C false] ∧
      r.steps=budget m := by
  obtain ⟨raw,hr,rf,rs⟩:=copy_run m pre tail out
  obtain ⟨hp,halted⟩:=prefix_of_run CloseoutRowsRawMonomialCopy.machine _ _ raw hr
  have finalCells:=SortMatrix.final_cells hp
  have recorded:=SelectiveReset.recording_prefix hp 0 0
  have rewind:=SelectiveReset.rewind_prefix CloseoutRowsRawMonomialCopy.machine 0
    raw.final.heads raw.final.tapes raw.steps 0
  have rewind':=rewind.enlarge (large:=raw.peakTapeCells+raw.steps) (by
    change raw.final.tapeCells+raw.steps+0≤_
    omega)
  have bridge:=Prefix.step
    (by
      simp only [Rewind.recording,Rewind.config_cells,List.length_replicate]
      change raw.final.tapeCells+raw.steps≤_
      omega)
    (by simp [SelectiveReset.machine,Rewind.machine,Rewind.recording,Rewind.config])
    (SelectiveReset.bridge_step CloseoutRowsRawMonomialCopy.machine 0 raw.final raw.steps halted) rewind'
  have trace:=(by simpa only [machine,Nat.zero_add,Nat.add_zero] using recorded :
    Prefix machine (raw.peakTapeCells+raw.steps) raw.steps
      (Rewind.recording (cfg 0 (pre++m.flatMap ExtIncidence.block++false::tail) pre.length out) 0)
      (Rewind.recording raw.final raw.steps)).trans bridge
  obtain ⟨base,hb,bf,bs,_⟩:=trace.run
    (by rfl) (by
      simp only [SelectiveReset.finished,Rewind.config_cells,List.length_replicate,Nat.add_zero]
      change raw.final.tapeCells+raw.steps≤_
      omega)
  obtain ⟨r,rr,rfinal,rsteps,_⟩:=ZeroPadding.run_config machine
    (Rewind.Workspace.capacities 2 C) _ _ base hb
  have time:raw.steps+(raw.steps+1+1)=budget m:=by unfold budget;omega
  rw [time] at rr
  have hf:r.final=SelectiveReset.finished (s:=3)
      (![pre.length,(out++m.flatMap ExtIncidence.block).length] : Fin 2→ℕ)
      (![pre++m.flatMap ExtIncidence.block++false::tail,out++m.flatMap ExtIncidence.block] : Fin 2→List Bool) C:=by
    rw [rfinal,bf,SelectiveReset.padded_finished]
    have small:raw.steps+0≤C:=by omega
    rw [max_eq_left small,rf,rs]
    congr 1
    funext i
    fin_cases i <;> simp [cfg]
  refine ⟨r,rr,?_,?_,rsteps.trans (bs.trans time)⟩
  · rw [hf]
    funext i;fin_cases i <;> rfl
  · rw [hf]
    funext i;fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsRawMonomialReturn
