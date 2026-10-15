import Proof.CaseAnalysis.RowsEstimatorDriverReturn

/-! The existing masked reset returns each selected cursor by its recorded
step count even when that cursor began farther right. No head bound is
needed for this exact subtraction endpoint. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverSweep
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open Rewind (recording rewinding config)
open SelectiveReset (finished)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem partial_reset {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool) (fuel : ℕ)
    (c : Configuration t s) (source : ExecutionReceipt t s) (hr : runFrom p fuel c=some source) :
    ∃ r,runFrom (MaskedReset.machine p selected) (2*source.steps+2) (recording c 0)=some r ∧
      r.final=finished (s:=s) (fun i => if selected i then source.final.heads i-source.steps else source.final.heads i)
        source.final.tapes source.steps ∧ r.steps=2*source.steps+2 := by
  obtain ⟨hp,hh⟩ := prefix_of_run p fuel c source hr
  have hc := SortMatrix.final_cells hp
  have recorded := MaskedReset.recording_prefix hp selected 0
  have reset := MaskedReset.rewind_prefix p selected source.final.heads source.final.tapes source.steps 0
  have reset' := reset.enlarge (large:=source.peakTapeCells+source.steps) (by
    change source.final.tapeCells+source.steps+0 ≤ _
    omega)
  have bridge := Prefix.step
    (by
      simp only [recording,Rewind.config_cells,List.length_replicate]
      change source.final.tapeCells+source.steps ≤ _
      omega : (recording source.final source.steps).tapeCells ≤ source.peakTapeCells+source.steps)
    (by simp [MaskedReset.machine,Rewind.machine,recording,config])
    (MaskedReset.bridge_step p selected source.final source.steps hh) reset'
  have joined := (by simpa only [Nat.zero_add,Nat.add_zero] using recorded :
    Prefix (MaskedReset.machine p selected) (source.peakTapeCells+source.steps) source.steps
      (recording c 0) (recording source.final source.steps)).trans bridge
  obtain ⟨r,hrun,hf,hs,_⟩ := joined.run
    (by simp [MaskedReset.machine,Rewind.machine,finished,config]) (by
      simp only [finished,Rewind.config_cells,List.length_replicate,Nat.add_zero]
      change source.final.tapeCells+source.steps ≤ _
      omega)
  exact ⟨r,by simpa only [Nat.add_zero,Nat.add_assoc,two_mul] using hrun,
    by simpa only [Nat.add_zero] using hf,by omega⟩

theorem partial_workspace {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool) (fuel cap : ℕ)
    (c : Configuration t s) (source : ExecutionReceipt t s) (hr : runFrom p fuel c=some source) :
    ∃ r,runFrom (MaskedReset.machine p selected) (2*source.steps+2)
        (ZeroPadding.config (Rewind.Workspace.capacities t cap) (recording c 0))=some r ∧
      r.final=finished (s:=s) (fun i => if selected i then source.final.heads i-source.steps else source.final.heads i)
        source.final.tapes (max cap source.steps) ∧ r.steps=2*source.steps+2 := by
  obtain ⟨base,hb,bf,bs⟩ := partial_reset p selected fuel c source hr
  obtain ⟨r,run,rf,rs,_⟩ := ZeroPadding.run_config (MaskedReset.machine p selected)
    (Rewind.Workspace.capacities t cap) _ _ base hb
  refine ⟨r,run,?_,rs.trans bs⟩
  rw [rf,bf,SelectiveReset.padded_finished]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverSweep
