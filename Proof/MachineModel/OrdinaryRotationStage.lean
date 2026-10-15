import Proof.MachineModel.OrdinaryRecordRotate
import Proof.MachineModel.OrdinaryRewindWorkspace
import Proof.Foundations.OrdinaryTapeEmbedding

/-! Record rotation on the same four-tape workspace as the Boolean pass.
Data tape2 is retained, and the existing counter supplies a paid reset. -/
namespace NearCubicWires.RepairOrdinary.RotationStage
open LocalBitMultitape StablePartition
open StablePartition.Workspace (overlay)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawMachine : Machine 3 14 := TapeEmbedding.machine 1 RecordRotate.machine
def machine : Machine 4 16 := Rewind.machine rawMachine

theorem raw_run (rs : List Record) (junk backing unused : List Bool) (capacity : ℕ)
    (hi : (stream rs).length + junk.length ≤ capacity)
    (hb : backing.length ≤ capacity) (hu : unused.length ≤ capacity) :
    ∃ r : ExecutionReceipt 3 14,
      run rawMachine (RecordRotate.recordsCost rs + 1)
        (fun i => if i.val = 0 then stream rs ++ junk else if i.val = 1 then backing else unused) = some r ∧
      r.final.tapes 1 = overlay (stream (rs.map RecordRotate.rotate)) backing ∧
      (∀ i, (r.final.tapes i).length ≤ capacity) ∧
      r.steps = RecordRotate.recordsCost rs + 1 ∧ r.steps ≤ 2 * (stream rs).length ∧
      r.peakTapeCells ≤ 4 * capacity := by
  obtain ⟨source, hr, _, hout, hcells, hsteps, hcost, hpeak⟩ := RecordRotate.rotate_run rs junk backing capacity hi hb
  have he := TapeEmbedding.run_embed RecordRotate.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => unused) (RecordRotate.recordsCost rs + 1) _ source hr
  have hinit : initialConfiguration rawMachine
        (fun i => if i.val = 0 then stream rs ++ junk else if i.val = 1 then backing else unused) =
      TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => unused)
        (initialConfiguration RecordRotate.machine (fun i => if i.val = 0 then stream rs ++ junk else backing)) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := 2) (n := 1) (fun j => ?_) (fun j => ?_) i <;> simp [initialConfiguration, TapeEmbedding.config]
    · funext i
      refine Fin.addCases (m := 2) (n := 1) (fun j => ?_) (fun j => ?_) i
      · fin_cases j <;> simp [initialConfiguration, TapeEmbedding.config, Fin.addCases]
      · fin_cases j
        simp [initialConfiguration, TapeEmbedding.config, Fin.addCases]
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => unused) source,
    ?_, ?_, ?_, hsteps, hcost, ?_⟩
  · change runFrom rawMachine _ _ = _
    rw [hinit]
    exact he
  · have h : (TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => unused) source).final.tapes
        ((1 : Fin 2).castAdd 1) = source.final.tapes 1 := by
      simp only [TapeEmbedding.receipt, TapeEmbedding.config, Fin.addCases_left]
    simpa using h.trans hout
  · intro i
    refine Fin.addCases (m := 2) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simpa [TapeEmbedding.receipt, TapeEmbedding.config] using hcells j
    · simpa [TapeEmbedding.receipt, TapeEmbedding.config] using hu
  · simp [TapeEmbedding.receipt, TapeEmbedding.extraCells]
    omega

theorem rotation_stage (rs : List Record) (junk backing unused : List Bool) (capacity : ℕ)
    (hi : (stream rs).length + junk.length ≤ capacity)
    (hb : backing.length ≤ capacity) (hu : unused.length ≤ capacity) :
    ∃ r : ExecutionReceipt 4 16,
      run machine (2 * (RecordRotate.recordsCost rs + 1) + 2)
        (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
          (fun i : Fin 3 => if i.val = 0 then stream rs ++ junk else if i.val = 1 then backing else unused)
          (fun _ : Fin 1 => List.replicate (2 * capacity) false)) = some r ∧
      r.final.tapes 1 = overlay (stream (rs.map RecordRotate.rotate)) backing ∧
      (∀ i : Fin 3, (r.final.tapes (i.castAdd 1)).length ≤ capacity) ∧
      r.final.tapes 3 = List.replicate (2 * capacity) false ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps ≤ 4 * (stream rs).length + 2 ∧
      r.peakTapeCells ≤ 8 * capacity := by
  obtain ⟨source, hr, hout, hcells, hsteps, hcost, hpeak⟩ := raw_run rs junk backing unused capacity hi hb hu
  obtain ⟨r, hrun, he, hcounter, hheads, hcount, hspace⟩ := Rewind.Workspace.reset_workspace rawMachine
    (RecordRotate.recordsCost rs + 1) _ source hr (2 * capacity)
  refine ⟨r, ?_, ?_, ?_, ?_, hheads, ?_, ?_⟩
  · simpa only [machine, hsteps] using hrun
  · have h := (he 1).trans hout
    simpa using h
  · intro i
    rw [he i]
    exact hcells i
  · have hn : max (2 * capacity) source.steps = 2 * capacity := max_eq_left (by omega)
    simpa [hn] using hcounter
  · omega
  · omega

end NearCubicWires.RepairOrdinary.RotationStage
