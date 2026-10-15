import Proof.MachineModel.OrdinaryFramedIncrement

/-! Advance and store a bucket's lower boundary using only bounded scalar
tapes. The actual source and growing output can remain inactive extras. -/
namespace NearCubicWires.RepairOrdinary.BoundaryStore
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (W a b : ℕ) (upper : List Bool) : Configuration 5 s :=
  ⟨state, fun _ => 0, ![frame (binary W a), frame (binary W b), upper,
    List.replicate (2 * W + 1) false, List.replicate (4 * W + 3) false]⟩
def layout : Fin 5 ≃ Fin 5 where
  toFun := ![2, 0, 3, 4, 1]
  invFun := ![1, 4, 0, 2, 3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 5 → Fin 5) = ![1, 4, 0, 2, 3] := rfl
def advance : Machine 5 7 := TapeEmbedding.machine 1 BoundaryAdvance.machine
def store : Machine 5 6 := TapeRenaming.machine layout (TapeEmbedding.machine 1 RecordClone.machine)
def machine : Machine 5 13 := Composition.machine advance store

theorem advance_store_run (W a b : ℕ) (upper : List Bool) (hfit : a + b < 2 ^ W)
    (hu : upper.length ≤ 2 * W + 1) :
    ∃ r : ExecutionReceipt 5 13,
      runFrom machine (12 * W + 13) (config machine.start W a b upper) = some r ∧
      r.final = config 12 W (a + b) b (frame (binary W (a + b))) ∧
      r.steps = 12 * W + 13 ∧ r.peakTapeCells ≤ 20 * W + 12 := by
  obtain ⟨first, hr, hleft, hright, hupper, hcounter, hheads, hsteps, hpeak⟩ := BoundaryAdvance.advance_run W a b upper hfit hu
  let extra := fun _ : Fin 1 => List.replicate (4 * W + 3) false
  have he := TapeEmbedding.run_embed BoundaryAdvance.machine (fun _ : Fin 1 => 0) extra _ _ first hr
  obtain ⟨second, hs, ht, hh, htime, hspace⟩ := RecordClone.clone_run (binary W (a + b)) (frame (binary W a)) (by simp)
  simp only [binary_length] at hs htime hspace
  let retained := fun _ : Fin 1 => frame (binary W b)
  have hc := TapeEmbedding.run_embed RecordClone.machine (fun _ : Fin 1 => 0) retained _ _ second hs
  have hn := TapeRenaming.run_rename layout (TapeEmbedding.machine 1 RecordClone.machine) _ _ _ hc
  let next := TapeRenaming.receipt layout (TapeEmbedding.receipt (fun _ : Fin 1 => 0) retained second)
  have hmid : Composition.restart (TapeEmbedding.config (fun _ : Fin 1 => 0) extra first.final) store.start =
      TapeRenaming.config layout (TapeEmbedding.config (fun _ : Fin 1 => 0) retained
        (initialConfiguration RecordClone.machine (RecordClone.input (binary W (a + b)) (frame (binary W a))))) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, TapeEmbedding.config, TapeRenaming.config,
        initialConfiguration, hheads, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.restart, TapeEmbedding.config, TapeRenaming.config,
        initialConfiguration, RecordClone.input, RecordClone.raw, Fin.addCases, extra, retained,
        hleft, hright, hupper, hcounter]
  have hnext : runFrom store (8 * W + 8)
      (Composition.restart (TapeEmbedding.receipt (fun _ : Fin 1 => 0) extra first).final store.start) = some next := by
    change runFrom store (8 * W + 8)
      (Composition.restart (TapeEmbedding.config (fun _ : Fin 1 => 0) extra first.final) store.start) = some next
    rw [hmid]
    exact hn
  have hj := Composition.run_join advance store (4 * W + 4) (8 * W + 8) _
    (TapeEmbedding.receipt (fun _ : Fin 1 => 0) extra first) next he hnext
  have hinit : Composition.leftConfig 6 (TapeEmbedding.config (fun _ : Fin 1 => 0) extra
      (initialConfiguration BoundaryAdvance.machine (BoundaryAdvance.input W a b upper))) = config machine.start W a b upper := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.leftConfig, TapeEmbedding.config, initialConfiguration, config, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.leftConfig, TapeEmbedding.config, initialConfiguration, BoundaryAdvance.input, config, extra, Fin.addCases]
  have hbudget : 4 * W + 4 + 1 + (8 * W + 8) = 12 * W + 13 := by omega
  rw [hinit, hbudget] at hj
  have hhalt := (prefix_of_run _ _ _ _ hs).2
  have hcontrol : second.final.control = 5 := by
    have h : ∀ state : Fin 6, RecordClone.machine.halted state = true → state = 5 := by
      intro state
      fin_cases state <;> simp [RecordClone.machine, Rewind.machine, Fin.addCases]
    exact h _ hhalt
  refine ⟨Composition.joinedReceipt (TapeEmbedding.receipt (fun _ : Fin 1 => 0) extra first) next, hj, ?_, ?_, ?_⟩
  · change Composition.rightConfig 7 (TapeRenaming.config layout
      (TapeEmbedding.config (fun _ : Fin 1 => 0) retained second.final)) = _
    apply configuration_ext
    · change Fin.natAdd 7 second.final.control = _
      rw [hcontrol]
      rfl
    · funext i
      fin_cases i <;> simp [Composition.rightConfig, TapeRenaming.config, TapeEmbedding.config, config, hh, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.rightConfig, TapeRenaming.config, TapeEmbedding.config,
        config, ht, RecordClone.output, retained, Fin.addCases]
  · change first.steps + 1 + second.steps = _
    omega
  · change max (first.peakTapeCells + TapeEmbedding.extraCells extra)
      (second.peakTapeCells + TapeEmbedding.extraCells retained) ≤ _
    simp [TapeEmbedding.extraCells, extra, retained]
    omega

end NearCubicWires.RepairOrdinary.BoundaryStore
