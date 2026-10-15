import Proof.MachineModel.OrdinarySelectiveReset

/-! Reuse the selective-reset counter and discharge its head bound from the
actual transition prefix. Other heads may start arbitrarily far to the right. -/
namespace NearCubicWires.RepairOrdinary.SelectiveReset
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem step_head {t s : ℕ} (p : Machine t s) (c d : Configuration t s) (target : Fin t)
    (hs : step p c = some d) : d.heads target ≤ c.heads target + 1 := by
  cases hr : p.rule c.control c.scanned with
  | none => simp [step, hr] at hs
  | some action =>
    have hd : applyAction c action = d := by simpa [step, hr] using hs
    subst d
    change (action.move target).apply (c.heads target) ≤ c.heads target + 1
    cases action.move target <;> simp only [HeadMove.apply] <;> omega

theorem prefix_head {t s space n : ℕ} {p : Machine t s} {c d : Configuration t s}
    (hp : Prefix p space n c d) (target : Fin t) : d.heads target ≤ c.heads target + n := by
  induction hp with
  | refl => omega
  | step _ _ hs _ ih =>
    have h := step_head p _ _ target hs
    omega

theorem padded_finished {t s : ℕ} (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (n cap : ℕ) :
    ZeroPadding.config (Rewind.Workspace.capacities t cap) (finished (s := s) heads tapes n) =
      finished (s := s) heads tapes (max cap n) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [ZeroPadding.config, Rewind.Workspace.capacities, finished, Rewind.config, Rewind.Workspace.pad_zeros]

theorem workspace_run {t s : ℕ} (p : Machine t s) (target : Fin t) (fuel cap : ℕ)
    (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some source) (hstart : c.heads target = 0) (hcap : source.steps ≤ cap) :
    ∃ r : ExecutionReceipt (t + 1) (s + 2),
      runFrom (machine p target) (2 * source.steps + 2)
        (ZeroPadding.config (Rewind.Workspace.capacities t cap) (Rewind.recording c 0)) = some r ∧
      r.final = finished (s := s) (fun i => if i = target then 0 else source.final.heads i) source.final.tapes cap ∧
      r.steps = 2 * source.steps + 2 ∧ r.peakTapeCells ≤ source.peakTapeCells + source.steps + cap := by
  have hhead := prefix_head (prefix_of_run p fuel c source hr).1 target
  rw [hstart, Nat.zero_add] at hhead
  obtain ⟨base, hb, hf, hs, hp⟩ := reset_run p target fuel c source hr hhead
  obtain ⟨r, hrun, hfinal, hsteps, hpeak⟩ := ZeroPadding.run_config (machine p target)
    (Rewind.Workspace.capacities t cap) _ _ base hb
  refine ⟨r, hrun, ?_, hsteps.trans hs, ?_⟩
  · rw [hfinal, hf, padded_finished, max_eq_left hcap]
  · rw [Rewind.Workspace.capacity_cells] at hpeak
    omega

end NearCubicWires.RepairOrdinary.SelectiveReset
