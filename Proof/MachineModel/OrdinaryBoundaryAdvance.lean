import Proof.MachineModel.OrdinaryAdd

/-! Consecutive bucket-boundary addition with paid reset and reused scalar
workspace. The increment word is preserved for the next iteration. -/
namespace NearCubicWires.RepairOrdinary.BoundaryAdvance
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (width a b : ℕ) (backing : List Bool) : Fin 4 → List Bool :=
  ![frame (binary width a), frame (binary width b), backing, List.replicate (2 * width + 1) false]
def machine : Machine 4 7 := Rewind.machine Add.machine

theorem advance_run (width a b : ℕ) (backing : List Bool) (hfit : a + b < 2 ^ width)
    (hb : backing.length ≤ 2 * width + 1) :
    ∃ r : ExecutionReceipt 4 7,
      run machine (4 * width + 4) (input width a b backing) = some r ∧
      r.final.tapes 0 = frame (binary width a) ∧ r.final.tapes 1 = frame (binary width b) ∧
      r.final.tapes 2 = frame (binary width (a + b)) ∧
      r.final.tapes 3 = List.replicate (2 * width + 1) false ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps = 4 * width + 4 ∧ r.peakTapeCells ≤ 12 * width + 6 := by
  obtain ⟨source, hr, hleft, hright, hout, _, _, _, hs, hp⟩ := Add.add_run width a b backing hfit hb
  let raw : Fin 3 → List Bool := ![frame (binary width a), frame (binary width b), backing]
  have hi : Add.config (Add.scanState false) (frame (binary width a)) (frame (binary width b)) 0 0 [] backing =
      initialConfiguration Add.machine raw := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [Add.config, initialConfiguration, raw, StablePartition.Workspace.overlay]
  have hr' : run Add.machine (2 * width + 1) raw = some source := by rw [run, ← hi]; exact hr
  obtain ⟨r, hrun, ht, hcounter, hheads, hsteps, hpeak⟩ :=
    Rewind.Workspace.reset_workspace Add.machine (2 * width + 1) raw source hr' (2 * width + 1)
  have hinput : (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
      raw (fun _ : Fin 1 => List.replicate (2 * width + 1) false)) =
      input width a b backing := by
    funext i
    fin_cases i <;> simp [raw, input, Fin.addCases]
  have hfuel : 2 * source.steps + 2 = 4 * width + 4 := by rw [hs]; omega
  refine ⟨r, by rw [hinput, hfuel] at hrun; exact hrun, ?_, ?_, ?_, ?_, hheads,
    hsteps.trans hfuel, ?_⟩
  · exact (ht 0).trans hleft
  · exact (ht 1).trans hright
  · exact (ht 2).trans hout
  · have hindex : (0 : Fin 1).natAdd 3 = (3 : Fin 4) := by decide
    simpa only [hs, max_self, hindex] using hcounter
  · omega

theorem bucket_advance_run (width bucketSize h : ℕ) (backing : List Bool)
    (hfit : (h + 1) * (bucketSize + 1) < 2 ^ width) (hb : backing.length ≤ 2 * width + 1) :
    ∃ r : ExecutionReceipt 4 7,
      run machine (4 * width + 4) (input width (h * (bucketSize + 1)) (bucketSize + 1) backing) = some r ∧
      r.final.tapes 0 = frame (binary width (h * (bucketSize + 1))) ∧
      r.final.tapes 1 = frame (binary width (bucketSize + 1)) ∧
      r.final.tapes 2 = frame (binary width ((h + 1) * (bucketSize + 1))) ∧
      r.final.tapes 3 = List.replicate (2 * width + 1) false ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps = 4 * width + 4 ∧ r.peakTapeCells ≤ 12 * width + 6 := by
  have he : h * (bucketSize + 1) + (bucketSize + 1) = (h + 1) * (bucketSize + 1) := by simp [Nat.add_mul]
  simpa only [he] using advance_run width (h * (bucketSize + 1)) (bucketSize + 1) backing (by simpa only [he] using hfit) hb

end NearCubicWires.RepairOrdinary.BoundaryAdvance
