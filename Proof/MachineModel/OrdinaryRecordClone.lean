import Proof.MachineModel.OrdinaryHalfPosition

/-! Create the two bounded record copies used by half extraction. Copying,
all-head reset and retained counter space are actual interpreter operations. -/
namespace NearCubicWires.RepairOrdinary.RecordClone
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw (bits backing : List Bool) : Fin 3 → List Bool :=
  ![frame bits, backing, List.replicate (2 * bits.length + 1) false]
def input (bits backing : List Bool) : Fin 4 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool) (raw bits backing)
    (fun _ => List.replicate (4 * bits.length + 3) false)
def output (bits : List Bool) : Fin 4 → List Bool :=
  ![frame bits, frame bits, List.replicate (2 * bits.length + 1) false,
    List.replicate (4 * bits.length + 3) false]
def machine : Machine 4 6 := Rewind.machine FrameLoad.machine

theorem clone_run (bits backing : List Bool) (hb : backing.length ≤ 2 * bits.length + 1) :
    ∃ r : ExecutionReceipt 4 6,
      run machine (8 * bits.length + 8) (input bits backing) = some r ∧
      r.final.tapes = output bits ∧ (∀ i, r.final.heads i = 0) ∧
      r.steps = 8 * bits.length + 8 ∧ r.peakTapeCells ≤ 18 * bits.length + 11 := by
  obtain ⟨base, hr, hf, hs, hp⟩ := CellLoad.loader_run [] bits [] backing hb
  have hi : CellLoad.loaderInput ([] ++ frame bits ++ []) 0 backing bits.length =
      initialConfiguration FrameLoad.machine (raw bits backing) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · simp [CellLoad.loaderInput, initialConfiguration, raw]
  have hr' : run FrameLoad.machine (4 * bits.length + 3) (raw bits backing) = some base := by
    rw [run, ← hi]
    exact hr
  obtain ⟨r, hrun, ht, hc, hh, hsteps, hpeak⟩ := Rewind.Workspace.reset_workspace FrameLoad.machine
    (4 * bits.length + 3) (raw bits backing) base hr' (4 * bits.length + 3)
  have htime : 2 * base.steps + 2 = 8 * bits.length + 8 := by rw [hs]; omega
  refine ⟨r, by rw [htime] at hrun; exact hrun, ?_, hh, hsteps.trans htime, ?_⟩
  · have hcore (i : Fin 3) : r.final.tapes (i.castAdd 1) =
        (FrameLoad.reset 3 (frame bits) (2 * bits.length + 1) (frame bits) 0 (2 * bits.length + 1)).tapes i := by
      rw [ht i, hf]
      simp
    have hlast : r.final.tapes 3 = List.replicate (4 * bits.length + 3) false := by
      have hindex : (0 : Fin 1).natAdd 3 = (3 : Fin 4) := by decide
      simpa only [hs, max_self, hindex] using hc
    funext i
    fin_cases i
    · exact hcore 0
    · exact hcore 1
    · simpa [FrameLoad.reset, output] using hcore 2
    · exact hlast
  · simp only [List.nil_append, List.append_nil, frame_length] at hp
    omega

end NearCubicWires.RepairOrdinary.RecordClone
