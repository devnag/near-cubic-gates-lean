import Proof.MachineModel.OrdinaryWidthHeader
import Proof.MachineModel.OrdinaryRadixEven
import Proof.Foundations.OrdinarySourceHandoff

/-! Actual first-record width scan followed by paid head reset. Its exact
retained counter is carried into the subsequent fixed sorting program. -/
namespace NearCubicWires.RepairOrdinary.SortPreparation
open LocalBitMultitape StablePartition RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstWord : List Record → List Bool
  | [] => []
  | r :: _ => word r

def suffix : List Record → List Bool
  | [] => []
  | _ :: rs => stream rs

def width (rs : List Record) : ℕ := (firstWord rs).length

theorem stream_first (rs : List Record) : stream rs = frame (firstWord rs) ++ suffix rs := by
  cases rs with
  | nil => rfl
  | cons r rs => simp [stream, recordsBits, recordBits, firstWord, suffix, word, frame, List.append_assoc]

def machine : Machine 6 6 := Rewind.machine WidthHeader.machine

def prepared (rs : List Record) : Fin 6 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (5 + 1) => List Bool)
    (RadixEven.input rs (width rs))
    (fun _ : Fin 1 => List.replicate (3 * width rs + 1) false)

theorem prepare_run (rs : List Record) :
    ∃ r : ExecutionReceipt 6 6,
      run machine (6 * width rs + 4) (SourceHandoff.sourceTapes (stream rs)) = some r ∧
      r.final.tapes = prepared rs ∧ (∀ i, r.final.heads i = 0) ∧
      r.steps = 6 * width rs + 4 ∧ r.peakTapeCells ≤ (stream rs).length + 5 * width rs + 2 := by
  obtain ⟨raw, hr, hf, hs, hp⟩ := WidthHeader.scan_run (firstWord rs) (suffix rs)
  rw [← stream_first] at hr hf hp
  have hraw : run WidthHeader.machine (3 * width rs + 1)
      (SourceHandoff.sourceTapes (stream rs)) = some raw := hr
  obtain ⟨r, hrun, hfinal, hsteps, hpeak⟩ := Rewind.recorded_run WidthHeader.machine
    (3 * width rs + 1) (initialConfiguration WidthHeader.machine (SourceHandoff.sourceTapes (stream rs)))
    raw hraw 0 (by simp [initialConfiguration])
  have hi : Rewind.recording
      (initialConfiguration WidthHeader.machine (SourceHandoff.sourceTapes (stream rs))) 0 =
      initialConfiguration machine (SourceHandoff.sourceTapes (stream rs)) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Rewind.recording, Rewind.config, initialConfiguration, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Rewind.recording, Rewind.config, initialConfiguration,
        SourceHandoff.sourceTapes, Fin.addCases]
  have hrawSteps : raw.steps = 3 * width rs + 1 := hs
  rw [hi, hrawSteps] at hrun
  refine ⟨r, ?_, ?_, ?_, ?_, ?_⟩
  · have he : 0 + 2 * (3 * width rs + 1) + 2 = 6 * width rs + 4 := by omega
    rw [he] at hrun
    exact hrun
  · rw [hfinal, hf, hrawSteps]
    funext i
    fin_cases i <;> simp [Rewind.finished, Rewind.config, WidthHeader.config,
      prepared, RadixEven.input, width, RadixIteration.driver, Fin.addCases]
  · intro i
    rw [hfinal]
    fin_cases i <;> simp [Rewind.finished, Rewind.config, Fin.addCases]
  · omega
  · change raw.peakTapeCells ≤ (stream rs).length + 2 * width rs + 1 at hp
    omega

end NearCubicWires.RepairOrdinary.SortPreparation
