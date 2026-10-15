import Proof.Amplification.RecoverySquareRoot
import Proof.Amplification.RecoveryRadixInput

/-! Actual blank-workspace entry for the shared unpair implementation.
All four heads are reset by executed steps. The resulting most-significant
first stream has two bits per original input bit, ready for radix-4 rounds. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRadixInput
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def entryMachine : Machine 4 8 := Rewind.machine machine

theorem entry_run (bits : List Bool) :
    ∃ r : ExecutionReceipt 4 8,
      run entryMachine (8 * bits.length + 6)
        (fun i => if i.val = 0 then frame bits else []) = some r ∧
      r.final.tapes 0 = frame bits ∧
      r.final.tapes 1 = frame (prepared bits) ∧
      r.final.tapes 2 = List.replicate (2 * bits.length) false ∧
      r.final.tapes 3 = List.replicate (4 * bits.length + 2) false ∧
      (∀ i, r.final.heads i = 0) ∧
      r.steps = 8 * bits.length + 6 ∧ r.peakTapeCells ≤ 12 * bits.length + 4 := by
  obtain ⟨source, hr, hf, hs, hpeak⟩ := prepare_run bits
  obtain ⟨r, hrun, htapes, hcounter, hheads, hsteps, hspace⟩ :=
    Rewind.Workspace.reset_workspace machine (4 * bits.length + 2)
      (fun i => if i.val = 0 then frame bits else []) source hr 0
  have hin : Fin.addCases (motive := fun _ : Fin 4 => List Bool)
      (fun i : Fin 3 => if i.val = 0 then frame bits else [])
      (fun _ : Fin 1 => List.replicate 0 false) =
      (fun i : Fin 4 => if i.val = 0 then frame bits else []) := by
    funext i; fin_cases i <;> rfl
  rw [hin, hs] at hrun
  refine ⟨r, ?_, ?_, ?_, ?_, ?_, hheads, ?_, ?_⟩
  · have he : 2 * (4 * bits.length + 2) + 2 = 8 * bits.length + 6 := by omega
    rw [he] at hrun
    exact hrun
  · simpa [hf, reverse] using htapes (0 : Fin 3)
  · simpa [hf, reverse] using htapes (1 : Fin 3)
  · simpa [hf, reverse] using htapes (2 : Fin 3)
  · simpa [hs] using hcounter
  · rw [hs] at hsteps; omega
  · rw [hs] at hspace; omega

def entryProgram : Program where
  tapeCount := 4
  stateCount := 8
  twoTapes := by decide
  machine := entryMachine
  outputTape := 1
  outputFresh := by decide

def entryWordFunction : RewoundWordFunction (List Bool) id
    (fun bits => frame (prepared bits)) (fun bits => 8 * bits.length + 6) where
  program := entryProgram
  realizes := by
    intro bits
    obtain ⟨r, hr, _, hout, _⟩ := entry_run bits
    exact ⟨r, hr, hout⟩
  headsReset := by
    intro bits receipt hrun
    obtain ⟨r, hr, _, _, _, _, hh, _⟩ := entry_run bits
    have he : receipt = r := Option.some.inj (hrun.symm.trans hr)
    subst receipt
    exact hh

end NearCubicWires.RepairOrdinary.RecoveryRadixInput
