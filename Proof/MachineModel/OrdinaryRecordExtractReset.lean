import Proof.MachineModel.OrdinaryRecordExtract

/-! Return the annotated-record extractor's bounded workspace with all heads
zero. The outer record stream and matrix output are inactive extra tapes. -/
namespace NearCubicWires.RepairOrdinary.RecordExtractReset
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (word rank backing rankBacking : List Bool) : Fin 7 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (6 + 1) => List Bool) (RecordExtract.input word rank backing rankBacking)
    (fun _ => List.replicate (24 * word.length + 14) false)
def output (word rank : List Bool) : Fin 7 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (6 + 1) => List Bool) (RecordExtract.finished word rank).tapes
    (fun _ => List.replicate (24 * word.length + 14) false)
def machine : Machine 7 17 := Rewind.machine RecordExtract.machine

theorem reset_run (word rank backing rankBacking : List Bool) (hw : rank.length = word.length)
    (hb : backing.length ≤ 4 * word.length + 1) (hrb : rankBacking.length ≤ 2 * word.length + 1) :
    ∃ r : ExecutionReceipt 7 17,
      run machine (48 * word.length + 30) (input word rank backing rankBacking) = some r ∧
      r.final.control = 16 ∧ r.final.tapes = output word rank ∧ (∀ i, r.final.heads i = 0) ∧
      r.steps = 48 * word.length + 30 ∧ r.peakTapeCells ≤ 88 * word.length + 41 := by
  obtain ⟨base, hr, hf, hs, hp⟩ := RecordExtract.extract_run word rank backing rankBacking hw hb hrb
  obtain ⟨r, hrun, ht, hc, hh, hsteps, hpeak⟩ := Rewind.Workspace.reset_workspace RecordExtract.machine
    (24 * word.length + 14) (RecordExtract.input word rank backing rankBacking) base hr (24 * word.length + 14)
  have htime : 2 * base.steps + 2 = 48 * word.length + 30 := by rw [hs]; omega
  have hcontrol : r.final.control = 16 := by
    have halted := (prefix_of_run (Rewind.machine RecordExtract.machine) _ _ r hrun).2
    have haltOnly : ∀ state : Fin 17, machine.halted state = true → state = 16 := by
      intro state
      fin_cases state <;> decide
    exact haltOnly _ halted
  refine ⟨r, by rw [htime] at hrun; exact hrun, hcontrol, ?_, hh, hsteps.trans htime, by omega⟩
  have hcore (i : Fin 6) : r.final.tapes (i.castAdd 1) = (RecordExtract.finished word rank).tapes i := by
    rw [ht i, hf]
  have hlast : r.final.tapes 6 = List.replicate (24 * word.length + 14) false := by
    have hindex : (0 : Fin 1).natAdd 6 = (6 : Fin 7) := by decide
    simpa only [hs, max_self, hindex] using hc
  funext i
  refine Fin.addCases (motive := fun i : Fin (6 + 1) => r.final.tapes i = output word rank i)
    (fun j : Fin 6 => ?_) (fun j : Fin 1 => ?_) i
  · simpa [output] using hcore j
  · fin_cases j
    simpa [output, Fin.addCases] using hlast

end NearCubicWires.RepairOrdinary.RecordExtractReset
