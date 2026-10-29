import SourceAdapters.Machine.CappedClockPreservation

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: prepared run with its literal unary cap retained. -/
namespace NearCubicGates.Adapters.Machine.Capped
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins
set_option autoImplicit false

def preparedClockSlot (p : Program) : Fin (p.tapeCount+1+1+1+1) :=
  (((Fin.last p.tapeCount).castAdd 1).castAdd 1).castAdd 1

theorem prepared_run_clock (p : Program) (cap : ℕ) (word : List Bool) :
    ∃ result output marker,
      run (preparedMachine p) (2*cap+4) (preparedInput p cap word) = some result ∧
      (∀ i, result.final.heads i = 0) ∧
      result.final.tapes (preparedOutputSlot p) = output ∧
      result.final.tapes (preparedMarkerSlot p) = marker ∧
      OutputTracking.Marked output marker ∧
      result.final.tapes (preparedStatusSlot p) = [(run p.machine cap (p.inputTapes word)).isSome] ∧
      (∀ source, run p.machine cap (p.inputTapes word) = some source →
        output = source.final.tapes p.outputTape) ∧
      result.final.tapes (preparedClockSlot p) = List.replicate cap true := by
  obtain ⟨capped, hc, hg⟩ := run_lift p.machine cap
    (initialConfiguration p.machine (p.inputTapes word)) 0
  have hc' : run (machine p.machine) (cap+1)
      (cappedInputTapes cap (p.inputTapes word)) = some capped := by
    simpa [run, lift_initial] using hc
  have hblank : cappedInputTapes cap (p.inputTapes word) p.outputTape.castSucc = [] := by
    simp [cappedInputTapes, p.outputTape.isLt, Program.inputTapes, p.outputFresh]
  obtain ⟨marked, marker, hm, hmf, hms, hmarked⟩ := OutputTracking.marked_run
    (machine p.machine) p.outputTape.castSucc (cap+1) _ capped hc' hblank
  obtain ⟨tagged, ht, htf, hts⟩ := Status.tagged_run
    (OutputTracking.machine (machine p.machine) p.outputTape.castSucc)
    (successTag p.stateCount) (cap+1) _ marked hm
  have hstart : successTag p.stateCount
      (OutputTracking.machine (machine p.machine) p.outputTape.castSucc).start = true := by
    simp [successTag, OutputTracking.machine, machine, p.machine.start.isLt]
  rw [hstart] at ht
  obtain ⟨result, hr, hrt, hrh, _, _⟩ := Rewind.reset_run _ (cap+1) _ tagged ht
  have hs := runFrom_steps_le _ (cap+1) _ tagged ht
  have hbudget : 2*tagged.steps+2 ≤ 2*cap+4 := by omega
  have hmore := run_moreFuel _ (2*tagged.steps+2)
    (2*cap+4-(2*tagged.steps+2)) _ result hr
  rw [Nat.add_sub_of_le hbudget] at hmore
  refine ⟨result, capped.final.tapes p.outputTape.castSucc, marker,
    hmore, hrh, ?_, ?_, hmarked, ?_, ?_, ?_⟩
  · rw [preparedOutputSlot, hrt, htf, hmf]
    simp [Status.config, OutputTracking.config]
  · rw [preparedMarkerSlot, hrt, htf, hmf]
    simp [Status.config, OutputTracking.config]
  · rw [preparedStatusSlot, hrt, htf, hmf]
    simp only [Status.config, Fin.addCases_right, OutputTracking.config]
    congr 1
    exact agreement_tag _ capped hg
  · intro source hsource
    change CappedResultAgreement (run p.machine cap (p.inputTapes word)) capped at hg
    rw [hsource] at hg
    exact (hg.2 p.outputTape).2

  · rw [preparedClockSlot,hrt,htf,hmf]
    simp only [Status.config,OutputTracking.config,Fin.addCases_left]
    have hclock := run_preserves_tape (machine p.machine) (Fin.last p.tapeCount)
      (clock_write_none p.machine) (cap+1)
      (initialConfiguration (machine p.machine) (cappedInputTapes cap (p.inputTapes word))) capped hc'
    simpa [initialConfiguration,cappedInputTapes] using hclock

end NearCubicGates.Adapters.Machine.Capped
