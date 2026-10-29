import SourceAdapters.Machine.CappedStatus

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: capped execution with observable outcome,
exact materialized output extent, and all heads reset at linear cost.
The serialized input loader and result writer are separate paid stages. -/
namespace NearCubicGates.Adapters.Machine.Capped
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins
set_option autoImplicit false

def successTag (s : ℕ) (q : Fin (s+1)) : Bool := decide (q.val < s)

def preparedMachine (p : Program) : Machine (p.tapeCount+1+1+1+1) (p.stateCount+1+2) :=
  Rewind.machine (Status.machine
    (OutputTracking.machine (machine p.machine) p.outputTape.castSucc) (successTag p.stateCount))

def preparedInput (p : Program) (cap : ℕ) (word : List Bool) :
    Fin (p.tapeCount+1+1+1+1) → List Bool :=
  Fin.addCases (Fin.addCases
    (Fin.addCases (cappedInputTapes cap (p.inputTapes word)) (fun _ => []))
    (fun _ => [true])) (fun _ => [])

def preparedOutputSlot (p : Program) : Fin (p.tapeCount+1+1+1+1) :=
  (((p.outputTape.castSucc).castAdd 1).castAdd 1).castAdd 1

def preparedMarkerSlot (p : Program) : Fin (p.tapeCount+1+1+1+1) :=
  (((0 : Fin 1).natAdd (p.tapeCount+1)).castAdd 1).castAdd 1

def preparedStatusSlot (p : Program) : Fin (p.tapeCount+1+1+1+1) :=
  ((0 : Fin 1).natAdd (p.tapeCount+1+1)).castAdd 1

theorem agreement_tag {t s : ℕ} (source : Option (ExecutionReceipt t s))
    (r : ExecutionReceipt (t+1) (s+1)) (h : CappedResultAgreement source r) :
    successTag s r.final.control = source.isSome := by
  cases source with
  | none => simp [CappedResultAgreement] at h; simp [successTag, h]
  | some source =>
    obtain ⟨hc, _⟩ := h
    simp [successTag, hc, source.final.control.isLt]

/-- One actual machine, with cap+4 tapes, not a semantic evaluator. -/
theorem prepared_run (p : Program) (cap : ℕ) (word : List Bool) :
    ∃ result output marker,
      run (preparedMachine p) (2*cap+4) (preparedInput p cap word) = some result ∧
      (∀ i, result.final.heads i = 0) ∧
      result.final.tapes (preparedOutputSlot p) = output ∧
      result.final.tapes (preparedMarkerSlot p) = marker ∧
      OutputTracking.Marked output marker ∧
      result.final.tapes (preparedStatusSlot p) = [(run p.machine cap (p.inputTapes word)).isSome] ∧
      (∀ source, run p.machine cap (p.inputTapes word) = some source →
        output = source.final.tapes p.outputTape) := by
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
    hmore, hrh, ?_, ?_, hmarked, ?_, ?_⟩
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

end NearCubicGates.Adapters.Machine.Capped
