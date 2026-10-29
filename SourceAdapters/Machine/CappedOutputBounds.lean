import SourceAdapters.Machine.CappedOutputTracking
import Proof.Foundations.OrdinaryRewindCarrier

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: exact output extent and a paid reset of the marked run. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputTracking
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Close.CheckedPCPP.Dock
set_option autoImplicit false

theorem step_output_bound {t s : ℕ} (M : Machine t s) (c d : Configuration t s)
    (out : Fin t) (A : ℕ) (hs : step M c = some d)
    (ht : (c.tapes out).length ≤ A) (hh : c.heads out ≤ A) :
    (d.tapes out).length ≤ A+1 ∧ d.heads out ≤ A+1 := by
  cases ha : M.rule c.control c.scanned with
  | none => simp [step, ha] at hs
  | some a =>
    have he : applyAction c a = d := by simpa [step, ha] using hs
    subst d
    constructor
    · simp only [applyAction]
      cases a.write out with
      | none => exact ht.trans (Nat.le_succ A)
      | some v => simp only [writeTapeBit_len]; omega
    · change (a.move out).apply (c.heads out) ≤ A+1
      cases a.move out <;> simp [HeadMove.apply] <;> omega

theorem run_output_bound {t s : ℕ} (M : Machine t s) (fuel : ℕ)
    (c : Configuration t s) (r : ExecutionReceipt t s) (out : Fin t) (A : ℕ)
    (hr : runFrom M fuel c = some r)
    (ht : (c.tapes out).length ≤ A) (hh : c.heads out ≤ A) :
    (r.final.tapes out).length ≤ A+r.steps ∧ r.final.heads out ≤ A+r.steps := by
  induction fuel generalizing c r A with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact ⟨ht, hh⟩
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact ⟨ht, hh⟩
    · cases hs : step M c with
      | none => simp [hs] at hr
      | some next =>
        cases hn : runFrom M fuel next with
        | none => simp [hs, hn] at hr
        | some tail =>
          simp only [hs, hn, Option.some.injEq] at hr
          subst r
          obtain ⟨ht', hh'⟩ := step_output_bound M c next out A hs ht hh
          obtain ⟨ht'', hh''⟩ := ih next tail (A+1) hn ht' hh'
          constructor <;> dsimp only <;> omega

/-- Fresh physical output contains at most one new cell per elapsed step. -/
theorem program_output_bound (p : Program) (word : List Bool) (fuel : ℕ)
    (r : ExecutionReceipt p.tapeCount p.stateCount)
    (hr : run p.machine fuel (p.inputTapes word) = some r) :
    (r.final.tapes p.outputTape).length ≤ fuel := by
  have ht := run_output_bound p.machine fuel _ r p.outputTape 0 hr
    (by simp [initialConfiguration, Program.inputTapes, p.outputFresh])
    (by simp [initialConfiguration])
  have hs := runFrom_steps_le p.machine fuel _ r hr
  omega

theorem initial_config {t s : ℕ} (M : Machine t s) (out : Fin t)
    (input : Fin t → List Bool) :
    config out (initialConfiguration M input) [] =
      initialConfiguration (machine M out) (Fin.addCases input (fun _ => [])) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [config, initialConfiguration]
  · rfl

theorem marked_run {t s : ℕ} (M : Machine t s) (out : Fin t)
    (fuel : ℕ) (input : Fin t → List Bool) (source : ExecutionReceipt t s)
    (hr : run M fuel input = some source) (hi : input out = []) :
    ∃ result marker,
      run (machine M out) fuel (Fin.addCases input (fun _ => [])) = some result ∧
      result.final = config out source.final marker ∧
      result.steps = source.steps ∧ Marked (source.final.tapes out) marker := by
  have hm : Marked ((initialConfiguration M input).tapes out) [] := by
    simp [Marked, initialConfiguration, hi]
  obtain ⟨r, marker, hrun, hf, hs, hm'⟩ := run_config M out fuel _ source hr [] hm
  refine ⟨r, marker, ?_, hf, hs, hm'⟩
  simpa only [initial_config, run] using hrun

end NearCubicGates.Adapters.Machine.Capped.OutputTracking
