import SourceAdapters.Machine.CappedCore

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: correctness of the explicit-tape cap transformation. -/
namespace NearCubicGates.Adapters.Machine.Capped
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins
set_option autoImplicit false

theorem failure_run {t s : ℕ} (M : Machine t s)
    (c : Configuration (t+1) (s+1)) (fuel : ℕ)
    (hh : (machine M).halted c.control = false)
    (hr : (machine M).rule c.control c.scanned = some (failureAction t s)) :
    ∃ receipt, runFrom (machine M) (fuel+1) c = some receipt ∧
      receipt.final.control.val = s := by
  let next := applyAction c (failureAction t s)
  have hn : (machine M).halted next.control = true := failure_halted M c
  have hs := halted_run (machine M) next fuel hn
  refine ⟨_, runFrom_step (machine M) c next _ hh ?_ hs, rfl⟩
  simp [step, hr, next]

theorem source_halted_run {t s : ℕ} (M : Machine t s)
    (c : Configuration t s) (fuel cap k : ℕ)
    (hh : M.halted c.control = true) :
    ∃ receipt,
      runFrom (machine M) (fuel+1) (liftConfig c cap k) = some receipt ∧
      CappedResultAgreement (runFrom M fuel c) receipt := by
  have hc : (machine M).halted (liftConfig c cap k).control = true := by
    simpa using hh
  refine ⟨_, halted_run (machine M) (liftConfig c cap k) (fuel+1) hc, ?_⟩
  rw [halted_run M c fuel hh]
  simp [CappedResultAgreement, liftConfig, cappedInputTapes]

theorem run_lift {t s : ℕ} (M : Machine t s) (fuel : ℕ)
    (c : Configuration t s) (k : ℕ) :
    ∃ receipt,
      runFrom (machine M) (fuel+1) (liftConfig c (k+fuel) k) = some receipt ∧
      CappedResultAgreement (runFrom M fuel c) receipt := by
  induction fuel generalizing c k with
  | zero =>
      by_cases hh : M.halted c.control = true
      · exact source_halted_run M c 0 (k+0) k hh
      · have hn : M.halted c.control = false := Bool.eq_false_iff.mpr hh
        obtain ⟨r, hr, hf⟩ := failure_run M (liftConfig c k k) 0
          (by simpa using hn) (rule_end M c k)
        refine ⟨r, hr, ?_⟩
        simpa [runFrom, hn, CappedResultAgreement] using hf
  | succ fuel ih =>
      by_cases hh : M.halted c.control = true
      · exact source_halted_run M c (fuel+1) (k+(fuel+1)) k hh
      · have hn : M.halted c.control = false := Bool.eq_false_iff.mpr hh
        have hk : k < k+(fuel+1) := by omega
        cases ha : M.rule c.control c.scanned with
        | none =>
            obtain ⟨r, hr, hf⟩ := failure_run M (liftConfig c (k+(fuel+1)) k) (fuel+1)
              (by simpa using hn) (by simpa [ha] using rule_live M c _ k hk)
            refine ⟨r, hr, ?_⟩
            simpa [runFrom, hn, step, ha, CappedResultAgreement] using hf
        | some a =>
            obtain ⟨r, hr, hgood⟩ := ih (applyAction c a) (k+1)
            have he : k+1+fuel = k+(fuel+1) := by omega
            rw [he] at hr
            have hc := runFrom_step (machine M) (liftConfig c (k+(fuel+1)) k)
              (liftConfig (applyAction c a) (k+(fuel+1)) (k+1)) r
              (by simpa using hn) (step_live M c a _ k hk ha) hr
            refine ⟨_, hc, ?_⟩
            cases ht : runFrom M fuel (applyAction c a) with
            | none =>
                simpa [runFrom, hn, step, ha, ht, CappedResultAgreement] using hgood
            | some source =>
                simpa [runFrom, hn, step, ha, ht, CappedResultAgreement] using hgood

theorem lift_initial {t s : ℕ} (M : Machine t s)
    (input : Fin t → List Bool) (cap : ℕ) :
    liftConfig (initialConfiguration M input) cap 0 =
      initialConfiguration (machine M) (cappedInputTapes cap input) := by
  apply configuration_ext
  · rfl
  · funext i
    simp [liftConfig, initialConfiguration]
  · rfl

/-- `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: the generic cap transform, with exact source tapes and
control on success, and a non-source failure state on every other branch. -/
theorem cappedMachineRun : CappedMachineRun := by
  intro t s M
  refine ⟨machine M, fun _ => rfl, ?_⟩
  intro cap input
  obtain ⟨r, hr, hg⟩ := run_lift M cap (initialConfiguration M input) 0
  refine ⟨r, ?_, hg⟩
  simpa [run, lift_initial] using hr

end NearCubicGates.Adapters.Machine.Capped
