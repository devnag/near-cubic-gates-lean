import SourceAdapters.Machine.CappedOutputBounds

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: retain the cap outcome on a real tape before paid head reset. -/
namespace NearCubicGates.Adapters.Machine.Capped.Status
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

def action {t s : ℕ} (tag : Fin s → Bool) (a : Action t s) : Action (t+1) s where
  nextControl := a.nextControl
  write := Fin.addCases a.write (fun _ => some (tag a.nextControl))
  move := Fin.addCases a.move (fun _ => .stay)

def machine {t s : ℕ} (M : Machine t s) (tag : Fin s → Bool) : Machine (t+1) s where
  descriptionBits := 0
  start := M.start
  halted := M.halted
  rule := fun q scan => (M.rule q (fun i => scan (i.castAdd 1))).map (action tag)

def config {t s : ℕ} (tag : Fin s → Bool) (c : Configuration t s) : Configuration (t+1) s where
  control := c.control
  heads := Fin.addCases c.heads (fun _ => 0)
  tapes := Fin.addCases c.tapes (fun _ => [tag c.control])

theorem apply_action {t s : ℕ} (tag : Fin s → Bool) (c : Configuration t s) (a : Action t s) :
    applyAction (config tag c) (action tag a) = config tag (applyAction c a) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, config, action, HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, config, action, writeTapeBit]

theorem step_config {t s : ℕ} (M : Machine t s) (tag : Fin s → Bool)
    (c : Configuration t s) (a : Action t s) (ha : M.rule c.control c.scanned = some a) :
    step (machine M tag) (config tag c) = some (config tag (applyAction c a)) := by
  have hr : (machine M tag).rule (config tag c).control (config tag c).scanned = some (action tag a) := by
    simp only [machine, config, Configuration.scanned, Fin.addCases_left]
    change (M.rule c.control c.scanned).map (action tag) = some (action tag a)
    rw [ha]
    rfl
  simp [step, hr, apply_action]

theorem run_config {t s : ℕ} (M : Machine t s) (tag : Fin s → Bool)
    (fuel : ℕ) (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom M fuel c = some source) :
    ∃ result, runFrom (machine M tag) fuel (config tag c) = some result ∧
      result.final = config tag source.final ∧ result.steps = source.steps := by
  induction fuel generalizing c source with
  | zero =>
    by_cases hh : M.halted c.control = true
    · simp [runFrom, hh] at hr
      subst source
      refine ⟨⟨config tag c, 0, (config tag c).tapeCells⟩, ?_, rfl, rfl⟩
      simp [runFrom, machine, config, hh]
    · simp [runFrom, hh] at hr
  | succ fuel ih =>
    by_cases hh : M.halted c.control = true
    · simp [runFrom, hh] at hr
      subst source
      refine ⟨⟨config tag c, 0, (config tag c).tapeCells⟩, ?_, rfl, rfl⟩
      simp [runFrom, machine, config, hh]
    · have hn : M.halted c.control = false := Bool.eq_false_iff.mpr hh
      cases ha : M.rule c.control c.scanned with
      | none => simp [runFrom, hn, step, ha] at hr
      | some a =>
        cases ht : runFrom M fuel (applyAction c a) with
        | none => simp [runFrom, hn, step, ha, ht] at hr
        | some tail =>
          simp only [runFrom, hn, Bool.false_eq_true, if_false, step, ha,
            Option.map_some, ht, Option.some.injEq] at hr
          subst source
          obtain ⟨r, hrun, hf, hs⟩ := ih (applyAction c a) tail ht
          have hj := runFrom_step (machine M tag) (config tag c)
            (config tag (applyAction c a)) r hn (step_config M tag c a ha) hrun
          exact ⟨_, hj, hf, congrArg (fun k => k+1) hs⟩

theorem initial_config {t s : ℕ} (M : Machine t s) (tag : Fin s → Bool)
    (input : Fin t → List Bool) :
    config tag (initialConfiguration M input) =
      initialConfiguration (machine M tag) (Fin.addCases input (fun _ => [tag M.start])) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [config, initialConfiguration]
  · rfl

theorem tagged_run {t s : ℕ} (M : Machine t s) (tag : Fin s → Bool)
    (fuel : ℕ) (input : Fin t → List Bool) (source : ExecutionReceipt t s)
    (hr : run M fuel input = some source) :
    ∃ result, run (machine M tag) fuel
        (Fin.addCases input (fun _ => [tag M.start])) = some result ∧
      result.final = config tag source.final ∧ result.steps = source.steps := by
  obtain ⟨r, hrun, hf, hs⟩ := run_config M tag fuel _ source hr
  refine ⟨r, ?_, hf, hs⟩
  simpa only [initial_config, run] using hrun

end NearCubicGates.Adapters.Machine.Capped.Status
