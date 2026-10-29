import SourceAdapters.Machine.CappedResultOutput

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: the explicit unary cap remains available to the output serializer. -/
namespace NearCubicGates.Adapters.Machine.Capped
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

theorem step_preserves_tape {t s : ℕ} (M : Machine t s) (i : Fin t)
    (hw : ∀ q scan a, M.rule q scan=some a → a.write i=none)
    (c next : Configuration t s) (hs : step M c=some next) : next.tapes i=c.tapes i := by
  cases ha : M.rule c.control c.scanned with
  | none => simp [step,ha] at hs
  | some a =>
    simp only [step,ha,Option.map_some,Option.some.injEq] at hs
    subst next
    simp [applyAction,hw _ _ a ha]

theorem run_preserves_tape {t s : ℕ} (M : Machine t s) (i : Fin t)
    (hw : ∀ q scan a, M.rule q scan=some a → a.write i=none)
    (fuel : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s)
    (hr : runFrom M fuel c=some r) : r.final.tapes i=c.tapes i := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; rfl
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; rfl
    · cases hs : step M c with
      | none => simp [hs] at hr
      | some next =>
        cases ht : runFrom M fuel next with
        | none => simp [hs,ht] at hr
        | some tail =>
          simp only [hs,ht,Option.some.injEq] at hr
          subst r
          exact (ih next tail ht).trans (step_preserves_tape M i hw c next hs)

theorem clock_write_none {t s : ℕ} (M : Machine t s) (q : Fin (s+1))
    (scan : Fin (t+1) → Bool) (a : Action (t+1) (s+1))
    (ha : (machine M).rule q scan=some a) : a.write (Fin.last t)=none := by
  simp only [machine] at ha
  split at ha
  · split at ha
    · split at ha
      · cases ha; rfl
      · cases ha
        simp [liftAction]
    · cases ha; rfl
  · contradiction

end NearCubicGates.Adapters.Machine.Capped
