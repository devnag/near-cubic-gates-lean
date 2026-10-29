import SourceAdapters.Joins.CappedRun
import Proof.Foundations.OrdinaryMachine

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: execute unchanged source steps beside a unary clock.
interface: Joins.CappedRun, 4d5fdf4c. -/
namespace NearCubicGates.Adapters.Machine.Capped
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins
set_option autoImplicit false

def liftAction {t s : ℕ} (a : Action t s) : Action (t+1) (s+1) where
  nextControl := a.nextControl.castSucc
  write := fun i => if h : i.val < t then a.write ⟨i.val,h⟩ else none
  move := fun i => if h : i.val < t then a.move ⟨i.val,h⟩ else .right

def failureAction (t s : ℕ) : Action (t+1) (s+1) where
  nextControl := Fin.last s
  write := fun _ => none
  move := fun _ => .stay

def machine {t s : ℕ} (M : Machine t s) : Machine (t+1) (s+1) where
  descriptionBits := 0
  start := M.start.castSucc
  halted := fun q => if h : q.val < s then M.halted ⟨q.val,h⟩ else true
  rule := fun q scan =>
    if h : q.val < s then
      if scan (Fin.last t) then
        match M.rule ⟨q.val,h⟩ (fun i => scan i.castSucc) with
        | none => some (failureAction t s)
        | some a => some (liftAction a)
      else some (failureAction t s)
    else none

def liftConfig {t s : ℕ} (c : Configuration t s) (cap k : ℕ) :
    Configuration (t+1) (s+1) where
  control := c.control.castSucc
  heads := fun i => if h : i.val < t then c.heads ⟨i.val,h⟩ else k
  tapes := cappedInputTapes cap c.tapes

@[simp] theorem halted_lift {t s : ℕ} (M : Machine t s)
    (c : Configuration t s) (cap k : ℕ) :
    (machine M).halted (liftConfig c cap k).control = M.halted c.control := by
  simp [machine, liftConfig, c.control.isLt]

@[simp] theorem scanned_source {t s : ℕ} (c : Configuration t s)
    (cap k : ℕ) (i : Fin t) :
    (liftConfig c cap k).scanned i.castSucc = c.scanned i := by
  simp [Configuration.scanned, liftConfig, cappedInputTapes, i.isLt]

theorem scanned_clock_live {t s : ℕ} (c : Configuration t s)
    (cap k : ℕ) (h : k < cap) :
    (liftConfig c cap k).scanned (Fin.last t) = true := by
  simpa [Configuration.scanned, liftConfig, cappedInputTapes, readTapeBit]
    using (List.getD_replicate (x := true) (y := false) h)

@[simp] theorem scanned_clock_end {t s : ℕ} (c : Configuration t s)
    (cap : ℕ) :
    (liftConfig c cap cap).scanned (Fin.last t) = false := by
  simp [Configuration.scanned, liftConfig, cappedInputTapes, readTapeBit,
    List.getD]

theorem applyAction_lift {t s : ℕ} (c : Configuration t s)
    (a : Action t s) (cap k : ℕ) :
    applyAction (liftConfig c cap k) (liftAction a) =
      liftConfig (applyAction c a) cap (k+1) := by
  apply configuration_ext
  · rfl
  · funext i
    by_cases h : i.val < t
    · simp [applyAction, liftConfig, liftAction, h]
    · simp [applyAction, liftConfig, liftAction, h, HeadMove.apply]
  · funext i
    by_cases h : i.val < t
    · simp [applyAction, liftConfig, liftAction, cappedInputTapes, h]
    · simp [applyAction, liftConfig, liftAction, cappedInputTapes, h]

theorem rule_live {t s : ℕ} (M : Machine t s) (c : Configuration t s)
    (cap k : ℕ) (h : k < cap) :
    (machine M).rule (liftConfig c cap k).control (liftConfig c cap k).scanned =
      match M.rule c.control c.scanned with
      | none => some (failureAction t s)
      | some a => some (liftAction a) := by
  change (if hq : c.control.val < s then
    if (liftConfig c cap k).scanned (Fin.last t) then
      match M.rule ⟨c.control.val,hq⟩ (fun i => (liftConfig c cap k).scanned i.castSucc) with
      | none => some (failureAction t s)
      | some a => some (liftAction a)
    else some (failureAction t s) else none) = _
  simp only [dif_pos c.control.isLt, scanned_clock_live c cap k h]
  simp

theorem rule_end {t s : ℕ} (M : Machine t s) (c : Configuration t s)
    (cap : ℕ) :
    (machine M).rule (liftConfig c cap cap).control
      (liftConfig c cap cap).scanned = some (failureAction t s) := by
  change (if hq : c.control.val < s then
    if (liftConfig c cap cap).scanned (Fin.last t) then _ else _ else _) = _
  simp [c.control.isLt]

theorem step_live {t s : ℕ} (M : Machine t s) (c : Configuration t s)
    (a : Action t s) (cap k : ℕ) (h : k < cap)
    (ha : M.rule c.control c.scanned = some a) :
    step (machine M) (liftConfig c cap k) =
      some (liftConfig (applyAction c a) cap (k+1)) := by
  simp [step, rule_live M c cap k h, ha, applyAction_lift]

@[simp] theorem failure_halted {t s : ℕ} (M : Machine t s)
    (c : Configuration (t+1) (s+1)) :
    (machine M).halted (applyAction c (failureAction t s)).control = true := by
  simp [machine, applyAction, failureAction]

theorem halted_run {t s : ℕ} (M : Machine t s) (c : Configuration t s)
    (fuel : ℕ) (h : M.halted c.control = true) :
    runFrom M fuel c = some {final := c, steps := 0, peakTapeCells := c.tapeCells} := by
  cases fuel <;> simp [runFrom, h]

end NearCubicGates.Adapters.Machine.Capped
