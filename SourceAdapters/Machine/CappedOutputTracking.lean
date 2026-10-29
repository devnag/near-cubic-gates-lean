import SourceAdapters.Machine.CappedRunProof
import Proof.Gates.CheckedPCPP.Dock

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: record every materialized output cell,
including a false write, without changing any source step. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputTracking
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Close.CheckedPCPP.Dock
set_option autoImplicit false

/-- The last materialized marker is true even when the source's last cell is false. -/
def Marked (source marker : List Bool) : Prop :=
  marker.length = source.length ∧ (marker = [] ∨ ∃ pre, marker = pre ++ [true])

theorem write_marker_end (marker : List Bool) (pos : ℕ)
    (h : marker = [] ∨ ∃ pre, marker = pre ++ [true]) :
    ∃ pre, writeTapeBit marker pos true = pre ++ [true] := by
  induction pos generalizing marker with
  | zero =>
    cases marker with
    | nil => exact ⟨[], rfl⟩
    | cons b bs =>
      cases bs with
      | nil => exact ⟨[], rfl⟩
      | cons c cs =>
        rcases h with h | ⟨pre, hp⟩
        · contradiction
        · cases pre with
          | nil => simp at hp
          | cons d ds =>
            simp only [List.cons_append, List.cons.injEq] at hp
            exact ⟨true :: ds, by simp [writeTapeBit, hp.2]⟩
  | succ pos ih =>
    cases marker with
    | nil =>
      obtain ⟨pre, hp⟩ := ih [] (Or.inl rfl)
      exact ⟨false :: pre, by simp [writeTapeBit, hp]⟩
    | cons b bs =>
      have ht : bs = [] ∨ ∃ pre, bs = pre ++ [true] := by
        rcases h with h | ⟨pre, hp⟩
        · contradiction
        · cases pre with
          | nil => simp only [List.nil_append, List.cons.injEq] at hp; exact Or.inl hp.2
          | cons d ds =>
            simp only [List.cons_append, List.cons.injEq] at hp
            exact Or.inr ⟨ds, hp.2⟩
      obtain ⟨pre, hp⟩ := ih bs ht
      exact ⟨b :: pre, by simp [writeTapeBit, hp]⟩

theorem marked_write (source marker : List Bool) (pos : ℕ) (value : Bool)
    (h : Marked source marker) :
    Marked (writeTapeBit source pos value) (writeTapeBit marker pos true) := by
  exact ⟨by simp only [writeTapeBit_len, h.1], Or.inr (write_marker_end marker pos h.2)⟩

def action {t s : ℕ} (out : Fin t) (a : Action t s) : Action (t+1) s where
  nextControl := a.nextControl
  write := Fin.addCases a.write (fun _ => (a.write out).map (fun _ => true))
  move := Fin.addCases a.move (fun _ => a.move out)

def machine {t s : ℕ} (M : Machine t s) (out : Fin t) : Machine (t+1) s where
  descriptionBits := 0
  start := M.start
  halted := M.halted
  rule := fun q scan => (M.rule q (fun i => scan (i.castAdd 1))).map (action out)

def config {t s : ℕ} (out : Fin t) (c : Configuration t s) (marker : List Bool) :
    Configuration (t+1) s where
  control := c.control
  heads := Fin.addCases c.heads (fun _ => c.heads out)
  tapes := Fin.addCases c.tapes (fun _ => marker)

def update {t s : ℕ} (out : Fin t) (c : Configuration t s)
    (a : Action t s) (marker : List Bool) : List Bool :=
  match a.write out with
  | none => marker
  | some _ => writeTapeBit marker (c.heads out) true

theorem apply_action {t s : ℕ} (out : Fin t) (c : Configuration t s)
    (a : Action t s) (marker : List Bool) :
    applyAction (config out c marker) (action out a) =
      config out (applyAction c a) (update out c a marker) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, config, action]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [applyAction, config, action]
    · simp [applyAction, config, action, update]
      cases a.write out <;> rfl

theorem marked_update {t s : ℕ} (out : Fin t) (c : Configuration t s)
    (a : Action t s) (marker : List Bool) (h : Marked (c.tapes out) marker) :
    Marked ((applyAction c a).tapes out) (update out c a marker) := by
  cases hw : a.write out with
  | none => simpa [applyAction, update, hw] using h
  | some v => simpa [applyAction, update, hw] using marked_write (c.tapes out) marker (c.heads out) v h

theorem step_config {t s : ℕ} (M : Machine t s) (out : Fin t)
    (c : Configuration t s) (a : Action t s) (marker : List Bool)
    (ha : M.rule c.control c.scanned = some a) :
    step (machine M out) (config out c marker) =
      some (config out (applyAction c a) (update out c a marker)) := by
  have hr : (machine M out).rule (config out c marker).control
      (config out c marker).scanned = some (action out a) := by
    simp only [machine, config, Configuration.scanned, Fin.addCases_left]
    change (M.rule c.control c.scanned).map (action out) = some (action out a)
    rw [ha]
    rfl
  simp [step, hr, apply_action]

/-- Each source transition is one actual marker-machine transition. -/
theorem run_config {t s : ℕ} (M : Machine t s) (out : Fin t)
    (fuel : ℕ) (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom M fuel c = some source) (marker : List Bool)
    (hm : Marked (c.tapes out) marker) :
    ∃ result finalMarker,
      runFrom (machine M out) fuel (config out c marker) = some result ∧
      result.final = config out source.final finalMarker ∧
      result.steps = source.steps ∧ Marked (source.final.tapes out) finalMarker := by
  induction fuel generalizing c source marker with
  | zero =>
    by_cases hh : M.halted c.control = true
    · simp [runFrom, hh] at hr
      subst source
      refine ⟨⟨config out c marker, 0, (config out c marker).tapeCells⟩, marker, ?_, rfl, rfl, hm⟩
      simp [runFrom, machine, config, hh]
    · simp [runFrom, hh] at hr
  | succ fuel ih =>
    by_cases hh : M.halted c.control = true
    · simp [runFrom, hh] at hr
      subst source
      refine ⟨⟨config out c marker, 0, (config out c marker).tapeCells⟩, marker, ?_, rfl, rfl, hm⟩
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
          obtain ⟨r, finalMarker, hrun, hf, hs, hm'⟩ :=
            ih (applyAction c a) tail ht (update out c a marker) (marked_update out c a marker hm)
          have hj := runFrom_step (machine M out) (config out c marker)
            (config out (applyAction c a) (update out c a marker)) r
            hn (step_config M out c a marker ha) hrun
          exact ⟨_, finalMarker, hj, hf, congrArg (fun k => k+1) hs, hm'⟩

end NearCubicGates.Adapters.Machine.Capped.OutputTracking
