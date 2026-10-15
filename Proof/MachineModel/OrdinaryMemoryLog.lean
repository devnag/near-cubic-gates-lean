import Proof.Foundations.OrdinaryMachine

/-!
The semantic boundary of the fixed computation-log verifier. Memory events
may be grouped by cell only when each cell's chronological subsequence is
preserved. This proves that boundary; it does not assert a verifier runtime.
-/
namespace NearCubicWires.RepairOrdinary.MemoryLog
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Cell := ℕ × ℕ
abbrev Memory := Cell → Bool

structure Event where
  cell : Cell
  read : Bool
  after : Bool
  deriving DecidableEq

def localRun : Bool → List Event → Option Bool
  | b, [] => some b
  | b, e :: es => if e.read = b then localRun e.after es else none

def atCell (cell : Cell) (events : List Event) : List Event :=
  events.filter (fun e => e.cell == cell)

def run : Memory → List Event → Option Memory
  | memory, [] => some memory
  | memory, e :: es =>
      if e.read = memory e.cell then
        run (Function.update memory e.cell e.after) es
      else none

def valid (memory : Memory) (events : List Event) : Prop :=
  ∀ cell, (localRun (memory cell) (atCell cell events)).isSome = true

theorem valid_cons (memory : Memory) (e : Event) (es : List Event) :
    valid memory (e :: es) ↔
      e.read = memory e.cell ∧ valid (Function.update memory e.cell e.after) es := by
  constructor
  · intro hv
    have hcell := hv e.cell
    simp only [atCell, List.filter_cons, beq_self_eq_true,
      if_true, localRun] at hcell
    split at hcell
    · next hread =>
        refine ⟨hread, ?_⟩
        intro cell
        by_cases he : e.cell = cell
        · subst cell
          simpa only [Function.update_self, atCell] using hcell
        · have hc := hv cell
          simpa [atCell, he, Function.update_of_ne (Ne.symm he)] using hc
    · simp at hcell
  · rintro ⟨hread, hv⟩ cell
    by_cases he : e.cell = cell
    · subst cell
      have hc := hv e.cell
      simpa [atCell, localRun, hread] using hc
    · have hc := hv cell
      simpa [atCell, he, Function.update_of_ne (Ne.symm he)] using hc

theorem run_success_iff (memory : Memory) (events : List Event) :
    (run memory events).isSome = true ↔ valid memory events := by
  induction events generalizing memory with
  | nil => simp [run, valid, atCell, localRun]
  | cons e es ih =>
      rw [valid_cons]
      by_cases h : e.read = memory e.cell
      · simpa only [run, h, if_true, true_and] using
          ih (Function.update memory e.cell e.after)
      · simp [run, h]

/-- The exact obligation of sorting: retain the chronological subsequence at
each cell. A mere permutation does not meet this premise. -/
theorem grouped_success_iff (memory : Memory) (events grouped : List Event)
    (horder : ∀ cell, atCell cell grouped = atCell cell events) :
    (run memory grouped).isSome = true ↔ (run memory events).isSome = true := by
  rw [run_success_iff, run_success_iff]
  simp only [valid, horder]

/-- Independently checking each sorted cell group yields a successful actual
chronological memory replay, with no guessed permutation accepted for free. -/
theorem chronological_replay (memory : Memory) (events grouped : List Event)
    (horder : ∀ cell, atCell cell grouped = atCell cell events)
    (hchecks : valid memory grouped) :
    ∃ finalMemory, run memory events = some finalMemory := by
  have hg := (run_success_iff memory grouped).mpr hchecks
  have hr := (grouped_success_iff memory events grouped horder).mp hg
  cases h : run memory events with
  | none => simp [h] at hr
  | some result => exact ⟨result, rfl⟩

end NearCubicWires.RepairOrdinary.MemoryLog
