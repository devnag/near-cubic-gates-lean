import Proof.MachineModel.OrdinaryMemorySortedReplay

/-! A checked log's claimed reads select the actual finite machine rule.
Each transition emits exactly one memory event per simulated tape. -/
namespace NearCubicWires.RepairOrdinary.MemoryTransition
open LocalBitMultitape MemoryLog
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def event {t : ℕ} (heads : Fin t → ℕ) (reads after : Fin t → Bool) (i : Fin t) : Event :=
  ⟨(i.val, heads i), reads i, after i⟩

def batch {t : ℕ} (heads : Fin t → ℕ) (reads after : Fin t → Bool) : List Event :=
  (List.finRange t).map (event heads reads after)

theorem at_tape {t : ℕ} (heads : Fin t → ℕ) (reads after : Fin t → Bool) (i : Fin t) :
    atCell (i.val, heads i) (batch heads reads after) = [event heads reads after i] := by
  have he : (fun j : Fin t => (event heads reads after j).cell == (i.val, heads i)) =
      (fun j => j == i) := by
    funext j
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, event, Prod.mk.injEq]
    constructor
    · rintro ⟨hj, _⟩
      exact Fin.ext hj
    · intro hj
      subst j
      exact ⟨rfl, rfl⟩
  simp only [atCell, batch, List.filter_map, Function.comp_def]
  rw [he, List.filter_beq]
  simp

theorem checked_reads {t : ℕ} (heads : Fin t → ℕ) (reads after : Fin t → Bool)
    (memory : Memory) (hcheck : valid memory (batch heads reads after)) :
    ∀ i, reads i = memory (i.val, heads i) := by
  intro i
  have h := hcheck (i.val, heads i)
  rw [at_tape] at h
  by_cases he : reads i = memory (i.val, heads i)
  · exact he
  · simp [localRun, event, he] at h

def memoryOf {t s : ℕ} (c : Configuration t s) : Memory :=
  fun cell => if h : cell.1 < t then readTapeBit (c.tapes ⟨cell.1, h⟩) cell.2 else false

@[simp] theorem memoryOf_head {t s : ℕ} (c : Configuration t s) (i : Fin t) :
    memoryOf c (i.val, c.heads i) = c.scanned i := by
  simp [memoryOf, i.isLt, Configuration.scanned]

/-- The log does not get to choose a different rule by inventing scanned
bits: successful memory checks force those bits to equal the real tapes. -/
theorem actual_step {t s : ℕ} (machine : Machine t s) (c : Configuration t s)
    (reads : Fin t → Bool) (action : Action t s)
    (hrule : machine.rule c.control reads = some action)
    (hcheck : valid (memoryOf c)
      (batch c.heads reads (fun i => (action.write i).getD (reads i)))) :
    step machine c = some (applyAction c action) := by
  have hreads : reads = c.scanned := by
    funext i
    simpa only [memoryOf_head] using checked_reads c.heads reads _ (memoryOf c) hcheck i
  rw [hreads] at hrule
  simp only [step, hrule, Option.map_some]

end NearCubicWires.RepairOrdinary.MemoryTransition
