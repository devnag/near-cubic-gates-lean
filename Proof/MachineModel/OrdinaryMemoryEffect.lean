import Proof.MachineModel.OrdinaryMemoryTransition

/-! The memory state returned by a checked transition batch is exactly the
memory of the actual next configuration. This is the invariant needed to
iterate the computation-log check across a whole trace. -/
namespace NearCubicWires.RepairOrdinary
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace MemoryLog

theorem run_cell_result (memory : Memory) (events : List Event) (finalMemory : Memory)
    (hr : run memory events = some finalMemory) (cell : Cell) :
    localRun (memory cell) (atCell cell events) = some (finalMemory cell) := by
  induction events generalizing memory with
  | nil =>
      simp only [run, Option.some.injEq] at hr
      subst memory
      rfl
  | cons e es ih =>
      simp only [run] at hr
      split at hr
      · next hread =>
          have hc := ih (Function.update memory e.cell e.after) hr
          by_cases he : e.cell = cell
          · subst cell
            simpa [atCell, localRun, hread] using hc
          · simpa [atCell, he, Function.update_of_ne (Ne.symm he)] using hc
      · cases hr

end MemoryLog

namespace MemoryTransition
open MemoryLog

theorem at_other {t : ℕ} (heads : Fin t → ℕ) (reads after : Fin t → Bool) (cell : Cell)
    (hne : ∀ i, (i.val, heads i) ≠ cell) : atCell cell (batch heads reads after) = [] := by
  rw [atCell, List.filter_eq_nil_iff]
  intro e he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  simpa [event] using hne i

def batchMemory {t : ℕ} (memory : Memory) (heads : Fin t → ℕ) (after : Fin t → Bool) : Memory :=
  fun cell => if ht : cell.1 < t then
    if cell.2 = heads ⟨cell.1, ht⟩ then after ⟨cell.1, ht⟩ else memory cell
    else memory cell

theorem batch_effect {t : ℕ} (heads : Fin t → ℕ) (reads after : Fin t → Bool)
    (memory finalMemory : Memory) (hr : MemoryLog.run memory (batch heads reads after) = some finalMemory) :
    finalMemory = batchMemory memory heads after := by
  have hreads := checked_reads heads reads after memory ((run_success_iff _ _).mp (by simp [hr]))
  funext cell
  have hc := run_cell_result memory (batch heads reads after) finalMemory hr cell
  by_cases ht : cell.1 < t
  · let i : Fin t := ⟨cell.1, ht⟩
    by_cases hpos : cell.2 = heads i
    · have he : (i.val, heads i) = cell := Prod.ext rfl hpos.symm
      rw [← he, at_tape] at hc
      have hv : after i = finalMemory (i.val, heads i) := by
        simpa [localRun, event, hreads i] using hc
      simpa [batchMemory, ht, hpos, i, he] using hv.symm
    · have hb := at_other heads reads after cell (by
        intro j hj
        have hji : j = i := Fin.ext (congrArg Prod.fst hj)
        subst j
        exact hpos (congrArg Prod.snd hj).symm)
      rw [hb] at hc
      have hv : memory cell = finalMemory cell := by simpa [localRun] using hc
      simpa [batchMemory, ht, hpos, i] using hv.symm
  · have hb := at_other heads reads after cell (by
      intro j hj
      have hj' := congrArg Prod.fst hj
      exact ht (hj' ▸ j.isLt))
    rw [hb] at hc
    have hv : memory cell = finalMemory cell := by simpa [localRun] using hc
    simpa [batchMemory, ht] using hv.symm

theorem read_write (bits : List Bool) (position address : ℕ) (b : Bool) :
    readTapeBit (writeTapeBit bits position b) address =
      if address = position then b else readTapeBit bits address := by
  induction position generalizing bits address with
  | zero => cases bits <;> cases address <;> simp [readTapeBit, writeTapeBit]
  | succ position ih =>
      cases bits <;> cases address <;> simp_all [readTapeBit, writeTapeBit]

theorem memoryOf_action {t s : ℕ} (c : Configuration t s) (action : Action t s) :
    memoryOf (applyAction c action) =
      batchMemory (memoryOf c) c.heads (fun i => (action.write i).getD (c.scanned i)) := by
  funext cell
  by_cases ht : cell.1 < t
  · let i : Fin t := ⟨cell.1, ht⟩
    change (if h : cell.1 < t then readTapeBit ((applyAction c action).tapes ⟨cell.1,h⟩) cell.2 else false) = _
    simp only [ht, ↓reduceDIte, applyAction, batchMemory]
    change readTapeBit (match action.write i with | none => c.tapes i | some b => writeTapeBit (c.tapes i) (c.heads i) b) cell.2 = _
    cases hw : action.write i with
    | none =>
        by_cases hp : cell.2 = c.heads i <;>
          simp [ht, hp, memoryOf, Configuration.scanned, i]
    | some b =>
        rw [read_write]
        simp [ht, memoryOf, i]
  · simp [memoryOf, batchMemory, ht]

theorem actual_step_and_memory {t s : ℕ} (machine : Machine t s) (c : Configuration t s)
    (reads : Fin t → Bool) (action : Action t s) (finalMemory : Memory)
    (hrule : machine.rule c.control reads = some action)
    (hr : MemoryLog.run (memoryOf c)
      (batch c.heads reads (fun i => (action.write i).getD (reads i))) = some finalMemory) :
    step machine c = some (applyAction c action) ∧ finalMemory = memoryOf (applyAction c action) := by
  have hs : (MemoryLog.run (memoryOf c)
      (batch c.heads reads (fun i => (action.write i).getD (reads i)))).isSome = true := by
    rw [hr]
    rfl
  have hcheck := (run_success_iff _ _).mp hs
  refine ⟨actual_step machine c reads action hrule hcheck, ?_⟩
  have hreads : reads = c.scanned := by
    funext i
    simpa only [memoryOf_head] using checked_reads c.heads reads _ (memoryOf c) hcheck i
  rw [batch_effect c.heads reads _ (memoryOf c) finalMemory hr, hreads, ← memoryOf_action]

end MemoryTransition
end NearCubicWires.RepairOrdinary
