import Proof.MachineModel.OrdinaryMemoryEffect

/-! Whole-trace soundness of the computation-log skeleton. The symbolic walk
stores only control and head positions. Checked memory events recover an
actual bounded run of the original finite multitape machine. -/
namespace NearCubicWires.RepairOrdinary
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace MemoryLog

theorem run_append (memory : Memory) (xs ys : List Event) :
    run memory (xs ++ ys) = (run memory xs).bind (fun next => run next ys) := by
  induction xs generalizing memory with
  | nil => rfl
  | cons e es ih =>
      by_cases h : e.read = memory e.cell
      · simpa only [List.cons_append, run, if_pos h] using
          ih (Function.update memory e.cell e.after)
      · simp [run, h]

theorem run_append_split (memory finalMemory : Memory) (xs ys : List Event)
    (hr : run memory (xs ++ ys) = some finalMemory) :
    ∃ middle, run memory xs = some middle ∧ run middle ys = some finalMemory := by
  rw [run_append] at hr
  cases hx : run memory xs with
  | none => simp [hx] at hr
  | some middle => exact ⟨middle, rfl, by simpa [hx] using hr⟩

end MemoryLog

namespace ClaimedTrace
open MemoryLog MemoryTransition

structure View (t s : ℕ) where
  control : Fin s
  heads : Fin t → ℕ

def view {t s : ℕ} (c : Configuration t s) : View t s := ⟨c.control, c.heads⟩

def advance {t s : ℕ} (v : View t s) (a : Action t s) : View t s :=
  ⟨a.nextControl, fun i => (a.move i).apply (v.heads i)⟩

def check {t s : ℕ} (machine : Machine t s) :
    View t s → List (Fin t → Bool) → Option (View t s × List Event)
  | v, [] => some (v, [])
  | v, reads :: rest =>
      if machine.halted v.control then none else
      match machine.rule v.control reads with
      | none => none
      | some action =>
          (check machine (advance v action) rest).map (fun result =>
            (result.1, batch v.heads reads (fun i => (action.write i).getD (reads i)) ++ result.2))

theorem sound {t s : ℕ} (machine : Machine t s) (c : Configuration t s)
    (claims : List (Fin t → Bool)) (finalView : View t s) (events : List Event)
    (finalMemory : Memory)
    (hcheck : check machine (view c) claims = some (finalView, events))
    (hmemory : MemoryLog.run (memoryOf c) events = some finalMemory)
    (hhalt : machine.halted finalView.control = true) :
    ∃ r : ExecutionReceipt t s,
      runFrom machine claims.length c = some r ∧
      view r.final = finalView ∧ memoryOf r.final = finalMemory := by
  induction claims generalizing c finalView events finalMemory with
  | nil =>
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hcheck
      obtain ⟨rfl, rfl⟩ := hcheck
      simp only [MemoryLog.run, Option.some.injEq] at hmemory
      refine ⟨⟨c, 0, c.tapeCells⟩, ?_, rfl, hmemory⟩
      simp only [List.length_nil, runFrom, view] at hhalt ⊢
      simp [hhalt]
  | cons reads rest ih =>
      cases hst : machine.halted c.control with
      | true => simp [check, view, hst] at hcheck
      | false =>
        cases ha : machine.rule c.control reads with
        | none => simp [check, view, hst, ha] at hcheck
        | some action =>
          cases ht : check machine (advance (view c) action) rest with
          | none =>
            dsimp only [view] at ht
            simp [check, view, hst, ha, ht] at hcheck
          | some result =>
            dsimp only [view] at ht
            rcases result with ⟨v, es⟩
            have he : (v, batch c.heads reads (fun i => (action.write i).getD (reads i)) ++ es) =
                (finalView, events) := by
              simpa only [check, view, hst, Bool.false_eq_true, if_false, ha, ht, Option.map_some,
                Option.some.injEq] using hcheck
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
            obtain ⟨middle, hfirst, htail⟩ := run_append_split (memoryOf c) finalMemory _ _ hmemory
            obtain ⟨hstep, hmiddle⟩ := actual_step_and_memory machine c reads action middle ha hfirst
            rw [hmiddle] at htail
            have hnext : check machine (view (applyAction c action)) rest = some (v, es) := ht
            obtain ⟨r, hr, hv, hm⟩ := ih (applyAction c action) v es finalMemory hnext htail hhalt
            refine ⟨⟨r.final, r.steps+1, max c.tapeCells r.peakTapeCells⟩, ?_, hv, hm⟩
            simp only [List.length_cons, runFrom, hst, Bool.false_eq_true, if_false, hstep, hr]

end ClaimedTrace
end NearCubicWires.RepairOrdinary
