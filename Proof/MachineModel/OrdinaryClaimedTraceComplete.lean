import Proof.MachineModel.OrdinaryClaimedTrace

/-! Every actual finite-machine run supplies a valid bounded computation log.
Together with ClaimedTrace.sound, this closes the certificate's semantic
equivalence; the fixed ordinary verifier and its total time are separate. -/
namespace NearCubicWires.RepairOrdinary
open LocalBitMultitape MemoryLog MemoryTransition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace MemoryTransition

theorem actual_batch_run {t s : ℕ} (c : Configuration t s) (action : Action t s) :
    MemoryLog.run (memoryOf c)
      (batch c.heads c.scanned (fun i => (action.write i).getD (c.scanned i))) =
        some (memoryOf (applyAction c action)) := by
  let after : Fin t → Bool := fun i => (action.write i).getD (c.scanned i)
  have hv : valid (memoryOf c) (batch c.heads c.scanned after) := by
    intro cell
    by_cases ht : cell.1 < t
    · let i : Fin t := ⟨cell.1, ht⟩
      by_cases hp : cell.2 = c.heads i
      · have he : (i.val, c.heads i) = cell := Prod.ext rfl hp.symm
        rw [← he, at_tape, memoryOf_head]
        simp [localRun, event]
      · have hb := at_other c.heads c.scanned after cell (by
          intro j hj
          have hji : j = i := Fin.ext (congrArg Prod.fst hj)
          subst j
          exact hp (congrArg Prod.snd hj).symm)
        rw [hb]
        rfl
    · have hb := at_other c.heads c.scanned after cell (by
        intro j hj
        have he := congrArg Prod.fst hj
        exact ht (he ▸ j.isLt))
      rw [hb]
      rfl
  have hs := (run_success_iff _ _).mpr hv
  change MemoryLog.run (memoryOf c) (batch c.heads c.scanned after) = _
  cases hr : MemoryLog.run (memoryOf c) (batch c.heads c.scanned after) with
  | none => simp [hr] at hs
  | some middle =>
      have hm := batch_effect c.heads c.scanned after (memoryOf c) middle hr
      change middle = batchMemory (memoryOf c) c.heads (fun i => (action.write i).getD (c.scanned i)) at hm
      rw [← memoryOf_action] at hm
      exact congrArg some hm

end MemoryTransition

namespace ClaimedTrace

theorem complete_prefix {t s space n : ℕ} (machine : Machine t s)
    {c d : Configuration t s} (hp : Prefix machine space n c d) :
    ∃ claims events,
      claims.length = n ∧ events.length = t*n ∧
      check machine (view c) claims = some (view d, events) ∧
      MemoryLog.run (memoryOf c) events = some (memoryOf d) := by
  induction hp with
  | refl c hc => exact ⟨[], [], rfl, by simp, rfl, rfl⟩
  | @step n c d e hc hnot hstep hp ih =>
      cases ha : machine.rule c.control c.scanned with
      | none => simp [step, ha] at hstep
      | some action =>
        have he : applyAction c action = d := by simpa [step, ha] using hstep
        subst d
        obtain ⟨claims, events, hlen, hevents, hcheck, hmem⟩ := ih
        refine ⟨c.scanned :: claims,
          batch c.heads c.scanned (fun i => (action.write i).getD (c.scanned i)) ++ events,
          by simp [hlen], ?_, ?_, ?_⟩
        · simp [batch, hevents, Nat.mul_add, Nat.add_comm]
        · change check machine (advance (view c) action) claims = _ at hcheck
          dsimp only [view] at hcheck
          simp only [check, view, hnot, Bool.false_eq_true, if_false, ha, hcheck, Option.map_some]
        · rw [MemoryLog.run_append, actual_batch_run]
          exact hmem

theorem complete {t s : ℕ} (machine : Machine t s) (fuel : ℕ)
    (c : Configuration t s) (r : ExecutionReceipt t s)
    (hr : runFrom machine fuel c = some r) :
    ∃ claims events,
      claims.length = r.steps ∧ events.length = t*r.steps ∧
      check machine (view c) claims = some (view r.final, events) ∧
      MemoryLog.run (memoryOf c) events = some (memoryOf r.final) ∧
      machine.halted r.final.control = true := by
  obtain ⟨hp, hh⟩ := prefix_of_run machine fuel c r hr
  obtain ⟨claims, events, hl, he, hc, hm⟩ := complete_prefix machine hp
  exact ⟨claims, events, hl, he, hc, hm, hh⟩

end ClaimedTrace
end NearCubicWires.RepairOrdinary
