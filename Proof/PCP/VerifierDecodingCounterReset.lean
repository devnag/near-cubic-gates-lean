import Proof.PCP.VerifierDecodingGuardedEntry

/-! Restore one physically produced capped counter while retaining every
other tape and head. This pays the table guard's t/s cursor handoff to the
state-width producer and record scans. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.CounterReset
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slot {k : ℕ} (target : Fin k) : Fin 1 → Fin k := fun _ => target
theorem slot_injective {k : ℕ} (target : Fin k) : Function.Injective (slot target) := by
  intro a b _; exact Subsingleton.elim _ _
theorem slot_pick {k : ℕ} (target i : Fin k) :
    RecoveryFocus.pick (slot target) i=if i=target then some 0 else none := by
  by_cases h : i=target
  · subst i
    simpa [slot] using RecoveryFocus.pick_slot (slot target) (slot_injective target) 0
  · simp [RecoveryFocus.pick,slot,h,Ne.symm h]

noncomputable def program {k : ℕ} (target : Fin k) :=
  RecoveryFocus.machine (slot target) UnaryTemplate.machine

theorem focused_cfg {k : ℕ} (target : Fin k) (heads : Fin k → ℕ)
    (tapes : Fin k → List Bool) (c n pos : ℕ) (q : Fin 3)
    (ht : tapes target=CapMachine.counter c n) :
    RecoveryFocus.config (slot target) heads tapes
      (UnaryTemplate.config q (CapMachine.counter c n) pos)=
      ⟨q,(fun i => if i=target then pos else heads i),tapes⟩ := by
  apply configuration_ext
  · rfl
  · funext i; by_cases h : i=target <;> simp [RecoveryFocus.config,slot_pick,UnaryTemplate.config,h]
  · funext i; by_cases h : i=target
    · subst i; simp [RecoveryFocus.config,slot_pick,UnaryTemplate.config,ht]
    · simp [RecoveryFocus.config,slot_pick,h]

theorem reset_run {k : ℕ} (target : Fin k) (heads : Fin k → ℕ)
    (tapes : Fin k → List Bool) (c n pos : ℕ)
    (hn : n≤c) (hp : pos≤n)
    (ht : tapes target=CapMachine.counter c n) (hh : heads target=pos+1) :
    ∃ r, runFrom (program target) (pos+2) ⟨0,heads,tapes⟩=some r ∧
      r.final=⟨2,(fun i => if i=target then 1 else heads i),tapes⟩ ∧ r.steps=pos+2 := by
  obtain ⟨base,hr,hf,hs,_⟩ := CapMachine.reset_run c n pos hn hp
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config (slot target)
    (slot_injective target) UnaryTemplate.machine heads tapes _ _ base hr
  rw [focused_cfg target heads tapes c n (pos+1) 0 ht] at hrun
  have hi : (⟨0,(fun i => if i=target then pos+1 else heads i),tapes⟩ : Configuration k 3)=
      ⟨0,heads,tapes⟩ := by
    apply configuration_ext
    · rfl
    · funext i; by_cases h : i=target <;> simp [h,hh]
    · rfl
  rw [hi] at hrun
  rw [hf,focused_cfg target heads tapes c n 1 2 ht] at hfinal
  exact ⟨r,hrun,hfinal,hsteps.trans hs⟩

end NearCubicWires.RepairSource.VerifierDecoding.CounterReset
