import Proof.Amplification.RecoveryTseitinAppend
import Proof.Amplification.RecoveryPrefixCounter

/-! Advance the actual canonical index after emitting its tautology.
The live formula cursor is retained and the appender's cleared log is reused. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinKernel CircuitInputCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def incrementSlots : Fin 2→Fin 241 := ![0,240]
theorem increment_injective : Function.Injective incrementSlots := by decide
noncomputable def incrementMachine := RecoveryFocus.machine incrementSlots ClockIncrement.machine

theorem increment_run (cap index : Nat) (head : Fin 241→Nat) (data : Fin 241→List Bool)
    (hc : ClockIncrement.work index.bits ≤ cap) (h0 : head 0=0) (h240 : head 240=0)
    (d0 : data 0=ZeroPadding.pad cap (RepairOrdinary.frame index.bits))
    (d240 : data 240=List.replicate cap false) : ∃ r,
    runFrom incrementMachine (4*index.bits.length+8) ⟨incrementMachine.start,head,data⟩=some r ∧
      r.final.heads=head ∧
      r.final.tapes=Function.update data 0 (ZeroPadding.pad cap (RepairOrdinary.frame (index+1).bits)) ∧
      r.steps ≤ 4*index.bits.length+8 := by
  obtain ⟨base,hr,bt,bh,bs⟩ := RecoveryPrefixCounter.increment_ready cap index hc
  obtain ⟨r,rr,_rc,rs,rh,rt,ro⟩ := RecoveryFocus.dock incrementSlots increment_injective
    ClockIncrement.machine (4*index.bits.length+8) head data _
    (by intro j; fin_cases j; exact h0; exact h240)
    (by intro j; fin_cases j; exact d0; exact d240) base hr
  refine ⟨r,rr,?_,?_,rs.trans_le bs⟩
  · funext i
    by_cases hi0 : i=0
    · subst i; exact (rh 0).trans ((bh 0).trans h0.symm)
    by_cases hi240 : i=240
    · subst i; exact (rh 1).trans ((bh 1).trans h240.symm)
    exact (ro i (by intro j; fin_cases j; exact Ne.symm hi0; exact Ne.symm hi240)).1
  · funext i
    by_cases hi0 : i=0
    · subst i
      rw [Function.update_self]
      have h := rt 0
      rw [bt] at h
      exact h
    rw [Function.update_of_ne hi0]
    by_cases hi240 : i=240
    · subst i
      have h := rt 1
      rw [bt] at h
      exact h.trans d240.symm
    exact (ro i (by intro j; fin_cases j; exact Ne.symm hi0; exact Ne.symm hi240)).2

end NearCubicWires.RepairSource.RecoveryTseitinTautology
