import Proof.Amplification.RecoveryBinaryBound

/-! Install the executed binary at-least-one correction into the same
five-tape dimensions bank, preserving its produced width driver and both
paid counter workspaces. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdBinaryFix
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2→Fin 5 := ![0,2]
theorem slots_injective : Function.Injective slots := by decide
theorem pick_eq (i : Fin 5) : RecoveryFocus.pick slots i=![some 0,none,some 1,none,none] i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot slots slots_injective 0
  · have hn : ¬∃ j,slots j=(1 : Fin 5) := by decide
    simp [RecoveryFocus.pick,hn]
  · exact RecoveryFocus.pick_slot slots slots_injective 1
  · have hn : ¬∃ j,slots j=(3 : Fin 5) := by decide
    simp [RecoveryFocus.pick,hn]
  · have hn : ¬∃ j,slots j=(4 : Fin 5) := by decide
    simp [RecoveryFocus.pick,hn]
noncomputable def machine := RecoveryFocus.machine slots RecoveryColdBinaryBound.machine

def output (bits : List Bool) (cap scratch : Nat) : Fin 5→List Bool :=
  ![frame bits,RecoveryColdWidth.word (RecoveryColdWidth.width bits.length),
    frame (ClockBinary.word (max 1 bits.length)),List.replicate cap false,List.replicate scratch false]

theorem fix_run (bits : List Bool) (cap scratch : Nat) :
    ∃ r,runFrom machine 4 ⟨machine.start,RecoveryColdBinaryCount.heads,RecoveryColdBinaryCount.output bits cap scratch⟩=some r ∧
      r.final.heads=RecoveryColdBinaryCount.heads ∧ r.final.tapes=output bits cap scratch ∧ r.steps ≤ 4 := by
  obtain ⟨base,hbase,hb,hn⟩ := RecoveryColdBinaryBound.bound_run bits
  obtain ⟨r,hr,hf,hsteps⟩ := RecoveryFocus.run_config slots slots_injective RecoveryColdBinaryBound.machine
    RecoveryColdBinaryCount.heads (RecoveryColdBinaryCount.output bits cap scratch) 4 _ base hbase
  have hi : RecoveryFocus.config slots RecoveryColdBinaryCount.heads (RecoveryColdBinaryCount.output bits cap scratch)
      (RecoveryColdBinaryBound.cfg 0 (frame bits) (frame (ClockBinary.word bits.length)) 0)=
      (⟨machine.start,RecoveryColdBinaryCount.heads,RecoveryColdBinaryCount.output bits cap scratch⟩ : Configuration 5 _) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [RecoveryFocus.config,pick_eq,RecoveryColdBinaryBound.cfg,RecoveryColdBinaryCount.heads]
    · funext i
      fin_cases i <;> simp [RecoveryFocus.config,pick_eq,RecoveryColdBinaryBound.cfg,RecoveryColdBinaryCount.output]
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,hsteps.le.trans hn⟩
  · rw [hf,hb]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_eq,RecoveryColdBinaryBound.cfg,RecoveryColdBinaryCount.heads]
  · rw [hf,hb]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_eq,RecoveryColdBinaryBound.cfg,RecoveryColdBinaryCount.output,output]

end NearCubicWires.RepairOrdinary.RecoveryColdBinaryFix
