import Proof.Amplification.RecoveryReturnBit
import Proof.MachineModel.OrdinaryZeroUnpadding

/-! The actual all-code machine now ends in accepting/rejecting control.
Existing inverse-padding transport permits physically blank false-only
backing, while every true driver and framed datum remains required. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAllCodeAccepted
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle RecoveryAllCode
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev states {t s : Nat} (_ : Machine t s) := s
noncomputable def machine := RecoveryReturnBit.machine RecoveryAllCode.machine (93 : Fin 348)
noncomputable def accepting := RecoveryReturnBit.accepting (states RecoveryAllCode.machine)
def budget (width : Nat) := RecoveryAllCode.budget width+2

theorem budget_le (width : Nat) : budget width ≤ 8589934592*(width+1)^4 := by
  have h := RecoveryAllCode.budget_le width
  have hp : 1 ≤ (width+1)^4 := Nat.one_le_pow _ _ (by omega)
  unfold budget
  omega

theorem checked_run (x : State) (limit : Nat) (word : List Bool) (k : Nat)
    (innerBits outerBits innerPre outerPre : List Bool)
    (hx : Prepared x limit word k innerBits outerBits innerPre outerPre) :
    ∃ r,runFrom machine (budget x.width) (cfg x machine.start)=some r ∧
      r.steps ≤ 8589934592*(x.width+1)^4 ∧
      (accepting r.final.control=true → correctedSat x.code=true) := by
  obtain ⟨first,hr,_,hh,⟨bit,ht⟩,hs⟩ := checker_run x limit word k innerBits outerBits innerPre outerPre hx
  obtain ⟨r,hrun,ha⟩ := RecoveryReturnBit.finish_run RecoveryAllCode.machine (93 : Fin 348)
    (RecoveryAllCode.budget x.width) (cfg x RecoveryAllCode.machine.start) first hr bit hh ht
  have hsteps := runFrom_steps_le machine (budget x.width) (cfg x machine.start) r hrun
  refine ⟨r,hrun,hsteps.trans (budget_le x.width),?_⟩
  intro haccept
  have hb : bit=true := ha.symm.trans haccept
  apply hs
  rw [ht,hb]

theorem unpadded_run (x : State) (limit : Nat) (word : List Bool) (k : Nat)
    (innerBits outerBits innerPre outerPre : List Bool)
    (hx : Prepared x limit word k innerBits outerBits innerPre outerPre)
    (capacity : Fin 348→Nat) (source : Configuration 348 (states machine))
    (hc : ZeroPadding.config capacity source=cfg x machine.start) :
    ∃ r,runFrom machine (budget x.width) source=some r ∧
      r.steps ≤ 8589934592*(x.width+1)^4 ∧
      (accepting r.final.control=true → correctedSat x.code=true) := by
  obtain ⟨base,hb,hn,hs⟩ := checked_run x limit word k innerBits outerBits innerPre outerPre hx
  rw [←hc] at hb
  obtain ⟨r,hr,hf,hsteps,_⟩ := ZeroPadding.run_unpad machine capacity (budget x.width) source base hb
  refine ⟨r,hr,?_,?_⟩
  · rw [hsteps]
    exact hn
  · intro ha
    apply hs
    rw [←hf]
    exact ha

end NearCubicWires.RepairOrdinary.RecoveryAllCodeAccepted
