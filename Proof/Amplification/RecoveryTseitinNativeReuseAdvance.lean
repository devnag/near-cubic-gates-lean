import Proof.Amplification.RecoveryTseitinNativeReusePrefix
import Proof.Amplification.RecoveryTseitinRawIncrement

/-! Advance the retained raw node index on the actual reusable tape bank. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advanceSlots : Fin 2→Fin 1338 := ![1,2]
noncomputable def advanceMachine := RecoveryFocus.machine advanceSlots RecoveryTseitinRawIncrement.machine
theorem advance_run {z : Nat} (n index pos : Nat) (word out : List Bool) (cap : Nat)
    (hcap : index+1 ≤ cap) (ambient : Configuration 1338 z)
    (hh : ambient.heads=heads pos out.length) (ht : ambient.tapes=data n index word out cap) :
    ∃ r,runFrom advanceMachine (2*index+4) (Composition.restart ambient advanceMachine.start)=some r ∧
      r.final.heads=heads pos out.length ∧ r.final.tapes=data n (index+1) word out cap ∧
      r.steps ≤ 2*index+4 := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryTseitinRawIncrement.increment_ready index cap hcap).focus_at
    advanceSlots (by decide) ambient.heads ambient.tapes
    (by intro j; rw [ht]; fin_cases j <;> rfl)
    (by intro j; rw [hh]; fin_cases j <;> rfl)
  refine ⟨r,hr,rh.trans hh,?_,rs.le⟩
  rw [rt]
  funext i
  by_cases h1 : i=1
  · subst i
    exact install_slot advanceSlots (by decide) _ _ 0
  by_cases h2 : i=2
  · subst i
    exact install_slot advanceSlots (by decide) _ _ 1
  rw [install_other advanceSlots _ _ _ (by intro j; fin_cases j <;> exact Ne.symm (by assumption)),ht]
  simp only [data,if_neg h1]

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
