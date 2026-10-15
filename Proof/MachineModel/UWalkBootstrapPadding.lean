import Proof.MachineModel.UInitializedWalkFields
import Proof.MachineModel.UWalkArrayLiteral

/-! The actual decoder counter may have a shorter all-zero tail than the
numeric bootstrap's logical capped representation. This exact same-program
padding transport preserves all observations and executes no allocation. -/
namespace NearCubicWires.RepairOrdinary.UWalkBootstrap
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity {u : ℕ} (c : ℕ) (i : Fin u) : ℕ := if i.val=50 then c+2 else 0
noncomputable def entry {s : ℕ} (base : Configuration 97 s) := UWalkArray.entry97 base.heads base.tapes

theorem entry_padding {s : ℕ} (c : ℕ) (base : Configuration 97 s) :
    ZeroPadding.config (capacity c) (entry base)=entry (ZeroPadding.config (capacity c) base) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (motive := fun i : Fin (97+42) =>
      (ZeroPadding.config (capacity c) (entry base)).tapes i=
      (entry (ZeroPadding.config (capacity c) base)).tapes i)
      (fun k : Fin 97 => ?_) (fun k : Fin 42 => ?_) i
    · simp [entry,UWalkArray.entry97,UWalkArray.entry,RecoveryCalls.restarted,UWalkArray.extendTapes,
        ZeroPadding.config,capacity]
      rfl
    · have hk : k.val+97≠50 := by omega
      simp [entry,UWalkArray.entry97,UWalkArray.entry,RecoveryCalls.restarted,UWalkArray.extendTapes,
        ZeroPadding.config,capacity,hk,Nat.add_comm]

end NearCubicWires.RepairOrdinary.UWalkBootstrap
