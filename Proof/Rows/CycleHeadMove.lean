import Proof.MachineModel.Runs

/-! A single paid transition for a fixed finite vector of head movements. -/
namespace Theorem25Completion.CycleHeadMove
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
set_option autoImplicit false
set_option warningAsError true

def machine {t : Nat} (directions : Fin t→HeadMove) : Machine t 2 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==1
  rule:=fun s _=>if s.val=0 then some ⟨1,fun _=>none,directions⟩ else none

theorem run {t : Nat} (directions : Fin t→HeadMove) (H : Fin t→Nat) (A : Fin t→List Bool) :
    Step (machine directions) 1 H A (fun i=>(directions i).apply (H i)) A := by
  have hs : step (machine directions) (⟨0,H,A⟩ : Configuration t 2)=
      some (⟨1,fun i=>(directions i).apply (H i),A⟩ : Configuration t 2) := by
    simp [step,machine]
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  obtain ⟨r,hr,hf,ht⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,ht.le⟩

end Theorem25Completion.CycleHeadMove
