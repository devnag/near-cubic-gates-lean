import Proof.Amplification.RecoveryQueryInputs
import Proof.Amplification.RecoveryQueryBounds

/-! Retained outputs used by later fixed query nodes.  No assumption that
an arithmetic call preserves its consumed operands is required. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stage_result (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (outs : Fin 9→Fin 39→List Bool) (k : Fin 9) :
    stage cap flat payload committed count original outs (k.val+1) (bank k 26)=outs k 26 := by
  have he : (⟨k.val%9,Nat.mod_lt _ (by decide)⟩ : Fin 9)=k :=
    Fin.ext (Nat.mod_eq_of_lt k.isLt)
  rw [stage,he]
  exact install_slot _ (cell_injective k) _ _ 26

theorem saved_one (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (outs : Fin 9→Fin 39→List Bool) :
    stage cap flat payload committed count original outs 3 (bank 1 26)=outs 1 26 := by
  change install (cellSlots 2) (stage cap flat payload committed count original outs 2) (outs 2) (bank 1 26)=_
  rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
  exact stage_result cap flat payload committed count original outs 1

theorem saved_four (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (outs : Fin 9→Fin 39→List Bool) :
    stage cap flat payload committed count original outs 7 (bank 4 26)=outs 4 26 := by
  change install (cellSlots 6) (stage cap flat payload committed count original outs 6) (outs 6) (bank 4 26)=_
  rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
  change install (cellSlots 5) (stage cap flat payload committed count original outs 5) (outs 5) (bank 4 26)=_
  rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
  exact stage_result cap flat payload committed count original outs 4

end NearCubicWires.RepairOrdinary.RecoveryQueryKernel
