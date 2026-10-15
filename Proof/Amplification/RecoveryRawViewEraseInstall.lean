import Proof.Amplification.RecoveryRawViewEraseState

/-! Exact sparse installation for the physical counter sweep. The retained
unary erase driver is preserved and only counter/reset tapes are changed. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem erase_install (ambient : Fin 65→List Bool) (capacity reset : Nat)
    (hd : ambient 21=List.replicate capacity true) :
    install eraseSlots ambient
      ![List.replicate capacity false,List.replicate capacity true,List.replicate reset false]=
      Function.update (Function.update ambient 35 (List.replicate capacity false)) 22 (List.replicate reset false) := by
  funext i
  by_cases hi : ∃ j,eraseSlots j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [install_slot eraseSlots eraseSlots_injective]
    fin_cases j
    · rfl
    · exact hd.symm
    · rfl
  · rw [install_other eraseSlots _ _ _ (by intro j hj; exact hi ⟨j,hj⟩)]
    have h35 : i≠(35 : Fin 65) := by intro he; exact hi ⟨0,he.symm⟩
    have h22 : i≠(22 : Fin 65) := by intro he; exact hi ⟨2,he.symm⟩
    rw [Function.update_of_ne h22,Function.update_of_ne h35]

end NearCubicWires.RepairOrdinary.RecoveryRawView
