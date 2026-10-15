import Proof.Amplification.RecoveryRawViewCopyTapes

/-! The sparse copy installation is proved over opaque ambient tapes, so
the enclosing machine does not normalize its entire retained workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copy_install (ambient : Fin 65→List Bool) (bits : List Bool) (capacity reset : Nat)
    (hf : ambient 60=frame bits) :
    install copySlots ambient ![frame bits,frame bits,List.replicate capacity false,List.replicate reset false]=
      Function.update (Function.update (Function.update ambient 58 (List.replicate capacity false)) 0 (frame bits))
        22 (List.replicate reset false) := by
  funext i
  by_cases hi : ∃ j,copySlots j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [install_slot copySlots copySlots_injective]
    fin_cases j
    · exact hf.symm
    · rfl
    · rfl
    · rfl
  · rw [install_other copySlots _ _ _ (by intro j hj; exact hi ⟨j,hj⟩)]
    have h0 : i≠(0 : Fin 65) := by intro he; exact hi ⟨1,he.symm⟩
    have h58 : i≠(58 : Fin 65) := by intro he; exact hi ⟨2,he.symm⟩
    have h22 : i≠(22 : Fin 65) := by intro he; exact hi ⟨3,he.symm⟩
    rw [Function.update_of_ne h22,Function.update_of_ne h0,Function.update_of_ne h58]

end NearCubicWires.RepairOrdinary.RecoveryRawView
