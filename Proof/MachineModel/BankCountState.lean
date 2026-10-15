import Proof.MachineModel.BankCountRaw

/-! Exact ambient state after the original raw incidence pass. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem after_tapes_eq (A : Fin 128→List Bool) (C : ℕ) (table : List Bool) (M : ℕ) :
    afterTapes A C table M=Function.update (Function.update A 36 (ZeroPadding.pad C table))
      115 (ZeroPadding.pad C (List.replicate M true)):=by
  funext i
  by_cases inside : ∃ j,rawOld j=i
  · obtain ⟨j,rfl⟩:=inside
    rw [after_tapes_old]
    simp only [BankExecution.changedTapes,Function.update_apply,Function.comp_apply,
      rawOld,Fin.ext_iff,Fin.val_castAdd]
    rfl
  · have outside : ∀ j,rawOld j≠i:=by simpa only [not_exists] using inside
    have n36 : i≠36:=Ne.symm (outside 36)
    have n115 : i≠115:=Ne.symm (outside 115)
    rw [afterTapes,install_other rawOld A _ i outside,
      Function.update_of_ne n115,Function.update_of_ne n36]

theorem after_heads_eq (H : Fin 128→ℕ) (pos : ℕ) :
    afterHeads H pos=Function.update (Function.update (Function.update H 113 pos) 36 0) 115 0:=by
  funext i
  by_cases inside : ∃ j,rawOld j=i
  · obtain ⟨j,rfl⟩:=inside
    rw [after_heads_old]
    simp only [BankExecution.changedHeads,Function.update_apply,Function.comp_apply,
      rawOld,Fin.ext_iff,Fin.val_castAdd]
    rfl
  · have outside : ∀ j,rawOld j≠i:=by simpa only [not_exists] using inside
    have n113 : i≠113:=Ne.symm (outside 113)
    have n36 : i≠36:=Ne.symm (outside 36)
    have n115 : i≠115:=Ne.symm (outside 115)
    rw [afterHeads,dockH_other rawOld H _ i outside,
      Function.update_of_ne n115,Function.update_of_ne n36,Function.update_of_ne n113]

end NearCubicWires.ExtIncidence.BankCount
