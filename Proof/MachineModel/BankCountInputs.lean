import Proof.MachineModel.BankCountState

/-! The raw pass physically supplies the converter count and preserves the
empty native template, the same width and every private scratch field. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem counted_inputs (A : Fin 128→List Bool) (C w M : ℕ) (table : List Bool)
    (ha : ∀ j,A (slots j)=CountIndexCopy.input C w 0 j) :
    ∀ j,afterTapes A C table M (slots j)=CountIndexCopy.input C w M j:=by
  intro j
  rw [after_tapes_eq]
  fin_cases j
  · rfl
  all_goals simp only [slots,Function.update_apply]
  all_goals exact ha _

theorem counted_heads (H : Fin 128→ℕ) (pos : ℕ) (hh : ∀ j,H (slots j)=0) :
    ∀ j,afterHeads H pos (slots j)=0:=by
  intro j
  rw [after_heads_eq]
  fin_cases j
  · rfl
  all_goals simp only [slots,Function.update_apply]
  all_goals exact hh _

theorem native_heads (H : Fin 128→ℕ) (pos : ℕ) (out : List Bool)
    (hh : ∀ i,H (old i)=CloseoutRowsBankFields.heads out i) :
    ∀ i,afterHeads H pos (old i)=CloseoutRowsBankFields.heads out i:=by
  intro i
  rw [after_heads_eq]
  have n115 : old i≠115:=by
    intro he
    have hv : i.val=115:=congrArg (fun x : Fin 128=>x.val) he
    have hi:=i.isLt;omega
  have n113 : old i≠113:=by
    intro he
    have hv : i.val=113:=congrArg (fun x : Fin 128=>x.val) he
    have hi:=i.isLt;omega
  rw [Function.update_of_ne n115]
  by_cases h36 : i=36
  · subst i;rfl
  · have n36 : old i≠36:=fun he=>h36 (Fin.ext (congrArg (fun x : Fin 128=>x.val) he))
    rw [Function.update_of_ne n36,Function.update_of_ne n113]
    exact hh i

theorem native_other (A : Fin 128→List Bool) (C M : ℕ) (table : List Bool)
    (i : Fin 113) (hi : i≠36) : afterTapes A C table M (old i)=A (old i):=by
  rw [after_tapes_eq]
  have n115 : old i≠115:=by
    intro he
    have hv : i.val=115:=congrArg (fun x : Fin 128=>x.val) he
    have hi:=i.isLt;omega
  have n36 : old i≠36:=fun he=>hi (Fin.ext (congrArg (fun x : Fin 128=>x.val) he))
  rw [Function.update_of_ne n115,Function.update_of_ne n36]

end NearCubicWires.ExtIncidence.BankCount
