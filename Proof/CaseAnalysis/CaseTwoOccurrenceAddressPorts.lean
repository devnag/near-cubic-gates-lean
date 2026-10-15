import Proof.CaseAnalysis.CaseTwoOccurrenceAddressLayout

/-! Disjoint literal ports used by the composed occurrence crop and field
read. Every retained scalar is one already produced by the fixed schedule. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem crop_high (D : ℕ) (j : Fin 8) : 53 ≤ (cropSlots D j).val:=by
  have h8:=scalar_high D 8 (by decide)
  have h2:=scalar_high D 2 (by decide)
  dsimp only [cropSlots,base]
  split_ifs <;>(try simp only [Fin.val_castAdd]) <;>omega
theorem field_high (D : ℕ) (j : Fin 27) : 53 ≤ (fieldSlots D j).val:=by
  have h18:=scalar_high D 18 (by decide)
  have h14:=scalar_high D 14 (by decide)
  have h6:=crop_high D 6
  dsimp only [fieldSlots,base]
  split_ifs <;>(try simp only [Fin.val_castAdd]) <;>omega
theorem crop_outside (D : ℕ) (i : Fin (tapes D))
    (hi : (i.val<58 ∧ i.val≠57) ∨ 58+Widths.tapes D+8 ≤ i.val) :
    ∀ j,cropSlots D j≠i:=by
  intro j he
  have h:=congrArg Fin.val he
  have hj:=j.isLt
  have l8:=scalar_high D 8 (by decide)
  have l2:=scalar_high D 2 (by decide)
  have u8:=width_upper D (Widths.scalarSlots D 8)
  have u2:=width_upper D (Widths.scalarSlots D 2)
  change (scalarPort D 8).val<58+Widths.tapes D at u8
  change (scalarPort D 2).val<58+Widths.tapes D at u2
  dsimp only [cropSlots,base] at h
  split_ifs at h <;>(try simp only [Fin.val_castAdd] at h) <;>omega
theorem crop_scalar_outside (D : ℕ) (i : Fin 22) (hi : 2 ≤ i.val) (h2 : i≠2) (h8 : i≠8) :
    ∀ j,cropSlots D j≠scalarPort D i:=by
  intro j he
  have h:=congrArg Fin.val he
  have lo:=scalar_high D i hi
  have up:=width_upper D (Widths.scalarSlots D i)
  have n2:=scalar_ne D i 2 h2
  have n8:=scalar_ne D i 8 h8
  change (scalarPort D i).val<58+Widths.tapes D at up
  dsimp only [cropSlots,base] at h
  split_ifs at h <;>(try simp only [Fin.val_castAdd] at h) <;>omega
theorem field_outside (D : ℕ) (i : Fin (tapes D)) (hi : i.val<58 ∧ i.val≠53) :
    ∀ j,fieldSlots D j≠i:=by
  intro j he
  have h:=congrArg Fin.val he
  have l18:=scalar_high D 18 (by decide)
  have l14:=scalar_high D 14 (by decide)
  have h6 : (cropSlots D 6).val=58+Widths.tapes D+6:=rfl
  dsimp only [fieldSlots,base] at h
  split_ifs at h <;>(try simp only [Fin.val_castAdd] at h) <;>omega

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceAddress
