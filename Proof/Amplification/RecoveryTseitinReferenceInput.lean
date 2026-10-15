import Proof.Amplification.RecoveryTseitinReferenceBanks

/-! Route the actually computed unary offsets into the disjoint cold banks.
Only arity, position and the two native operands occur in the cold input. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def counts (arity index left right : Nat) : Fin 4→Nat := ![arity+index,left,arity+left,arity+right]
def scalarSlot (i : Fin 10) : Fin 1062 := i.castAdd 1052
theorem scalar_injective : Function.Injective scalarSlot := by
  intro i j h
  have hv:=congrArg Fin.val h
  exact Fin.ext hv
def coldInput (arity index left right : Nat) (i : Fin 1062) : List Bool :=
  if h : i.val<10 then input arity index left right ⟨i.val,h⟩ else []
noncomputable def afterSums (arity index left right : Nat) :=
  install scalarSlot (coldInput arity index left right) (output arity index left right)
noncomputable def scalarMachine := RecoveryFocus.machine scalarSlot sumsMachine

theorem scalar_run (arity index left right : Nat) :
    ClockJoin.ReadyRun scalarMachine (budget arity index left right)
      (coldInput arity index left right) (afterSums arity index left right) := by
  apply (sums_run arity index left right).focus scalarSlot scalar_injective
  intro j
  simp only [coldInput,scalarSlot,Fin.val_castAdd,dif_pos j.isLt]

theorem bank_large (k : Fin 4) (j : Fin 262) (hj : j≠242) : 10≤(bankSlots k j).val := by
  dsimp only [bankSlots,referenceSlot]
  split_ifs <;> simp_all only <;> omega

theorem after_sums_banks (arity index left right : Nat) (k : Fin 4) (j : Fin 262) :
    afterSums arity index left right (bankSlots k j)=
      RecoveryTseitinTautology.Cold.driversInput (counts arity index left right k) j := by
  by_cases hj : j=242
  · subst j
    have hf:=output_fields arity index left right
    have h4:=install_slot scalarSlot scalar_injective (coldInput arity index left right)
      (output arity index left right) 4
    have h2:=install_slot scalarSlot scalar_injective (coldInput arity index left right)
      (output arity index left right) 2
    have h6:=install_slot scalarSlot scalar_injective (coldInput arity index left right)
      (output arity index left right) 6
    have h8:=install_slot scalarSlot scalar_injective (coldInput arity index left right)
      (output arity index left right) 8
    fin_cases k
    · exact h4.trans hf.1
    · exact h2.trans hf.2.1
    · exact h6.trans hf.2.2.1
    · exact h8.trans hf.2.2.2
  · have hl:=bank_large k j hj
    have hn : ∀ a,scalarSlot a≠bankSlots k j := by
      intro a he
      have hv:=congrArg Fin.val he
      have ha:=a.isLt
      dsimp only [scalarSlot,Fin.val_castAdd] at hv
      omega
    rw [afterSums,install_other scalarSlot _ _ _ hn]
    simp only [coldInput,dif_neg (by omega : ¬(bankSlots k j).val<10),
      RecoveryTseitinTautology.Cold.driversInput,if_neg hj]

end NearCubicWires.RepairSource.RecoveryTseitinReferences
