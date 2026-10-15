import Proof.Amplification.RecoveryTseitinInputs

/-! Retained outputs used by later fixed query nodes.  No assumption that
an arithmetic call preserves its consumed operands is required. -/
namespace NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryTseitin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stage_result (cap : Nat) (ls : Literals)
    (original : Fin 239→List Bool) (outs : Fin 6→Fin 39→List Bool) (k : Fin 6) :
    stage cap ls original outs (k.val+1) (bank k 26)=outs k 26 := by
  have he : (⟨k.val%6,Nat.mod_lt _ (by decide)⟩ : Fin 6)=k :=
    Fin.ext (Nat.mod_eq_of_lt k.isLt)
  rw [stage,he]
  exact install_slot _ (cell_injective k) _ _ 26

theorem saved_0 (cap : Nat) (ls : Literals)
    (original : Fin 239→List Bool) (outs : Fin 6→Fin 39→List Bool) :
    stage cap ls original outs 5 (bank 0 26)=outs 0 26 := by
  change install (cellSlots 4) (stage cap ls original outs 4) (outs 4) (bank 0 26)=_
  rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
  change install (cellSlots 3) (stage cap ls original outs 3) (outs 3) (bank 0 26)=_
  rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
  change install (cellSlots 2) (stage cap ls original outs 2) (outs 2) (bank 0 26)=_
  rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
  change install (cellSlots 1) (stage cap ls original outs 1) (outs 1) (bank 0 26)=_
  rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
  exact stage_result cap ls original outs 0

theorem saved_1 (cap : Nat) (ls : Literals)
    (original : Fin 239→List Bool) (outs : Fin 6→Fin 39→List Bool) :
    stage cap ls original outs 4 (bank 1 26)=outs 1 26 := by
  change install (cellSlots 3) (stage cap ls original outs 3) (outs 3) (bank 1 26)=_
  rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
  change install (cellSlots 2) (stage cap ls original outs 2) (outs 2) (bank 1 26)=_
  rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
  exact stage_result cap ls original outs 1

theorem left_ready (cap : Nat) (ls : Literals)
    (original : Fin 239→List Bool) (outs : Fin 6→Fin 39→List Bool) (k : Fin 6)
    (hc : 1 ≤ cap)
    (hf : ∀ j : Fin 6,j.val<k.val → outs j 26=ZeroPadding.pad cap (frame (values ls j).bits)) :
    stage cap ls original outs k.val (leftPort k)=
      ZeroPadding.pad cap (frame (lefts ls k).bits) := by
  have _ := hc
  fin_cases k
  · change stage cap ls original outs 0 (bank 0 2)=_
    rw [stage_bank _ _ _ _ _ _ _ (by decide),prepared_bank]
    rfl
  · change stage cap ls original outs 1 (bank 1 2)=_
    rw [stage_bank _ _ _ _ _ _ _ (by decide),prepared_bank]
    rfl
  · change stage cap ls original outs 2 (bank 2 2)=_
    rw [stage_bank _ _ _ _ _ _ _ (by decide),prepared_bank]
    rfl
  · exact (stage_result cap ls original outs 2).trans (hf 2 (by decide))
  · exact (saved_1 cap ls original outs).trans (hf 1 (by decide))
  · exact (saved_0 cap ls original outs).trans (hf 0 (by decide))

theorem right_ready (cap : Nat) (ls : Literals)
    (original : Fin 239→List Bool) (outs : Fin 6→Fin 39→List Bool) (k : Fin 6)
    (hc : 1 ≤ cap)
    (hf : ∀ j : Fin 6,j.val<k.val → outs j 26=ZeroPadding.pad cap (frame (values ls j).bits)) :
    stage cap ls original outs k.val (rightPort k)=
      ZeroPadding.pad cap (frame (rights ls k).bits) := by
  fin_cases k
  · change stage cap ls original outs 0 (bank 0 3)=_
    rw [stage_bank _ _ _ _ _ _ _ (by decide),prepared_bank]
    rfl
  · change stage cap ls original outs 1 (bank 1 3)=_
    rw [stage_bank _ _ _ _ _ _ _ (by decide),prepared_bank]
    rfl
  · change stage cap ls original outs 2 (bank 2 3)=_
    rw [stage_bank _ _ _ _ _ _ _ (by decide),prepared_bank]
    rfl
  · change stage cap ls original outs 3 (bank 3 3)=ZeroPadding.pad cap (frame (0 : Nat).bits)
    rw [stage_bank _ _ _ _ _ _ _ (by decide),prepared_bank]
    exact (padded_zero cap hc).symm
  · exact (stage_result cap ls original outs 3).trans (hf 3 (by decide))
  · exact (stage_result cap ls original outs 4).trans (hf 4 (by decide))

theorem cell_input (cap : Nat) (ls : Literals)
    (original : Fin 239→List Bool) (outs : Fin 6→Fin 39→List Bool) (k : Fin 6)
    (hc : 1 ≤ cap)
    (hf : ∀ j : Fin 6,j.val<k.val → outs j 26=ZeroPadding.pad cap (frame (values ls j).bits))
    (i : Fin 39) :
    stage cap ls original outs k.val (cellSlots k i)=
      RecoveryQueryCell.paddedInput cap (lefts ls k)
        (rights ls k) i := by
  by_cases h2 : i.val=2
  · have he : i=2 := Fin.ext h2
    subst i
    exact left_ready cap ls original outs k hc hf
  by_cases h3 : i.val=3
  · have he : i=3 := Fin.ext h3
    subst i
    exact right_ready cap ls original outs k hc hf
  rw [cellSlots,if_neg h2,if_neg h3,stage_bank _ _ _ _ _ _ _ (Nat.le_refl _),prepared_bank]
  simp [RecoveryQueryCell.paddedInput,RecoveryQueryCell.input,RecoveryQueryPairSuccessor.input,h2,h3,ZeroPadding.pad]

end NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
