import Proof.Amplification.RecoveryQueryOperandSources

/-! Each actual arithmetic call receives the exact two fields already
produced by preparation or by its earlier fixed node. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem left_ready (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (outs : Fin 9→Fin 39→List Bool) (k : Fin 9)
    (hc : 1 ≤ cap)
    (hf : ∀ j : Fin 9,j.val<k.val → outs j 26=ZeroPadding.pad cap (frame (values flat payload committed count j).bits)) :
    stage cap flat payload committed count original outs k.val (leftPort k)=
      ZeroPadding.pad cap (frame (lefts flat payload committed count k).bits) := by
  fin_cases k
  · change stage cap flat payload committed count original outs 0 (bank 0 2)=_
    rw [stage_bank _ _ _ _ _ _ _ _ _ _ (by decide),prepared_bank]
    rfl
  · exact (stage_result cap flat payload committed count original outs 0).trans (hf 0 (by decide))
  · change stage cap flat payload committed count original outs 2 (bank 2 2)=ZeroPadding.pad cap (frame (0 : Nat).bits)
    rw [stage_bank _ _ _ _ _ _ _ _ _ _ (by decide),prepared_bank]
    exact (padded_zero cap hc).symm
  · exact (stage_result cap flat payload committed count original outs 2).trans (hf 2 (by decide))
  · exact (stage_result cap flat payload committed count original outs 3).trans (hf 3 (by decide))
  · change stage cap flat payload committed count original outs 5 (bank 5 2)=_
    rw [stage_bank _ _ _ _ _ _ _ _ _ _ (by decide),prepared_bank]
    rfl
  · exact (stage_result cap flat payload committed count original outs 5).trans (hf 5 (by decide))
  · exact (stage_result cap flat payload committed count original outs 6).trans (hf 6 (by decide))
  · change stage cap flat payload committed count original outs 8 (bank 8 2)=ZeroPadding.pad cap (frame (0 : Nat).bits)
    rw [stage_bank _ _ _ _ _ _ _ _ _ _ (by decide),prepared_bank]
    exact (padded_zero cap hc).symm

theorem right_ready (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (outs : Fin 9→Fin 39→List Bool) (k : Fin 9)
    (hc : 1 ≤ cap)
    (hf : ∀ j : Fin 9,j.val<k.val → outs j 26=ZeroPadding.pad cap (frame (values flat payload committed count j).bits)) :
    stage cap flat payload committed count original outs k.val (rightPort k)=
      ZeroPadding.pad cap (frame (rights flat payload committed count k).bits) := by
  fin_cases k
  · change stage cap flat payload committed count original outs 0 (bank 0 3)=_
    rw [stage_bank _ _ _ _ _ _ _ _ _ _ (by decide),prepared_bank]
    rfl
  · change stage cap flat payload committed count original outs 1 (bank 1 3)=ZeroPadding.pad cap (frame (0 : Nat).bits)
    rw [stage_bank _ _ _ _ _ _ _ _ _ _ (by decide),prepared_bank]
    exact (padded_zero cap hc).symm
  · change stage cap flat payload committed count original outs 2 (bank 2 3)=_
    rw [stage_bank _ _ _ _ _ _ _ _ _ _ (by decide),prepared_bank]
    rfl
  · exact (saved_one cap flat payload committed count original outs).trans (hf 1 (by decide))
  · change stage cap flat payload committed count original outs 4 (bank 4 3)=ZeroPadding.pad cap (frame (0 : Nat).bits)
    rw [stage_bank _ _ _ _ _ _ _ _ _ _ (by decide),prepared_bank]
    exact (padded_zero cap hc).symm
  · change stage cap flat payload committed count original outs 5 (bank 5 3)=_
    rw [stage_bank _ _ _ _ _ _ _ _ _ _ (by decide),prepared_bank]
    rfl
  · change stage cap flat payload committed count original outs 6 (bank 6 3)=ZeroPadding.pad cap (frame (0 : Nat).bits)
    rw [stage_bank _ _ _ _ _ _ _ _ _ _ (by decide),prepared_bank]
    exact (padded_zero cap hc).symm
  · exact (saved_four cap flat payload committed count original outs).trans (hf 4 (by decide))
  · exact (stage_result cap flat payload committed count original outs 7).trans (hf 7 (by decide))

theorem cell_input (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (outs : Fin 9→Fin 39→List Bool) (k : Fin 9)
    (hc : 1 ≤ cap)
    (hf : ∀ j : Fin 9,j.val<k.val → outs j 26=ZeroPadding.pad cap (frame (values flat payload committed count j).bits))
    (i : Fin 39) :
    stage cap flat payload committed count original outs k.val (cellSlots k i)=
      RecoveryQueryCell.paddedInput cap (lefts flat payload committed count k)
        (rights flat payload committed count k) i := by
  by_cases h2 : i.val=2
  · have he : i=2 := Fin.ext h2
    subst i
    exact left_ready cap flat payload committed count original outs k hc hf
  by_cases h3 : i.val=3
  · have he : i=3 := Fin.ext h3
    subst i
    exact right_ready cap flat payload committed count original outs k hc hf
  rw [cellSlots,if_neg h2,if_neg h3,stage_bank _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _),prepared_bank]
  simp [RecoveryQueryCell.paddedInput,RecoveryQueryCell.input,RecoveryQueryPairSuccessor.input,h2,h3,ZeroPadding.pad]

end NearCubicWires.RepairOrdinary.RecoveryQueryKernel
