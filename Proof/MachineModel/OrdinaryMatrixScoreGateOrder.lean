import Proof.MachineModel.OrdinaryMatrixScoreBothHalves

/-! The physical left-then-right traversal is exactly the existing joint
stable-sort input order, with every occurrence present once. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreGateOrder
open LocalBitMultitape SignedSortKey MatrixScoreBatch SupplierPrinter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem left_records_eq (r : Request) (gate : Fin r.Gates) (n count : ℕ) :
    MatrixScoreLeftLoop.records r gate n count=
      (List.ofFn (fun i : Fin count => MatrixScoreLeftLoop.record r gate (n+i.val))).flatten := by
  induction count generalizing n with
  | zero => rfl
  | succ count ih =>
    rw [MatrixScoreLeftLoop.records,List.ofFn_succ,List.flatten_cons,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1]

theorem right_records_eq (r : Request) (gate : Fin r.Gates) (n count : ℕ) :
    MatrixScoreRightLoop.records r gate n count=
      (List.ofFn (fun i : Fin count => MatrixScoreRightLoop.record r gate (n+i.val))).flatten := by
  induction count generalizing n with
  | zero => rfl
  | succ count ih =>
    rw [MatrixScoreRightLoop.records,List.ofFn_succ,List.flatten_cons,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1]

theorem records_eq (r : Request) (gate : Fin r.Gates) :
    MatrixScoreBothHalves.records r gate=
      StablePartition.recordsBits (DominanceSort.records r.S r.M (leftScore r) (rightScore r) gate) := by
  unfold MatrixScoreBothHalves.records
  rw [left_records_eq,right_records_eq]
  have hcast (i : Fin r.U) : Fin.castLE (Nat.le_add_right r.U r.U) i=Fin.castAdd r.U i := rfl
  simp only [StablePartition.recordsBits,DominanceSort.records,DominanceSort.copies,List.flatMap_def,
    List.map_append,List.map_ofFn,List.ofFn_add,List.flatten_append,hcast,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd]
  simp only [Function.comp_def,dominanceRecord,stableDominanceCopyScore,stableDominanceCopyId,
    finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd,
    MatrixScoreLeftLoop.record,MatrixScoreRightLoop.record,leftScore,rightScore,Nat.zero_add]

end NearCubicWires.RepairOrdinary.MatrixScoreGateOrder
