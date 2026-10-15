import Proof.CaseAnalysis.RowsTouchingMaskShiftRun
import Proof.CaseAnalysis.RowsTouchingMaskShiftMeaning

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.MaskShift
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem typed_run {q : ℕ} (picked : Bool) (selected : Finset (Fin q)) (j C : ℕ)
    (hj:j<q) (hC:4*q+3≤C):
    Step machine (8*q+8) readyHeads (readyData picked (cells selected j) false q C) readyHeads
      (readyData picked (cells (if picked then insert ⟨j,hj⟩ selected else selected) (j+1))
        (decide (q=j+1)) q C):=by
  have actual:=shift_run picked (cells selected j) C (by simpa only [cells_length] using hC)
  simpa only [cells_length,transformed_cells picked selected j hj,carry_cells selected j q (Nat.le_refl q)] using actual

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.MaskShift
