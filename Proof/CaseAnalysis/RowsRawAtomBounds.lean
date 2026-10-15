import Proof.CaseAnalysis.RowsRawAtomNative
import Proof.CaseAnalysis.RowsPreparationInput

/-! The actual child-count reader and absolute-index emitter use only a
quadratic in the already produced total child count. Their cost is added
before the row-table scan; no witness padding length enters this bound. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomBounds
open RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_bound (offset n B : ℕ) (hB : offset+n≤B) :
    CloseoutRowsRawAtomNative.budget offset n+1≤64*(B+2)^2 := by
  have hn:n≤B:=by omega
  have hw:natBitLength n≤B+1:=
    (Nat.add_le_add_right (Nat.log_le_self 2 n) 1).trans (by omega)
  have first:=Nat.mul_le_mul hn (show 8*natBitLength n+10≤8*(B+1)+10 by omega)
  have second:=Nat.mul_le_mul hn (show 4*(offset+n)+31≤4*B+31 by omega)
  unfold CloseoutRowsRawAtomNative.budget MatrixDimensionPrepare.budget CloseoutRowsRawAtomLoop.budget
  nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomBounds
