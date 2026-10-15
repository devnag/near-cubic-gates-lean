import Proof.MachineModel.OrdinaryMatrixRightGatePass
import Proof.MachineModel.OrdinaryMatrixBatchRightBank

/-! Literal native-field agreement between the completed left bank and
right-pass entry. The only changed old data fields are the output and inner
coordinate; their reset/allocation has an independent actual receipt. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightPassEntry
open LocalBitMultitape MatrixScoreBatch
open MatrixBucketGateLoop (Store)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (j : Fin 36) : Fin 38 := if j.val<35 then ⟨j.val,by omega⟩ else 37

theorem old_tapes (r : Request) (unused : Fin 3 → List Bool) (s : Store r)
    (j : Fin 36) (h8 : j≠8) (h17 : j≠17) :
    (MatrixBucketGateFinish.final r unused s).tapes j=
      (MatrixRightGateBootstrap.input MatrixRightGateBootstrap.machine.start r unused s).tapes (native j) := by
  fin_cases j
  all_goals first
    | exact (h8 rfl).elim
    | exact (h17 rfl).elim
    | simp [native,MatrixBucketGateFinish.final,MatrixBucketGateFinish.before,
        MatrixBucketGateNativeLoop.cfg_tapes,MatrixRightGateBootstrap.input,MatrixRightGateBootstrap.target,
        MatrixRightGateNativeLoop.cfg_tapes,MatrixRightGateLayout.data,MatrixRightGateLoop.state,
        MatrixBucketGatePrepare.data,MatrixBucketGatePrepare.native_core,MatrixBucketGatePrepare.core,
        MatrixBucketGatePrepare.extra,Fin.addCases]

theorem old_heads (r : Request) (unused other : Fin 3 → List Bool) (s t : Store r)
    (j : Fin 36) (h8 : j≠8) (h34 : j≠34) (h35 : j≠35) :
    (MatrixBucketGateFinish.final r unused s).heads j=
      (MatrixRightGateBootstrap.input MatrixRightGateBootstrap.machine.start r other t).heads (native j) := by
  fin_cases j
  all_goals first
    | exact (h8 rfl).elim
    | exact (h34 rfl).elim
    | exact (h35 rfl).elim
    | rfl

end NearCubicWires.RepairOrdinary.MatrixRightPassEntry
