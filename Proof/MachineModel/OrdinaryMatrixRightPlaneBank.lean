import Proof.MachineModel.OrdinaryMatrixBatchRightPadDriver

/-! The exact reusable tape projection for the right-plane consumer.
Fourteen scratch tapes and both native zero words already exist at the
executed right-gate endpoint. No new allocation premise is introduced. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightPlaneBank
open LocalBitMultitape MatrixScoreBatch MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 24 → Fin 362 :=
  ![309,311,313,317,318,319,320,344,322,324,358,325,359,326,327,332,333,345,346,360,39,285,356,361]
theorem slots_injective : Function.Injective slots := by decide
def native : Fin 16 → Fin 38 := ![3,5,7,11,12,13,14,16,18,19,20,21,31,32,35,36]
def fields : Fin 16 → Fin 24 := ![0,1,2,3,4,5,6,8,9,11,13,14,15,16,17,18]

theorem slots_native (j : Fin 16) : slots (fields j)=
    ((MatrixBatchRightPassFields.slots ((native j).castAdd 1)).castAdd 10).castAdd 4 := by
  fin_cases j <;> rfl

theorem reused_tapes (r : Request) (unused : Fin 3 → List Bool) (store : MatrixBucketGateLoop.Store r)
    (j : Fin 16) : (MatrixRightGateFinish.final r unused store).tapes (native j)=
      MatrixRightPlaneNative.input r (fields j) := by
  have hb := MatrixBucketCallBounds.workspace_fit r
  have h2 : 2*MatrixBatchBucketEndpoints.H r+1≤MatrixScoreReusableRanks.D r := by omega
  have h6 : 6*MatrixBatchBucketEndpoints.H r+6≤MatrixScoreReusableRanks.D r := by omega
  have h4 : 4*MatrixBatchBucketEndpoints.H r+1≤MatrixScoreReusableRanks.D r := by omega
  have h8 : 8*MatrixBatchBucketEndpoints.H r+3≤MatrixScoreReusableRanks.D r := by omega
  have h4' : 4*MatrixBatchBucketEndpoints.H r+3≤MatrixScoreReusableRanks.D r := by omega
  have h1 : 1≤MatrixScoreReusableRanks.D r := by omega
  fin_cases j
  all_goals simp [native,fields,MatrixRightPlaneNative.input,MatrixRightPlaneLayout.input,
    MatrixRightGateFinish.final,MatrixRightGateFinish.before,MatrixRightGateNativeLoop.cfg_tapes,
    MatrixRightGateLayout.data,MatrixRightGateLoop.state,MatrixBucketGatePrepare.data,
    MatrixBucketGatePrepare.native_core,MatrixBucketGatePrepare.core,MatrixBucketGatePrepare.extra,
    Fin.addCases,scalar,zeros,ZeroPadding.pad,Nat.add_sub_of_le h2,Nat.add_sub_of_le h6,
    Nat.add_sub_of_le h4,Nat.add_sub_of_le h8,Nat.add_sub_of_le h4',Nat.add_sub_of_le hb]
  change false::List.replicate (MatrixScoreReusableRanks.D r-1) false=List.replicate (MatrixScoreReusableRanks.D r) false
  rw [← List.replicate_succ]
  congr 1
  omega

theorem reused_heads (r : Request) (unused : Fin 3 → List Bool) (store : MatrixBucketGateLoop.Store r)
    (j : Fin 16) : (if native j=8 then 0 else (MatrixRightGateFinish.final r unused store).heads (native j))=0 := by
  fin_cases j <;> rfl

end NearCubicWires.RepairOrdinary.MatrixRightPlaneBank
