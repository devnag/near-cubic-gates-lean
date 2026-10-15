import Proof.MachineModel.OrdinaryMatrixBatchGateCopy
import Proof.MachineModel.OrdinaryMatrixBatchWidthSetup

namespace NearCubicWires.RepairOrdinary.MatrixBatchGateLayout
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C)
open MatrixScoreReusableRanks (D)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The width setup's 26 local tapes. -/
def widthSlots : Fin 26 → Fin 166 := ![1,132,133,134,135,136,137,138,139,140,141,92,142,143,144,145,146,148,149,150,151,152,153,154,155,156]
theorem width_injective : Function.Injective widthSlots := by decide
/-- The native loop's 49 tapes. -/
def slots : Fin 49 → Fin 166 := ![157,151,158,159,160,161,49,163,165,92,95,99,144,145,149,77,107,146,61,65,153,150,147,32,154,106,152,39,155,156,23,90,91,93,28,94,96,97,98,100,101,162,142,103,130,164,1,102,89]
theorem slots_injective : Function.Injective slots := by decide
def heads (r : Request) : Fin 49 → ℕ := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,(header r).length,0,1]

theorem native_heads (r : Request) (s : MatrixBatchGateStore.Store r) :
    (MatrixBatchGateNativeLoop.cfg r 0 (word r) (header r).length [] s).heads=heads r := by
  rw [MatrixBatchGateNativeLoop.cfg_heads]
  funext i
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.MatrixBatchGateLayout
