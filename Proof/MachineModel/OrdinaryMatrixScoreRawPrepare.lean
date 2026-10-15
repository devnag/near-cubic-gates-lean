import Proof.MachineModel.OrdinaryMatrixScoreColdSetup
import Proof.MachineModel.OrdinaryMatrixScoreBankReady

/-! Cold raw gate input to the literal score-pass entry. All words, the
local cut bank and both driver positions are physically produced here. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRawPrepare
open LocalBitMultitape RecoveryExecution SignedSortKey RepairRepresentation MatrixScoreBatch
open MatrixScoreLeftLoop (C State)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (r : Request) (gate : Fin r.Gates) := (MatrixScoreColdSetup.budget r.d r.p (cutWord r.p (r.cuts.get gate))+1+1)+1+
  MatrixScoreBankReady.budget r.d r.p

end NearCubicWires.RepairOrdinary.MatrixScoreRawPrepare
