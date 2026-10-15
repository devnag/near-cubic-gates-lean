import Proof.MachineModel.OrdinaryMatrixScoreRawPrepare

/-! The literal cold raw gate-word producer: parsed headers and executed
bank/initial fields feed the entire score enumeration and native sort tape.
An actual aggregate rewind returns all heads for the next enclosing call. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRawGate
open LocalBitMultitape SignedSortKey MatrixScoreBatch MatrixScoreRawPrepare
open MatrixScoreLeftLoop (C)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coreBudget (r : Request) (gate : Fin r.Gates) := MatrixScoreRawPrepare.budget r gate+1+MatrixScoreGateStream.budget r
def budget (r : Request) (gate : Fin r.Gates) := 2*coreBudget r gate+2

end NearCubicWires.RepairOrdinary.MatrixScoreRawGate
