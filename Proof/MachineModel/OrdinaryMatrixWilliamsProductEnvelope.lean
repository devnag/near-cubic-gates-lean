import Proof.MachineModel.OrdinaryMatrixPreparationBounds

/-! The complete explicit preprocessing/source call has a uniform quadratic
assignment-table envelope. This is the physical clear capacity supplier for
repeating the cold call, with the source logarithmic exponent retained. -/
namespace NearCubicWires.RepairOrdinary.MatrixWilliamsProductBounds
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficient (a : WilliamsAlgorithm) : ℕ := 1000000000000+2*WilliamsCall.coefficient a*3^(a.logExponent+1)+3
def exponent (a : WilliamsAlgorithm) : ℕ := a.logExponent+3

end NearCubicWires.RepairOrdinary.MatrixWilliamsProductBounds
