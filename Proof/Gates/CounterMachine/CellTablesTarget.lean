import Proof.Gates.CounterMachine.TabCallSpec
import Proof.Gates.CounterMachine.CellTablesSpec

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicGates.Close.Interfaces.Formats

/-- **STATEMENT CellTables (from RK).** -/
def CellTablesTarget (B1 B2 cT : ℕ) (PolyTab : TabMachine) : Type := TabCallMachine B1 B2 cT PolyTab → TablesMachine B1 B2 cT

end NearCubicGates.Close.CounterMachine
