import Proof.Gates.CellsGatherQ.Query6
import Proof.Gates.CellsGatherK.Final

set_option autoImplicit false

namespace NearCubicGates.Close.Cells.QueryPass

/-- **The query-record pass.** -/
def qP : St VV MM := qPOf QueryKey.keyP

/-- **Its cost.** -/
def qCost : Ctx → NearCubicGates.Close.Interfaces.Call → NearCubicGates.Close.Counter.Params → ℕ → ℕ :=
  qCostOf QueryKey.keyCost

theorem qP_spec : RecordEmission.QryGoal qP qCost := qPOf_spec QueryKey.keyP QueryKey.keyCost QueryKey.keyP_spec

theorem qP_class : RecordEmission.QryClass qCost := qCostOf_class QueryKey.keyCost QueryKey.keyP_class

end NearCubicGates.Close.Cells.QueryPass
