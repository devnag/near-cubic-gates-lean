import Proof.Gates.CellsGather.Final
import Proof.Gates.CellsGatherE.Emit7

set_option autoImplicit false

namespace NearCubicGates.Close.Cells.GatherPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

def gatherPQ (qP : St VV MM) : St VV MM := gatherPOf (RecordEmission.emitP qP)

noncomputable def gatherCostQ (qCost : Ctx → Call → Params → ℕ → ℕ) : Ctx → Call → Params → ℕ → ℕ :=
  gatherCostOf (RecordEmission.emitCost qCost)

theorem gatherPQ_spec (qP : St VV MM) (qCost : Ctx → Call → Params → ℕ → ℕ) (hq : RecordEmission.QryGoal qP qCost) :
    GatherGoal (gatherPQ qP) (gatherCostQ qCost) :=
  gatherPOf_spec _ _ (RecordEmission.emitP_spec_of qP qCost hq)

theorem gatherCostQ_class (qCost : Ctx → Call → Params → ℕ → ℕ) (hq : RecordEmission.QryClass qCost) :
    GatherClass (gatherCostQ qCost) :=
  gatherCostOf_class _ (RecordEmission.emitCost_class_of qCost hq)

end NearCubicGates.Close.Cells.GatherPhase
