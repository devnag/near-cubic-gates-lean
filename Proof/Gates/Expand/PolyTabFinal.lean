import Proof.Gates.Expand.PolyTabReady
import Proof.Gates.Expand.PolyTabTail3

set_option autoImplicit false

namespace NearCubicGates.Close.Expand

open PolyTab
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine

theorem tailSpec_expansionMachine (a : WilliamsAlgorithm) : TailSpec Expand.expansionMachine a (tailP (te Expand.expansionMachine) a) :=
  fun r cap σ h => tail_spec Expand.expansionMachine a r cap σ h

/-- **PolyTabReady modulo the tail's cost class.** -/
theorem polyTabReady_of_tailCls (hc : ∀ a, TabCls (tailCost Expand.expansionMachine a)) :
    ∀ _a : WilliamsAlgorithm, ∃ PolyTab : TabMachine, ∀ R : TabReq, PolyTab.order R = printerOrder R.s :=
  polyTabReady_of (fun a => tailP (te Expand.expansionMachine) a) tailSpec_expansionMachine hc

end NearCubicGates.Close.Expand
