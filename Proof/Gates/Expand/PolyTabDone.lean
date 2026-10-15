import Proof.Gates.Expand.PolyTabTail4Fin
import Proof.Gates.Expand.PolyTabCutCls

set_option autoImplicit false

namespace NearCubicGates.Close.Expand

/-- **The tail's cost class** (`tailCost_cls`). -/
theorem tailCost_cls (a : NearCubicWires.RepairRepresentation.WilliamsAlgorithm) :
    PolyTab.TabCls (PolyTab.tailCost Expand.expansionMachine a) :=
  PolyTab.tailCost_cls_of Expand.expansionMachine (PolyTab.cutCls Expand.expansionMachine) a

/-- **PolyTabReady.** -/
theorem polyTabReady : CounterMachine.Supply.PolyTabReady := PolyTab.polyTabReady_of_cut (PolyTab.cutCls Expand.expansionMachine)

end NearCubicGates.Close.Expand
