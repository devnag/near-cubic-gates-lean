import Proof.Gates.Expand.PolyTabCls4

set_option autoImplicit false

namespace NearCubicGates.Close.Expand

open PolyTab

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.CounterMachine

noncomputable def PolyTab (a : WilliamsAlgorithm) (prog : WMX (NSx (te Expand.expansionMachine) (Qa a)) NRk)
    (hT : TailSpec Expand.expansionMachine a prog) (hc : TabCls (tailCost Expand.expansionMachine a)) : TabMachine :=
  PolyTabOf Expand.expansionMachine a prog hT (headCost_cls Expand.expansionMachine) hc

theorem PolyTab_order (a : WilliamsAlgorithm) (prog : WMX (NSx (te Expand.expansionMachine) (Qa a)) NRk)
    (hT : TailSpec Expand.expansionMachine a prog) (hc : TabCls (tailCost Expand.expansionMachine a)) (R : TabReq) :
    (PolyTab a prog hT hc).order R = printerOrder R.s := rfl

/-- **PolyTabReady** (`CounterMachine.Supply.PolyTabReady`, unfolded). -/
theorem polyTabReady_of (prog : ∀ a : WilliamsAlgorithm, WMX (NSx (te Expand.expansionMachine) (Qa a)) NRk)
    (hT : ∀ a, TailSpec Expand.expansionMachine a (prog a)) (hc : ∀ a, TabCls (tailCost Expand.expansionMachine a)) :
    ∀ _a : WilliamsAlgorithm, ∃ PolyTab : TabMachine, ∀ R : TabReq, PolyTab.order R = printerOrder R.s :=
  fun a => ⟨PolyTab a (prog a) (hT a) (hc a), PolyTab_order a (prog a) (hT a) (hc a)⟩

end NearCubicGates.Close.Expand
