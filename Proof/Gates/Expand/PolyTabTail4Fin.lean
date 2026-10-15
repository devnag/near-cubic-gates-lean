import Proof.Gates.Expand.PolyTabTail4
import Proof.Gates.Expand.PolyTabTail1
import Proof.Gates.Expand.PolyTabFinal
import Proof.Gates.CounterMachine.Supply

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine

theorem tc_const (c : ℕ) : TabCls (fun _ => c) :=
  ⟨c, 0, fun r => by have : 1 ≤ 2 ^ r.s := Nat.one_le_two_pow; simp; nlinarith⟩

/-- **The tail's cost class**, from the cut part's. -/
theorem tailCost_cls_of (E : ExpandMachine) (hcut : TabCls (fun r => cutCost E r)) (a : WilliamsAlgorithm) :
    TabCls (tailCost E a) :=
  tc_mono (tc_add (tc_add hcut (tc_const 1)) (backCls E a)) (fun r => by unfold tailCost cutCost; omega)

/-- **`PolyTabReady`**, from the cut part's class at `expansionMachine`. -/
theorem polyTabReady_of_cut (hcut : TabCls (fun r => cutCost Expand.expansionMachine r)) : CounterMachine.Supply.PolyTabReady :=
  Expand.polyTabReady_of_tailCls (tailCost_cls_of Expand.expansionMachine hcut)

end NearCubicGates.Close.Expand.PolyTab
