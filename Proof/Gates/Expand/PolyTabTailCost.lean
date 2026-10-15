import Proof.Gates.Expand.PolyTabTail

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine NearCubicGates.Close.Interfaces.Formats

/-- A cost bound of the tail's register program (`d` doublings twice, unary register arithmetic). -/
def bregsCost (d p : ℕ) : ℕ := 100 * (d + p + 10) + (2 * d + 1) * (25 * 2 ^ (2 * d) + 20)

/-- **The tail's cost.** -/
noncomputable def tailCost (E : ExpandMachine) (a : WilliamsAlgorithm) (r : TabReq) : ℕ :=
  cutMCost (Wk E r) r.s (hsK E r).length (tsK E r).length (xsK E r).length (CMk E r)
      (EquationRowCuts.stream (Wdk E r) (tabT E r).exactCuts).length ((r.s + 1) / 2) (Wdk E r)
      (tabT E r).exactCuts.length + 1 +
    (bregsCost ((r.s + 1) / 2) (Wdk E r) + 1 + backCost a (inp E r))

/-- The request size of `TabMachine.cls`. -/
def tabSz (r : TabReq) : ℕ :=
  r.n + r.G + r.B + r.V + (formulaWord ⟨r.V, r.F⟩).length + r.F.size + r.F.weight + 1

end NearCubicGates.Close.Expand.PolyTab
