import SourceAdapters.Refuter.RLoad
import SourceAdapters.Refuter.HierarchyExists

/-!
# Input 7 from the X5(b) join (the refuter half + the hierarchy half)

Consumer: the `NineInputs` field `refuter : CLW20_Theorem1_13` (`Statement.lean` l.1583, body l.1059–1081).
Paper anchor: `imp:ae-refuter`, `lem:multitape-refuter`, `cor:framed-refuter`.

The refuter half `RefuterRealization T` for every admissible clock is `refuterRealization_of_computationToCNF`
(the round machine `step_spec` and the loader `initOK`), from the join `ComputationToCNF` (X5(b),
`Joins/ComputationToCNF.lean`); the hierarchy half and the assembly are `clw20_theorem1_13_of_realization`
(`HierarchyExists.lean`).
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicGates.Adapters.Compile (ComputationToCNF)

set_option autoImplicit false

/-- **Input 7 (`CLW20_Theorem1_13`, every time-constructible `T` with `n ≤ T(n) ≤ 2^{poly(n)}`) from the X5(b)
join.** -/
theorem clw20_theorem1_13_of_computationToCNF (h : ComputationToCNF) :
    NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13 :=
  clw20_theorem1_13_of_realization (refuterRealization_of_computationToCNF h)

end NearCubicGates.Adapters.Refuter.RM
