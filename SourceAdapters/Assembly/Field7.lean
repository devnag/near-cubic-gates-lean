import SourceAdapters.Refuter.RLoadField
import SourceAdapters.Compile.CNFMainE

/-!
# Input 7: the framed full-range refuter

`CLW20_Theorem1_13`, proved outright: the hierarchy and its recurrence (`Refuter.hierarchy_exists`), the refuter program
with its loader and rounds (`Refuter.RM`), and the bounded computation-to-3-CNF compiler
(`Compile.computationToCNF`). No published statement is assumed for this input.
-/

namespace NearCubicGates.Adapters.Assembly

theorem field7 : NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13 :=
  NearCubicGates.Adapters.Refuter.RM.clw20_theorem1_13_of_computationToCNF
    NearCubicGates.Adapters.Compile.computationToCNF

end NearCubicGates.Adapters.Assembly
