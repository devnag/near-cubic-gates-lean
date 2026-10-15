import Proof.Assembly.Initializer
import Proof.Assembly.Terminal
import Proof.Assembly.ActualPrefixRecipe

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

namespace ActualNativeCode
open NearCubicWires NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal

/-- This parameter is concrete source-global native code, chosen before runtime
input. Its actual execution and full costs remain duties of the actual-call
recipe. No universal Admissible correctness is required merely to compose code. -/
abbrev NativeCode := (sources : EightSources) → (gamma : Real) →
 (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) →
 FamilyInitGenerator.PrefixCode

/-- Compose the actual retained native code with the already supplied fixed
terminal branch and physical initializer. The same chosen result data survives
for every dependent actual-call obligation. -/
noncomputable def assemble
 (g : FamilyInitGenerator.PrefixCode) :
 NativeFamilyGenerator.Data :=
 let terminal : NativeTerminalDispatch.Branch g :=
   { states := 35
     machine := TerminalPrefixDriver.machine g
     result := TerminalPrefixDriver.result g }
 let combined := NativeTerminalDispatch.combined g terminal
 let initializer : FamilyInitGenerator.Initializer combined.printer :=
   { states := 39
     machine := PaidDriverBank.machine combined.printer
     run := PaidDriverBank.run combined.printer }
 FamilyInitGenerator.assemble combined initializer

noncomputable def global (native : NativeCode) :
 ActualPrefixRecipes.GlobalData :=
 fun sources gamma hg hh p => assemble (native sources gamma hg hh p)

end ActualNativeCode
