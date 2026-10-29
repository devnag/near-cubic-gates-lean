import SourceAdapters.Routing.CoordinateMachineSampleProgram
import SourceAdapters.Routing.CoordinateMachineUpdateStep
import SourceAdapters.Routing.CoordinateMachineInput
import SourceAdapters.Routing.CoordinateMachineOutput

/-!
# The complete coordinate-array program

The construction in `lem:generator`: compute each coordinate row using the iterative triangular coefficient construction,
then emit its reduced coefficients in order. Recomputing the annihilator per row uses O(m³) field operations and
only O(m) field words of working storage. Every evaluator uses successive squaring and every coefficient update
uses a counted loop of length at most m+1.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open ShortPCP.Machines.FL

/-- Initialize the annihilator to X and the selected row to zero, then perform all triangular stages. -/
def solveRow : S := .seq (.set 25 (.k 1)) (.seq (.set 26 (.k 0))
  (.loop 24 (.v 22) (.seq sampleProgram updateStep)))

/-- Compute and print all rows, in the exact order required by the coordinate-array encoding. -/
def solveArray : S := .loop 23 (.v 22) (.seq solveRow rowEmit)

/-- Parse the request and print its coordinate array. -/
def program : S := .seq coordParse solveArray

theorem solveRow_wf (d : ℕ) (hd : d ≤ 6) : wfS solveRow d = true := by
  simp [solveRow, wfS, dE, sample_wellFormed (d + 1) (by omega), updateStep_wf (d + 1) (by omega)]
  omega

theorem solveArray_wf (d : ℕ) (hd : d ≤ 5) : wfS solveArray d = true := by
  simp [solveArray, wfS, dE, solveRow_wf (d + 1) (by omega), rowEmit_wf (d + 1) (by omega)]
  omega

theorem program_wf : wfS program 0 = true := by
  simp [program, wfS, coordParse_wf 0 (by decide), solveArray_wf 0 (by decide)]

end NearCubicGates.Adapters.Routing.CoordinateMachine
