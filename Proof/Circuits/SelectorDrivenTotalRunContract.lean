import Proof.Circuits.UniformTargetTotalRun

/-! # Total selector runs at an arbitrary retained frame -/

namespace NearCubicWires.SelectorDrivenTotalRunContract

open NearCubicWires
open NearCubicWires.ExecutableInterfaces

/-- A selector that always returns a Boolean tag beside an arbitrary retained
frame. The quantifier includes zero and malformed request codes. -/
def SelectorTotalRunsAtFrame
    (selector : NPOracleProgram)
    (selectorBits selectorFuel frame : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ request : LanguageEvaluationRequest, ∃ tag ≤ 1,
    runNPOracleProgram selector (selectorBits request) (selectorFuel request)
        (initialNPOracleState request.length (frame request)) =
      some (Nat.pair tag (frame request))

end NearCubicWires.SelectorDrivenTotalRunContract
