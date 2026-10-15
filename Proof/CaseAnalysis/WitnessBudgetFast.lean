import Proof.CaseAnalysis.WitnessBudgetTools

namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BudgetTools
open PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

macro "fast_budget_poly" : tactic => `(tactic|
  repeat first
  | with_reducible assumption
  | with_reducible exact sourcePoly_id
  | with_reducible exact polyDominated_const _
  | with_reducible apply bits
  | with_reducible apply sourcePoly_logScale
  | with_reducible apply PolyDominated.add
  | with_reducible apply PolyDominated.mul
  | with_reducible apply sourcePoly_pow
  | with_reducible apply div
  | with_reducible apply sub
  | with_reducible apply max)

theorem arithmetic {f : ℕ→ℕ} (hf:SourcePoly f) :
    SourcePoly (fun n=>3*(f n+2)^4+natBitLength (f n+1)) := by
  fast_budget_poly

end NearCubicWires.RepairOrdinary.CloseoutWitness.BudgetTools
