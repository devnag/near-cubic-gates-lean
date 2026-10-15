import Proof.CaseAnalysis.RecoveryRowRun

/-! One sufficient fixed polynomial for the entire original verifier row.
Clause count is bounded by the actual original graph, not a new prepass. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRow
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clauses_length_count {q : ℕ} (clauses : List (Fin 3→Literal q)) :
    clauses.length ≤ clausesNodeCount clauses := by
  induction clauses with
  | nil=>simp only [List.length_nil,clausesNodeCount,Nat.zero_le]
  | cons clause clauses ih=>simp only [List.length_cons,clausesNodeCount];omega

theorem clauses_bound {sourceMachine : TimedDecisionMachine} {timeBound : ℕ→ℕ}
    (pcp : ProjectionPCP sourceMachine timeBound) {n bound : ℕ} (input : BitInput n)
    (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (count : ℕ) (hc : count ≤ bound) (randomness : BitInput (pcp.nativeWidth n)) (W : ℕ)
    (hFinal : (compileVerifierRow pcp input b count hc randomness).compiled.final.nodes.length ≤ W) :
    (pcp.decision input randomness).clauses.length ≤ W := by
  have hs:=(compileVerifierRow pcp input b count hc randomness).compiled.extension.nodes_eq
  have hl:=congrArg List.length hs
  rw [List.length_append,compileVerifierRow_addedNodes] at hl
  unfold verifierRowNodeCount at hl
  have hc:=clauses_length_count (pcp.decision input randomness).clauses
  omega

theorem clauses_budget_cubic (count W : ℕ) (hc : count ≤ W) :
    RecoveryBoundedClauses.budget count W (capacity W) ≤ 100000000*(W+1)^3 := by
  have hf:=Nat.mul_le_mul_right (RecoveryBoundedClauseBody.budget W (capacity W)+2) hc
  have hr:=Nat.mul_le_mul_right (24*capacity W+66) hc
  have ht : RecoveryBoundedNativeUnaryPhase.trueBits.length ≤ 16:=by decide
  unfold RecoveryBoundedClauses.budget RecoveryBoundedClauses.forwardBudget
    RecoveryBoundedClauseFold.budget RecoveryBoundedClauseFold.prepareBudget
  unfold RecoveryBoundedClauseBody.budget RecoveryBoundedClauseRun.budget
    RecoveryBoundedClauseState.literalBudget capacity at hf ⊢
  unfold capacity at hr
  nlinarith [Nat.zero_le (W^3),Nat.zero_le (W^2)]

theorem budget_sextic (queries clauses W : ℕ) (hq : queries ≤ W) (hc : clauses ≤ W) :
    budget queries clauses W ≤ 10000000000*(W+1)^6 := by
  have hq:=RecoveryBoundedQueries.budget_sextic queries W hq
  have hc:=clauses_budget_cubic clauses W hc
  unfold budget
  nlinarith [Nat.zero_le (W^6),Nat.zero_le (W^5),Nat.zero_le (W^4),Nat.zero_le (W^3),Nat.zero_le (W^2)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedRow
