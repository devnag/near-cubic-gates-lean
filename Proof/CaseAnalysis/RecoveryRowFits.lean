import Proof.CaseAnalysis.RecoveryQueryFits
import Proof.CaseAnalysis.RecoveryRowMeaning

/-! The original row consumer needs only its original final graph bound.
The complete recursive query Fits tree is now discharged by that bound. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
open BoundedOracleStructuralCircuit FinitePredicateCircuit OuterPCPRecovery SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem row_fits {machine : TimedDecisionMachine} {timeBound : ℕ→ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ} (input : BitInput n)
    (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (count G : ℕ) (hc : count ≤ bound) (randomness : BitInput (pcp.nativeWidth n))
    (hg : (compileVerifierRow pcp input b count hc randomness).compiled.final.nodes.length ≤ G) :
    RecoveryBoundedQueries.Fits b count (workspace (pcp.nativeWidth n) bound G) hc
      (projectedAddresses pcp input randomness) :=
  queries_fits b count G hc _ (RecoveryBoundedRow.query_bound pcp input b count hc randomness G hg)

theorem original_workspace_fields (q bound queries clauses : ℕ) :
    q ≤ originalWorkspace q bound queries clauses ∧
    bound ≤ originalWorkspace q bound queries clauses ∧
    queries ≤ originalWorkspace q bound queries clauses ∧
    clauses ≤ originalWorkspace q bound queries clauses ∧
    boundedCircuitFieldLimit q bound ≤ originalWorkspace q bound queries clauses ∧
    descriptionWidth q bound ≤ originalWorkspace q bound queries clauses := by
  let G:=R1Leaf56StructuralGateBudgetEnvelope.structuralGateEnvelope q bound queries clauses+queries+clauses
  have hs:=(workspace_bounds q bound G).2.2.2
  have hqueries : queries ≤ G := by unfold G; omega
  have hclauses : clauses ≤ G := by unfold G; omega
  have hd:=(workspace_bounds q bound G).2.1
  have he : descriptionWidth q bound=(bound+1)*rowWidth q bound := rfl
  have hm:=Nat.mul_le_mul_right (rowWidth q bound) (show bound+1 ≤ bound+2 by omega)
  change q ≤ workspace q bound G ∧ bound ≤ workspace q bound G ∧
    queries ≤ workspace q bound G ∧ clauses ≤ workspace q bound G ∧
    boundedCircuitFieldLimit q bound ≤ workspace q bound G ∧
    descriptionWidth q bound ≤ workspace q bound G
  rw [he]
  change q ≤ workspace q bound G ∧ bound ≤ workspace q bound G ∧
    queries ≤ workspace q bound G ∧ clauses ≤ workspace q bound G ∧
    q+bound+1 ≤ workspace q bound G ∧ (bound+1)*rowWidth q bound ≤ workspace q bound G
  exact ⟨by omega,by omega,graph_le_workspace hqueries,graph_le_workspace hclauses,hs,by omega⟩

end NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
