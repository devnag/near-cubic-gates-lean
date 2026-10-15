import Proof.CaseAnalysis.RecoveryRowQueries

/-! Exact original verifier-row boundaries: queries precede their original
clauses, and all query wires retain the same shared description block. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRow
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {machine : TimedDecisionMachine} {timeBound : ℕ→ℕ}
  (pcp : ProjectionPCP machine timeBound) {n bound : ℕ} (input : BitInput n)
  (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
  (count : ℕ) (hc : count ≤ bound) (randomness : BitInput (pcp.nativeWidth n))

def rowQueries:=compileUniversalOutputs b count hc (projectedAddresses pcp input randomness)
theorem query_length : (rowQueries pcp input b count hc randomness).values.length=pcp.queryCount n := by
  rw [rowQueries,compileUniversalOutputs_values_length,projectedAddresses_length]
def rowDecision:=
  let q:=rowQueries pcp input b count hc randomness
  compileClauses q.final q.values (query_length pcp input b count hc randomness) (pcp.decision input randomness).clauses

theorem original_final : (compileVerifierRow pcp input b count hc randomness).compiled.final=
    (rowDecision pcp input b count hc randomness).final := rfl
theorem original_output : (compileVerifierRow pcp input b count hc randomness).compiled.output.val=
    (rowDecision pcp input b count hc randomness).output.val := rfl
theorem original_native :
    (compileVerifierRow pcp input b count hc randomness).compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native=
      RecoveryBoundedQueries.native b count hc (projectedAddresses pcp input randomness)++
      (rowDecision pcp input b count hc randomness).extension.suffix.flatMap PCPPRequestNodeSchema.native := by
  change List.flatMap PCPPRequestNodeSchema.native (_++_)=_
  rw [List.flatMap_append]
  rfl
theorem query_bound (W : ℕ)
    (h : (compileVerifierRow pcp input b count hc randomness).compiled.final.nodes.length ≤ W) :
    (rowQueries pcp input b count hc randomness).final.nodes.length ≤ W := by
  exact (rowDecision pcp input b count hc randomness).extension.length_le.trans h
theorem references_eq :
    RecoveryBoundedLiteral.references (rowQueries pcp input b count hc randomness).values=
      RecoveryBoundedQueries.references b count hc (projectedAddresses pcp input randomness) := rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedRow
