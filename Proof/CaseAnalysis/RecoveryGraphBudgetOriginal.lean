import Proof.CaseAnalysis.RecoveryGraphBudgetResources

/-! Specialize the resource skeleton to the original normalized PCP and
paper structural gate envelope, including the count compiler's final bound. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
open RepairSource ProjectionNormalization SourceInterfaces CanonicalRecoveryLanguage
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open CloseoutRecoveryWorkspace R1Leaf56StructuralGateBudgetEnvelope
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def originalG (p : RawProjectionPCP) (R Q bound : ℕ) :=
  structuralGateEnvelope R bound Q (Codec.clauses p).length+Q+(Codec.clauses p).length

variable (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
variable {n bound : ℕ} (x : BitInput n)

theorem original_final :
    (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x
      (BooleanDAGBuilder.empty (descriptionWidth R bound)) (List.finRange bound)).final.nodes.length ≤
      originalG p R Q bound := by
  let pcp := compactProjectionPCP (p.normalized R Q hr hq)
  have clauses : ∀ randomness,(pcp.decision x randomness).clauses.length ≤ (Codec.clauses p).length := by
    intro randomness
    have h := congrArg List.length (Codec.decision_codes p R Q hr hq x randomness)
    simpa only [List.length_map] using h.le
  have h := boundedOracleStructuralGateBudget_envelope pcp x bound (Codec.clauses p).length clauses
  rw [←boundedOracleVerifierCircuit_size] at h
  change (compileCountCases pcp x (BooleanDAGBuilder.empty (descriptionWidth R bound))
    (List.ofFn (id : Fin bound→Fin bound))).final.nodes.length ≤
      structuralGateEnvelope R bound Q (Codec.clauses p).length at h
  rw [List.ofFn_id] at h
  exact h.trans (by unfold originalG;omega)

/-- Only physical W and S domination remains. The original source supplies
all clause counts and the complete final graph bound without a prepass. -/
noncomputable def originalResources (W S : ℕ) (sourceTail : List Bool)
    (hW : originalWorkspace R bound Q (Codec.clauses p).length ≤ W)
    (hS : support W R Q bound (DedupBytes.fields p++sourceTail) ≤ S) :
    RecoveryBoundedCountUniform.Resources p R Q hr hq (bound:=bound) x := by
  have h := original_workspace_fields R bound Q (Codec.clauses p).length
  exact resources p R Q hr hq x (originalG p R Q bound) W S sourceTail hW
    (h.2.2.1.trans hW) (h.2.2.2.1.trans hW) hS

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
