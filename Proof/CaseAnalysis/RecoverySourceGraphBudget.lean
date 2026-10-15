import Proof.CaseAnalysis.RecoverySourceGraphBudgetSource

/-! The original circuit's checked paper gate bound funds graph construction
and serialization. Add it to the actual source/scalar supplier polynomial. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization SourceInterfaces
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryScheduleEnvelope
open CloseoutRecoveryWorkspace PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem graph_budget_bound (k d CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n)
    (W : ℕ) (hpad : k+3 ≤ Cpad)
    (hW : originalWorkspace (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
      (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))
      (PCPPNativeHierarchyNodes.queries source k CH Cpad code x)
      (Codec.clauses (PCPPNativeHierarchyNodes.pcp source k CH Cpad code x)).length ≤ W)
    (htwo : 2^(PCPPNativeHierarchyNodes.width source k CH Cpad code x) ≤ W) :
    RecoveryBoundedColdGraph.budget (RecoveryBoundedGraphBudget.scalarBacking W) W
      (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
      (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))
      (circuit source k d CH Cpad code x hpad) ≤ RecoveryBoundedColdGraph.coefficient*(W+1)^48:=by
  let p:=PCPPNativeHierarchyNodes.pcp source k CH Cpad code x
  let R:=PCPPNativeHierarchyNodes.width source k CH Cpad code x
  let Q:=PCPPNativeHierarchyNodes.queries source k CH Cpad code x
  let b:=oracleSizeBound d R
  let hr:=PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad
  let hq:=PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad
  let pcp:=compactProjectionPCP (p.normalized R Q hr hq)
  let c:=circuit source k d CH Cpad code x hpad
  have hf:=original_workspace_fields R b Q (Codec.clauses p).length
  have hc : c.nodes.length ≤ W:=by
    have hclauses : ∀ randomness,(pcp.decision x randomness).clauses.length ≤ (Codec.clauses p).length:=by
      intro randomness
      have h:=congrArg List.length (Codec.decision_codes p R Q hr hq x randomness)
      simpa only [List.length_map] using h.le
    exact (original_graph_bound pcp x b (Codec.clauses p).length hclauses).trans hW
  exact RecoveryBoundedColdGraph.budget_bound (R:=R) (W:=W) (bound:=b) c
    (hf.2.2.2.2.2.trans hW) hc (hf.1.trans hW) (hf.2.1.trans hW) htwo

theorem budget_bound {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad d : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (r : InputRequest) (W : ℕ) (hN : r.1 ≤ W)
    (hW : originalWorkspace (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)
      (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
      (PCPPNativeHierarchyNodes.queries source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)
      (Codec.clauses (PCPPNativeHierarchyNodes.pcp source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)).length ≤ W)
    (htwo : 2^(PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) ≤ W) :
    budget source k d H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 W hpad ≤ envelope source H Cpad d W:=by
  let p:=PCPPNativeHierarchyNodes.pcp source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let R:=PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let Q:=PCPPNativeHierarchyNodes.queries source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  have hf:=original_workspace_fields R (oracleSizeBound d R) Q (Codec.clauses p).length
  have hs:=suppliers_bound source H Cpad d hcoeff hpad r W hN
    (hf.1.trans hW) (hf.2.2.1.trans hW) (hf.2.2.2.1.trans hW) htwo
  have hg:=graph_budget_bound source k d H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 W hpad hW htwo
  unfold budget envelope
  omega

theorem polynomial_budget {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad d : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) :
    ∃ C E : ℕ,1 ≤ C ∧ ∀ (r : InputRequest) (W : ℕ),r.1 ≤ W →
      originalWorkspace (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)
        (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
        (PCPPNativeHierarchyNodes.queries source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)
        (Codec.clauses (PCPPNativeHierarchyNodes.pcp source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)).length ≤ W →
      2^(PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) ≤ W →
      budget source k d H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 W hpad ≤ C*(W+1)^E:=by
  obtain ⟨E,C,h⟩:=envelope_polynomial source H Cpad d
  refine ⟨C+1,E,by omega,fun r W hN hW htwo=>?_⟩
  exact (budget_bound source H Cpad d hcoeff hpad r W hN hW htwo).trans
    ((h W).trans (Nat.mul_le_mul_right _ (by omega)))

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph
