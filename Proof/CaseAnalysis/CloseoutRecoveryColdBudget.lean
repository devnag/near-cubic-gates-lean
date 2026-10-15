import Proof.CaseAnalysis.Recovery

/-! C.12 pays one fixed polynomial in the physically supplied W. The
source length is bounded by that same W, whose exponent uses final length. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedCold
open LocalBitMultitape RepairOrdinary SourceInterfaces ProjectionNormalization
open RecoveryScheduleEnvelope CloseoutRecoveryWorkspace BoundedOracleStructuralCircuit
open PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

private theorem cubic_product (K W : Nat) :
    1099511627776*((K+7)*(W+1)^48)^3=
      (1099511627776*(K+7)^3)*(W+1)^144 := by
  rw [Nat.mul_pow,←Nat.pow_mul,Nat.mul_assoc]

theorem search_budget_bound (k d CH Cpad : Nat) (code : List Bool) {n : Nat} (x : BitInput n)
    (W : Nat) (hpad : k+3 ≤ Cpad)
    (hW : originalWorkspace (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
      (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))
      (PCPPNativeHierarchyNodes.queries source k CH Cpad code x)
      (Codec.clauses (PCPPNativeHierarchyNodes.pcp source k CH Cpad code x)).length ≤ W) :
    1099511627776*(RecoveryPrefixCold.radius (payload source k d CH Cpad code x hpad)
      (total source k d CH Cpad code x))^3 ≤ RecoveryBoundedSearchExecution.graphSearchCoefficient*(W+1)^144 := by
  let p:=PCPPNativeHierarchyNodes.pcp source k CH Cpad code x
  let R:=PCPPNativeHierarchyNodes.width source k CH Cpad code x
  let Q:=PCPPNativeHierarchyNodes.queries source k CH Cpad code x
  let b:=oracleSizeBound d R
  let hr:=PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad
  let hq:=PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad
  let pcp:=compactProjectionPCP (p.normalized R Q hr hq)
  let c:=RecoveryBoundedColdSourceGraph.circuit source k d CH Cpad code x hpad
  have hf:=original_workspace_fields R b Q (Codec.clauses p).length
  have hc : c.nodes.length ≤ W:=by
    have hclauses : ∀ randomness,(pcp.decision x randomness).clauses.length ≤ (Codec.clauses p).length:=by
      intro randomness
      have h:=congrArg List.length (Codec.decision_codes p R Q hr hq x randomness)
      simpa only [List.length_map] using h.le
    exact (original_graph_bound pcp x b (Codec.clauses p).length hclauses).trans hW
  have h:=Nat.mul_le_mul_left 1099511627776
    (Nat.pow_le_pow_left (RecoveryBoundedSearchExecution.radius_bound c W (hf.2.2.2.2.2.trans hW) hc) 3)
  exact h.trans_eq (cubic_product RecoveryBoundedGraphBudget.serializerCoefficient W)

def envelope {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad d W : Nat):=
  RecoveryBoundedColdSourceGraph.envelope source H Cpad d W+2+
    RecoveryBoundedSearchExecution.graphSearchCoefficient*(W+1)^144

theorem polynomial_budget {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad d : Nat)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) :
    ∃ C E : Nat,1 ≤ C ∧ ∀ (r : InputRequest) (W : Nat),r.1 ≤ W →
      originalWorkspace (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)
        (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
        (PCPPNativeHierarchyNodes.queries source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)
        (Codec.clauses (PCPPNativeHierarchyNodes.pcp source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)).length ≤ W →
      2^(PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) ≤ W →
      budget source k d H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 W hpad ≤ C*(W+1)^E := by
  have he : SourcePoly (envelope source H Cpad d):=
    ((RecoveryBoundedColdSourceGraph.envelope_polynomial source H Cpad d).add (polyDominated_const 2)).add
      ((sourcePoly_pow (sourcePoly_id.add (polyDominated_const 1)) 144).const_mul
        RecoveryBoundedSearchExecution.graphSearchCoefficient)
  obtain ⟨E,C,h⟩:=he
  refine ⟨C+1,E,by omega,fun r W hN hW htwo=>?_⟩
  have hg:=RecoveryBoundedColdSourceGraph.budget_bound source H Cpad d hcoeff hpad r W hN hW htwo
  have hs:=search_budget_bound source k d H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 W hpad hW
  have hb : budget source k d H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 W hpad ≤
      envelope source H Cpad d W:=Nat.add_le_add (Nat.add_le_add_right hg 2) hs
  exact hb.trans ((h W).trans (Nat.mul_le_mul_right _ (by omega)))

end
end NearCubicWires.RepairSource.RecoveryBoundedCold
