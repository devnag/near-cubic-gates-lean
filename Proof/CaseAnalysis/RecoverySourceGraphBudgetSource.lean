import Proof.CaseAnalysis.RecoverySourceGraph
import Proof.Hierarchy.HierarchyStreamReady
import Proof.Circuits.PaddedRunnerBudgetClosure

/-! The source and all physical scalar suppliers have one fixed polynomial
in the paid W. The hierarchy clock is fixed before these C.12 constants. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization SourceInterfaces
open RecoveryScheduleEnvelope PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
  {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad d : ℕ)

def sourceEnvelope (W : ℕ):=
  HierarchyStreamCost.coefficient source H Cpad*(W+1)^HierarchyStreamCost.inputExponent source*
    (H.time W+2)^HierarchyStreamCost.logExponent source
def envelope (W : ℕ):=
  sourceEnvelope source H Cpad W+1+(2*W+8)+1+RecoveryCapacityDrivers.budget W+1+
    10000000000000*(W+1)^6+1+RecoveryFullBound.coefficient d*(W+2)^RecoveryFullBound.degree d+1+
    RecoveryBoundedColdGraph.coefficient*(W+1)^48

theorem sourceEnvelope_polynomial : SourcePoly (sourceEnvelope source H Cpad):=by
  have hn:=sourcePoly_id.add (polyDominated_const 1)
  have ht : SourcePoly H.time:=
    ((sourcePoly_pow sourcePoly_id (k+2)).add (polyDominated_const 1)).const_mul H.coefficient
  exact ((sourcePoly_pow hn (HierarchyStreamCost.inputExponent source)).const_mul
    (HierarchyStreamCost.coefficient source H Cpad)).mul
      (sourcePoly_pow (ht.add (polyDominated_const 2)) (HierarchyStreamCost.logExponent source))

theorem envelope_polynomial : SourcePoly (envelope source H Cpad d):=by
  have one : SourcePoly (fun _ : ℕ=>1):=polyDominated_const 1
  have hn:=sourcePoly_id.add (polyDominated_const 1)
  have hcl:=(sourcePoly_id.const_mul 2).add (polyDominated_const 8)
  have hcap : SourcePoly RecoveryCapacityDrivers.budget:=
    RecoveryCapacityDrivers.generic_polynomial 16384 (33*10000000000) 64
  have hp:=(sourcePoly_pow hn 6).const_mul 10000000000000
  have hf:=(sourcePoly_pow (sourcePoly_id.add (polyDominated_const 2))
    (RecoveryFullBound.degree d)).const_mul (RecoveryFullBound.coefficient d)
  have hg:=(sourcePoly_pow hn 48).const_mul RecoveryBoundedColdGraph.coefficient
  have hpre:=(((((sourceEnvelope_polynomial source H Cpad).add one).add hcl).add one).add hcap).add one
  exact ((((hpre.add hp).add one).add hf).add one).add hg

theorem source_bound (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad)
    (r : InputRequest) (W : ℕ) (hN : r.1 ≤ W) :
    HierarchyStreams.budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2) ≤
      sourceEnvelope source H Cpad W:=by
  have hs:=HierarchyStreamCost.budget_bound source H Cpad hcoeff hpad r
  rw [HierarchyStreams.framed_budget_eq source H Cpad hpad r] at hs
  have ht : H.time r.1 ≤ H.time W:=by
    change H.coefficient*(r.1^(k+2)+1) ≤ H.coefficient*(W^(k+2)+1)
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.pow_le_pow_left hN _) 1)
  have hz : natBitLength (H.time r.1)+1 ≤ H.time W+2:=by
    have h:=PCPPQueryCost.width_le (H.time r.1)
    omega
  have hm : HierarchyStreamCost.coefficient source H Cpad*(r.1+1)^HierarchyStreamCost.inputExponent source*
      (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logExponent source ≤ sourceEnvelope source H Cpad W:=by
    unfold sourceEnvelope
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) _))
      (Nat.pow_le_pow_left hz _)
  omega

theorem suppliers_bound (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad)
    (r : InputRequest) (W : ℕ) (hN : r.1 ≤ W)
    (hR : HierarchyStreams.R source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2) ≤ W)
    (hQ : HierarchyStreams.Q source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2) ≤ W)
    (hclauses : (Codec.clauses (source.output
      (HierarchyStreams.request k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)))).length ≤ W)
    (htwo : 2^(HierarchyStreams.R source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)) ≤ W) :
    RecoveryBoundedColdSuppliers.budget source k d H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2) W ≤
      sourceEnvelope source H Cpad W+1+(2*W+8)+1+RecoveryCapacityDrivers.budget W+1+
        10000000000000*(W+1)^6+1+RecoveryFullBound.coefficient d*(W+2)^RecoveryFullBound.degree d:=by
  let R:=HierarchyStreams.R source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)
  let Q:=HierarchyStreams.Q source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)
  have hs:=source_bound source H Cpad hcoeff hpad r W hN
  have hp:=RecoveryProjectionCold.budget_bound W R Q hR hQ htwo
  have hf:=(RecoveryFullBound.budget_bound d R).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hR 2) _))
  unfold RecoveryBoundedColdSuppliers.budget RecoveryBoundedColdHierarchyDock.Count.budget
    RecoveryBoundedColdClauseCount.budget RecoveryBoundedColdHierarchyDock.Count.clauses
  change _ ≤ sourceEnvelope source H Cpad W+1+(2*W+8)+1+RecoveryCapacityDrivers.budget W+1+
    10000000000000*(W+1)^6+1+RecoveryFullBound.coefficient d*(W+2)^RecoveryFullBound.degree d
  change RecoveryProjectionCold.budget R Q (RecoveryCapacityDrivers.capacityB W) ≤ _ at hp
  dsimp only [R,Q] at hp hf
  omega

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph
