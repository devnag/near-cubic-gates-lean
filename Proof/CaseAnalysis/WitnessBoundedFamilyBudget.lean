import Proof.CaseAnalysis.WitnessFamilySupportLayout
import Proof.CaseAnalysis.WitnessBoundedFamilyRun

/-! The original all-input bounded header pays exactly one cold mode.
The hierarchy-independent tail covers both mode choices before k is fixed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamily
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def outerBound (a : PointwisePCPPAlgorithm) (G D copies E K symDen thrDen : ℕ) (delta : ℚ) (N : ℕ):=
  26010*(N+1)^2+2+
    ColdFamily.outerBound source a G D copies 5 E K symDen delta true N+
    ColdFamily.outerBound source a G D copies 9 E K thrDen delta false N

theorem budget_le (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad cutoff D G copies E K symDen thrDen : ℕ) (delta : ℚ)
    (hcoeff:H.coefficient≤Cpad) (hpad:k+3≤Cpad) (hcut:2^a.minimumArity≤cutoff)
    (hbudget:∀ N,FamilyResources.capacity (ColdFamily.scale source a G D copies delta N)≤K*(N+1)^E)
    (r : InputRequest) (bits : List Bool) :
    budget source a k H.coefficient Cpad cutoff D G copies E K symDen thrDen delta
      (VerifierEncoding.code H.verifier) r.2 bits hpad≤
      ColdNative.bound source a D G copies cutoff delta (HierarchyBudget.scale source H Cpad r.1)+
        outerBound source a G D copies E K symDen thrDen delta r.1 := by
  classical
  unfold budget outerBound CompetitorWitnessBounded.budget
  simp only [List.length_ofFn]
  split_ifs with live
  · have cap:16*bits.length≤r.1:=by
      have h:=of_decide_eq_true live
      simpa only [List.length_ofFn] using h.1
    have raw:16*(BoundedFields.oracle bits).length≤r.1:=by rw [(BoundedFields.lengths bits).1];exact cap
    have family:(BoundedFields.family bits).length≤r.1:=by rw [(BoundedFields.lengths bits).2];omega
    have child:=ColdFamily.budget_le source a H Cpad cutoff D G copies
      (exponent (BoundedFields.symmetric bits)) E K (denominator (BoundedFields.symmetric bits) symDen thrDen)
      delta (BoundedFields.symmetric bits) hcoeff hpad hcut hbudget r
      (BoundedFields.oracle bits) (BoundedFields.family bits) raw family
    change childBudget source a k H.coefficient Cpad cutoff D G copies E K symDen thrDen delta
      (VerifierEncoding.code H.verifier) r.2 bits hpad (BoundedFields.symmetric bits)≤_ at child
    cases hs:BoundedFields.symmetric bits <;>
      simp only [hs,exponent,denominator,Bool.false_eq_true,if_false,if_true] at child ⊢ <;> omega
  · omega

theorem outer_polynomial (a : PointwisePCPPAlgorithm) (G D copies E K symDen thrDen : ℕ) (delta : ℚ) :
    SourcePoly (outerBound source a G D copies E K symDen thrDen delta) := by
  have sym:=ColdFamily.outer_polynomial source a G D copies 5 E K symDen delta true
  have thr:=ColdFamily.outer_polynomial source a G D copies 9 E K thrDen delta false
  change SourcePoly (fun n=>outerBound source a G D copies E K symDen thrDen delta n)
  dsimp only [outerBound]
  fast_budget_poly

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamily
