import Proof.CaseAnalysis.WitnessFamilyMeaning
import Proof.PCP.ProjectionDimensionPolynomialBounds

/-! The actual family continuation, including physical P/H production,
has a source-fixed polynomial bound independent of hierarchy k and code. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def tailBound (a : PointwisePCPPAlgorithm) (G D copies E K : ℕ) (delta : ℚ) (N : ℕ) :=
  FamilyCapacity.budget E K N+1+
    FamilyResources.totalCost (scale source a G D copies delta N) (FamilyCapacity.value E K N)

theorem tail_budget_le (a : PointwisePCPPAlgorithm) (k CH Cpad D G copies E K : ℕ)
    (delta : ℚ) (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool) (hpad:k+3≤Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)))
    (hbudget:∀ N,FamilyResources.capacity (scale source a G D copies delta N)≤K*(N+1)^E)
    (hcore:(ColdNative.request source a k CH Cpad code x hpad oracle).arity=
      SelectedOracle.width source k CH Cpad code (List.ofFn x))
    (hR:SelectedOracle.width source k CH Cpad code (List.ofFn x)≤n)
    (hbits:bits.length≤n)
    (ho:oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G
      (SelectedOracle.width source k CH Cpad code (List.ofFn x))) :
    tailBudget source a k CH Cpad D G copies E K delta code x bits hpad oracle≤
      tailBound source a G D copies E K delta n := by
  have fits:=ColdFamilyResources.native_fits a source.coefficient source.degrees.queries G D delta copies K E
    hbudget (SelectedStreams.pcp source k CH Cpad code (List.ofFn x))
    (SelectedOracle.width source k CH Cpad code (List.ofFn x))
    (SelectedStreams.queries source k CH Cpad code (List.ofFn x))
    (PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad)
    (PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad) x oracle n bits hcore hR hbits
    (ColdFamilyGuards.query_bound source k CH Cpad code (List.ofFn x)) ho
  exact Nat.add_le_add_left (FamilyResources.total_cost _ _ _ _ _ _ bits _ fits.1 fits.2) _

theorem tail_polynomial (a : PointwisePCPPAlgorithm) (G D copies E K : ℕ) (delta : ℚ) :
    SourcePoly (tailBound source a G D copies E K delta) := by
  have hc (v : ℕ) : SourcePoly (fun _=>v):=polyDominated_const v
  have hp:SourcePoly (FamilyCapacity.value E K):=
    (sourcePoly_pow (sourcePoly_id.add (hc 1)) E).const_mul K
  have hd:SourcePoly (DimensionPolynomial.budget E K):=
    ((sourcePoly_pow (sourcePoly_id.add (hc 2)) (2*E+2)).const_mul
      (DimensionPolynomial.coefficient E K)).mono (DimensionPolynomial.budget_bound E K)
  have hb:SourcePoly (FamilyCapacity.budget E K):=
    (((hd.add (hc 1)).add ((hp.const_mul 2).add (hc 8))).add (hc 1)).add
      (((hp.add (hc 1)).const_mul 4).add (hc 12))
  exact (hb.add (hc 1)).add (FamilyResources.costs_polynomial
    (FamilyResources.source_scale_polynomial a source.coefficient source.degrees.queries G D delta copies) hp).2.2

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
