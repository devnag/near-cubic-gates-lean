import Proof.CaseAnalysis.WitnessLegalBudgetEnvelope

/-! The actual guarded source request enters one uniform legal-policy
envelope whose degree is fixed before hierarchy k and its encoded program. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure
open CloseoutWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def tailBound (a : PointwisePCPPAlgorithm) (G D copies e den : ℕ) (delta : ℚ) (sym : Bool) (N : ℕ) :=
  LegalBudget.envelope e den copies delta sym
    (ColdFamily.scale source a G D copies delta N+FamilyResources.coreBound D N+1)

theorem tail_budget_le (a : PointwisePCPPAlgorithm) (k CH Cpad D G copies e den : ℕ)
    (delta : ℚ) (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (hpad:k+3≤Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)))
    (hcore:(ColdNative.request source a k CH Cpad code x hpad oracle).arity=
      SelectedOracle.width source k CH Cpad code (List.ofFn x))
    (hR:SelectedOracle.width source k CH Cpad code (List.ofFn x)≤n)
    (ho:oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G
      (SelectedOracle.width source k CH Cpad code (List.ofFn x))) :
    tailBudget source a k CH Cpad D copies e den delta code sym x hpad oracle≤
      tailBound source a G D copies e den delta sym n := by
  let p:=SelectedStreams.pcp source k CH Cpad code (List.ofFn x)
  let R:=SelectedOracle.width source k CH Cpad code (List.ofFn x)
  let Q:=SelectedStreams.queries source k CH Cpad code (List.ofFn x)
  let hwidth:=PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad
  let hqueries:=PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad
  let projections:=(p.normalized R Q hwidth hqueries).queryAddressBits x
  let formula:=(p.normalized R Q hwidth hqueries).decision x (fun _=>false)
  let r:=ColdNative.request source a k CH Cpad code x hpad oracle
  let S:=ColdFamily.scale source a G D copies delta n
  have core:r.arity=R:=hcore
  have core_le:r.arity≤n:=core.le.trans hR
  have identity:r=PCPPSubstitution.sourceRequest a oracle projections formula:=rfl
  have hq:Q ≤ source.coefficient*(R+1)^source.degrees.queries:=Nat.le_refl _
  have counts:=CloseoutSourceCounts.short_counts a oracle projections formula source.coefficient
    source.degrees.queries G hq ho
  have short:=FamilyResources.counts_bound a source.coefficient source.degrees.queries G R n hR
  have hm:2^(a.output r).clauseBits≤S:=by
    have hs:FamilyResources.countBound (FamilyResources.countCoefficient a source.coefficient source.degrees.queries G)
        (FamilyResources.countDegree a source.coefficient source.degrees.queries G) n≤S:=by
      dsimp only [S,ColdFamily.scale,FamilyResources.sourceScale,FamilyResources.scale]
      omega
    rw [identity]
    exact counts.2.trans (short.trans hs)
  have resources:=FamilyResources.source_bounds a source.coefficient source.degrees.queries G D delta copies
    oracle projections formula n hR hq ho
  have coefficient:FamilyResources.coefficientCap delta copies D r.arity (a.output r).clauseBits≤S:=by
    have eq:=congrArg (fun u=>FamilyResources.coefficientCap delta copies D u (a.output r).clauseBits) core
    rw [eq,identity]
    exact resources.2.2.1
  have q0:CorePolicy.q0 D r.arity≤FamilyResources.coreBound D n:=
    FamilyResources.core_bound D r.arity n core_le
  have hb:=PCPPQueryCost.width_le (FamilyResources.coefficientCap delta copies D r.arity (a.output r).clauseBits)
  have hcb: (a.output r).clauseBits≤2^(a.output r).clauseBits:=(Nat.lt_two_pow_self).le
  apply LegalBudget.budget_le
  · change r.arity≤S+FamilyResources.coreBound D n+1
    have hs:n+1≤S:=resources.1
    omega
  · exact q0.trans (by omega)
  · exact (hcb.trans hm).trans (by omega)
  · change natBitLength (FamilyResources.coefficientCap delta copies D r.arity (a.output r).clauseBits)≤_
    omega
  · exact hm.trans (by omega)

theorem tail_polynomial (a : PointwisePCPPAlgorithm) (G D copies e den : ℕ) (delta : ℚ) (sym : Bool) :
    SourcePoly (tailBound source a G D copies e den delta sym) := by
  have hs:=FamilyResources.source_scale_polynomial a source.coefficient source.degrees.queries G D delta copies
  have hcore:SourcePoly (FamilyResources.coreBound D):=
    (sourcePoly_id.add (polyDominated_const 1)).const_mul (D+1)
  exact LegalBudget.envelope_polynomial e den copies delta sym ((hs.add hcore).add (polyDominated_const 1))

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
