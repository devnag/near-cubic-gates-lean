import Proof.CaseAnalysis.WitnessSampledSource
import Proof.CaseAnalysis.WitnessFamilySupportRun

/-! The physical source call and the selected outer PCP give the same
request. Dimension casts are discharged before the source circuit is used. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedSource
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem request_compact (a : PointwisePCPPAlgorithm) {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q→Fin n→ProjectedRandomBit r) (formula : ThreeCNF q) :
    PCPPSubstitution.sourceRequest a oracle projections (compactThreeCNF formula)=
      PCPPSubstitution.sourceRequest a oracle projections formula := by
  unfold PCPPSubstitution.sourceRequest PCPPSubstitution.compactSubstituted compactThreeCNF
  rw [List.dedup_idem]

private theorem request_transport (a : PointwisePCPPAlgorithm) {p p' : RawProjectionPCP} {R R' Q Q' : ℕ}
    (hp:p=p') (hR:R=R') (hQ:Q=Q') (hr:p.width≤R) (hq:p.queries≤Q) (hr':p'.width≤R') (hq':p'.queries≤Q')
    {N : ℕ} (x : BitInput N) (oracle : BooleanCircuit R') :
    NativeCache.request a p R Q hr hq x (cast (congrArg BooleanCircuit hR.symm) oracle)=
      NativeCache.request a p' R' Q' hr' hq' x oracle := by
  cases hp;cases hR;cases hQ;rfl

def hierarchy (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n=>n^(k+2))):=
  (sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
def code (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n=>n^(k+2))):=
  VerifierEncoding.code (hierarchy sources k clock).verifier

theorem width (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n=>n^(k+2)))
    {N : ℕ} (x : BitInput N) :
    SelectedOracle.width (fixedProjection sources) k (hierarchy sources k clock).coefficient
      (padding sources k clock) (code sources k clock) (List.ofFn x)=
        (outer sources k clock).result.pcp.nativeWidth N :=
  (HierarchyStreams.hierarchy_dimensions (fixedProjection sources) (hierarchy sources k clock)
    (padding sources k clock) (Nat.le_max_right _ _) ⟨N,x⟩).2.1

theorem request_eq (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n=>n^(k+2)))
    {N : ℕ} (x : BitInput N) (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth N)) :
    ColdNative.request (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) k
      (hierarchy sources k clock).coefficient (padding sources k clock) (code sources k clock) x (Nat.le_max_right _ _)
      (cast (congrArg BooleanCircuit (width sources k clock x).symm) oracle)=
        CloseoutWitnessPolicy.request sources k clock x oracle := by
  have dims:=HierarchyStreams.hierarchy_dimensions (fixedProjection sources) (hierarchy sources k clock)
    (padding sources k clock) (Nat.le_max_right _ _) ⟨N,x⟩
  have native:=request_transport (CloseoutLanguage.selectedPCPP sources)
    (congrArg (fixedProjection sources).output dims.1) dims.2.1 dims.2.2
    (PCPPNativeHierarchyNodes.width_fits (fixedProjection sources) k (hierarchy sources k clock).coefficient
      (padding sources k clock) (code sources k clock) x (Nat.le_max_right _ _))
    (PCPPNativeHierarchyNodes.queries_fit (fixedProjection sources) k (hierarchy sources k clock).coefficient
      (padding sources k clock) (code sources k clock) x (Nat.le_max_right _ _))
    (HierarchyProjection.width_fits (fixedProjection sources) (hierarchy sources k clock)
      (padding sources k clock) (Nat.le_max_right _ _) ⟨N,x⟩)
    (HierarchyProjection.queries_fit (fixedProjection sources) (hierarchy sources k clock)
      (padding sources k clock) (Nat.le_max_right _ _) ⟨N,x⟩) x oracle
  exact native.trans (request_compact (CloseoutLanguage.selectedPCPP sources) oracle _ _).symm

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedSource
