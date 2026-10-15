import Proof.CaseAnalysis.WitnessSourceSize

/-! The physical gate parser must use the actual padded PCPP request domain.
The retained native oracle arity is interchangeable only under this explicit
minimum-arity condition. No additional guard or source field is assumed. -/
namespace NearCubicWires.RepairSource.CloseoutWitnessPolicy
open SourceInterfaces RepairRepresentation RepairOrdinary CloseoutLanguage SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem source_arity (a : PointwisePCPPAlgorithm) {n r q : Nat}
    (oracle : BooleanCircuit n) (projections : Fin q→Fin n→ProjectedRandomBit r)
    (formula : ThreeCNF q) :
    (PCPPSubstitution.sourceRequest a oracle projections formula).arity=max r a.minimumArity := rfl

theorem actual_arity (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) {N : Nat} (input : BitInput N)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth N)) :
    (request sources k clock input oracle).arity=
      max ((outer sources k clock).result.pcp.nativeWidth N) (selectedPCPP sources).minimumArity := rfl

theorem actual_arity_eq_native (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) {N : Nat} (input : BitInput N)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth N))
    (hmin : (selectedPCPP sources).minimumArity≤(outer sources k clock).result.pcp.nativeWidth N) :
    (request sources k clock input oracle).arity=(outer sources k clock).result.pcp.nativeWidth N := by
  rw [actual_arity, max_eq_left hmin]

end
end NearCubicWires.RepairSource.CloseoutWitnessPolicy
