import Proof.CaseAnalysis.WitnessAritySeam

/-! The weak verifier's own finite-input rejection permits reuse of the
already produced padded-domain field for its exact coefficient policy.
This source-fixed cutoff does NOT depend on M or on its refuter onset. -/
namespace NearCubicWires.RepairSource.CloseoutWitnessPolicy
open SourceInterfaces RepairRepresentation RepairOrdinary CloseoutLanguage SelectedRecoveryIntegration
open ProjectionNormalization CloseoutNativeWidth
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def inputCutoff (sources : EightSources) := 2^(selectedPCPP sources).minimumArity

theorem input_cutoff_native (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (N : Nat) (hN : inputCutoff sources ≤ N) :
    (selectedPCPP sources).minimumArity ≤ (outer sources k clock).result.pcp.nativeWidth N := by
  let H := (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy
  have hp : 2^(selectedPCPP sources).minimumArity ≤ Dimensions.envelope (fixedProjection sources)
      (HierarchyEncode.length H (padding sources k clock) N) :=
    hN.trans ((Nat.le_succ N).trans (input_le_envelope (fixedProjection sources) H (padding sources k clock) N))
  exact (Nat.le_log_of_pow_le (by decide : 1 < 2) hp).trans (Nat.le_succ _)

theorem input_cutoff_arity (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) {N : Nat} (input : BitInput N)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth N))
    (hN : inputCutoff sources ≤ N) :
    (request sources k clock input oracle).arity = (outer sources k clock).result.pcp.nativeWidth N :=
  actual_arity_eq_native sources k clock input oracle (input_cutoff_native sources k clock N hN)

theorem input_cutoff_q0 (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) {N : Nat} (input : BitInput N)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth N))
    (degree : Nat) (hN : inputCutoff sources ≤ N) :
    coreWidth 1 degree (request sources k clock input oracle).arity =
      (request sources k clock input oracle).arity+
        clauseWidth degree ((outer sources k clock).result.pcp.nativeWidth N)+1 := by
  rw [input_cutoff_arity sources k clock input oracle hN]
  simp only [coreWidth,one_mul]

end
end NearCubicWires.RepairSource.CloseoutWitnessPolicy
