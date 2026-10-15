import Proof.CaseAnalysis.RecoverySourceGraphPrefix
import Proof.PCP.PCPPNativeHierarchyNodesCircuit

/-! The supplier enters the SAME original verifier circuit and balanced CNF.
Only the proved names of its paid C and B capacities are reconciled. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization SourceInterfaces
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryScheduleEnvelope
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem capacity_eq (W : ℕ) : RecoveryCapacityDrivers.capacityC W=RecoveryBoundedSelectorLoop.capacity W:=rfl
theorem backing_eq (W : ℕ) : RecoveryCapacityDrivers.capacityB W=RecoveryBoundedGraphBudget.scalarBacking W:=by
  unfold RecoveryCapacityDrivers.capacityB RecoveryBoundedGraphBudget.scalarBacking
    CloseoutRecoveryGrammarResources.backing RecoveryBoundedGraphBudget.scalarSupport
  ring

def circuit (k d CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) (hpad : k+3 ≤ Cpad):=
  boundedOracleVerifierCircuit (compactProjectionPCP
    ((PCPPNativeHierarchyNodes.pcp source k CH Cpad code x).normalized
      (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
      (PCPPNativeHierarchyNodes.queries source k CH Cpad code x)
      (PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad)
      (PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad)))
    x (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))

theorem output_original (k d CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) (W : ℕ) :
    RecoveryBoundedColdSuppliers.output source k d CH Cpad code (List.ofFn x) W=
      RecoveryBoundedColdPrepared.input
        (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
        (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))
        (RecoveryBoundedSelectorLoop.capacity W)
        (PCPPNativeHierarchyNodes.queries source k CH Cpad code x)
        (Codec.clauses (PCPPNativeHierarchyNodes.pcp source k CH Cpad code x)).length
        (RecoveryBoundedGraphBudget.scalarBacking W)
        (RecoveryBoundedRowProjection.bank (PCPPNativeHierarchyNodes.pcp source k CH Cpad code x)
          (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
          (PCPPNativeHierarchyNodes.queries source k CH Cpad code x)
          (CanonicalRecoveryLanguage.bitInputOfCode (PCPPNativeHierarchyNodes.width source k CH Cpad code x) 0)
          (RecoveryBoundedGraphBudget.scalarBacking W))
        (DedupBytes.fields (PCPPNativeHierarchyNodes.pcp source k CH Cpad code x)):=by
  unfold RecoveryBoundedColdSuppliers.output
  rw [capacity_eq,backing_eq]
  rfl

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph
