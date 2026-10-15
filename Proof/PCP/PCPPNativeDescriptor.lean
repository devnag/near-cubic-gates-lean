import Proof.PCP.PCPPNativeCircuitNodes
import Proof.PCP.PCPPNativeRequestSchema

/-! Frozen literal output for the physical native substitution emitter. -/
namespace NearCubicWires.RepairOrdinary.PCPPNative
open SourceInterfaces RepairRepresentation PCPPSubstitution PCPPRequestBoundary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSize {q : ℕ} (size : ℕ) (formula : ThreeCNF q) :=
  q*(2*size+1)+3*(RepairSource.compactThreeCNF formula).clauses.length+1
def nativePadding (a : PointwisePCPPAlgorithm) (r size : ℕ) {q : ℕ} (formula : ThreeCNF q) :=
  domain a r-nativeSize size formula
def sourceDescriptor (a : PointwisePCPPAlgorithm) {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF q) :=
  natWord (domain a r)++natWord (nativeSize oracle.size formula+nativePadding a r oracle.size formula)++
    (substitutedNodes oracle projections (RepairSource.compactThreeCNF formula).clauses).flatMap
      PCPPRequestNodeSchema.native++
    (List.replicate (nativePadding a r oracle.size formula)
      (PCPPRequestNodeSchema.native (.const false : BooleanNode r))).flatten++
    natWord (nativeSize oracle.size formula-1)

theorem sourceDescriptor_eq (a : PointwisePCPPAlgorithm) {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF q) :
    descriptor (sourceRequest a oracle projections formula).circuit=
      sourceDescriptor a oracle projections formula := by
  rw [sourceRequest,request_descriptor]
  simp only [compactSubstituted,substituted_output,substituted_size,padding,substituted_nodes,
    sourceDescriptor,nativeSize,nativePadding,Nat.add_sub_cancel]

end NearCubicWires.RepairOrdinary.PCPPNative
