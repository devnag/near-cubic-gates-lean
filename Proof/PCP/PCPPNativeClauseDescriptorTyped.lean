import Proof.PCP.PCPPNativeClauseDescriptorAssembly

/-! The physically assembled bytes are exactly the faithful source's
request for the original circuit, including its required arity/size padding. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptor
open LocalBitMultitape SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem emitted_request (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) :
    emitted a.minimumArity n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native)=
      PCPPNative.descriptor (PCPPRequestBoundary.request a c).circuit := by
  rw [PCPPNative.request_descriptor]
  have hs : PCPPNativeColdMetadata.padded a.minimumArity n c.size=c.size+PCPPRequestBoundary.padding a c := by
    unfold PCPPNativeColdMetadata.padded PCPPNativeColdMetadata.domain PCPPRequestBoundary.padding PCPPRequestBoundary.domain
    omega
  simp only [emitted,hs,PCPPNativeDescriptorTail.emitted,PCPPNativePadding.emitted_nodes n,List.append_assoc]
  rfl

theorem request_run (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) : ∃ result,
    run (machine a.minimumArity) (budget a.minimumArity n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native))
      (input n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native))=some result ∧
    result.steps≤budget a.minimumArity n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native) ∧
    result.final.tapes 26=PCPPNative.descriptor (PCPPRequestBoundary.request a c).circuit ∧
    result.final.heads 26=(PCPPNative.descriptor (PCPPRequestBoundary.request a c).circuit).length ∧
    result.final.heads 10=0 ∧ result.final.tapes 10=List.replicate (PCPPRequestBoundary.request a c).arity true ∧
    result.final.heads 27=0 ∧ result.final.tapes 27=List.replicate (PCPPRequestBoundary.request a c).circuit.size true := by
  have h:=assemble_run a.minimumArity n c.size c.output.val (c.nodes.flatMap PCPPRequestNodeSchema.native)
  rw [emitted_request] at h
  have hs : PCPPNativeColdMetadata.padded a.minimumArity n c.size=(PCPPRequestBoundary.request a c).circuit.size := by
    rw [PCPPRequestBoundary.request_size]
    exact Nat.max_comm _ _
  rw [hs] at h
  exact h

end NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptor
