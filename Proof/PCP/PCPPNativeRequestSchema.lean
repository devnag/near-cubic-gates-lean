import Proof.PCP.PCPPRequestSource

/-! Literal native bytes for the source's actual domain lift and isolated
size padding. The completed source caller consumes exactly this descriptor. -/
namespace NearCubicWires.RepairOrdinary.PCPPNative
open SourceInterfaces RepairRepresentation PCPPRequestBoundary InputLiftedBooleanCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def descriptor {n : ℕ} (c : BooleanCircuit n) : List Bool :=
  PCPPRequestNodeGlobal.payload c.nodes (natWord c.output.val)

theorem descriptor_eq {n : ℕ} (c : BooleanCircuit n) :
    descriptor c=natWord n++natWord c.nodes.length++
      c.nodes.flatMap PCPPRequestNodeSchema.native++natWord c.output.val := by
  simp only [descriptor,PCPPRequestNodeGlobal.payload,DecompositionInputCounts.word,
    PCPPRequestNodeLoop.stream,List.append_assoc]

theorem native_lift {n N : ℕ} (h : n ≤ N) (node : BooleanNode n) :
    PCPPRequestNodeSchema.native (liftBooleanNodeInputs h node)=PCPPRequestNodeSchema.native node := by
  cases node <;> rfl

theorem request_nodes (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) :
    (request a c).circuit.nodes=c.nodes.map (liftBooleanNodeInputs (Nat.le_max_left n a.minimumArity))++
      List.replicate (padding a c) (.const false) := by
  simp only [request,pointwiseRequest,BooleanCircuit.padToArity,BooleanCircuit.padSize,
    BooleanDAGBuilder.finish,BooleanDAGBuilder.appendFalse_nodes,BooleanCircuit.toBuilder,
    lifted,liftBooleanCircuitInputs,padding,domain,BooleanCircuit.size,List.length_map]

theorem request_output (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) :
    (request a c).circuit.output.val=c.output.val := by
  simp only [request,pointwiseRequest,BooleanCircuit.padToArity,BooleanCircuit.padSize,
    BooleanDAGBuilder.finish,BooleanDAGExtension.lift_val,lifted,liftBooleanCircuitInputs]

theorem request_descriptor (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) :
    descriptor (request a c).circuit=
      natWord (domain a n)++natWord (c.size+padding a c)++
      c.nodes.flatMap PCPPRequestNodeSchema.native++
      (List.replicate (padding a c) (PCPPRequestNodeSchema.native (.const false : BooleanNode n))).flatten++
      natWord c.output.val := by
  simp only [descriptor,PCPPRequestNodeGlobal.payload,DecompositionInputCounts.word,
    PCPPRequestNodeLoop.stream,request,pointwiseRequest,BooleanCircuit.padToArity,
    BooleanCircuit.padSize,BooleanDAGBuilder.finish,BooleanDAGBuilder.appendFalse_nodes,
    BooleanCircuit.toBuilder,BooleanDAGExtension.lift_val,lifted,liftBooleanCircuitInputs,
    List.length_append,List.length_map,List.length_replicate,List.flatMap_append,
    List.flatMap_map,native_lift,List.flatMap_replicate,
    padding,domain,BooleanCircuit.size,List.append_assoc]
  rfl

end NearCubicWires.RepairOrdinary.PCPPNative
