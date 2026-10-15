import Proof.PCP.PCPPNativeNodeLoop

/-! Identify the bytes returned by the executed original-node loop with
the native encoding of the exact copied shared-DAG node list. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeLoop
open SourceInterfaces PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem emitted_zipIdx {n r : ℕ} (base index : ℕ) (projection : Fin n → ProjectedRandomBit r)
    (nodes : List (BooleanNode n)) :
    emitted base index projection nodes=(nodes.zipIdx index).flatMap fun p => emittedNode base p.2 projection p.1 := by
  induction nodes generalizing index with
  | nil => rfl
  | cons node nodes ih =>
    simp only [emitted,List.zipIdx_cons,List.flatMap_cons,ih]

theorem zipIdx_range {n : ℕ} (nodes : List (BooleanNode n)) :
    nodes.zipIdx=(List.range nodes.length).map fun i => ((nodes[i]?).getD (.const false),i) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < nodes.length := by simpa only [List.length_zipIdx] using hi
    simp only [List.getElem_zipIdx,List.getElem_map,List.getElem_range,List.getElem?_eq_getElem h,Option.getD_some,Nat.zero_add]

theorem emitted_copiedNodes {n r : ℕ} (base : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) :
    emitted base 0 projection oracle.nodes=
      (PCPPNative.copiedNodes base oracle projection oracle.size).flatMap PCPPRequestNodeSchema.native := by
  rw [emitted_zipIdx,zipIdx_range,List.flatMap_map]
  simp only [PCPPNative.copiedNodes,List.flatMap_assoc]
  congr 1
  funext i
  simp only [emittedNode,List.flatMap_cons,List.flatMap_nil,List.append_nil]

end NearCubicWires.RepairOrdinary.PCPPNativeNodeLoop
