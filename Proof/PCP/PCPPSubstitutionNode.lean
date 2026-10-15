import Proof.PCP.PCPPRequestBoundary

/-! Two emitted DAG nodes per original oracle node. The fixed address map
keeps sharing explicit and gives the native emitter a simple exact layout. -/
namespace NearCubicWires.RepairOrdinary.PCPPSubstitution
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def address (base index : ℕ) := base+2*index+1
def firstNode {n r : ℕ} (projection : Fin n → ProjectedRandomBit r) : BooleanNode n → BooleanNode r
  | .input i => match projection i with
    | .bit j => .input j
    | .negatedBit j => .input j
    | .constant b => .const b
  | _ => .const false
def secondNode {n r : ℕ} (base index : ℕ) (projection : Fin n → ProjectedRandomBit r) :
    BooleanNode n → BooleanNode r
  | .const b => .const b
  | .input i => match projection i with
    | .bit j => .input j
    | .negatedBit _ => .not (base+2*index)
    | .constant b => .const b
  | .not j => .not (address base j)
  | .and j k => .and (address base j) (address base k)
  | .or j k => .or (address base j) (address base k)

theorem first_wellFormed {n r : ℕ} (projection : Fin n → ProjectedRandomBit r)
    (node : BooleanNode n) (position : ℕ) : (firstNode projection node).WellFormedAt position := by
  cases node with
  | input i => cases hp : projection i <;> simp [firstNode,hp,BooleanNode.WellFormedAt]
  | _ => trivial

theorem second_wellFormed {n r : ℕ} (base index : ℕ) (projection : Fin n → ProjectedRandomBit r)
    (node : BooleanNode n) (hwf : node.WellFormedAt index) :
    (secondNode base index projection node).WellFormedAt (base+2*index+1) := by
  cases node with
  | const b => trivial
  | input i => cases hp : projection i <;> simp [secondNode,hp,BooleanNode.WellFormedAt]
  | not j => dsimp [secondNode,BooleanNode.WellFormedAt,address] at *; omega
  | and j k => dsimp [secondNode,BooleanNode.WellFormedAt,address] at *; omega
  | or j k => dsimp [secondNode,BooleanNode.WellFormedAt,address] at *; omega

def copyNode {n r : ℕ} (builder : BooleanDAGBuilder r) (base index : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n)
    (hlen : builder.nodes.length=base+2*index) (hwf : node.WellFormedAt index) : BooleanDAGBuilder r :=
  (builder.appendNode (firstNode projection node) (first_wellFormed projection node _)).appendNode
    (secondNode base index projection node) (by
      rw [BooleanDAGBuilder.appendNode_length,hlen]
      exact second_wellFormed base index projection node hwf)

theorem copyNode_nodes {n r : ℕ} (builder : BooleanDAGBuilder r) (base index : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n)
    (hlen : builder.nodes.length=base+2*index) (hwf : node.WellFormedAt index) :
    (copyNode builder base index projection node hlen hwf).nodes=
      builder.nodes++[firstNode projection node,secondNode base index projection node] := by
  simp only [copyNode,BooleanDAGBuilder.appendNode_nodes,List.append_assoc,List.singleton_append]

theorem copyNode_length {n r : ℕ} (builder : BooleanDAGBuilder r) (base index : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n)
    (hlen : builder.nodes.length=base+2*index) (hwf : node.WellFormedAt index) :
    (copyNode builder base index projection node hlen hwf).nodes.length=base+2*(index+1) := by
  rw [copyNode_nodes,List.length_append]
  simp only [List.length_cons,List.length_nil]
  omega

def copyNodeExtension {n r : ℕ} (builder : BooleanDAGBuilder r) (base index : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n)
    (hlen : builder.nodes.length=base+2*index) (hwf : node.WellFormedAt index) :
    BooleanDAGExtension builder (copyNode builder base index projection node hlen hwf) where
  suffix := [firstNode projection node,secondNode base index projection node]
  nodes_eq := copyNode_nodes builder base index projection node hlen hwf

end NearCubicWires.RepairOrdinary.PCPPSubstitution
