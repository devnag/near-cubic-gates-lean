import Proof.PCP.PCPPSubstitutionNode

/-! Literal semantics of the two-node copy, preserving every existing DAG
wire and returning exactly the projected original node value. -/
namespace NearCubicWires.RepairOrdinary.PCPPSubstitution
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem second_eval {n r : ℕ} (builder : BooleanDAGBuilder r) (base index : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n)
    (hlen : builder.nodes.length=base+2*index) (hwf : node.WellFormedAt index)
    (input : BitInput r) (original : Array Bool)
    (href : ∀ j,j < index → (builder.values input)[address base j]?=original[j]?) :
    (secondNode base index projection node).eval input
      ((builder.appendNode (firstNode projection node) (first_wellFormed projection node _)).values input)=
      node.eval (fun i => (projection i).eval input) original := by
  let first := builder.appendNode (firstNode projection node) (first_wellFormed projection node _)
  have hold (j : ℕ) (hj : j < index) : (first.values input)[address base j]?=original[j]? := by
    have hb : address base j < builder.nodes.length := by unfold address; omega
    exact (builder.appendNode_preserves _ _ input ⟨address base j,hb⟩).trans (href j hj)
  have hnew : (first.values input)[base+2*index]?=some ((firstNode projection node).eval input (builder.values input)) := by
    have h := builder.appendNode_newest (firstNode projection node) (first_wellFormed projection node _) input
    simpa only [BooleanDAGBuilder.newest,hlen] using h
  change (secondNode base index projection node).eval input (first.values input)=_
  cases node with
  | const b => rfl
  | input i =>
    cases hp : projection i with
    | bit j => simp only [secondNode,hp,BooleanNode.eval,ProjectedRandomBit.eval]
    | negatedBit j =>
      simp only [secondNode,hp,BooleanNode.eval,hnew,Option.getD_some,firstNode,ProjectedRandomBit.eval]
    | constant b => simp only [secondNode,hp,BooleanNode.eval,ProjectedRandomBit.eval]
  | not j =>
    simp only [secondNode,BooleanNode.eval]
    rw [hold j hwf]
  | and j k =>
    simp only [secondNode,BooleanNode.eval]
    rw [hold j hwf.1,hold k hwf.2]
  | or j k =>
    simp only [secondNode,BooleanNode.eval]
    rw [hold j hwf.1,hold k hwf.2]

theorem copyNode_eval {n r : ℕ} (builder : BooleanDAGBuilder r) (base index : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n)
    (hlen : builder.nodes.length=base+2*index) (hwf : node.WellFormedAt index)
    (input : BitInput r) (original : Array Bool)
    (href : ∀ j,j < index → (builder.values input)[address base j]?=original[j]?) :
    ((copyNode builder base index projection node hlen hwf).values input)[address base index]?=
      some (node.eval (fun i => (projection i).eval input) original) := by
  unfold copyNode
  have h := (builder.appendNode (firstNode projection node) (first_wellFormed projection node _)).appendNode_newest
    (secondNode base index projection node) (by rw [BooleanDAGBuilder.appendNode_length,hlen]; exact second_wellFormed _ _ _ _ hwf) input
  rw [second_eval builder base index projection node hlen hwf input original href] at h
  simpa only [BooleanDAGBuilder.newest,BooleanDAGBuilder.appendNode_length,hlen,address] using h

end NearCubicWires.RepairOrdinary.PCPPSubstitution
