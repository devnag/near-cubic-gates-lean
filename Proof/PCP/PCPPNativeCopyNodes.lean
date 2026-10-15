import Proof.PCP.PCPPSubstitutionCircuit

/-! Literal node lists for the native emitter of the already verified DAG.
This exposes the existing semantic construction; it creates no new circuit. -/
namespace NearCubicWires.RepairOrdinary.PCPPNative
open SourceInterfaces PCPPSubstitution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copiedNodes {n r : ℕ} (base : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (count : ℕ) : List (BooleanNode r) :=
  (List.range count).flatMap fun i =>
    let node := (oracle.nodes[i]?).getD (.const false)
    [firstNode projection node,secondNode base i projection node]

theorem copiedNodes_succ {n r : ℕ} (base : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (count : ℕ) (hc : count < oracle.nodes.length) :
    copiedNodes base oracle projection (count+1)=copiedNodes base oracle projection count++
      [firstNode projection oracle.nodes[count],secondNode base count projection oracle.nodes[count]] := by
  simp [copiedNodes,List.range_succ,List.flatMap_append,List.getElem?_eq_getElem hc]

theorem copyPrefix_nodes {n r : ℕ} (prior : BooleanDAGBuilder r) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (count : ℕ) (hc : count ≤ oracle.nodes.length) :
    (copyPrefix prior oracle projection count hc).builder.nodes=
      prior.nodes++copiedNodes prior.nodes.length oracle projection count := by
  induction count with
  | zero => simp [copyPrefix,copiedNodes]
  | succ count ih =>
    simp only [copyPrefix]
    rw [copyNode_nodes,ih,copiedNodes_succ _ _ _ count (by omega),List.append_assoc]

theorem copyOracle_nodes {n r : ℕ} (prior : BooleanDAGBuilder r) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) :
    (copyOracle prior oracle projection).final.nodes=
      prior.nodes++copiedNodes prior.nodes.length oracle projection oracle.size :=
  copyPrefix_nodes prior oracle projection oracle.nodes.length (by omega)

def queryNodes {n r : ℕ} (base : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) :=
  copiedNodes base oracle projection oracle.size++[BooleanNode.not (address base oracle.output.val)]

theorem copyQuery_nodes {n r : ℕ} (prior : BooleanDAGBuilder r) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) :
    (copyQuery prior oracle projection).final.nodes=prior.nodes++queryNodes prior.nodes.length oracle projection := by
  simp only [copyQuery,BooleanDAGBuilder.appendNot,BooleanDAGBuilder.append,
    BooleanDAGBuilder.appendNode_nodes,copyOracle_nodes,queryNodes,List.append_assoc]
  rfl

end NearCubicWires.RepairOrdinary.PCPPNative
