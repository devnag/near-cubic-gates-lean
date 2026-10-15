import Proof.PCP.PCPPSubstitutionNodeEval

/-! Topological prefix copying for one projected oracle DAG. Every prefix
has its exact two-nodes-per-source-node length and preserves old wires. -/
namespace NearCubicWires.RepairOrdinary.PCPPSubstitution
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure CopyPrefixResult {r : ℕ} (prior : BooleanDAGBuilder r) (count : ℕ) where
  builder : BooleanDAGBuilder r
  length : builder.nodes.length=prior.nodes.length+2*count
  extension : BooleanDAGExtension prior builder

def copyPrefix {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) :
    (count : ℕ) → count ≤ circuit.nodes.length → CopyPrefixResult prior count
  | 0,_ => ⟨prior,by omega,BooleanDAGExtension.refl prior⟩
  | count+1,hcount =>
    let previous := copyPrefix prior circuit projection count (by omega)
    let node := circuit.nodes[count]'(by omega)
    let hwf := circuit.wellFormed ⟨count,by omega⟩
    ⟨copyNode previous.builder prior.nodes.length count projection node previous.length hwf,
      copyNode_length previous.builder prior.nodes.length count projection node previous.length hwf,
      previous.extension.trans (copyNodeExtension previous.builder prior.nodes.length count projection node previous.length hwf)⟩

def originalValues {n : ℕ} (circuit : BooleanCircuit n) (input : BitInput n) (count : ℕ) :=
  (circuit.nodes.take count).foldl (fun values node => values.push (node.eval input values)) (#[] : Array Bool)

theorem originalValues_size {n : ℕ} (circuit : BooleanCircuit n) (input : BitInput n) (count : ℕ)
    (hcount : count ≤ circuit.nodes.length) : (originalValues circuit input count).size=count := by
  have fold_size (nodes : List (BooleanNode n)) (initial : Array Bool) :
      (nodes.foldl (fun values node => values.push (node.eval input values)) initial).size=initial.size+nodes.length := by
    induction nodes generalizing initial with
    | nil => simp
    | cons node nodes ih => simp only [List.foldl_cons,ih,Array.size_push,List.length_cons]; omega
  simp only [originalValues,fold_size,Array.size_empty,Nat.zero_add,List.length_take,Nat.min_eq_left hcount]

theorem originalValues_step {n : ℕ} (circuit : BooleanCircuit n) (input : BitInput n) (count : ℕ)
    (hcount : count < circuit.nodes.length) :
    originalValues circuit input (count+1)=
      (originalValues circuit input count).push (circuit.nodes[count].eval input (originalValues circuit input count)) := by
  simp only [originalValues,List.take_succ_eq_append_getElem hcount,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem originalValues_whole {n : ℕ} (circuit : BooleanCircuit n) (input : BitInput n) :
    originalValues circuit input circuit.nodes.length=circuit.values input := by
  simp only [originalValues,List.take_length,BooleanCircuit.values]

end NearCubicWires.RepairOrdinary.PCPPSubstitution
