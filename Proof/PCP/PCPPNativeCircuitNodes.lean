import Proof.PCP.PCPPNativeQueryNodes
import Proof.PCP.PCPPNativeClauseNodes

/-! Exact flat query/accumulator/clause sequence for the existing substituted
circuit. Its addresses are bounded counters, not recursively expanded wires. -/
namespace NearCubicWires.RepairOrdinary.PCPPNative
open SourceInterfaces PCPPSubstitution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def literalAddress {n q : ℕ} (oracle : BooleanCircuit n) : Literal q → ℕ
  | .positive j => queryAddress 0 oracle.size oracle.output.val j.val false
  | .negative j => queryAddress 0 oracle.size oracle.output.val j.val true

def substitutedNodes {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (clauses : List (Fin 3 → Literal q)) :=
  queryNodesPrefix 0 oracle projections q++[BooleanNode.const true]++
    clauseStreamNodes (q*(2*oracle.size+1)+1) (q*(2*oracle.size+1)) (literalAddress oracle) clauses

theorem substituted_nodes {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF q) :
    (substituted oracle projections formula).nodes=substitutedNodes oracle projections formula.clauses := by
  let prior := BooleanDAGBuilder.empty r
  let bank := queryBank prior oracle projections
  let initial := bank.appendConst true
  have hnodes : initial.builder.nodes=queryNodesPrefix 0 oracle projections q++[.const true] := by
    simp only [initial,BooleanDAGBuilder.appendConst,BooleanDAGBuilder.append,
      BooleanDAGBuilder.appendNode_nodes,bank,queryBank_nodes,prior,BooleanDAGBuilder.empty,
      List.nil_append,List.length_nil]
  have hlen : initial.builder.nodes.length=q*(2*oracle.size+1)+1 := by
    simp only [initial,BooleanDAGBuilder.appendConst,BooleanDAGBuilder.append,
      BooleanDAGBuilder.appendNode_length,bank,queryBank_length,prior,BooleanDAGBuilder.empty,
      List.length_nil,Nat.zero_add]
  have hacc : initial.output.val=q*(2*oracle.size+1) := by
    simp only [initial,BooleanDAGBuilder.appendConst,BooleanDAGBuilder.append,BooleanDAGBuilder.newest,
      bank,queryBank_length,prior,BooleanDAGBuilder.empty,List.length_nil,Nat.zero_add]
  have href : (fun l : Literal q => (initial.lift (literalRef prior oracle projections l)).val)=
      literalAddress oracle := by
    funext l
    cases l <;> rfl
  change (compileClauses initial.builder
    (fun l => initial.lift (literalRef prior oracle projections l)) initial.output formula.clauses).final.nodes=_
  rw [compileClauses_nodes,href,hacc,hlen,hnodes]
  rfl

theorem substituted_output {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF q) :
    (substituted oracle projections formula).output.val=
      q*(2*oracle.size+1)+3*formula.clauses.length := by
  let prior := BooleanDAGBuilder.empty r
  let bank := queryBank prior oracle projections
  let initial := bank.appendConst true
  have hlen : initial.builder.nodes.length=q*(2*oracle.size+1)+1 := by
    simp only [initial,BooleanDAGBuilder.appendConst,BooleanDAGBuilder.append,
      BooleanDAGBuilder.appendNode_length,bank,queryBank_length,prior,BooleanDAGBuilder.empty,
      List.length_nil,Nat.zero_add]
  have hacc : initial.output.val=q*(2*oracle.size+1) := by
    simp only [initial,BooleanDAGBuilder.appendConst,BooleanDAGBuilder.append,BooleanDAGBuilder.newest,
      bank,queryBank_length,prior,BooleanDAGBuilder.empty,List.length_nil,Nat.zero_add]
  change ((compileClauses initial.builder
    (fun l => initial.lift (literalRef prior oracle projections l)) initial.output formula.clauses).output 0).val=_
  rw [compileClauses_output,hacc,hlen]
  split_ifs with h
  · simp only [h,List.length_nil,Nat.mul_zero,Nat.add_zero]
  · omega

end NearCubicWires.RepairOrdinary.PCPPNative
