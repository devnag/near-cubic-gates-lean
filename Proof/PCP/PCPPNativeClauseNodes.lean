import Proof.PCP.PCPPNativeCopyNodes

namespace NearCubicWires.RepairOrdinary.PCPPNative
open SourceInterfaces PCPPSubstitution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clauseNodes {r : ℕ} (base accumulator : ℕ) (refs : Fin 3 → ℕ) : List (BooleanNode r) :=
  [.or (refs 0) (refs 1),.or base (refs 2),.and accumulator (base+1)]

theorem clauseBlock_nodes {r : ℕ} (prior : BooleanDAGBuilder r)
    (refs : Fin 3 → Fin prior.nodes.length) (accumulator : Fin prior.nodes.length) :
    (clauseBlock prior refs accumulator).final.nodes=
      prior.nodes++clauseNodes prior.nodes.length accumulator.val (fun i => (refs i).val) := by
  simp only [clauseBlock,BooleanDAGBuilder.appendOr,BooleanDAGBuilder.appendAnd,
    BooleanDAGBuilder.append,BooleanDAGBuilder.appendNode_nodes,BooleanDAGBuilder.newest,
    BooleanDAGBuilder.liftRef_val,clauseNodes,List.append_assoc,List.cons_append,List.nil_append,
    List.length_append,List.length_cons,List.length_nil]

theorem clauseBlock_output {r : ℕ} (prior : BooleanDAGBuilder r)
    (refs : Fin 3 → Fin prior.nodes.length) (accumulator : Fin prior.nodes.length) :
    ((clauseBlock prior refs accumulator).output 0).val=prior.nodes.length+2 := by
  simp only [clauseBlock,BooleanDAGBuilder.appendOr,BooleanDAGBuilder.appendAnd,
    BooleanDAGBuilder.append,BooleanDAGBuilder.newest,BooleanDAGBuilder.appendNode_length]

def clauseStreamNodes {r q : ℕ} (base accumulator : ℕ) (refs : Literal q → ℕ) :
    List (Fin 3 → Literal q) → List (BooleanNode r)
  | [] => []
  | clause::tail => clauseNodes base accumulator (fun i => refs (clause i))++
      clauseStreamNodes (base+3) (base+2) refs tail

theorem compileClauses_nodes {r q : ℕ} (prior : BooleanDAGBuilder r)
    (refs : Literal q → Fin prior.nodes.length) (accumulator : Fin prior.nodes.length)
    (clauses : List (Fin 3 → Literal q)) :
    (compileClauses prior refs accumulator clauses).final.nodes=
      prior.nodes++clauseStreamNodes prior.nodes.length accumulator.val (fun l => (refs l).val) clauses := by
  induction clauses generalizing prior with
  | nil => simp [compileClauses,clauseStreamNodes]
  | cons clause tail ih =>
    simp only [compileClauses]
    rw [ih]
    simp only [BooleanDAGExtension.lift_val,clauseBlock_output]
    rw [clauseBlock_length,clauseBlock_nodes]
    simp only [clauseStreamNodes,List.append_assoc]

theorem compileClauses_output {r q : ℕ} (prior : BooleanDAGBuilder r)
    (refs : Literal q → Fin prior.nodes.length) (accumulator : Fin prior.nodes.length)
    (clauses : List (Fin 3 → Literal q)) :
    ((compileClauses prior refs accumulator clauses).output 0).val=
      if clauses=[] then accumulator.val else prior.nodes.length+3*clauses.length-1 := by
  induction clauses generalizing prior with
  | nil => rfl
  | cons clause tail ih =>
    simp only [compileClauses]
    rw [ih,clauseBlock_output,clauseBlock_length]
    simp only [List.cons_ne_nil,reduceIte,List.length_cons]
    split_ifs <;> simp_all only [List.length_nil] <;> omega

end NearCubicWires.RepairOrdinary.PCPPNative
