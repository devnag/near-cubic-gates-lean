import Proof.PCP.PCPPSubstitutionCNF

/-! Exact compact projection substitution with a shared guessed-oracle DAG. -/
namespace NearCubicWires.RepairOrdinary.PCPPSubstitution
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def substituted {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF q) : BooleanCircuit r :=
  let prior := BooleanDAGBuilder.empty r
  let bank := queryBank prior oracle projections
  let initial := bank.appendConst true
  let compiled := compileClauses initial.builder
    (fun literal => initial.lift (literalRef prior oracle projections literal)) initial.output formula.clauses
  compiled.final.finish (compiled.output 0)

theorem substituted_size {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF q) :
    (substituted oracle projections formula).size=q*(2*oracle.size+1)+3*formula.clauses.length+1 := by
  unfold substituted
  rw [BooleanDAGBuilder.finish_size,compileClauses_length]
  simp only [BooleanDAGBuilder.appendConst,BooleanDAGBuilder.append,
    BooleanDAGBuilder.appendNode_length,queryBank_length,BooleanDAGBuilder.empty,List.length_nil,Nat.zero_add]
  omega

theorem substituted_eval {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF q) (input : BitInput r) :
    (substituted oracle projections formula).eval input=
      formula.eval (fun j => oracle.eval (fun i => (projections j i).eval input)) := by
  let prior := BooleanDAGBuilder.empty r
  let bank := queryBank prior oracle projections
  let initial := bank.appendConst true
  have hrefs : ∀ literal,wireValue initial.builder input
      (initial.lift (literalRef prior oracle projections literal))=
      literal.eval (fun j => oracle.eval (fun i => (projections j i).eval input)) := by
    intro literal
    exact (append_lift_value bank (.const true) trivial input _).trans
      (literalRef_eval prior oracle projections input literal)
  have he := compileClauses_eval initial.builder
    (fun literal => initial.lift (literalRef prior oracle projections literal)) initial.output
    input (fun j => oracle.eval (fun i => (projections j i).eval input)) hrefs formula.clauses
  have hinitial : wireValue initial.builder input initial.output=true :=
    append_value bank (.const true) trivial input
  rw [hinitial,Bool.true_and] at he
  exact he

def compactSubstituted {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF q) : BooleanCircuit r :=
  substituted oracle projections (RepairSource.compactThreeCNF formula)

theorem compactSubstituted_eval {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF q) (input : BitInput r) :
    (compactSubstituted oracle projections formula).eval input=
      formula.eval (fun j => oracle.eval (fun i => (projections j i).eval input)) := by
  rw [compactSubstituted,substituted_eval,RepairSource.compactThreeCNF_eval]

theorem compactSubstituted_size {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF q) :
    (compactSubstituted oracle projections formula).size≤q*(2*oracle.size+1)+3*(2*q)^3+1 := by
  rw [compactSubstituted,substituted_size]
  have h := RepairSource.compactThreeCNF_clauses formula
  omega

end NearCubicWires.RepairOrdinary.PCPPSubstitution
