import Proof.PCP.PCPPSubstitutionClause

/-! Linear clause compilation over the physically representable shared query DAG. -/
namespace NearCubicWires.RepairOrdinary.PCPPSubstitution
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clauseValue {q : ℕ} (clause : Fin 3 → Literal q) (assignment : BitInput q) : Bool :=
  (clause 0).eval assignment || (clause 1).eval assignment || (clause 2).eval assignment

theorem clauseValue_decide {q : ℕ} (clause : Fin 3 → Literal q) (assignment : BitInput q) :
    clauseValue clause assignment=decide (∃ i,(clause i).eval assignment) := by
  apply Bool.eq_iff_iff.mpr
  simp [clauseValue,Fin.exists_fin_succ,or_assoc]

def compileClauses {r q : ℕ} (prior : BooleanDAGBuilder r)
    (refs : Literal q → Fin prior.nodes.length) (accumulator : Fin prior.nodes.length) :
    List (Fin 3 → Literal q) → BooleanDAGBuildResult prior 1
  | [] => ⟨prior,BooleanDAGExtension.refl prior,fun _ => accumulator⟩
  | clause::tail =>
    let next := clauseBlock prior (fun i => refs (clause i)) accumulator
    let rest := compileClauses next.final (fun literal => next.extension.lift (refs literal))
      (next.output 0) tail
    ⟨rest.final,next.extension.trans rest.extension,rest.output⟩

theorem compileClauses_length {r q : ℕ} (prior : BooleanDAGBuilder r)
    (refs : Literal q → Fin prior.nodes.length) (accumulator : Fin prior.nodes.length)
    (clauses : List (Fin 3 → Literal q)) :
    (compileClauses prior refs accumulator clauses).final.nodes.length=
      prior.nodes.length+3*clauses.length := by
  induction clauses generalizing prior with
  | nil => simp [compileClauses]
  | cons clause tail ih =>
    simp only [compileClauses]
    rw [ih,clauseBlock_length,List.length_cons]
    omega

theorem compileClauses_eval {r q : ℕ} (prior : BooleanDAGBuilder r)
    (refs : Literal q → Fin prior.nodes.length) (accumulator : Fin prior.nodes.length)
    (input : BitInput r) (assignment : BitInput q)
    (hrefs : ∀ literal,wireValue prior input (refs literal)=literal.eval assignment)
    (clauses : List (Fin 3 → Literal q)) :
    wireValue (compileClauses prior refs accumulator clauses).final input
        ((compileClauses prior refs accumulator clauses).output 0)=
      (wireValue prior input accumulator && (ThreeCNF.mk clauses).eval assignment) := by
  induction clauses generalizing prior with
  | nil => simp [compileClauses,ThreeCNF.eval]
  | cons clause tail ih =>
    let next := clauseBlock prior (fun i => refs (clause i)) accumulator
    have hnext : ∀ literal,wireValue next.final input (next.extension.lift (refs literal))=
        literal.eval assignment := by
      intro literal
      exact (extension_value next.extension input (refs literal)).trans (hrefs literal)
    change wireValue (compileClauses next.final _ (next.output 0) tail).final input
      ((compileClauses next.final _ (next.output 0) tail).output 0)=_
    rw [ih _ _ _ hnext]
    rw [show wireValue next.final input (next.output 0)=
        (wireValue prior input accumulator && clauseValue clause assignment) by
      rw [clauseBlock_eval,hrefs,hrefs,hrefs]
      rfl]
    rw [clauseValue_decide]
    simp only [ThreeCNF.eval,List.all_cons,Bool.and_assoc]

end NearCubicWires.RepairOrdinary.PCPPSubstitution
