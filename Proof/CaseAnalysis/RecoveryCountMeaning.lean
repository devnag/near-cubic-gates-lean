import Proof.CaseAnalysis.RecoveryCountConjunctionRun

/-! The exact fixed-count AND and outer count-case recursion. Each spine
records the original compiler; no alternative graph or description is used. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCounts
open SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
open RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {machine : TimedDecisionMachine} {timeBound : ℕ→ℕ}
variable (pcp : ProjectionPCP machine timeBound) {n bound : ℕ} (x : BitInput n)

theorem rows_output_succ (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (count : ℕ) (hc : count≤bound) (rows : List (BitInput (pcp.nativeWidth n))) :
    (compileVerifierRows pcp x count hc b rows).output.val+1=
      (compileVerifierRows pcp x count hc b rows).final.nodes.length := by
  cases rows with
  | nil=>rw [RecoveryBoundedRows.nil_output,RecoveryBoundedRows.nil_nodes,List.length_append,List.length_singleton]
  | cons r rows=>rw [RecoveryBoundedRows.cons_output,RecoveryBoundedRows.cons_nodes,List.length_append,List.length_singleton]

theorem fixed_nodes (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound)) (count : Fin bound) :
    let grammar:=compileExpr b (fixedCountGrammarExpr (n:=pcp.nativeWidth n) count)
    let rows:=compileVerifierRows pcp x (count.val+1) (by omega) grammar.final (allRandomness (pcp.nativeWidth n))
    (compileFixedCount pcp x b count).final.nodes=rows.final.nodes++[.and grammar.output.val rows.output.val] := rfl

theorem fixed_output (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound)) (count : Fin bound) :
    let grammar:=compileExpr b (fixedCountGrammarExpr (n:=pcp.nativeWidth n) count)
    let rows:=compileVerifierRows pcp x (count.val+1) (by omega) grammar.final (allRandomness (pcp.nativeWidth n))
    (compileFixedCount pcp x b count).output.val=rows.final.nodes.length := rfl

theorem fixed_rows_bound (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (count : Fin bound) (G : ℕ) (h : (compileFixedCount pcp x b count).final.nodes.length≤G) :
    (compileVerifierRows pcp x (count.val+1) (by omega)
      (compileExpr b (fixedCountGrammarExpr (n:=pcp.nativeWidth n) count)).final
      (allRandomness (pcp.nativeWidth n))).final.nodes.length≤G := by
  rw [fixed_nodes,List.length_append,List.length_singleton] at h
  omega

theorem fixed_output_succ (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound)) (count : Fin bound) :
    (compileFixedCount pcp x b count).output.val+1=(compileFixedCount pcp x b count).final.nodes.length := by
  rw [fixed_output,fixed_nodes,List.length_append,List.length_singleton]

theorem nil_nodes (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound)) :
    (compileCountCases pcp x b []).final.nodes=b.nodes++[.const false] := rfl

theorem nil_output (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound)) :
    (compileCountCases pcp x b []).output.val=b.nodes.length := rfl

theorem cons_nodes (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (count : Fin bound) (rest : List (Fin bound)) :
    let head:=compileFixedCount pcp x b count
    let tail:=compileCountCases pcp x head.final rest
    (compileCountCases pcp x b (count::rest)).final.nodes=tail.final.nodes++[.or head.output.val tail.output.val] := rfl

theorem cons_output (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (count : Fin bound) (rest : List (Fin bound)) :
    (compileCountCases pcp x b (count::rest)).output.val=
      (compileCountCases pcp x (compileFixedCount pcp x b count).final rest).final.nodes.length := rfl

theorem tail_bound (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (count : Fin bound) (rest : List (Fin bound)) (G : ℕ)
    (h : (compileCountCases pcp x b (count::rest)).final.nodes.length≤G) :
    (compileCountCases pcp x (compileFixedCount pcp x b count).final rest).final.nodes.length≤G := by
  rw [cons_nodes,List.length_append,List.length_singleton] at h
  omega

theorem head_bound (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (count : Fin bound) (rest : List (Fin bound)) (G : ℕ)
    (h : (compileCountCases pcp x b (count::rest)).final.nodes.length≤G) :
    (compileFixedCount pcp x b count).final.nodes.length≤G :=
  (compileCountCases pcp x _ rest).extension.length_le.trans (tail_bound pcp x b count rest G h)

def anySuffix {q : ℕ} (base : ℕ) : List ℕ→List (BooleanNode q)
  | []=>[.const false]
  | ref::refs=>anySuffix base refs++[.or ref (base+refs.length)]

theorem anySuffix_length {q : ℕ} (base : ℕ) (refs : List ℕ) :
    (anySuffix (q:=q) base refs).length=refs.length+1 := by
  induction refs with
  | nil=>rfl
  | cons ref refs ih=>simp only [anySuffix,List.length_append,ih,List.length_cons,List.length_nil]

theorem anySuffix_reverse {q : ℕ} (base : ℕ) (refs : List ℕ) :
    anySuffix (q:=q) base refs=[BooleanNode.const false]++foldNodes false base refs.reverse := by
  induction refs with
  | nil=>rfl
  | cons ref refs ih=>
    rw [anySuffix,ih,List.reverse_cons,foldNodes_append]
    simp [foldNodes]

inductive Spine : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound) → List (Fin bound) →
    BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound) → List ℕ → Prop
  | nil (b) : Spine b [] b []
  | cons (b count rest next refs) :
      Spine (compileFixedCount pcp x b count).final rest next refs →
      Spine b (count::rest) next ((compileFixedCount pcp x b count).output.val::refs)

theorem Spine.append {b c d : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound)}
    {counts rest : List (Fin bound)} {refs saved : List ℕ}
    (h : Spine pcp x b counts c refs) (g : Spine pcp x c rest d saved) :
    Spine pcp x b (counts++rest) d (refs++saved) := by
  induction h with
  | nil=>exact g
  | cons b count cs next refs h ih=>exact .cons b count (cs++rest) d (refs++saved) (ih g)

theorem Spine.original {b c : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound)}
    {counts : List (Fin bound)} {refs : List ℕ} (h : Spine pcp x b counts c refs) :
    (compileCountCases pcp x b counts).final.nodes=c.nodes++anySuffix c.nodes.length refs ∧
    (compileCountCases pcp x b counts).output.val=c.nodes.length+refs.length := by
  induction h with
  | nil=>exact ⟨rfl,rfl⟩
  | cons b count rest next refs h ih=>
    constructor
    · rw [cons_nodes,ih.2,ih.1]
      simp only [anySuffix,List.append_assoc]
    · rw [cons_output,ih.1,List.length_append,anySuffix_length,List.length_cons]

end NearCubicWires.RepairOrdinary.RecoveryBoundedCounts
