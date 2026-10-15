import Proof.CaseAnalysis.RecoveryClauseBody
import Proof.Amplification.RecoveryBoundedNativeFoldMeaning

/-! Only the original compileClauses recursion is exposed. Its forward
clause suffixes and saved outputs will feed the existing reverse AND fold. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseList
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word {q : ℕ} (clauses : List (Fin 3→Literal q)):=clauses.flatMap RecoveryBoundedClauseRun.word
def stackWord (refs : List ℕ):=refs.flatMap (fun ref=>(frame (List.replicate ref true)).reverse)

theorem allSuffix_length {n : ℕ} (base : ℕ) (refs : List ℕ) :
    (allSuffix (n:=n) base refs).length=refs.length+1 := by
  induction refs with
  | nil=>rfl
  | cons ref refs ih=>simp only [allSuffix,List.length_append,ih,List.length_cons,List.length_nil]

theorem nil_nodes {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b)) (hv : values.length=q) :
    (compileClauses b values hv []).final.nodes=b.nodes++[.const true] := rfl
theorem nil_output {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b)) (hv : values.length=q) :
    (compileClauses b values hv []).output.val=b.nodes.length := rfl

theorem cons_nodes {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b)) (hv : values.length=q)
    (clause : Fin 3→Literal q) (clauses : List (Fin 3→Literal q)) :
    let head:=compileClause b values hv clause
    let lifted:=liftLiveWires head.compiled.extension values
    let hl : lifted.length=q:=by rw [liftLiveWires_length];exact hv
    let tail:=compileClauses head.compiled.final lifted hl clauses
    (compileClauses b values hv (clause::clauses)).final.nodes=
      tail.final.nodes++[.and head.compiled.output.val tail.output.val] := rfl
theorem cons_output {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b)) (hv : values.length=q)
    (clause : Fin 3→Literal q) (clauses : List (Fin 3→Literal q)) :
    let head:=compileClause b values hv clause
    let lifted:=liftLiveWires head.compiled.extension values
    let hl : lifted.length=q:=by rw [liftLiveWires_length];exact hv
    let tail:=compileClauses head.compiled.final lifted hl clauses
    (compileClauses b values hv (clause::clauses)).output.val=tail.final.nodes.length := rfl

theorem tail_bound {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b)) (hv : values.length=q)
    (clause : Fin 3→Literal q) (clauses : List (Fin 3→Literal q)) (W : ℕ)
    (h : (compileClauses b values hv (clause::clauses)).final.nodes.length ≤ W) :
    let head:=compileClause b values hv clause
    let lifted:=liftLiveWires head.compiled.extension values
    let hl : lifted.length=q:=by rw [liftLiveWires_length];exact hv
    (compileClauses head.compiled.final lifted hl clauses).final.nodes.length ≤ W := by
  rw [cons_nodes,List.length_append,List.length_singleton] at h
  omega
theorem head_bound {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b)) (hv : values.length=q)
    (clause : Fin 3→Literal q) (clauses : List (Fin 3→Literal q)) (W : ℕ)
    (h : (compileClauses b values hv (clause::clauses)).final.nodes.length ≤ W) :
    (compileClause b values hv clause).compiled.final.nodes.length ≤ W := by
  exact (compileClauses _ _ _ clauses).extension.length_le.trans (tail_bound b values hv clause clauses W h)
theorem third_bound {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b)) (hv : values.length=q)
    (clause : Fin 3→Literal q) (W : ℕ)
    (h : (compileClause b values hv clause).compiled.final.nodes.length ≤ W) :
    (RecoveryBoundedClauseMeaning.third b values hv clause).compiled.output.val ≤ W := by
  have ht:=(RecoveryBoundedClauseMeaning.third b values hv clause).compiled.output.isLt
  rw [RecoveryBoundedClauseMeaning.original_count] at h
  omega

theorem suffix_eq {n : ℕ} {b c final : BooleanDAGBuilder n} (e : BooleanDAGExtension b c)
    (original : BooleanDAGExtension b final) (refs : List ℕ)
    (hn : final.nodes=c.nodes++allSuffix c.nodes.length refs) :
    original.suffix=e.suffix++allSuffix c.nodes.length refs := by
  apply List.append_cancel_left (as:=b.nodes)
  rw [←original.nodes_eq,←List.append_assoc,←e.nodes_eq]
  exact hn

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseList
