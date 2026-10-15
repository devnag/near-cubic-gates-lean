import Proof.CaseAnalysis.RecoveryGrammarFoldRowRun

/-! Concrete row states retain the original builder's graph and a list
of emitted references. These identities only normalize the checked graph. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape RecoveryRootRound SourceInterfaces RepairRepresentation
open FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def graphWord {n : ℕ} (pre : List Bool) (b : BooleanDAGBuilder n):=
  pre++b.nodes.flatMap PCPPRequestNodeSchema.native
def saved (pre : List Bool) (refs : List ℕ):=pre++RecoveryBoundedNativeUnaryLoop.stackWords refs
def originalState {n : ℕ} (fields : Fin 78→List Bool) (b : BooleanDAGBuilder n)
    (graphPre stackPre packet : List Bool) (refs : List ℕ) : RowState:=
  ⟨fields,b.nodes.length,graphWord graphPre b,saved stackPre refs,packet⟩

theorem graphWord_extension {n : ℕ} {b c : BooleanDAGBuilder n} (e : BooleanDAGExtension b c)
    (pre : List Bool) : graphWord pre b++e.suffix.flatMap PCPPRequestNodeSchema.native=graphWord pre c := by
  simp only [graphWord,e.nodes_eq,List.flatMap_append,List.append_assoc]
theorem saved_push (pre : List Bool) (refs : List ℕ) (ref : ℕ) :
    pushed ref (saved pre refs)=saved pre (refs++[ref]) := by
  simp only [pushed,saved,RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_append,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
theorem saved_append (pre : List Bool) (refs extra : List ℕ) :
    saved pre refs++RecoveryBoundedNativeUnaryLoop.stackWords extra=saved pre (refs++extra) := by
  simp only [saved,RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_append,List.append_assoc]

theorem saved_length (W : ℕ) (pre : List Bool) (refs : List ℕ) (h : ∀ ref∈refs,ref≤W) :
    (saved pre refs).length≤pre.length+refs.length*(2*W+1) := by
  have hh : (RecoveryBoundedNativeUnaryLoop.stackWords refs).length≤refs.length*(2*W+1) := by
    induction refs with
    | nil=>simp [RecoveryBoundedNativeUnaryLoop.stackWords]
    | cons ref refs ih=>
      have hr:=h ref (by simp)
      have ht:=ih (by intro r hm;exact h r (by simp [hm]))
      dsimp only [RecoveryBoundedNativeUnaryLoop.stackWords] at ht
      simp only [RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_cons,List.length_append,
        List.length_reverse,frame_length,List.length_replicate,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  simpa only [saved,List.length_append] using Nat.add_le_add_left hh pre.length

theorem original_expression {n : ℕ} (b : BooleanDAGBuilder n) (e : BoolExpr n)
    (graphPre stackPre packet : List Bool) (refs : List ℕ) (fields : Fin 78→List Bool) :
    expressionState b e (graphWord graphPre b) (saved stackPre refs) packet fields=
      originalState fields (compileExpr b e).final graphPre stackPre packet
        (refs++[(compileExpr b e).output.val]) := by
  unfold expressionState originalState
  rw [graphWord_extension,saved_push]

structure ValidReferences {n : ℕ} (b : BooleanDAGBuilder n) (refs : List ℕ) (W : ℕ) : Prop where
  count : refs.length≤b.nodes.length
  values : ∀ ref∈refs,ref≤W

theorem ValidReferences.after {n W : ℕ} {b : BooleanDAGBuilder n} {refs : List ℕ}
    (h : ValidReferences b refs W) (e : BoolExpr n)
    (hg : (compileExpr b e).final.nodes.length≤W) :
    ValidReferences (compileExpr b e).final (refs++[(compileExpr b e).output.val]) W := by
  constructor
  · have hn:=nodeCount_pos e
    have hc:=h.count
    rw [List.length_append,List.length_singleton,compileExpr_length]
    omega
  · intro ref hr
    simp only [List.mem_append,List.mem_singleton] at hr
    rcases hr with hr|rfl
    · exact h.values ref hr
    · exact Nat.le_of_lt ((compileExpr b e).output.isLt.trans_le hg)

theorem ValidReferences.support {n W G S : ℕ} {b : BooleanDAGBuilder n} {refs : List ℕ}
    (h : ValidReferences b refs W) (pre : List Bool) (hg : b.nodes.length≤G) (gw : G≤W)
    (hs : pre.length+W*(2*W+1)≤S) : (saved pre refs).length≤S := by
  have hh:=saved_length W pre refs h.values
  have hc:=h.count
  have hm:=Nat.mul_le_mul_right (2*W+1) (show refs.length≤W by omega)
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
