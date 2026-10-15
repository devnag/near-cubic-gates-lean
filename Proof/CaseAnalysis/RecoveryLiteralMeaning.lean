import Proof.CaseAnalysis.RecoveryLiteralBank

/-! The literal bank's reference, output index and native suffix are exactly
those of the original structural compiler, including the stationary positive case. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteral
open LocalBitMultitape SourceInterfaces RepairRepresentation BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def query {q : ℕ} : Literal q→Fin q
  | .positive j=>j
  | .negative j=>j
def negative {q : ℕ} : Literal q→Bool
  | .positive _=>false
  | .negative _=>true
def references {n : ℕ} {b : BooleanDAGBuilder n} (values : List (LiveWire b)):=values.map (fun w=>w.output.val)
def reference {n q : ℕ} {b : BooleanDAGBuilder n} (values : List (LiveWire b))
    (hlength : values.length=q) (literal : Literal q):=(literalWire values hlength literal).output.val

theorem sourceWord_append (a b : List ℕ) : sourceWord (a++b)=sourceWord a++sourceWord b := by
  induction a with
  | nil=>rfl
  | cons x xs ih=>
    change frame (List.replicate x true)++sourceWord (xs++b)=
      (frame (List.replicate x true)++sourceWord xs)++sourceWord b
    rw [ih,List.append_assoc]

theorem sourceWord_index (refs : List ℕ) (j : ℕ) (hj : j<refs.length) :
    sourceWord refs=sourceWord (refs.take j)++frame (List.replicate refs[j] true)++sourceWord (refs.drop (j+1)) := by
  have ht:=List.take_append_getElem (l:=refs) (i:=j) hj
  have he : refs.take j++[refs[j]]++refs.drop (j+1)=refs := by rw [ht,List.take_append_drop]
  have hs:=congrArg sourceWord he
  rw [sourceWord_append,sourceWord_append] at hs
  change (sourceWord (refs.take j)++(frame (List.replicate refs[j] true)++[]))++sourceWord (refs.drop (j+1))=sourceWord refs at hs
  simpa only [List.append_nil] using hs.symm

theorem reference_at {n q : ℕ} {b : BooleanDAGBuilder n} (values : List (LiveWire b))
    (hlength : values.length=q) (literal : Literal q) :
    (references values)[(query literal).val]'(by simpa only [references,List.length_map,hlength] using (query literal).isLt)=
      reference values hlength literal := by
  cases literal <;> simp only [references,List.getElem_map,query,reference,literalWire]

theorem literal_stream {n q : ℕ} {b : BooleanDAGBuilder n} (values : List (LiveWire b))
    (hlength : values.length=q) (literal : Literal q) :
    sourceWord (references values)=sourceWord ((references values).take (query literal).val)++
      frame (List.replicate (reference values hlength literal) true)++sourceWord ((references values).drop ((query literal).val+1)) := by
  have hi : (query literal).val<(references values).length := by
    simpa only [references,List.length_map,hlength] using (query literal).isLt
  have h:=sourceWord_index (references values) (query literal).val hi
  rw [reference_at values hlength literal] at h
  exact h

theorem original_native {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hlength : values.length=q) (literal : Literal q) :
    (compileLiteral b values hlength literal).compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native=
      if negative literal then PCPPRequestNodeSchema.native (.not (reference values hlength literal) : BooleanNode n) else [] := by
  cases literal
  · rfl
  · simp only [compileLiteral,BuiltWire.ofCompiled,compileNot,LiveWire.stationary,CompiledWire.not,
      BooleanDAGExtension.trans,BooleanDAGExtension.refl,BooleanDAGExtension.single,negative,reference,literalWire,
      List.nil_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,↓reduceIte]

theorem original_output {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hlength : values.length=q) (literal : Literal q) :
    (compileLiteral b values hlength literal).compiled.output.val=
      if negative literal then b.nodes.length else reference values hlength literal := by
  cases literal <;> rfl

theorem original_count {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hlength : values.length=q) (literal : Literal q) :
    (compileLiteral b values hlength literal).compiled.final.nodes.length=b.nodes.length+(negative literal).toNat := by
  cases literal with
  | positive j=>rfl
  | negative j=>
    change (b.nodes++([.not (reference values hlength (.negative j))] : List (BooleanNode n))).length=b.nodes.length+1
    simp only [List.length_append,List.length_singleton]

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteral
