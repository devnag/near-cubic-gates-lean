import Proof.CaseAnalysis.RecoveryLiteralOriginal

/-! Exact original clause stages, without an alternative expression or
graph. These names expose only the existing first/second/OR/third/OR order. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseMeaning
open LocalBitMultitape SourceInterfaces RepairRepresentation BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem references_lift {n : ℕ} {b c : BooleanDAGBuilder n} (e : BooleanDAGExtension b c)
    (values : List (LiveWire b)) :
    RecoveryBoundedLiteral.references (liftLiveWires e values)=RecoveryBoundedLiteral.references values := by
  simp only [RecoveryBoundedLiteral.references,liftLiveWires,List.map_map]
  rfl
theorem reference_lift {n q : ℕ} {b c : BooleanDAGBuilder n} (e : BooleanDAGExtension b c)
    (values : List (LiveWire b)) (hv : values.length=q)
    (hw : (liftLiveWires e values).length=q) (literal : Literal q) :
    RecoveryBoundedLiteral.reference (liftLiveWires e values) hw literal=
      RecoveryBoundedLiteral.reference values hv literal := by
  cases literal <;> simp only [RecoveryBoundedLiteral.reference,literalWire,liftLiveWires,List.getElem_map]
  all_goals rfl

def first {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (clause : Fin 3→Literal q):=compileLiteral b values hv (clause 0)
def second {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (clause : Fin 3→Literal q):=
  let x:=first b values hv clause
  compileLiteral x.compiled.final (liftLiveWires x.compiled.extension values)
    (by rw [liftLiveWires_length];exact hv) (clause 1)
def firstOr {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (clause : Fin 3→Literal q):=
  let x:=first b values hv clause
  let y:=second b values hv clause
  compileOr y.compiled.final (x.live.lift y.compiled.extension) y.live
def third {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (clause : Fin 3→Literal q):=
  let x:=first b values hv clause
  let y:=second b values hv clause
  let z:=firstOr b values hv clause
  compileLiteral z.final (liftLiveWires (x.compiled.extension.trans (y.compiled.extension.trans z.extension)) values)
    (by rw [liftLiveWires_length];exact hv) (clause 2)
def lastOr {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (clause : Fin 3→Literal q):=
  let z:=firstOr b values hv clause
  let t:=third b values hv clause
  compileOr t.compiled.final (z.live.lift t.compiled.extension) t.live

theorem original_final {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (clause : Fin 3→Literal q) :
    (compileClause b values hv clause).compiled.final=(lastOr b values hv clause).final := rfl
theorem original_output {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (clause : Fin 3→Literal q) :
    (compileClause b values hv clause).compiled.output.val=(third b values hv clause).compiled.final.nodes.length := rfl
theorem original_count {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (clause : Fin 3→Literal q) :
    (compileClause b values hv clause).compiled.final.nodes.length=(third b values hv clause).compiled.final.nodes.length+1 := by
  change ((third b values hv clause).compiled.final.nodes++
    ([.or (firstOr b values hv clause).output.val (third b values hv clause).compiled.output.val] : List (BooleanNode n))).length=_
  simp only [List.length_append,List.length_singleton]
theorem or_native {n : ℕ} (b : BooleanDAGBuilder n) (left right : LiveWire b) :
    (compileOr b left right).extension.suffix.flatMap PCPPRequestNodeSchema.native=
      PCPPRequestNodeSchema.native (.or left.output.val right.output.val : BooleanNode n) := by
  change ([_] : List (BooleanNode n)).flatMap PCPPRequestNodeSchema.native=_
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

theorem original_native {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (clause : Fin 3→Literal q) :
    (compileClause b values hv clause).compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native=
      (first b values hv clause).compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native++
      (second b values hv clause).compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native++
      (firstOr b values hv clause).extension.suffix.flatMap PCPPRequestNodeSchema.native++
      (third b values hv clause).compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native++
      (lastOr b values hv clause).extension.suffix.flatMap PCPPRequestNodeSchema.native := by
  change (((first b values hv clause).compiled.extension.suffix++
    ((second b values hv clause).compiled.extension.suffix++
    ((firstOr b values hv clause).extension.suffix++(third b values hv clause).compiled.extension.suffix)))++
    (lastOr b values hv clause).extension.suffix).flatMap PCPPRequestNodeSchema.native=_
  simp only [List.flatMap_append,List.append_assoc]

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseMeaning
