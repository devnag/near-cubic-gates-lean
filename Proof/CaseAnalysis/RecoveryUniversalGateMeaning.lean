import Proof.CaseAnalysis.RecoveryTagReferenceAppend

/-! The literal original three native operations have consecutive actual
outputs. Their tag references can be framed directly while incrementing the
existing counter; three additional saved scalar tapes are unnecessary. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalGates
open SourceInterfaces FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem original_three {n : ℕ} (b : BooleanDAGBuilder n) (left right : LiveWire b) :
    let negated:=compileNot b left
    let conjunction:=compileAnd negated.final (left.lift negated.extension) (right.lift negated.extension)
    let disjunction:=compileOr conjunction.final
      ((left.lift negated.extension).lift conjunction.extension) ((right.lift negated.extension).lift conjunction.extension)
    negated.output.val=b.nodes.length ∧ conjunction.output.val=b.nodes.length+1 ∧
    disjunction.output.val=b.nodes.length+2 ∧ disjunction.final.nodes.length=b.nodes.length+3 ∧
    (negated.extension.trans (conjunction.extension.trans disjunction.extension)).suffix=
      [.not left.output.val,.and left.output.val right.output.val,.or left.output.val right.output.val] := by
  dsimp only
  refine ⟨rfl,?_,?_,?_,rfl⟩
  · change (b.nodes++[BooleanNode.not left.output.val]).length=b.nodes.length+1
    simp only [List.length_append,List.length_singleton]
  · change ((b.nodes++[BooleanNode.not left.output.val])++[BooleanNode.and left.output.val right.output.val]).length=b.nodes.length+2
    simp only [List.length_append,List.length_singleton]
  · change (((b.nodes++[BooleanNode.not left.output.val])++[BooleanNode.and left.output.val right.output.val])++
      [BooleanNode.or left.output.val right.output.val]).length=b.nodes.length+3
    simp only [List.length_append,List.length_singleton]

theorem original_tag_references {n : ℕ} (b : BooleanDAGBuilder n) (left right : LiveWire b)
    (constant input : ℕ) (hb : input+1=b.nodes.length) :
    let negated:=compileNot b left
    let conjunction:=compileAnd negated.final (left.lift negated.extension) (right.lift negated.extension)
    let disjunction:=compileOr conjunction.final
      ((left.lift negated.extension).lift conjunction.extension) ((right.lift negated.extension).lift conjunction.extension)
    [constant,input,negated.output.val,conjunction.output.val,disjunction.output.val]=
      [constant,input,input+1,input+2,input+3] := by
  have h:=original_three b left right
  dsimp only at h ⊢
  rw [h.1,h.2.1,h.2.2.1,←hb]

end NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalGates
