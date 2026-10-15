import Proof.PCP.PCPPSubstitutionQueriesEval

/-! Three shared-reference gates append one compact clause to the running conjunction. -/
namespace NearCubicWires.RepairOrdinary.PCPPSubstitution
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def wireValue {r : ℕ} (builder : BooleanDAGBuilder r) (input : BitInput r)
    (reference : Fin builder.nodes.length) : Bool :=
  (getElem? (builder.values input) reference.val).getD false

theorem extension_value {r : ℕ} {prior final : BooleanDAGBuilder r}
    (extension : BooleanDAGExtension prior final) (input : BitInput r)
    (reference : Fin prior.nodes.length) :
    wireValue final input (extension.lift reference)=wireValue prior input reference :=
  congrArg (fun x : Option Bool => x.getD false) (extension.wireValue_lift input reference)

theorem append_value {r : ℕ} (prior : BooleanDAGBuilder r) (node : BooleanNode r)
    (hwf : node.WellFormedAt prior.nodes.length) (input : BitInput r) :
    wireValue (prior.append node hwf).builder input (prior.append node hwf).output=
      node.eval input (prior.values input) :=
  congrArg (fun x : Option Bool => x.getD false) (prior.appendNode_newest node hwf input)

theorem append_lift_value {r : ℕ} (prior : BooleanDAGBuilder r) (node : BooleanNode r)
    (hwf : node.WellFormedAt prior.nodes.length) (input : BitInput r)
    (reference : Fin prior.nodes.length) :
    wireValue (prior.append node hwf).builder input ((prior.append node hwf).lift reference)=
      wireValue prior input reference :=
  congrArg (fun x : Option Bool => x.getD false) (prior.appendNode_preserves node hwf input reference)

def clauseBlock {r : ℕ} (prior : BooleanDAGBuilder r)
    (refs : Fin 3 → Fin prior.nodes.length) (accumulator : Fin prior.nodes.length) :
    BooleanDAGBuildResult prior 1 :=
  let first := prior.appendOr (refs 0) (refs 1)
  let second := first.builder.appendOr first.output (first.lift (refs 2))
  let third := second.builder.appendAnd (second.lift (first.lift accumulator)) second.output
  { final := third.builder
    extension := (BooleanDAGExtension.single prior (.or (refs 0).val (refs 1).val)
        ⟨(refs 0).isLt,(refs 1).isLt⟩).trans
      ((BooleanDAGExtension.single first.builder (.or first.output.val (first.lift (refs 2)).val)
        ⟨first.output.isLt,(first.lift (refs 2)).isLt⟩).trans
        (BooleanDAGExtension.single second.builder
          (.and (second.lift (first.lift accumulator)).val second.output.val)
          ⟨(second.lift (first.lift accumulator)).isLt,second.output.isLt⟩))
    output := fun _ => third.output }

theorem clauseBlock_length {r : ℕ} (prior : BooleanDAGBuilder r)
    (refs : Fin 3 → Fin prior.nodes.length) (accumulator : Fin prior.nodes.length) :
    (clauseBlock prior refs accumulator).final.nodes.length=prior.nodes.length+3 := by
  simp only [clauseBlock,BooleanDAGBuilder.appendOr,BooleanDAGBuilder.appendAnd,
    BooleanDAGBuilder.append,BooleanDAGBuilder.appendNode_length]

theorem clauseBlock_eval {r : ℕ} (prior : BooleanDAGBuilder r)
    (refs : Fin 3 → Fin prior.nodes.length) (accumulator : Fin prior.nodes.length)
    (input : BitInput r) :
    wireValue (clauseBlock prior refs accumulator).final input
        ((clauseBlock prior refs accumulator).output 0)=
      (wireValue prior input accumulator &&
        (wireValue prior input (refs 0) || wireValue prior input (refs 1) || wireValue prior input (refs 2))) := by
  let first := prior.appendOr (refs 0) (refs 1)
  let second := first.builder.appendOr first.output (first.lift (refs 2))
  have hfirst : wireValue first.builder input first.output=
      (wireValue prior input (refs 0) || wireValue prior input (refs 1)) :=
    append_value prior (.or (refs 0).val (refs 1).val) _ input
  have hsecond : wireValue second.builder input second.output=
      (wireValue first.builder input first.output || wireValue first.builder input (first.lift (refs 2))) :=
    append_value first.builder (.or first.output.val (first.lift (refs 2)).val) _ input
  have hthird : wireValue (clauseBlock prior refs accumulator).final input
      ((clauseBlock prior refs accumulator).output 0)=
      (wireValue second.builder input (second.lift (first.lift accumulator)) &&
        wireValue second.builder input second.output) :=
    append_value second.builder
      (.and (second.lift (first.lift accumulator)).val second.output.val) _ input
  rw [hthird,hsecond,hfirst]
  rw [show wireValue second.builder input (second.lift (first.lift accumulator))=
      wireValue first.builder input (first.lift accumulator) from
        append_lift_value first.builder _ _ input (first.lift accumulator)]
  rw [show wireValue first.builder input (first.lift accumulator)=wireValue prior input accumulator from
    append_lift_value prior _ _ input accumulator]
  rw [show wireValue first.builder input (first.lift (refs 2))=wireValue prior input (refs 2) from
    append_lift_value prior _ _ input (refs 2)]

end NearCubicWires.RepairOrdinary.PCPPSubstitution
