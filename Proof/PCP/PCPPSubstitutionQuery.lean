import Proof.PCP.PCPPSubstitutionCopyEval

/-! One projected oracle copy exposes shared positive and negative query
wires. All later clause occurrences refer to these same two addresses. -/
namespace NearCubicWires.RepairOrdinary.PCPPSubstitution
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copyQuery {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) : BooleanDAGBuildResult prior 2 :=
  let copied := copyOracle prior circuit projection
  let negative := copied.final.appendNot (copied.output 0)
  { final := negative.builder
    extension := copied.extension.trans (BooleanDAGExtension.single copied.final
      (.not (copied.output 0).val) (copied.output 0).isLt)
    output := fun i => if i.val=0 then negative.lift (copied.output 0) else negative.output }

theorem copyQuery_length {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) :
    (copyQuery prior circuit projection).final.nodes.length=prior.nodes.length+(2*circuit.size+1) := by
  simp only [copyQuery,BooleanDAGBuilder.appendNot,BooleanDAGBuilder.append,
    BooleanDAGBuilder.appendNode_length,copyOracle_length]
  omega

theorem copyQuery_positive_index {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) :
    ((copyQuery prior circuit projection).output 0).val=address prior.nodes.length circuit.output.val := rfl

theorem copyQuery_negative_index {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) :
    ((copyQuery prior circuit projection).output 1).val=prior.nodes.length+2*circuit.size :=
  copyOracle_length prior circuit projection

theorem copyQuery_positive {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (input : BitInput r) :
    (getElem? ((copyQuery prior circuit projection).final.values input)
      ((copyQuery prior circuit projection).output 0).val).getD false=
      circuit.eval (fun i => (projection i).eval input) := by
  let copied := copyOracle prior circuit projection
  have h := copied.final.appendNode_preserves (.not (copied.output 0).val) (copied.output 0).isLt input (copied.output 0)
  exact (congrArg (fun x : Option Bool => x.getD false) h).trans (copyOracle_eval prior circuit projection input)

theorem copyQuery_negative {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (input : BitInput r) :
    (getElem? ((copyQuery prior circuit projection).final.values input)
      ((copyQuery prior circuit projection).output 1).val).getD false=
      !(circuit.eval (fun i => (projection i).eval input)) := by
  let copied := copyOracle prior circuit projection
  have h := copied.final.appendNode_newest (.not (copied.output 0).val) (copied.output 0).isLt input
  have he := congrArg (fun x : Option Bool => x.getD false) h
  change (getElem? ((copyQuery prior circuit projection).final.values input)
      ((copyQuery prior circuit projection).output 1).val).getD false=
      !(getElem? (copied.final.values input) (copied.output 0).val).getD false at he
  rw [show (getElem? (copied.final.values input) (copied.output 0).val).getD false=
      circuit.eval (fun i => (projection i).eval input) from copyOracle_eval prior circuit projection input] at he
  exact he

end NearCubicWires.RepairOrdinary.PCPPSubstitution
