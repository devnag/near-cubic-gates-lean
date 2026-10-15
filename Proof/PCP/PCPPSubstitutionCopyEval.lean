import Proof.PCP.PCPPSubstitutionCopy

/-! Every copied prefix retains the original oracle DAG's shared values. -/
namespace NearCubicWires.RepairOrdinary.PCPPSubstitution
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copyPrefix_eval {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (input : BitInput r)
    (count : ℕ) (hcount : count ≤ circuit.nodes.length) :
    ∀ j,j < count → ((copyPrefix prior circuit projection count hcount).builder.values input)[address prior.nodes.length j]?=
      (originalValues circuit (fun i => (projection i).eval input) count)[j]? := by
  induction count with
  | zero => intro j hj; omega
  | succ count ih =>
    intro j hj
    have hc : count < circuit.nodes.length := by omega
    let previous := copyPrefix prior circuit projection count hc.le
    let node := circuit.nodes[count]
    have hwf : node.WellFormedAt count := circuit.wellFormed ⟨count,hc⟩
    have hold : ∀ t,t < count → (previous.builder.values input)[address prior.nodes.length t]?=
        (originalValues circuit (fun i => (projection i).eval input) count)[t]? := ih hc.le
    change getElem? ((copyNode previous.builder prior.nodes.length count projection node previous.length hwf).values input)
      (address prior.nodes.length j)=_
    rw [originalValues_step circuit _ count hc,Array.getElem?_push,originalValues_size circuit _ count hc.le]
    by_cases hlt : j < count
    · rw [if_neg (by omega : j≠count)]
      have href : address prior.nodes.length j < previous.builder.nodes.length := by
        rw [previous.length]
        unfold address
        omega
      have he := (copyNodeExtension previous.builder prior.nodes.length count projection node previous.length hwf).wireValue_lift
        input ⟨address prior.nodes.length j,href⟩
      exact he.trans (hold j hlt)
    · have he : j=count := by omega
      subst j
      rw [if_pos rfl]
      exact copyNode_eval previous.builder prior.nodes.length count projection node previous.length hwf input _ hold

def copyOracle {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) : BooleanDAGBuildResult prior 1 where
  final := (copyPrefix prior circuit projection circuit.nodes.length (by omega)).builder
  extension := (copyPrefix prior circuit projection circuit.nodes.length (by omega)).extension
  output := fun _ => ⟨address prior.nodes.length circuit.output.val,by
    rw [(copyPrefix prior circuit projection circuit.nodes.length (by omega)).length]
    have h := circuit.output.isLt
    unfold address
    omega⟩

theorem copyOracle_length {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) :
    (copyOracle prior circuit projection).final.nodes.length=prior.nodes.length+2*circuit.size :=
  (copyPrefix prior circuit projection circuit.nodes.length (by omega)).length

theorem copyOracle_eval {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (input : BitInput r) :
    (getElem? ((copyOracle prior circuit projection).final.values input)
      ((copyOracle prior circuit projection).output 0).val).getD false=
      circuit.eval (fun i => (projection i).eval input) := by
  have h := copyPrefix_eval prior circuit projection input circuit.nodes.length (by omega)
    circuit.output.val circuit.output.isLt
  rw [originalValues_whole] at h
  exact congrArg (fun x : Option Bool => x.getD false) h

end NearCubicWires.RepairOrdinary.PCPPSubstitution
