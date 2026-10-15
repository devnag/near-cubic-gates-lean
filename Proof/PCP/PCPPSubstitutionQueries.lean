import Proof.PCP.PCPPSubstitutionQuery

/-! One stored oracle result and its negation per compact PCP query. -/
namespace NearCubicWires.RepairOrdinary.PCPPSubstitution
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def queryOffset (size output : ℕ) (negative : Bool) := if negative then 2*size else 2*output+1
def queryAddress (base size output query : ℕ) (negative : Bool) :=
  base+query*(2*size+1)+queryOffset size output negative
def signedValue (value negative : Bool) := if negative then !value else value
def signIndex (negative : Bool) : Fin 2 := if negative then 1 else 0

theorem copyQuery_index {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (negative : Bool) :
    ((copyQuery prior circuit projection).output (signIndex negative)).val=
      prior.nodes.length+queryOffset circuit.size circuit.output.val negative := by
  cases negative
  · exact copyQuery_positive_index prior circuit projection
  · exact copyQuery_negative_index prior circuit projection

theorem copyQuery_eval {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (input : BitInput r) (negative : Bool) :
    (getElem? ((copyQuery prior circuit projection).final.values input)
      ((copyQuery prior circuit projection).output (signIndex negative)).val).getD false=
      signedValue (circuit.eval (fun i => (projection i).eval input)) negative := by
  cases negative
  · exact copyQuery_positive prior circuit projection input
  · exact copyQuery_negative prior circuit projection input

structure QueryPrefixResult {r : ℕ} (prior : BooleanDAGBuilder r) (size count : ℕ) where
  builder : BooleanDAGBuilder r
  length : builder.nodes.length=prior.nodes.length+count*(2*size+1)
  extension : BooleanDAGExtension prior builder

def queryPrefix {n r q : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) :
    (count : ℕ) → count ≤ q → QueryPrefixResult prior circuit.size count
  | 0,_ => ⟨prior,by omega,BooleanDAGExtension.refl prior⟩
  | count+1,hcount =>
    let previous := queryPrefix prior circuit projections count (by omega)
    let next := copyQuery previous.builder circuit (projections ⟨count,by omega⟩)
    ⟨next.final,by
      dsimp only [next]
      rw [copyQuery_length,previous.length]
      ring,
      previous.extension.trans next.extension⟩

theorem queryAddress_lt {n r : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (count j : ℕ) (hj : j < count) (negative : Bool) :
    queryAddress prior.nodes.length circuit.size circuit.output.val j negative <
      prior.nodes.length+count*(2*circuit.size+1) := by
  have hout : circuit.output.val < circuit.size := circuit.output.isLt
  have hstep : (j+1)*(2*circuit.size+1) ≤ count*(2*circuit.size+1) :=
    Nat.mul_le_mul_right _ (by omega)
  unfold queryAddress queryOffset
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> nlinarith

end NearCubicWires.RepairOrdinary.PCPPSubstitution
