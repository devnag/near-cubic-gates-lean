import Proof.PCP.PCPPSubstitutionQueries

/-! Every clause occurrence uses the same cached projected-oracle wire. -/
namespace NearCubicWires.RepairOrdinary.PCPPSubstitution
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem queryPrefix_eval {n r q : ℕ} (prior : BooleanDAGBuilder r)
    (circuit : BooleanCircuit n) (projections : Fin q → Fin n → ProjectedRandomBit r)
    (input : BitInput r) (count : ℕ) (hcount : count ≤ q) :
    ∀ (j : ℕ) (hj : j < count) (negative : Bool),
      (getElem? ((queryPrefix prior circuit projections count hcount).builder.values input)
        (queryAddress prior.nodes.length circuit.size circuit.output.val j negative)).getD false=
      signedValue (circuit.eval (fun i => (projections ⟨j,by omega⟩ i).eval input)) negative := by
  induction count with
  | zero => intro j hj; omega
  | succ count ih =>
    intro j hj negative
    have hc : count < q := by omega
    let previous := queryPrefix prior circuit projections count hc.le
    let next := copyQuery previous.builder circuit (projections ⟨count,hc⟩)
    change (getElem? (next.final.values input)
      (queryAddress prior.nodes.length circuit.size circuit.output.val j negative)).getD false=_
    by_cases hlt : j < count
    · have href : queryAddress prior.nodes.length circuit.size circuit.output.val j negative <
          previous.builder.nodes.length := by
        rw [previous.length]
        exact queryAddress_lt prior circuit count j hlt negative
      have he := next.extension.wireValue_lift input
        ⟨queryAddress prior.nodes.length circuit.size circuit.output.val j negative,href⟩
      exact (congrArg (fun x : Option Bool => x.getD false) he).trans (ih hc.le j hlt negative)
    · have hjc : j=count := by omega
      subst j
      have he := copyQuery_eval previous.builder circuit (projections ⟨count,hc⟩) input negative
      rw [copyQuery_index,previous.length] at he
      exact he

def queryBank {n r q : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) : BooleanDAGBuilder r :=
  (queryPrefix prior circuit projections q (by omega)).builder

def queryRef {n r q : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (j : Fin q) (negative : Bool) :
    Fin (queryBank prior circuit projections).nodes.length :=
  ⟨queryAddress prior.nodes.length circuit.size circuit.output.val j.val negative,by
    rw [queryBank,(queryPrefix prior circuit projections q (by omega)).length]
    exact queryAddress_lt prior circuit q j.val j.isLt negative⟩

def literalRef {n r q : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) :
    Literal q → Fin (queryBank prior circuit projections).nodes.length
  | .positive j => queryRef prior circuit projections j false
  | .negative j => queryRef prior circuit projections j true

theorem literalRef_eval {n r q : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (input : BitInput r) (literal : Literal q) :
    (getElem? ((queryBank prior circuit projections).values input)
      (literalRef prior circuit projections literal).val).getD false=
      literal.eval (fun j => circuit.eval (fun i => (projections j i).eval input)) := by
  cases literal with
  | positive j => exact queryPrefix_eval prior circuit projections input q (by omega) j.val j.isLt false
  | negative j => exact queryPrefix_eval prior circuit projections input q (by omega) j.val j.isLt true

theorem queryBank_length {n r q : ℕ} (prior : BooleanDAGBuilder r) (circuit : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) :
    (queryBank prior circuit projections).nodes.length=prior.nodes.length+q*(2*circuit.size+1) :=
  (queryPrefix prior circuit projections q (by omega)).length

end NearCubicWires.RepairOrdinary.PCPPSubstitution
