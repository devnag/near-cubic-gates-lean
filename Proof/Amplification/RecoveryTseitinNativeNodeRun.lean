import Proof.Amplification.RecoveryTseitinNativeReferences

/-! Exact original node clauses from the physically generated reference
ports, using their own target-reference capacity. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNode
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinKernel RecoveryTseitinClauseAppend CircuitInputCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_node_run {n : Nat} (index : Nat) (node : BooleanNode n) (hw : node.WellFormedAt index)
    (ambient : Fin 239→List Bool) (padding : Fin 3→List Bool) (out : List Bool)
    (hb : Bounded (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) ambient)
    (hd : ambient 3=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) true)
    (hl : ambient 4=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)+1) false)
    (hi : ∀ j,ambient (sourceSlot j)=RepairOrdinary.frame (nativeReferences index node j).bits++padding j) :
    ∃ after : Fin 239→List Bool,∃ r,
      runFrom (machine (plans (kind node)))
        ((plans (kind node)).length*(20*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+5))
        ⟨(machine (plans (kind node))).start,heads out.length,
          input ambient out (RecoveryTseitinTautology.Cold.driverCapacity (n+index))⟩=some r ∧
      r.final.heads=heads (out++RecoveryFormulaPayload.input (circuitInputNodeClauses index node)).length ∧
      r.final.tapes=input after (out++RecoveryFormulaPayload.input (circuitInputNodeClauses index node))
        (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) ∧
      (∀ i : Fin 239,i.val<3 → after i=ambient i) ∧
      after 3=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) true ∧
      after 4=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)+1) false ∧
      Bounded (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) after ∧
      r.steps≤(plans (kind node)).length*(20*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+5) := by
  have hcap (p : Plan) (hp : p∈plans (kind node)) :
      RecoveryTseitin.capacity (Prepare.literals p.signs (indices (nativeReferences index node) p))≤
        RecoveryTseitinTautology.Cold.driverCapacity (n+index) := by
    rw [native_used index node p hp]
    exact (plan_capacity index index node hw (Nat.le_refl _) p).trans
      (RecoveryTseitinTautology.Cold.driver_capacity (n+index))
  have h:=plans_run (plans (kind node)) (RecoveryTseitinTautology.Cold.driverCapacity (n+index))
    (nativeReferences index node) ambient padding out hcap hb hd hl hi
  simpa only [emitted_formula,native_original] using h

end NearCubicWires.RepairSource.RecoveryTseitinNode
