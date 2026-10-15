import Proof.Amplification.RecoveryTseitinNodeCapacity

/-! Original node and final-assertion consumers with all clause capacities
discharged by the common arity/size bound. Numeric references are still
supplied by the physical circuit scanner; no gate value enters control. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNode
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinKernel CircuitInputCNF TseitinCNF RecoveryTseitinClauseAppend
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem node_bounded_run {n : Nat} (index size : Nat) (node : BooleanNode n) (cap : Nat)
    (hw : node.WellFormedAt index) (hindex : index ≤ size) (hc : capacity n size≤cap)
    (ambient : Fin 239→List Bool) (padding : Fin 3→List Bool) (out : List Bool)
    (hb : Bounded cap ambient) (hd : ambient 3=List.replicate cap true)
    (hl : ambient 4=List.replicate (cap+1) false)
    (hi : ∀ j,ambient (sourceSlot j)=RepairOrdinary.frame (references index node j).bits++padding j) :
    ∃ after : Fin 239→List Bool,∃ r,
      runFrom (machine (plans (kind node))) (60*cap+15)
        ⟨(machine (plans (kind node))).start,heads out.length,input ambient out cap⟩=some r ∧
      r.final.heads=heads (out++RecoveryFormulaPayload.input (circuitInputNodeClauses index node)).length ∧
      r.final.tapes=input after (out++RecoveryFormulaPayload.input (circuitInputNodeClauses index node)) cap ∧
      (∀ i : Fin 239,i.val<3 → after i=ambient i) ∧
      after 3=List.replicate cap true ∧ after 4=List.replicate (cap+1) false ∧
      Bounded cap after ∧ r.steps≤60*cap+15 := by
  obtain ⟨after,r,hr,rh,rt,rkeep,rd,rl,rb,rs⟩ := node_run index node cap ambient padding out
    (by intro p _; exact (plan_capacity index size node hw hindex p).trans hc) hb hd hl hi
  have htime : (plans (kind node)).length*(20*cap+5)≤60*cap+15 := by
    have h:=Nat.mul_le_mul_right (20*cap+5) (plan_count (kind node))
    omega
  have hmore:=runFrom_moreFuel (machine (plans (kind node))) _
    (60*cap+15-((plans (kind node)).length*(20*cap+5))) _ r hr
  rw [Nat.add_sub_of_le htime] at hmore
  exact ⟨after,r,hmore,rh,rt,rkeep,rd,rl,rb,rs.trans htime⟩

noncomputable def assertionMachine := emitMachine (fun _=>true) (fun _=>0)
theorem assertion_run (index bound cap : Nat) (hindex : index ≤ bound)
    (hc : 8388608*(natBitLength bound+1)^2≤cap)
    (ambient : Fin 239→List Bool) (padding out : List Bool)
    (hb : Bounded cap ambient) (hd : ambient 3=List.replicate cap true)
    (hl : ambient 4=List.replicate (cap+1) false)
    (hi : ambient 0=RepairOrdinary.frame index.bits++padding) :
    ∃ after : Fin 239→List Bool,∃ r,
      runFrom assertionMachine (20*cap+4)
        ⟨assertionMachine.start,heads out.length,input ambient out cap⟩=some r ∧
      r.final.heads=heads (out++RepairOrdinary.frame (Encodable.encode (positiveUnit index)).bits).length ∧
      r.final.tapes=input after (out++RepairOrdinary.frame (Encodable.encode (positiveUnit index)).bits) cap ∧
      (∀ i : Fin 239,i.val<3 → after i=ambient i) ∧
      after 3=List.replicate cap true ∧ after 4=List.replicate (cap+1) false ∧
      Bounded cap after ∧ r.steps≤20*cap+4 := by
  have hcap : RecoveryTseitin.capacity (Prepare.literals (fun _=>true) (fun _=>index))≤cap := by
    apply LE.le.trans (RecoveryTseitin.capacity_bound _ (natBitLength bound) ?_ ?_) hc
    · unfold natBitLength
      omega
    · intro j
      exact Nat.add_le_add_right (Nat.log_mono_right hindex) 1
  exact emit_run cap (cap+1) (fun _=>true) (fun _=>0) (fun _=>index)
    ambient (fun _=>padding) out hcap hb hd hl (Nat.le_refl _) (by intro j; exact hi)

end NearCubicWires.RepairSource.RecoveryTseitinNode
