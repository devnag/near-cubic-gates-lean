import Proof.Amplification.RecoveryTseitinNativeNodeController

/-! Execute the chosen original clause plan at the actual native-reference
ports and retained formula append cursor. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.NodeController
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinNode RecoveryTseitinKernel
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem node_run {n z : Nat} (index : Nat) (node : BooleanNode n) (hw : node.WellFormedAt index)
    (ambient : Configuration 1335 z) (data : Fin 239→List Bool) (padding : Fin 3→List Bool) (out : List Bool)
    (hb : Bounded (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) data)
    (hd : data 3=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) true)
    (hl : data 4=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)+1) false)
    (hi : ∀ j,data (sourceSlot j)=RepairOrdinary.frame (nativeReferences index node j).bits++padding j)
    (hh : ∀ i,ambient.heads (kernelSlots (decide (kind node=2)) i)=RecoveryTseitinClauseAppend.heads out.length i)
    (ht : ∀ i,ambient.tapes (kernelSlots (decide (kind node=2)) i)=
      RecoveryTseitinClauseAppend.input data out (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) i) :
    ∃ after : Fin 239→List Bool,∃ r,
      runFrom (nodeProgram (kind node))
        ((plans (kind node)).length*(20*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+5))
        (Composition.restart ambient (nodeProgram (kind node)).start)=some r ∧
      r.final.tapes 1333=out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node) ∧
      r.final.heads 1333=(out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)).length ∧
      (∀ i,r.final.tapes (kernelSlots (decide (kind node=2)) i)=
        RecoveryTseitinClauseAppend.input after
          (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node))
          (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) i) ∧
      Bounded (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) after ∧
      r.steps≤(plans (kind node)).length*(20*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+5) ∧
      (∀ i,(∀ j,kernelSlots (decide (kind node=2)) j≠i) →
        r.final.tapes i=ambient.tapes i ∧ r.final.heads i=ambient.heads i) := by
  obtain ⟨after,base,hbase,bh,bt,_bk,_bd,_bl,bb,bs⟩:=native_node_run index node hw data padding out hb hd hl hi
  obtain ⟨r,hr,_rc,rs,rh,rt,ro⟩:=RecoveryFocus.dock (kernelSlots (decide (kind node=2)))
    (kernel_injective _) (RecoveryTseitinNode.machine (plans (kind node))) _ ambient.heads ambient.tapes _ hh ht base hbase
  refine ⟨after,r,hr,?_,?_,?_,bb,rs.le.trans bs,?_⟩
  · change r.final.tapes (kernelSlots (decide (kind node=2)) 239)=_
    rw [rt,bt]
    rfl
  · change r.final.heads (kernelSlots (decide (kind node=2)) 239)=_
    rw [rh,bh]
    rfl
  · intro i
    rw [rt,bt]
  · intro i hn
    have h:=ro i hn
    exact ⟨h.2,h.1⟩

end NearCubicWires.RepairSource.RecoveryTseitinNative.NodeController
