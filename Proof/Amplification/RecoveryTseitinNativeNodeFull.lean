import Proof.Amplification.RecoveryTseitinNativeDispatchTyped
import Proof.Amplification.RecoveryTseitinNativeNodeDock

/-! One fixed controller executes the native tag dispatch and all original
node clauses, appending the exact formula words at the real output cursor. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.NodeController
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinNode RecoveryTseitinKernel
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem kernel_source_away (flag : Bool) : ∀ i,kernelSlots flag i≠1062 := by
  intro i
  refine Fin.addCases (m:=5) (n:=236) (fun j=>?_) (fun j=>?_) i
  · intro he
    have h:=congrArg Fin.val he
    simp only [kernelSlots,Fin.addCases_left] at h
    cases flag <;> fin_cases j <;> dsimp [kernelFront] at h <;> omega
  · intro he
    have h:=congrArg Fin.val he
    simp only [kernelSlots,Fin.addCases_right] at h
    change 1099+j.val=1062 at h
    omega

theorem full_run {n z : Nat} (index : Nat) (node : BooleanNode n) (hw : node.WellFormedAt index)
    (ambient : Configuration 1335 z) (data : Fin 239→List Bool) (padding : Fin 3→List Bool) (out : List Bool)
    (hb : Bounded (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) data)
    (hd : data 3=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) true)
    (hl : data 4=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)+1) false)
    (hi : ∀ j,data (sourceSlot j)=RepairOrdinary.frame (nativeReferences index node j).bits++padding j)
    (hh : ∀ i,ambient.heads (kernelSlots (decide (kind node=2)) i)=RecoveryTseitinClauseAppend.heads out.length i)
    (ht : ∀ i,ambient.tapes (kernelSlots (decide (kind node=2)) i)=
      RecoveryTseitinClauseAppend.input data out (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) i)
    (th : ambient.heads 1072=1)
    (td : ambient.tapes 1072=UnaryTemplate.tape (PCPPRequestNodeSchema.tag node).val)
    (vh : ambient.heads 1082=1)
    (vd : ambient.tapes 1082=UnaryTemplate.tape (PCPPRequestNodeSchema.fields node 1)) :
    ∃ r,runFrom machine (60*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+22)
      (boundary 0 ambient.heads ambient.tapes)=some r ∧
      r.final.tapes 1333=out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node) ∧
      r.final.heads 1333=(out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)).length ∧
      r.final.tapes 1062=ambient.tapes 1062 ∧ r.final.heads 1062=ambient.heads 1062 ∧
      r.steps≤60*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+22 := by
  obtain ⟨time,head,htime,hdispatch,hkernel,hother⟩:=dispatch_run node ambient th td vh vd
  let prepared : Configuration 1335 1 := ⟨0,head,ambient.tapes⟩
  obtain ⟨_after,body,hbody,bo,bh,_bt,_bb,bs,bkeep⟩:=node_run index node hw prepared data padding out
    hb hd hl hi (by intro i; exact (hkernel _ i).trans (hh i)) ht
  have hstop:=node_stop (kind node) _ head ambient.tapes body hbody
  have whole:=hdispatch.trans hstop
  obtain ⟨r,hr,rf,rs⟩:=whole.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hbound : time+(body.steps+1)≤60*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+22 := by
    have hcount:=Nat.mul_le_mul_right (20*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+5) (plan_count (kind node))
    omega
  have hmore:=runFrom_moreFuel machine _
    (60*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+22-(time+(body.steps+1))) _ r hr
  rw [Nat.add_sub_of_le hbound] at hmore
  refine ⟨r,hmore,?_,?_,?_,?_,rs.le.trans hbound⟩
  · rw [rf]; exact bo
  · rw [rf]; exact bh
  · rw [rf]; exact (bkeep 1062 (kernel_source_away _)).1
  · rw [rf]
    exact (bkeep 1062 (kernel_source_away _)).2.trans (hother 1062 (by decide) (by decide))

end NearCubicWires.RepairSource.RecoveryTseitinNative.NodeController
