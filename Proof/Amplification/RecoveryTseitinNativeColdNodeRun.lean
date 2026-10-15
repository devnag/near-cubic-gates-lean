import Proof.Amplification.RecoveryTseitinNativeAllocated
import Proof.Amplification.RecoveryTseitinNativeReadyDriver
import Proof.Amplification.RecoveryTseitinNativeNodeFull
import Proof.PCP.PCPPRequestNodeFieldsJoin

/-! One actual native descriptor, raw arity and raw index produce every
original Tseitin node clause, including both implication directions. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RepairRepresentation RecoveryExecution RecoveryRootRound RecoveryTseitinNode RecoveryTseitinKernel
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def coldNodeMachine :=
  Composition.machine (Composition.machine prepareMachine kernelBankMachine) NodeController.machine
def coldNodeBudget {n : Nat} (index : Nat) (node : BooleanNode n) :=
  ((referencesBudget n index (PCPPRequestNodeSchema.tag node).val
    (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)+1+
    (2*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+4))+1+
    (60*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+22))

theorem cold_node_run {n : Nat} (index : Nat) (node : BooleanNode n) (hw : node.WellFormedAt index)
    (pre tail out : List Bool) :
    ∃ r,runFrom coldNodeMachine (coldNodeBudget index node)
      ⟨coldNodeMachine.start,coldHeads pre out,coldInput n index
        (PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
          (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)) out⟩=some r ∧
      r.final.tapes 1333=out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node) ∧
      r.final.heads 1333=(out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)).length ∧
      r.final.tapes 1062=PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
        (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2) ∧
      r.final.heads 1062=pre.length+(natWord (PCPPRequestNodeSchema.tag node).val).length+
        (natWord (PCPPRequestNodeSchema.fields node 1)).length+(natWord (PCPPRequestNodeSchema.fields node 2)).length ∧
      r.steps ≤ coldNodeBudget index node := by
  obtain ⟨prepared,hprepared,ps,prefs,pd,pl,pdh,plh,pst,psh,pt,pth,pv,pvh,pw,po,poh⟩:=
    prepare_run n index pre tail out (PCPPRequestNodeSchema.tag node).val
      (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)
  obtain ⟨bank,hbank,view,keep,bs⟩:=allocated_run index node out prepared.final
    prefs pd pl pdh plh pw po poh
  obtain ⟨leaf,hleaf,lo,loh,lst,lsh,ls⟩:=NodeController.full_run index node hw bank.final
    (readyData index node) (nodePadding index node) out (ready_bounded index node) (ready_driver index node) (ready_log index node)
    (ready_references index node) (fun i=>(view i).2) (fun i=>(view i).1)
    ((keep 1072 (by decide)).2.trans pth) ((keep 1072 (by decide)).1.trans pt)
    ((keep 1082 (by decide)).2.trans pvh) ((keep 1082 (by decide)).1.trans pv)
  have hleaf' : runFrom NodeController.machine
      (60*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+22)
      (Composition.restart bank.final NodeController.machine.start)=some leaf := hleaf
  obtain ⟨result,hresult,rh,rt,rs⟩:=PCPPRequestNodeFields.join_three_run prepareMachine kernelBankMachine
    NodeController.machine _ _ _ _ prepared bank leaf hprepared hbank hleaf'
  refine ⟨result,hresult,?_,?_,?_,?_,?_⟩
  · rw [rt]; exact lo
  · rw [rh]; exact loh
  · rw [rt,lst]; exact (keep 1062 (by decide)).1.trans pst
  · rw [rh,lsh]; exact (keep 1062 (by decide)).2.trans psh
  · rw [rs]
    unfold coldNodeBudget
    omega

end NearCubicWires.RepairSource.RecoveryTseitinNative
