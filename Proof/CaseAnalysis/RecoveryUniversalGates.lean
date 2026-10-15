import Proof.CaseAnalysis.RecoveryUniversalAddress
import Proof.PCP.PCPPNativeClauseFullCapacity

/-! The original universal node's next three native nodes use the checked
native node printer, retaining both actual child references and workspaces. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalGates
open LocalBitMultitape SourceInterfaces RepairRepresentation PCPPNativeClauseBank
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def values (left right : ℕ) : Fin 7→ℕ:=![0,left,0,right,0,0,0]
noncomputable def machine:=Composition.machine
  (Composition.machine (nodeMachine 2 0 1 0 2) (nodeMachine 3 0 1 0 3)) (nodeMachine 4 0 1 0 3)
def emitted (left right : ℕ):=
  nodeBits 2 0 1 0 2 (values left right)++nodeBits 3 0 1 0 3 (values left right)++nodeBits 4 0 1 0 3 (values left right)
def budget (left right C : ℕ):=
  nodeBudget 2 0 1 0 2 (values left right) C+1+nodeBudget 3 0 1 0 3 (values left right) C+1+
    nodeBudget 4 0 1 0 3 (values left right) C

theorem block_run (left right W C : ℕ) (out : List Bool) (hl : left ≤ W) (hr : right ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) :
    AppendRun machine (budget left right C) (values left right) C out (emitted left right) := by
  have hleft:=PCPPNativeClauseCapacity.sum_capacity 0 left W C (by omega) hC
  have hright:=PCPPNativeClauseCapacity.sum_capacity 0 right W C (by omega) hC
  have hzero:=PCPPNativeClauseCapacity.sum_capacity 0 0 W C (by omega) hC
  have ha:=node_run 2 0 1 0 2 (by decide) (by decide) (values left right) C out hleft hzero
  have hb:=node_run 3 0 1 0 3 (by decide) (by decide) (values left right) C
    (out++nodeBits 2 0 1 0 2 (values left right)) hleft hright
  have hab:=AppendRun.join _ _ _ _ _ _ _ _ _ ha hb
  have hc:=node_run 4 0 1 0 3 (by decide) (by decide) (values left right) C
    (out++(nodeBits 2 0 1 0 2 (values left right)++nodeBits 3 0 1 0 3 (values left right))) hleft hright
  exact AppendRun.join _ _ _ _ _ _ _ _ _ hab hc

theorem emitted_nodes (n left right : ℕ) :
    emitted left right=([.not left,.and left right,.or left right] : List (BooleanNode n)).flatMap PCPPRequestNodeSchema.native := by
  simp [emitted,nodeBits,values,PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.append_assoc]

theorem budget_bound (left right W C : ℕ) (hl : left ≤ W) (hr : right ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    budget left right C ≤ 24*C+57 := by
  have hleft:=PCPPNativeClauseCapacity.sum_capacity 0 left W C (by omega) hC
  have hright:=PCPPNativeClauseCapacity.sum_capacity 0 right W C (by omega) hC
  have hzero:=PCPPNativeClauseCapacity.sum_capacity 0 0 W C (by omega) hC
  have h2 : (natWord 2).length=5 := by decide
  have h3 : (natWord 3).length=5 := by decide
  have h4 : (natWord 4).length=7 := by decide
  unfold budget nodeBudget PCPPNativeSumReusable.budget
  rw [h2,h3,h4]
  change (5+1+(2*PCPPNativeSumAppend.budget 0 left+2*C+7)+1+(2*PCPPNativeSumAppend.budget 0 0+2*C+7))+1+
    (5+1+(2*PCPPNativeSumAppend.budget 0 left+2*C+7)+1+(2*PCPPNativeSumAppend.budget 0 right+2*C+7))+1+
    (7+1+(2*PCPPNativeSumAppend.budget 0 left+2*C+7)+1+(2*PCPPNativeSumAppend.budget 0 right+2*C+7)) ≤ _
  omega

def caps (C : ℕ) (i : Fin 29):=if i=1 ∨ i=25 then C else 0
def data (left right C : ℕ) (out : List Bool) (i : Fin 29):=
  ZeroPadding.pad (caps C i) (PCPPNativeClauseBank.data (values left right) C out i)

theorem padded_run (left right W C : ℕ) (out : List Bool) (hl : left ≤ W) (hr : right ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r,runFrom machine (budget left right C)
      ⟨machine.start,PCPPNativeClauseBank.heads out,data left right C out⟩=some r ∧
      r.steps ≤ budget left right C ∧ r.final.heads=PCPPNativeClauseBank.heads (out++emitted left right) ∧
      r.final.tapes=data left right C (out++emitted left right) := by
  obtain ⟨p,hp,ps,ph,pt⟩:=block_run left right W C out hl hr hC
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config machine (caps C) _ _ p hp
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · rw [rf]
    change p.final.heads=_
    exact ph
  · rw [rf]
    change (fun i=>ZeroPadding.pad (caps C i) (p.final.tapes i))=_
    rw [pt]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalGates
