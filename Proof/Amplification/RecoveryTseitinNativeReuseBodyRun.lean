import Proof.Amplification.RecoveryTseitinJoinTwo

/-! Exact append-and-clear body on one fixed reusable native-node workspace. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem body_run {n : Nat} (index : Nat) (node : BooleanNode n) (hw : node.WellFormedAt index)
    (pre tail out : List Bool) (cap : Nat) (hcap : coldNodeBudget index node ≤ cap) :
    ∃ r,runFrom machine (4*cap+7)
      ⟨machine.start,heads pre.length out.length,data n index
        (PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
          (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)) out cap⟩=some r ∧
      r.final.heads=heads
        (pre.length+(natWord (PCPPRequestNodeSchema.tag node).val).length+
          (natWord (PCPPRequestNodeSchema.fields node 1)).length+(natWord (PCPPRequestNodeSchema.fields node 2)).length)
        (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)).length ∧
      r.final.tapes=data n index
        (PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
          (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2))
        (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)) cap ∧
      r.steps ≤ 4*cap+7 := by
  obtain ⟨a,ha,ah,atapes,ad,al,ab,asteps⟩:=prefix_run index node hw pre tail out cap hcap
  obtain ⟨b,hb,bh,bt,bs⟩:=erase_run n index _ _ _ cap a.final ah atapes ad al ab
  obtain ⟨result,joined,rh,rt,rs⟩:=join_two prefixMachine eraseMachine _ _ _ a b ha hb
  have htime : (2*coldNodeBudget index node+2)+1+(2*cap+4) ≤ 4*cap+7 := by omega
  have hm:=runFrom_moreFuel machine _
    (4*cap+7-((2*coldNodeBudget index node+2)+1+(2*cap+4))) _ _ joined
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨result,hm,rh.trans bh,rt.trans bt,?_⟩
  rw [rs]
  omega

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
