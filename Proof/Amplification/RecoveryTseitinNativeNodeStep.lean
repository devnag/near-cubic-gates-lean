import Proof.Amplification.RecoveryTseitinNativeReuseBodyRun
import Proof.Amplification.RecoveryTseitinNativeReuseAdvance
import Proof.Amplification.RecoveryTseitinNativeBudget

/-! One original native node appends its complete CNF, clears scratch,
and advances the raw node index on the same physical reusable bank. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def stepMachine := Composition.machine machine advanceMachine
def stepBudget (cap : Nat) := 6*cap+12
noncomputable def entry (n index pos : Nat) (word out : List Bool) (cap : Nat) :=
  (⟨stepMachine.start,heads pos out.length,data n index word out cap⟩ : Configuration 1338 _)
theorem join_entry {t a b : Nat} (p : Machine t a) (q : Machine t b)
    (h : Fin t→Nat) (d : Fin t→List Bool) :
    Composition.leftConfig b (⟨p.start,h,d⟩ : Configuration t a)=
      (⟨(Composition.machine p q).start,h,d⟩ : Configuration t (a+b)) := rfl
theorem original_source {n : Nat} (node : BooleanNode n) (pre tail : List Bool) :
    PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
      (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)=
      pre++PCPPRequestNodeSchema.native node++tail := by
  simp only [PCPPNativeNodeRead.source,PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.first_tag,List.append_assoc]
theorem step_run {n : Nat} (index : Nat) (node : BooleanNode n) (hw : node.WellFormedAt index)
    (pre tail out : List Bool) (cap : Nat) (hcap : coldNodeBudget index node ≤ cap) (hi : index+1 ≤ cap) :
    ∃ r,runFrom stepMachine (stepBudget cap)
      (entry n index pre.length (pre++PCPPRequestNodeSchema.native node++tail) out cap)=some r ∧
      r.final.heads=heads (pre++PCPPRequestNodeSchema.native node).length
        (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)).length ∧
      r.final.tapes=data n (index+1) (pre++PCPPRequestNodeSchema.native node++tail)
        (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)) cap ∧
      r.steps ≤ stepBudget cap := by
  obtain ⟨a,ha,ah,atapes,asteps⟩:=body_run index node hw pre tail out cap hcap
  obtain ⟨b,hb,bh,bt,bs⟩:=advance_run n index _ _ _ cap hi a.final ah atapes
  obtain ⟨result,joined,rh,rt,rs⟩:=join_two machine advanceMachine _ _ _ a b ha hb
  have htime : (4*cap+7)+1+(2*index+4) ≤ stepBudget cap := by unfold stepBudget; omega
  have hm:=runFrom_moreFuel stepMachine _
    (stepBudget cap-((4*cap+7)+1+(2*index+4))) _ _ joined
  rw [Nat.add_sub_of_le htime] at hm
  rw [join_entry machine advanceMachine] at hm
  refine ⟨result,?_,?_,?_,?_⟩
  · simpa only [entry,stepMachine,original_source] using hm
  · simpa only [PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.first_tag,List.length_append,Nat.add_assoc] using rh.trans bh
  · simpa only [original_source] using rt.trans bt
  · rw [rs]
    omega

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
