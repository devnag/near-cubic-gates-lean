import Proof.CaseAnalysis.CaseTwoTraversalLayout
import Proof.Amplification.RecoveryTseitinRawIncrement

namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def field:=RecoveryFocus.machine fieldSlots FieldStep.machine
noncomputable def increment:=RecoveryFocus.machine countSlots RepairSource.RecoveryTseitinRawIncrement.machine

theorem field_run (C F count value : ℕ) (pre tail tagWord out : List Bool) (flag : Bool)
    (hv : value≤F) (hsource : 2*(pre++orderedNatBits F value++tail).length+1≤C)
    (hoffset : pre.length+F+2≤C)
    (hbudget : FieldNative.budget pre.length F value+1≤C) :
    let source:=pre++orderedNatBits F value++tail
    ∃ r,runFrom field (FieldStep.budget pre.length F value C)
      ⟨field.start,heads out,data C F count source pre.length tagWord out flag⟩=some r ∧
      r.steps≤FieldStep.budget pre.length F value C ∧
      r.final.heads=heads (out++natWord value) ∧
      r.final.tapes=data C F count source (pre.length+F) tagWord (out++natWord value) flag := by
  let source:=pre++orderedNatBits F value++tail
  obtain ⟨base,hr,hs,bh,bt⟩:=FieldStep.field_run pre tail F value C out hv hsource hoffset hbudget
  obtain ⟨r,rr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock fieldSlots field_injective FieldStep.machine _
    (heads out) (data C F count source pre.length tagWord out flag)
    (⟨FieldStep.machine.start,FieldClear.heads out,FieldClear.data C source pre.length F out⟩ : Configuration 25 _)
    (field_heads out) (field_data C F count source pre.length tagWord out flag) base hr
  refine ⟨r,rr,rs.trans_le hs,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,fieldSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,bh]
      exact (field_heads (out++natWord value) j).symm
    · rw [(keep i (by intro j h;exact hi ⟨j,h⟩)).1]
      exact (field_head_outside out (out++natWord value) i (by intro j h;exact hi ⟨j,h⟩)).symm
  · have he:=HierarchyAllocation.install_eq fieldSlots field_injective
      (data C F count source pre.length tagWord out flag) r.final.tapes
      (FieldClear.data C source (pre.length+F) F (out++natWord value))
      (by intro j;rw [rt j,bt]) (by intro i hi;exact (keep i hi).2)
    rw [←he]
    apply HierarchyAllocation.install_eq fieldSlots field_injective
    · exact field_data C F count source (pre.length+F) tagWord (out++natWord value) flag
    · intro i hi
      exact field_outside C F count pre.length (pre.length+F) source tagWord out (out++natWord value) flag i hi

theorem count_data (C F count offset : ℕ) (source tagWord out : List Bool) (flag : Bool) :
    ∀ j,data C F count source offset tagWord out flag (countSlots j)=
      (![List.replicate count true,List.replicate C false] : Fin 2→List Bool) j:=by
  intro j;fin_cases j <;> simp [data,countSlots,TagReady.data,TagReady.localData,TagReady.pads,
    TagObserve.data,Fin.addCases]
theorem count_outside (C F count offset : ℕ) (source tagWord out : List Bool) (flag : Bool)
    (i : Fin 30) (hi : ∀ j,countSlots j≠i) :
    data C F (count+1) source offset tagWord out flag i=data C F count source offset tagWord out flag i:=by
  have hn : i≠29:=fun h=>hi 0 h.symm
  fin_cases i <;> first | contradiction | rfl

theorem increment_run (C F count offset : ℕ) (source tagWord out : List Bool) (flag : Bool)
    (hcount : count+1≤C) :
    ∃ r,runFrom increment (2*count+4)
      ⟨increment.start,heads out,data C F count source offset tagWord out flag⟩=some r ∧
      r.steps=2*count+4 ∧ r.final.heads=heads out ∧
      r.final.tapes=data C F (count+1) source offset tagWord out flag := by
  obtain ⟨r,rr,rh,rt,rs⟩:=(RepairSource.RecoveryTseitinRawIncrement.increment_ready count C hcount).focus_at
    countSlots (by decide) (heads out) (data C F count source offset tagWord out flag)
    (count_data C F count offset source tagWord out flag)
    (by intro j;fin_cases j <;> rfl)
  refine ⟨r,rr,rs,rh,?_⟩
  rw [rt]
  apply HierarchyAllocation.install_eq countSlots (by decide)
  · exact count_data C F (count+1) offset source tagWord out flag
  · exact count_outside C F count offset source tagWord out flag

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
