import Proof.CaseAnalysis.CaseTwoTraversalLayout
import Proof.CaseAnalysis.CaseTwoTagPublish

/-! Tag observation and publication dock into the one traversal bank. The
native node stream and the field-width/count drivers remain physically
retained through the tag call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tag:=RecoveryFocus.machine tagSlots TagReady.machine
noncomputable def publish:=RecoveryFocus.machine publishSlots TagPublish.machine

theorem tag_heads (out : List Bool) (j : Fin 27) : heads out (tagSlots j)=0:=by
  have hn : tagSlots j≠27:=by
    intro h
    have hv:=congrArg (fun x : Fin 30=>x.val) h
    change j.val=27 at hv
    have hj:=j.isLt
    omega
  simp only [heads,if_neg hn]
theorem tag_data (C F count : ℕ) (source : List Bool) (offset : ℕ) (tagWord out : List Bool) (flag : Bool)
    (j : Fin 27) : data C F count source offset tagWord out flag (tagSlots j)=
      TagReady.data C source offset tagWord flag j:=by
  simp only [data,tagSlots,Fin.addCases_left]
theorem tag_outside (C F count oldOffset offset : ℕ) (source oldTagWord tagWord out : List Bool)
    (oldFlag flag : Bool) (i : Fin 30) (hi : ∀ j,tagSlots j≠i) :
    data C F count source offset tagWord out flag i=data C F count source oldOffset oldTagWord out oldFlag i:=by
  revert hi
  refine Fin.addCases (m:=27) (n:=3) (fun j hj=>?_) (fun j _=>?_) i
  · exact False.elim (hj j rfl)
  · simp only [data,Fin.addCases_right]

theorem tag_run (C F count : ℕ) (pre tail out : List Bool) (value : Fin 6)
    (hsource : 2*(pre++orderedNatBits 6 value.val++tail).length+1≤C)
    (hoffset : pre.length+8≤C)
    (hbudget : FieldNative.budget pre.length 6 value.val+1≤C) :
    let source:=pre++orderedNatBits 6 value.val++tail
    ∃ r,runFrom tag (TagReady.budget C)
      ⟨tag.start,heads out,data C F count source pre.length [] out false⟩=some r ∧
      r.steps≤TagReady.budget C ∧ r.final.heads=heads out ∧
      r.final.tapes=data C F count source (pre.length+6) (natWord value.val) out (decide (value.val=5)) := by
  let source:=pre++orderedNatBits 6 value.val++tail
  obtain ⟨r,rr,rh,rt,rs⟩:=(TagReady.tag_ready pre tail value C false hsource hoffset hbudget).focus_at
    tagSlots tag_injective (heads out) (data C F count source pre.length [] out false)
    (tag_data C F count source pre.length [] out false) (tag_heads out)
  refine ⟨r,rr,rs,rh,?_⟩
  rw [rt]
  apply HierarchyAllocation.install_eq tagSlots tag_injective
  · exact tag_data C F count source (pre.length+6) (natWord value.val) out (decide (value.val=5))
  · exact tag_outside C F count pre.length (pre.length+6) source [] (natWord value.val) out false (decide (value.val=5))

theorem publish_heads (out : List Bool) (j : Fin 28) : heads out (publishSlots j)=TagPublish.heads out j:=by
  fin_cases j <;> rfl
theorem publish_data (C F count : ℕ) (source : List Bool) (offset : ℕ) (tagWord out : List Bool)
    (j : Fin 28) : data C F count source offset tagWord out false (publishSlots j)=
      TagPublish.data C source offset tagWord out j:=by
  fin_cases j <;> rfl
theorem publish_outside (C F count offset : ℕ) (source oldTagWord tagWord oldOut out : List Bool)
    (i : Fin 30) (hi : ∀ j,publishSlots j≠i) :
    data C F count source offset tagWord out false i=data C F count source offset oldTagWord oldOut false i:=by
  revert hi
  refine Fin.addCases (m:=28) (n:=2) (fun j hj=>?_) (fun j _=>?_) i
  · exact False.elim (hj j rfl)
  · fin_cases j <;> rfl

theorem publish_run (C F count offset value : ℕ) (source out : List Bool)
    (hC : 2*natBitLength value+3≤C) :
    ∃ r,runFrom publish (TagPublish.budget value C)
      ⟨publish.start,heads out,data C F count source offset (natWord value) out false⟩=some r ∧
      r.steps≤TagPublish.budget value C ∧ r.final.heads=heads (out++natWord value) ∧
      r.final.tapes=data C F count source offset [] (out++natWord value) false := by
  obtain ⟨base,hr,hs,bh,bt⟩:=TagPublish.publish_run C offset value source out hC
  obtain ⟨r,rr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock publishSlots publish_injective TagPublish.machine _
    (heads out) (data C F count source offset (natWord value) out false)
    (⟨TagPublish.machine.start,TagPublish.heads out,TagPublish.data C source offset (natWord value) out⟩ : Configuration 28 _)
    (publish_heads out) (publish_data C F count source offset (natWord value) out) base hr
  refine ⟨r,rr,rs.trans_le hs,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,publishSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,bh]
      exact (publish_heads (out++natWord value) j).symm
    · rw [(keep i (by intro j h;exact hi ⟨j,h⟩)).1]
      have hn : i≠27:=fun h=>hi ⟨27,h.symm⟩
      simp only [heads,if_neg hn]
  · have he:=HierarchyAllocation.install_eq publishSlots publish_injective
      (data C F count source offset (natWord value) out false) r.final.tapes
      (TagPublish.data C source offset [] (out++natWord value))
      (by intro j;rw [rt j,bt]) (by intro i hi;exact (keep i hi).2)
    rw [←he]
    apply HierarchyAllocation.install_eq publishSlots publish_injective
    · exact publish_data C F count source offset [] (out++natWord value)
    · exact publish_outside C F count offset source (natWord value) [] out (out++natWord value)

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
