import Proof.Amplification.RecoveryTseitinNativeNodeController

/-! Execute the actual tag classifiers while preserving every kernel tape
and kernel cursor used by the following original node-clause consumer. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.NodeController
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem kernel_tag_disjoint (inputNode value : Bool) (i : Fin 241) : kernelSlots inputNode i≠tagSlots value 0 := by
  refine Fin.addCases (m:=5) (n:=236) (fun j=>?_) (fun j=>?_) i
  · intro he
    have h:=congrArg Fin.val he
    simp only [kernelSlots,Fin.addCases_left] at h
    cases inputNode <;> cases value <;> fin_cases j <;> dsimp [kernelFront,tagSlots] at h <;> omega
  · intro he
    have h:=congrArg Fin.val he
    simp only [kernelSlots,Fin.addCases_right] at h
    cases value <;> dsimp [tagSlots] at h <;> omega

theorem tag_run {z : Nat} (value : Bool) (tag : Fin 5) (ambient : Configuration 1335 z)
    (hh : ambient.heads (tagSlots value 0)=1)
    (ht : ambient.tapes (tagSlots value 0)=UnaryTemplate.tape tag.val) :
    ∃ r,runFrom (tagProgram value) (tag.val+1) (Composition.restart ambient (tagProgram value).start)=some r ∧
      r.final.control.val=tag.val+5 ∧ r.steps=tag.val+1 ∧ r.final.tapes=ambient.tapes ∧
      (∀ i,i≠tagSlots value 0 → r.final.heads i=ambient.heads i) := by
  obtain ⟨r,hr,rc,rs,rh,rt,ro⟩:=RecoveryFocus.dock (tagSlots value)
    (by intro i j _; exact Subsingleton.elim i j) PCPPNativeTag.machine _ ambient.heads ambient.tapes _
    (by intro i; fin_cases i; exact hh) (by intro i; fin_cases i; exact ht)
    (PCPPNativeTag.receipt tag) (PCPPNativeTag.tag_run tag)
  refine ⟨r,hr,congrArg Fin.val rc,rs,?_,?_⟩
  · funext i
    by_cases hi : i=tagSlots value 0
    · subst i
      exact (rt 0).trans ht.symm
    exact (ro i (by intro j; fin_cases j; exact Ne.symm hi)).2
  · intro i hi
    exact (ro i (by intro j; fin_cases j; exact Ne.symm hi)).1

end NearCubicWires.RepairSource.RecoveryTseitinNative.NodeController
