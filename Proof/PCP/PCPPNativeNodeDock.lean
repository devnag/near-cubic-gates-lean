import Proof.PCP.PCPPNativeNodeEntry

/-! Literal and classifier calls in the concrete native-node layout.
The scalar hypotheses identify existing physical tapes and cursors; the
focused trace retains every other tape/head at its actual value. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem literal_run (bits out : List Bool) (heads : Fin 119 → ℕ) (data : Fin 119 → List Bool)
    (hh : heads 5=out.length) (ht : data 5=out) :
    ∃ r,runFrom (literalProgram bits) bits.length
      (RecoveryCalls.restarted (literalProgram bits) heads data)=some r ∧
      r.steps=bits.length ∧ r.final.heads 5=(out++bits).length ∧ r.final.tapes 5=out++bits ∧
      (∀ i,i≠5 → r.final.heads i=heads i ∧ r.final.tapes i=data i) := by
  obtain ⟨raw,hr,rf,rs⟩ := Constants.write_run bits out
  obtain ⟨r,hrun,_,steps,rh,rt,keep⟩ := RecoveryFocus.dock (fun _ : Fin 1 => (5 : Fin 119))
    (by intro i j _; exact Subsingleton.elim i j) (HierarchyFixedWord.raw bits) _ heads data
    (Constants.cfg bits out 0 (by omega))
    (by intro i; simpa only [Constants.cfg,Nat.add_zero] using hh)
    (by intro i; simpa only [Constants.cfg,List.take_zero,List.append_nil] using ht) raw hr
  refine ⟨r,hrun,steps.trans rs,?_,?_,?_⟩
  · have h := rh 0
    rw [rf] at h
    simpa only [Constants.cfg,List.length_append] using h
  · have h := rt 0
    rw [rf] at h
    simpa only [Constants.cfg,List.take_length] using h
  · intro i hi
    exact keep i (fun _ => Ne.symm hi)

theorem tag_run (slot : Fin 119) (tag : Fin 5) (heads : Fin 119 → ℕ) (data : Fin 119 → List Bool)
    (hh : heads slot=1) (ht : data slot=UnaryTemplate.tape tag.val) :
    ∃ r,runFrom (tagProgram slot) (tag.val+1)
      (RecoveryCalls.restarted (tagProgram slot) heads data)=some r ∧
      r.steps=tag.val+1 ∧ r.final.control.val=tag.val+5 ∧
      (∀ i,i≠slot → r.final.heads i=heads i ∧ r.final.tapes i=data i) := by
  have hr := PCPPNativeTag.tag_run tag
  obtain ⟨r,hrun,rc,steps,_,_,keep⟩ := RecoveryFocus.dock (fun _ : Fin 1 => slot)
    (by intro i j _; exact Subsingleton.elim i j) PCPPNativeTag.machine _ heads data
    (PCPPNativeTag.entry tag) (fun _ => hh) (fun _ => ht) (PCPPNativeTag.receipt tag) hr
  refine ⟨r,hrun,steps,?_,?_⟩
  · rw [rc]; rfl
  · intro i hi
    exact keep i (fun _ => Ne.symm hi)

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
