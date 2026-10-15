import Proof.CaseAnalysis.CaseTwoAssignmentLayout

/-! Actual comparison and variable-template preparation at the assignment
dispatcher's literal entry bank. The original source and both honest inputs
remain on their paid ports. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Assignment
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem prepared_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (index oldIndex : ℕ) : ∃ out,
    runFrom (prepare a) (VariablePrep.budget index (a.output r).systematicBits)
      ⟨(prepare a).start,heads a,input a r u index oldIndex⟩=some out ∧
      out.steps≤VariablePrep.budget index (a.output r).systematicBits ∧ out.final.heads=heads a ∧
      out.final.tapes (low a 15)=UnaryTemplate.tape index ∧
      out.final.tapes (low a 17)=[decide ((a.output r).systematicBits ≤ index)] ∧
      out.final.tapes (low a 14)=UnaryTemplate.tape (a.output r).systematicBits ∧
      (∀ i,(∀ j,prepareSlots a j≠i) → out.final.tapes i=input a r u index oldIndex i):=by
  obtain ⟨p,hp,p2,p4,_,p1⟩:=VariablePrep.prepare_run index (a.output r).systematicBits
  obtain ⟨out,ho,oh,ot,os⟩:=hp.focus_at (prepareSlots a) (prepare_injective a) (heads a)
    (input a r u index oldIndex) (by intro j;fin_cases j <;>rfl)
    (by intro j;fin_cases j <;>rfl)
  refine ⟨out,ho,os,oh,?_,?_,?_,?_⟩
  · rw [ot];exact (install_slot (prepareSlots a) (prepare_injective a) _ p 2).trans p2
  · rw [ot];exact (install_slot (prepareSlots a) (prepare_injective a) _ p 4).trans p4
  · rw [ot];exact (install_slot (prepareSlots a) (prepare_injective a) _ p 1).trans p1
  · intro i hi;rw [ot];exact install_other _ _ _ _ hi

theorem prepare_outside (a : PointwisePCPPAlgorithm) (i : Fin (tapes a))
    (hi : i.val < 13 ∨ 18 < i.val) : ∀ j,prepareSlots a j≠i:=by
  intro j he
  have h:=congrArg Fin.val he
  fin_cases j <;>simp [prepareSlots,low] at h <;>omega
theorem offset_outside (a : PointwisePCPPAlgorithm) (i : Fin (tapes a))
    (hi : i.val < 14 ∨ 24 < i.val) : ∀ j,offsetSlots a j≠i:=by
  intro j he
  have h:=congrArg Fin.val he
  fin_cases j <;>simp [offsetSlots,low] at h <;>omega

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Assignment
