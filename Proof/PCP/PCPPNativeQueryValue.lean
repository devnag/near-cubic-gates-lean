import Proof.PCP.PCPPNativeQueryFooter

/-! The output footer's real sentinel produces the raw original-output
index used in the shared negation address. All node-bank tapes are retained. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQuery
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem value_away (j : Fin 5) : 124 ≤ (valueSlots j).val := by fin_cases j <;> decide
theorem value_fresh (j : Fin 5) (hj : j≠0) : 164 ≤ (valueSlots j).val := by
  fin_cases j <;> first | contradiction | decide
theorem value_empty (index : ℕ) (j : Fin 5) (hj : j≠0) :
    (PCPPNativeTemplateRaw.entry index).tapes j=[] := by
  fin_cases j <;> first | contradiction | rfl

theorem value_run (index : ℕ) (ah : Fin 168 → ℕ) (atapes : Fin 168 → List Bool)
    (hindex : ah 124=1 ∧ atapes 124=UnaryTemplate.tape index)
    (hfresh : ∀ i : Fin 168,164 ≤ i.val → ah i=0 ∧ atapes i=[]) :
    ∃ result,runFrom value (4*index+16) ⟨value.start,ah,atapes⟩=some result ∧
      result.steps=4*index+16 ∧
      result.final.heads 164=0 ∧ result.final.tapes 164=List.replicate index true ∧
      result.final.heads 124=1 ∧ result.final.tapes 124=UnaryTemplate.tape index ∧
      (∀ i,(∀ j,valueSlots j≠i) → result.final.heads i=ah i ∧ result.final.tapes i=atapes i) := by
  obtain ⟨raw,hr,rs,r0,r1,_r2,_r3,rh⟩ := PCPPNativeTemplateRaw.template_run index
  obtain ⟨result,run,_,steps,hh,ht,keep⟩ := RecoveryFocus.dock valueSlots value_injective
    PCPPNativeTemplateRaw.machine _ ah atapes _
    (by intro j
        by_cases hj : j=0
        · subst j; exact hindex.1
        · simpa only [PCPPNativeTemplateRaw.entry,PCPPNativeTemplateRaw.heads,hj,ite_false] using
            (hfresh _ (value_fresh j hj)).1)
    (by intro j
        by_cases hj : j=0
        · subst j; exact hindex.2
        · rw [value_empty index j hj]
          exact (hfresh _ (value_fresh j hj)).2) raw hr
  refine ⟨result,run,steps.trans rs,?_,(ht 1).trans r1,?_,(ht 0).trans r0,keep⟩
  · exact (hh 1).trans (by rw [rh]; rfl)
  · exact (hh 0).trans (by rw [rh]; rfl)

end NearCubicWires.RepairOrdinary.PCPPNativeQuery
