import Proof.PCP.PCPPNativeQueryHeaderNodes

/-! Read the original descriptor's actual output index immediately after
the executed node stream, preserving the reusable bank and upper counters. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQuery
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem footer_reserved (j : Fin 11) (hj : j≠0) : reserved (footerSlots j) := by
  fin_cases j <;> first | contradiction | exact Or.inl rfl | exact Or.inr (by decide)
theorem footer_low_away (i : Fin 122) (hi : i≠0) (j : Fin 11) : footerSlots j≠i.castAdd 46 := by
  by_cases hj : j=0
  · subst j
    intro h
    apply hi
    apply Fin.ext
    exact (congrArg (fun k : Fin 168 => k.val) h).symm
  · have hl := reserved_high (footerSlots j) (footer_reserved j hj)
    apply Fin.ne_of_val_ne
    change (footerSlots j).val≠i.val
    omega
theorem footer_below (j : Fin 11) : (footerSlots j).val < 164 := by fin_cases j <;> decide

theorem footer_run (pre suffix queries : List Bool) (index base position C F : ℕ) (out : List Bool)
    (ah : Fin 168 → ℕ) (atapes : Fin 168 → List Bool)
    (hlow : lowFrame (pre++natWord index++suffix) queries pre.length base position C F out ah atapes)
    (hfresh : ∀ i,reserved i → ah i=0 ∧ atapes i=[]) :
    ∃ result,runFrom footer (PCPPQueryNatural.budget index) ⟨footer.start,ah,atapes⟩=some result ∧
      result.steps ≤ PCPPQueryNatural.budget index ∧
      lowFrame (pre++natWord index++suffix) queries (pre.length+(natWord index).length)
        base position C F out result.final.heads result.final.tapes ∧
      result.final.tapes 124=UnaryTemplate.tape index ∧ result.final.heads 124=1 ∧
      (∀ i : Fin 168,164 ≤ i.val → result.final.heads i=0 ∧ result.final.tapes i=[]) ∧
      (∀ i,(∀ j,footerSlots j≠i) → result.final.heads i=ah i ∧ result.final.tapes i=atapes i) := by
  obtain ⟨raw,hr,rs,r0,rh0,rt,rh⟩ := PCPPQueryNatural.natural_run pre suffix index
  obtain ⟨result,run,_,steps,hh,ht,keep⟩ := RecoveryFocus.dock footerSlots footer_injective
    PCPPQueryNatural.machine _ ah atapes _
    (by intro j
        by_cases hj : j=0
        · subst j; exact (hlow 0).1
        · simpa only [PCPPQueryNatural.entry,hj,ite_false] using (hfresh _ (footer_reserved j hj)).1)
    (by intro j
        by_cases hj : j=0
        · subst j; exact (hlow 0).2
        · simpa only [PCPPQueryNatural.entry,hj,ite_false] using (hfresh _ (footer_reserved j hj)).2) raw hr
  refine ⟨result,run,by omega,?_,(ht 10).trans rt,(hh 10).trans rh,?_,keep⟩
  · intro i
    by_cases hi : i=0
    · subst i
      refine ⟨?_,(ht 0).trans r0⟩
      have h := (hh 0).trans rh0
      change result.final.heads 0=pre.length+2*natBitLength index+1 at h
      change result.final.heads 0=pre.length+(natWord index).length
      simpa only [DecompositionSource.natWord_length,Nat.add_assoc] using h
    · have hk := keep (i.castAdd 46) (footer_low_away i hi)
      exact ⟨hk.1.trans (by simpa only [PCPPNativeNodeReusable.heads,hi,ite_false] using (hlow i).1),hk.2.trans (hlow i).2⟩
  · intro i hi
    have hk := keep i (by intro j; have hb := footer_below j; apply Fin.ne_of_val_ne; omega)
    have hf := hfresh i (Or.inr (by omega))
    exact ⟨hk.1.trans hf.1,hk.2.trans hf.2⟩

end NearCubicWires.RepairOrdinary.PCPPNativeQuery
