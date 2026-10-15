import Proof.Circuits.DecompositionInputArity

/-! Complete cold native arity/child-count prefix, using its checked first
receipt to avoid rechecking nested configuration reductions. -/
namespace NearCubicWires.RepairOrdinary.DecompositionInputCounts
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem counts_run (arity count : ℕ) (tail : List Bool) :
    ∃ r,run machine (budget arity count tail) (input arity count tail)=some r ∧
      r.final.tapes 0=frame (word arity count tail) ∧ r.final.heads 0=0 ∧
      r.final.tapes 1=word arity count tail ∧
      r.final.heads 1=(natWord arity++natWord count).length ∧
      r.final.tapes 12=UnaryTemplate.tape arity ∧ r.final.heads 12=1 ∧
      r.final.tapes 22=UnaryTemplate.tape count ∧ r.final.heads 22=1 ∧
      r.steps ≤ budget arity count tail := by
  obtain ⟨parsed,hprefix,p0,ph0,p1,ph1,p12,ph12,pfresh,ps⟩ := prefix_run arity count tail
  have ct (j : Fin 11) : parsed.final.tapes (countSlots j)=
      if j=0 then natWord arity++natWord count++tail else [] := by
    fin_cases j
    · change parsed.final.tapes 1=word arity count tail
      exact p1
    all_goals exact (pfresh _ (by decide)).1
  have ch (j : Fin 11) : parsed.final.heads (countSlots j)=
      if j=0 then (natWord arity).length else 0 := by
    fin_cases j
    · exact ph1
    all_goals exact (pfresh _ (by decide)).2
  obtain ⟨c,hc,cs,ct1,ch1,ct22,ch22,cOther⟩ :=
    PCPPQueryNatural.focus_run countSlots (by decide) parsed.final (natWord arity) tail count ct ch
  have whole := Composition.run_join prefixMachine countProgram _ _ _ parsed c hprefix hc
  have he : prefixBudget arity count tail+1+PCPPQueryNatural.budget count=budget arity count tail := by
    unfold prefixBudget budget
    omega
  rw [he] at whole
  refine ⟨Composition.joinedReceipt parsed c,whole,?_,?_,ct1,?_,?_,?_,ct22,ch22,?_⟩
  · change c.final.tapes 0=_
    exact ((cOther 0 (by decide)).1).trans p0
  · change c.final.heads 0=0
    exact ((cOther 0 (by decide)).2).trans ph0
  · change c.final.heads (countSlots 0)=_
    simpa only [List.length_append,DecompositionSource.natWord_length,Nat.add_assoc] using ch1
  · change c.final.tapes 12=_
    exact ((cOther 12 (by decide)).1).trans p12
  · change c.final.heads 12=1
    exact ((cOther 12 (by decide)).2).trans ph12
  · change parsed.steps+1+c.steps ≤ _
    rw [←he]
    omega

end NearCubicWires.RepairOrdinary.DecompositionInputCounts
