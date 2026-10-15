import Proof.CaseAnalysis.RowsCircuitBottomBounds

/-! The full accepted-bottom append stage: original description is always
charged, then the SAME mode/bitmap decides retention. Growing prefixes are
never rescanned; the actual shared C bounds all local work additively. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def publish (threshold : Bool):=Composition.machine describe (choice threshold)

theorem publish_run (threshold : Bool) (cap core pos memberPos a b support : ℕ)
    (bits out source membership : List Bool) (description wireCount : ℕ) (flag : Bool)
    (tapes : Fin 1059→List Bool) (hs : Stored cap core out source membership description wireCount flag tapes)
    (hn : tapes 1033=ZeroPadding.pad cap (frame bits))
    (ha : tapes 1041=ZeroPadding.pad cap (List.replicate a true))
    (hb : tapes 1045=ZeroPadding.pad cap (List.replicate b true))
    (hw : tapes 1047=ZeroPadding.pad cap (List.replicate support true))
    (hbits : 2*bits.length+1 ≤ cap) (hdesc : a+b+2 ≤ cap) (hwire : support+1+2 ≤ cap) : ∃ r,
    runFrom (publish threshold) (6*cap+10)
      ⟨(publish threshold).start,heads pos memberPos out description wireCount,tapes⟩=some r ∧
      r.steps ≤ 6*cap+10 ∧
      r.final.heads=heads pos memberPos (keptOutput (kept threshold membership memberPos) bits out)
        (description+(a+b)) (keptWires (kept threshold membership memberPos) support wireCount) ∧
      (∀ i,r.final.tapes (coreSlots i)=tapes (coreSlots i)) ∧
      Stored cap core (keptOutput (kept threshold membership memberPos) bits out) source membership
        (description+(a+b)) (keptWires (kept threshold membership memberPos) support wireCount) flag r.final.tapes := by
  obtain ⟨d,dr,dh,dt,ds⟩:=describe_run cap core pos memberPos a b out source membership
    description wireCount flag tapes hs ha hb hdesc
  let after:=Function.update tapes 1050 (List.replicate (description+(a+b)) true)
  obtain ⟨c,cr,cs,ch,ct,stored⟩:=choice_run threshold cap core pos memberPos support bits out source membership
    (description+(a+b)) wireCount flag after (hs.described _) (by
      change Function.update tapes 1050 _ 1033=_
      rw [Function.update_of_ne (by decide)];exact hn) (by
      change Function.update tapes 1050 _ 1047=_
      rw [Function.update_of_ne (by decide)];exact hw) hbits hwire
  have restart : Composition.restart d.final (choice threshold).start=
      (⟨(choice threshold).start,heads pos memberPos out (description+(a+b)) wireCount,after⟩ :
        Configuration 1059 _) := configuration_ext rfl dh dt
  rw [←restart] at cr
  have joined:=Composition.run_join describe (choice threshold) _ _ _ d c dr cr
  have bound:(2*(a+b)+6)+1+choiceBudget bits support ≤ 6*cap+10:=by
    have hc:=choice_budget_bound cap support bits hbits hwire
    omega
  have more:=runFrom_moreFuel (publish threshold) _
    (6*cap+10-((2*(a+b)+6)+1+choiceBudget bits support)) _ (Composition.joinedReceipt d c) joined
  rw [Nat.add_sub_of_le bound] at more
  refine ⟨Composition.joinedReceipt d c,more,?_,ch,?_,stored⟩
  · change d.steps+1+c.steps ≤ _
    omega
  · intro i
    change c.final.tapes (coreSlots i)=_
    rw [ct]
    exact Function.update_of_ne (show coreSlots i≠(1050 : Fin 1059) from core_other 1 i) _ _

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
