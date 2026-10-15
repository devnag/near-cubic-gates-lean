import Proof.Amplification.RecoveryProjectionReusable

/-! Physical loading of the next normalized projection field and the same
randomness word into the cleared evaluator bank. The source cursor advances
one field; both copied operands and all local heads are ready for evaluation. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionField
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceSlots : Fin 3→Fin 31 := ![28,0,30]
def randomSlots : Fin 3→Fin 31 := ![29,21,30]
def nativeSlots (i : Fin 28) : Fin 31 := i.castAdd 3
theorem source_injective : Function.Injective sourceSlots := by decide
theorem random_injective : Function.Injective randomSlots := by decide
theorem native_injective : Function.Injective nativeSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 31=>i.val) h)
def heads (pos : Nat) (i : Fin 31) := if i=28 then pos else 0
def input (cap : Nat) (source randomness tail : List Bool) (i : Fin 31) :=
  if i=28 then source else if i=29 then RepairOrdinary.frame randomness++tail else List.replicate cap false
noncomputable def copied (cap : Nat) (source bits randomness tail : List Bool) :=
  Function.update (input cap source randomness tail) 0 (ZeroPadding.pad cap (RepairOrdinary.frame bits))
noncomputable def prepared (cap : Nat) (source bits randomness tail : List Bool) :=
  Function.update (copied cap source bits randomness tail) 21 (ZeroPadding.pad cap (RepairOrdinary.frame randomness))
noncomputable def sourceMachine := RecoveryFocus.machine sourceSlots PCPFieldMoves.advanceMachine
noncomputable def randomMachine := RecoveryFocus.machine randomSlots PCPFieldMoves.readyMachine
noncomputable def machine := Composition.machine sourceMachine randomMachine

theorem source_run (cap : Nat) (pre bits suffix randomness tail : List Bool)
    (hb : 2*bits.length+1 ≤ cap) : ∃ r,
    runFrom sourceMachine (4*bits.length+4)
      ⟨sourceMachine.start,heads pre.length,input cap (pre++RepairOrdinary.frame bits++suffix) randomness tail⟩=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1) ∧
      r.final.tapes=copied cap (pre++RepairOrdinary.frame bits++suffix) bits randomness tail ∧
      r.steps=4*bits.length+4 := by
  obtain ⟨base,hr,ht,hh,hs⟩ := PCPFieldMoves.advance_run pre bits suffix cap cap
  obtain ⟨r,hrr,_hcontrol,hsteps,rh,rt,other⟩ := RecoveryFocus.dock sourceSlots source_injective
    PCPFieldMoves.advanceMachine _ (heads pre.length)
    (input cap (pre++RepairOrdinary.frame bits++suffix) randomness tail)
    (PCPFieldMoves.entry pre bits suffix cap cap)
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [input,PCPFieldMoves.entry,PCPFieldMoves.caps,
      ZeroPadding.config,ZeroPadding.pad,Rewind.recording,Rewind.config,
      ProjectionNormalization.Field.cfg] <;> rfl) base hr
  refine ⟨r,hrr,?_,?_,hsteps.trans hs⟩
  · funext i
    by_cases h28 : i=28
    · subst i; exact (rh 0).trans (congrFun hh 0)
    by_cases h0 : i=0
    · subst i; exact (rh 1).trans (congrFun hh 1)
    by_cases h30 : i=30
    · subst i; exact (rh 2).trans (congrFun hh 2)
    have hn : ∀ j,sourceSlots j≠i := by
      intro j; fin_cases j
      · exact Ne.symm h28
      · exact Ne.symm h0
      · exact Ne.symm h30
    rw [(other i hn).1]
    simp [heads,h28]
  · funext i
    by_cases h28 : i=28
    · subst i; simpa [sourceSlots,copied,input,PCPFieldMoves.output] using (rt 0).trans (congrFun ht 0)
    by_cases h0 : i=0
    · subst i; simpa [sourceSlots,copied,PCPFieldMoves.output] using (rt 1).trans (congrFun ht 1)
    by_cases h30 : i=30
    · subst i; simpa [sourceSlots,copied,input,PCPFieldMoves.output,max_eq_left hb] using (rt 2).trans (congrFun ht 2)
    have hn : ∀ j,sourceSlots j≠i := by
      intro j; fin_cases j
      · exact Ne.symm h28
      · exact Ne.symm h0
      · exact Ne.symm h30
    rw [(other i hn).2]
    simp [copied,h0]

end NearCubicWires.RepairSource.RecoveryProjectionField
