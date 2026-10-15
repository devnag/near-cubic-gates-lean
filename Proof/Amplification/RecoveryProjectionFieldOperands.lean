import Proof.Amplification.RecoveryProjectionFieldPrepare

/-! The second executed copy retains the same randomness word and seals the
entire physical operand-loading parent for the reusable projection evaluator. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionField
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem random_run (cap pos : Nat) (source bits randomness tail : List Bool)
    (hb : 2*randomness.length+1 ≤ cap) : ∃ r,
    runFrom randomMachine (4*randomness.length+4)
      ⟨randomMachine.start,heads pos,copied cap source bits randomness tail⟩=some r ∧
      r.final.heads=heads pos ∧ r.final.tapes=prepared cap source bits randomness tail ∧
      r.steps=4*randomness.length+4 := by
  obtain ⟨base,hr,ht,hh,hs⟩ := PCPFieldMoves.ready_run randomness tail cap cap
  obtain ⟨r,hrr,_hcontrol,hsteps,rh,rt,other⟩ := RecoveryFocus.dock randomSlots random_injective
    PCPFieldMoves.readyMachine _ (heads pos) (copied cap source bits randomness tail)
    (initialConfiguration PCPFieldMoves.readyMachine
      ![RepairOrdinary.frame randomness++tail,List.replicate cap false,List.replicate cap false])
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> simp [copied,input,randomSlots,initialConfiguration]) base hr
  refine ⟨r,hrr,?_,?_,hsteps.trans hs⟩
  · funext i
    by_cases h29 : i=29
    · subst i; exact (rh 0).trans (hh 0)
    by_cases h21 : i=21
    · subst i; exact (rh 1).trans (hh 1)
    by_cases h30 : i=30
    · subst i; exact (rh 2).trans (hh 2)
    have hn : ∀ j,randomSlots j≠i := by
      intro j; fin_cases j
      · exact Ne.symm h29
      · exact Ne.symm h21
      · exact Ne.symm h30
    exact (other i hn).1
  · funext i
    by_cases h29 : i=29
    · subst i; simpa [randomSlots,prepared,copied,input,PCPFieldMoves.output] using (rt 0).trans (congrFun ht 0)
    by_cases h21 : i=21
    · subst i; simpa [randomSlots,prepared,PCPFieldMoves.output] using (rt 1).trans (congrFun ht 1)
    by_cases h30 : i=30
    · subst i; simpa [randomSlots,prepared,copied,input,PCPFieldMoves.output,max_eq_left hb] using (rt 2).trans (congrFun ht 2)
    have hn : ∀ j,randomSlots j≠i := by
      intro j; fin_cases j
      · exact Ne.symm h29
      · exact Ne.symm h21
      · exact Ne.symm h30
    rw [(other i hn).2]
    simp [prepared,h21]

theorem operands_run (cap : Nat) (pre bits suffix randomness tail : List Bool)
    (hb : 2*bits.length+1 ≤ cap) (hr : 2*randomness.length+1 ≤ cap) : ∃ r,
    runFrom machine (4*bits.length+4*randomness.length+9)
      ⟨machine.start,heads pre.length,input cap (pre++RepairOrdinary.frame bits++suffix) randomness tail⟩=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1) ∧
      r.final.tapes=prepared cap (pre++RepairOrdinary.frame bits++suffix) bits randomness tail ∧
      r.steps=4*bits.length+4*randomness.length+9 := by
  obtain ⟨first,hfirst,fh,ft,fs⟩ := source_run cap pre bits suffix randomness tail hb
  obtain ⟨last,hlast,lh,lt,ls⟩ := random_run cap (pre.length+2*bits.length+1)
    (pre++RepairOrdinary.frame bits++suffix) bits randomness tail hr
  have he : Composition.restart first.final randomMachine.start=
      (⟨randomMachine.start,heads (pre.length+2*bits.length+1),
        copied cap (pre++RepairOrdinary.frame bits++suffix) bits randomness tail⟩ : Configuration 31 5) := by
    apply configuration_ext
    · rfl
    · exact fh
    · exact ft
  rw [←he] at hlast
  have hall := Composition.run_join sourceMachine randomMachine _ _ _ first last hfirst hlast
  have htime : (4*bits.length+4)+1+(4*randomness.length+4)=4*bits.length+4*randomness.length+9 := by omega
  rw [htime] at hall
  refine ⟨_,hall,lh,lt,?_⟩
  change first.steps+1+last.steps=_
  omega

theorem prepared_native (cap : Nat) (source bits randomness tail : List Bool) (i : Fin 28) :
    prepared cap source bits randomness tail (nativeSlots i)=
      RecoveryProjectionEval.reusableInput cap bits randomness i := by
  classical
  have hsmall := i.isLt
  have h28 : nativeSlots i≠28 := by intro h; have hv:=congrArg Fin.val h; dsimp [nativeSlots] at hv; omega
  have h29 : nativeSlots i≠29 := by intro h; have hv:=congrArg Fin.val h; dsimp [nativeSlots] at hv; omega
  have h0 : nativeSlots i=0 ↔ i=0 := by
    constructor
    · intro h; exact Fin.ext (congrArg (fun j : Fin 31=>j.val) h)
    · rintro rfl; rfl
  have h21 : nativeSlots i=21 ↔ i=21 := by
    constructor
    · intro h; exact Fin.ext (congrArg (fun j : Fin 31=>j.val) h)
    · rintro rfl; rfl
  by_cases hi0 : i=0
  · subst i; simp [prepared,copied,nativeSlots,RecoveryProjectionEval.reusableInput]
  by_cases hi21 : i=21
  · subst i; simp [prepared,nativeSlots,RecoveryProjectionEval.reusableInput]
  simp [prepared,copied,input,h0,h21,hi0,hi21,h28,h29,RecoveryProjectionEval.reusableInput]

end NearCubicWires.RepairSource.RecoveryProjectionField
