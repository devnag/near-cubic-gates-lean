import Proof.Amplification.RecoveryProjectionFieldOperands

/-! The actual source-field evaluation parent: two executed field copies,
then the same reusable original-code evaluator. Its external cursor and
randomness word survive for the next source-field iteration. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionField
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def evalMachine := RecoveryFocus.machine nativeSlots RecoveryProjectionEval.machine
noncomputable def fieldMachine := Composition.machine machine evalMachine
def fieldBudget (bits randomness : List Bool) :=
  4*bits.length+4*randomness.length+10+RecoveryProjectionEval.budget bits randomness

theorem native_small (i : Fin 28) : (nativeSlots i).val<28 := i.isLt

theorem evaluator_run (cap pos : Nat) (source bits randomness tail : List Bool)
    (hc : RecoveryProjectionEval.budget bits randomness+1 ≤ cap) : ∃ r,
    runFrom evalMachine (RecoveryProjectionEval.budget bits randomness)
      ⟨evalMachine.start,heads pos,prepared cap source bits randomness tail⟩=some r ∧
      r.final.heads=heads pos ∧
      r.final.tapes 26=ZeroPadding.pad cap [RecoveryProjectionEval.outputBit bits randomness] ∧
      (∀ i : Fin 28,(r.final.tapes (nativeSlots i)).length ≤ cap) ∧
      (∀ i : Fin 31,28 ≤ i.val → r.final.tapes i=prepared cap source bits randomness tail i) ∧
      r.steps ≤ RecoveryProjectionEval.budget bits randomness := by
  obtain ⟨out,⟨base,hr,ht,hh,hs⟩,hbit,hsize⟩ := RecoveryProjectionEval.reusable_ready cap bits randomness hc
  obtain ⟨r,hrr,_hcontrol,hsteps,rh,rt,other⟩ := RecoveryFocus.dock nativeSlots native_injective
    RecoveryProjectionEval.machine _ (heads pos) (prepared cap source bits randomness tail)
    (initialConfiguration RecoveryProjectionEval.machine (RecoveryProjectionEval.reusableInput cap bits randomness))
    (by
      intro j
      have hn : nativeSlots j≠28 := by intro h; have hv:=congrArg Fin.val h; have hj:=native_small j; omega
      simp [heads,hn,initialConfiguration])
    (prepared_native cap source bits randomness tail) base hr
  refine ⟨r,hrr,?_,?_,?_,?_,hsteps.trans_le hs⟩
  · funext i
    by_cases hi : i.val<28
    · let j : Fin 28 := ⟨i.val,hi⟩
      have he : nativeSlots j=i := Fin.ext rfl
      rw [←he,rh,hh]
      have hn : nativeSlots j≠28 := by intro h; have hv:=congrArg Fin.val h; have hj:=native_small j; omega
      simp [heads,hn]
    · have hn : ∀ j,nativeSlots j≠i := by
        intro j h; have hv:=congrArg Fin.val h; have hj:=native_small j; omega
      exact (other i hn).1
  · exact (rt 26).trans ((congrFun ht 26).trans hbit)
  · intro i; rw [rt,ht]; exact hsize i
  · intro i hi
    have hn : ∀ j,nativeSlots j≠i := by
      intro j h; have hv:=congrArg Fin.val h; have hj:=native_small j; omega
    exact (other i hn).2

theorem field_run (cap : Nat) (pre bits suffix randomness tail : List Bool)
    (hc : RecoveryProjectionEval.budget bits randomness+1 ≤ cap) : ∃ r,
    runFrom fieldMachine (fieldBudget bits randomness)
      ⟨fieldMachine.start,heads pre.length,input cap (pre++RepairOrdinary.frame bits++suffix) randomness tail⟩=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1) ∧
      r.final.tapes 26=ZeroPadding.pad cap [RecoveryProjectionEval.outputBit bits randomness] ∧
      (∀ i : Fin 28,(r.final.tapes (nativeSlots i)).length ≤ cap) ∧
      r.final.tapes 28=pre++RepairOrdinary.frame bits++suffix ∧
      r.final.tapes 29=RepairOrdinary.frame randomness++tail ∧
      r.final.tapes 30=List.replicate cap false ∧ r.steps ≤ fieldBudget bits randomness := by
  obtain ⟨hb,hr⟩ := RecoveryProjectionEval.frame_fits bits randomness cap hc
  rw [frame_length] at hb hr
  obtain ⟨first,hfirst,fh,ft,fs⟩ := operands_run cap pre bits suffix randomness tail hb hr
  obtain ⟨last,hlast,lh,bit,size,other,ls⟩ := evaluator_run cap (pre.length+2*bits.length+1)
    (pre++RepairOrdinary.frame bits++suffix) bits randomness tail hc
  have he : Composition.restart first.final evalMachine.start=
      (⟨evalMachine.start,heads (pre.length+2*bits.length+1),
        prepared cap (pre++RepairOrdinary.frame bits++suffix) bits randomness tail⟩ : Configuration 31 _) := by
    apply configuration_ext
    · rfl
    · exact fh
    · exact ft
  rw [←he] at hlast
  have hall := Composition.run_join machine evalMachine _ _ _ first last hfirst hlast
  have htime : (4*bits.length+4*randomness.length+9)+1+RecoveryProjectionEval.budget bits randomness=
      fieldBudget bits randomness := by unfold fieldBudget; omega
  rw [htime] at hall
  refine ⟨_,hall,lh,bit,size,?_,?_,?_,?_⟩
  · change last.final.tapes 28=_
    simpa [prepared,copied,input] using other 28 (by decide)
  · change last.final.tapes 29=_
    simpa [prepared,copied,input] using other 29 (by decide)
  · change last.final.tapes 30=_
    simpa [prepared,copied,input] using other 30 (by decide)
  · change first.steps+1+last.steps ≤ fieldBudget bits randomness
    unfold fieldBudget
    omega

end NearCubicWires.RepairSource.RecoveryProjectionField
