import Proof.Amplification.RecoveryLiteralTruth

/-! The literal decoder returns the same persistent clause-state carrier.
This supplies the next literal call with its actual bounded scratch/fields. -/
namespace NearCubicWires.RepairOrdinary.RecoveryLiteralDecode
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def decodedState (s : State) (which : Fin 3) (word : List Bool) : State :=
  ⟨s.bits,max s.capacity (RecoveryReusableUnpair.capacity word+1),
    RecoveryChildSelection.backing word s.capacity,
    Function.update s.fields which (frame (RecoveryChildSelection.word false word)),s.flag,s.result⟩

theorem decoded_slot (s : State) (which : Fin 3) (word : List Bool) (hw : word.length=s.bits.length) (j : Fin 23) :
    RecoveryReusableUnpair.input (RecoveryChildSelection.word false word)
      (max s.capacity (RecoveryReusableUnpair.capacity word+1)) (RecoveryChildSelection.backing word s.capacity) j=
      (decodedState s which word).tapes (slots which j) := by
  have hcap : RecoveryReusableUnpair.capacity (RecoveryChildSelection.word false word)=RecoveryReusableUnpair.capacity s.bits := by
    simp [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,RecoveryChildSelection.word_length,hw]
  fin_cases j
  · change frame (RecoveryChildSelection.word false word)=(decodedState s which word).tapes (savedSlot which)
    rw [tapes_saved]
    simp [decodedState]
  all_goals
    simp [slots,State.tapes,State.core,RecoveryRawListStep.input,RecoveryRawListStep.tapes,
      RecoveryReusableUnpair.input,Fin.addCases,decodedState,hcap]

theorem decoded_outside (s : State) (which : Fin 3) (word : List Bool) (i : Fin 28)
    (hi : ∀ j,slots which j≠i) : s.tapes i=(decodedState s which word).tapes i := by
  have hlarge : i.val=0 ∨ 23 ≤ i.val := by
    by_contra h
    have hn : i.val≠0 := by omega
    exact hi ⟨i.val,by omega⟩ (by simp [slots,hn])
  have hneq : i≠savedSlot which := by
    intro he
    exact hi 0 he.symm
  refine Fin.addCases (m:=24) (n:=4) (motive:=fun k=>
    (k.val=0 ∨ 23 ≤ k.val) → k≠savedSlot which → s.tapes k=(decodedState s which word).tapes k) ?_ ?_ i hlarge hneq
  · intro j hj _
    have he : j.val=0 ∨ j.val=23 := by simp only [Fin.val_castAdd] at hj; omega
    rcases he with he|he
    · have hz : j=0 := Fin.ext he
      subst j
      rfl
    · have hz : j=23 := Fin.ext he
      subst j
      rfl
  · intro j _ hj
    refine Fin.addCases (m:=3) (n:=1) (motive:=fun k=>
      k.natAdd 24≠savedSlot which → s.tapes (k.natAdd 24)=(decodedState s which word).tapes (k.natAdd 24)) ?_ ?_ j hj
    · intro k hk
      have hkw : k≠which := by intro he; subst k; exact hk rfl
      simp [State.tapes,decodedState,hkw]
    · intro k _
      fin_cases k
      rfl

theorem decoded_output (s : State) (which : Fin 3) (word : List Bool) (hw : word.length=s.bits.length) :
    output s which word=(decodedState s which word).tapes := by
  funext i
  by_cases hi : ∃ j,slots which j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [output,install_slot (slots which) (slots_injective which)]
    exact decoded_slot s which word hw j
  · rw [output,install_other (slots which) _ _ _ (by intro j he; exact hi ⟨j,he⟩)]
    exact decoded_outside s which word i (by intro j he; exact hi ⟨j,he⟩)

theorem decoded_valid (s : State) (which : Fin 3) (word : List Bool)
    (hv : s.Valid) (hw : word.length=s.bits.length) : (decodedState s which word).Valid := by
  constructor
  · intro i
    have h := RecoveryChildSelection.backing_bound word s.capacity i
    simpa [decodedState,RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hw] using h
  · intro i
    by_cases he : i=which
    · subst i
      simp [decodedState,RecoveryChildSelection.word_length,hw]
    · simpa [decodedState,he] using hv.2 i

end NearCubicWires.RepairOrdinary.RecoveryLiteralDecode
