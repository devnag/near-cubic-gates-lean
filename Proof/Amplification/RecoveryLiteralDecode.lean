import Proof.Amplification.RecoveryThreeCellSemantics

/-! The physically retained literal code is the input of the same reusable
unpair body. The literal's variable replaces that retained field, while its
natural Boolean tag remains on the decoder's left-output tape. -/
namespace NearCubicWires.RepairOrdinary.RecoveryLiteralDecode
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (which : Fin 3) (j : Fin 23) : Fin 28 :=
  if j.val=0 then savedSlot which else ⟨j.val,by omega⟩
theorem slots_injective (which : Fin 3) : Function.Injective (slots which) := by
  intro i j h
  have hv := congrArg (fun k : Fin 28 => k.val) h
  simp only [slots,savedSlot] at hv
  split at hv <;> split at hv <;> apply Fin.ext <;> dsimp at hv <;> omega

noncomputable def machine (which : Fin 3) := RecoveryFocus.machine (slots which) (RecoveryDecodeStep.machine false)
noncomputable def output (s : State) (which : Fin 3) (word : List Bool) :=
  install (slots which) s.tapes
    (RecoveryReusableUnpair.input (RecoveryChildSelection.word false word)
      (max s.capacity (RecoveryReusableUnpair.capacity word+1))
      (RecoveryChildSelection.backing word s.capacity))

theorem literal_ready (s : State) (which : Fin 3) (word : List Bool)
    (hv : s.Valid) (hw : word.length=s.bits.length) (hf : s.fields which=frame word) :
    ReadyRun (machine which) (RecoveryDecodeStep.time word) s.tapes (output s which word) := by
  have hcap : RecoveryReusableUnpair.capacity word=RecoveryReusableUnpair.capacity s.bits := by
    simp only [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hw]
  have hb : ∀ i,(s.backing i).length≤RecoveryReusableUnpair.capacity word := by
    intro i
    rw [hcap]
    exact hv.1 i
  exact (RecoveryDecodeStep.decode_ready false word s.capacity s.backing hb).focus
    (slots which) (slots_injective which) s.tapes (by
      intro j
      fin_cases j
      · change s.tapes (savedSlot which)=frame word
        rw [tapes_saved,hf]
      all_goals
        simp [slots,State.tapes,State.core,RecoveryRawListStep.input,
          RecoveryReusableUnpair.input,RecoveryRawListStep.tapes,Fin.addCases,hcap])

theorem output_variable (s : State) (which : Fin 3) (word : List Bool) :
    output s which word (savedSlot which)=frame (RecoveryChildSelection.word false word) := by
  exact install_slot (slots which) (slots_injective which) _ _ 0

theorem output_tag (s : State) (which : Fin 3) (word : List Bool) :
    output s which word 17=ZeroPadding.pad (RecoveryReusableUnpair.capacity word)
      (frame (RecoveryFixedUnpair.leftWord word)) := by
  exact install_slot (slots which) (slots_injective which) _ _ 17

theorem output_other (s : State) (which : Fin 3) (word : List Bool) (i : Fin 28)
    (hi : i.val=0 ∨ 23 ≤ i.val) (hn : i≠savedSlot which) :
    output s which word i=s.tapes i := by
  apply install_other (slots which)
  intro j hj
  have he := congrArg (fun k : Fin 28 => k.val) hj
  by_cases hz : j.val=0
  · apply hn
    simpa only [slots,hz,ite_true] using hj.symm
  · simp only [slots,hz,ite_false] at he
    omega

theorem literal_values (word : List Bool) :
    value (RecoveryFixedUnpair.leftWord word)=(Nat.unpair (value word)).1 ∧
    value (RecoveryChildSelection.word false word)=(Nat.unpair (value word)).2 := by
  exact ⟨(RecoveryFixedUnpair.word_values word).1,RecoveryDecodeStep.child_value false word⟩

end NearCubicWires.RepairOrdinary.RecoveryLiteralDecode
