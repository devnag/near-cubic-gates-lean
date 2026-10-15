import Proof.PCP.PCPSerializerCountEntry

/-! Whole entry controller for the fixed128-tape serializer. The retained
field-count sentinel is copied to the raw DFS count, both entry/return moves
and the continuation-bottom write are executed, and every other cursor lives. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerCountEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def output (n : ℕ) (tapes : Fin 128 → List Bool) : Fin 128 → List Bool :=
  install slots (bootTapes tapes) (UWalkUnary.result false false 0 n)

theorem output_fields (n : ℕ) (tapes : Fin 128 → List Bool) :
    output n tapes 2=CompareMachine.word n ∧ output n tapes 79=List.replicate n true ∧
    output n tapes 81=[false] ∧ output n tapes 88=List.replicate (n+2) false := by
  refine ⟨?_,?_,?_,?_⟩
  · change install slots _ _ (slots 0)=_
    rw [install_slot _ slots_injective]
    simp [UWalkUnary.result,UWalkUnary.source,ZeroPadding.pad]
  · change install slots _ _ (slots 1)=_
    rw [install_slot _ slots_injective]
    simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead]
  · rw [output,install_other _ _ _ _ (by intro i; fin_cases i <;> simp [slots])]
    simp [bootTapes]
  · change install slots _ _ (slots 2)=_
    rw [install_slot _ slots_injective]
    rfl

theorem output_other (n : ℕ) (tapes : Fin 128 → List Bool) (hc : tapes 2=CompareMachine.word n)
    (i : Fin 128) (h79 : i≠79) (h81 : i≠81) (h88 : i≠88) : output n tapes i=tapes i := by
  by_cases h2 : i=2
  · subst i; exact (output_fields n tapes).1.trans hc.symm
  rw [output,install_other _ _ _ _ (by
    intro j; fin_cases j <;> simp [slots,Ne.symm h2,Ne.symm h79,Ne.symm h88])]
  simp [bootTapes,h81]

theorem ready_run (n : ℕ) (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool)
    (hc : tapes 2=CompareMachine.word n) (h79 : tapes 79=[]) (h81 : tapes 81=[]) (h88 : tapes 88=[])
    (hcH : heads 2=1) (h79H : heads 79=0) (h81H : heads 81=0) (h88H : heads 88=0) :
    ∃ r,runFrom machine (2*n+10) ⟨machine.start,heads,tapes⟩=some r ∧
      r.steps ≤ 2*n+10 ∧ r.final.heads=finalHeads heads ∧ r.final.tapes=output n tapes := by
  obtain ⟨a,ha,haf,has⟩ := command_run true heads tapes
  rw [boot_config heads tapes hcH h81H h81] at haf
  have hp := UWalkUnary.ready false false 0 n
  obtain ⟨b,hb,hbh,hbt,hbs⟩ := hp.focus_at slots slots_injective (bootHeads heads) (bootTapes tapes)
    (by intro i; fin_cases i <;> simp [slots,bootTapes,UWalkUnary.input,UWalkUnary.source,ZeroPadding.pad,hc,h79,h88])
    (by intro i; fin_cases i <;> simp [slots,bootHeads,h79H,h88H])
  have hmid : Composition.restart a.final copy.start=
      (⟨(UWalkUnary.machine false false).start,bootHeads heads,bootTapes tapes⟩ : Configuration 128 _) := by
    rw [haf]
    rfl
  have hb' : runFrom copy (2*n+6) (Composition.restart a.final copy.start)=some b := by
    rw [hmid]
    exact hb
  have hfirst := Composition.run_join (command true) copy _ _ _ a b ha hb'
  obtain ⟨c,hcRun,hcf,hcs⟩ := command_run false (bootHeads heads) (output n tapes)
  rw [finish_config heads (output n tapes) hcH] at hcf
  have hend : Composition.restart (Composition.joinedReceipt a b).final (command false).start=
      (⟨0,bootHeads heads,output n tapes⟩ : Configuration 128 2) := by
    apply configuration_ext
    · rfl
    · exact hbh
    · exact hbt
  have hcRun' : runFrom (command false) 1
      (Composition.restart (Composition.joinedReceipt a b).final (command false).start)=some c := by
    rw [hend]
    exact hcRun
  have h := Composition.run_join (Composition.machine (command true) copy) (command false) _ _ _
    (Composition.joinedReceipt a b) c hfirst hcRun'
  have htime : (1+1+(2*n+6))+1+1=2*n+10 := by omega
  rw [htime] at h
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt a b) c,h,?_,?_,?_⟩
  · dsimp only [Composition.joinedReceipt]
    omega
  · change c.final.heads=finalHeads heads
    rw [hcf]
  · change c.final.tapes=output n tapes
    rw [hcf]

end NearCubicWires.RepairOrdinary.PCPSerializerCountEntry
