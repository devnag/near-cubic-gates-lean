import Proof.PCP.ProjectionNormalizationCodec

/-! Actual two-field raw header preparation. Two copies of the same fixed
field program read the source successively. The first dimension and its
cursor survive the second call; both unary drivers are produced from blank. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Header
open LocalBitMultitape RepairOrdinary RecoveryExecution RadixSemantics VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def secondSlots : Fin 7 → Fin 13 := ![0,7,8,9,10,11,12]
noncomputable def firstProgram := TapeEmbedding.machine 6 ValueField.machine
noncomputable def secondProgram := RecoveryFocus.machine secondSlots ValueField.machine
noncomputable def machine := Composition.machine firstProgram secondProgram
def source (a b tail : List Bool) := frame a++frame b++tail
noncomputable def input (word : List Bool) : Fin 13 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (7+6) => List Bool)
    (ValueField.input ValueField.machine.start word 0).tapes (fun _ : Fin 6 => [])
def budget (a b : List Bool) := ValueField.budget a+1+ValueField.budget b

theorem headers_run (a b tail : List Bool) :
    ∃ r,run machine (budget a b) (input (source a b tail))=some r ∧
      r.final.tapes 0=source a b tail ∧ r.final.tapes 5=CompareMachine.word (value a) ∧
      r.final.tapes 11=CompareMachine.word (value b) ∧
      (∀ i,r.final.heads i=if i=0 then (frame a++frame b).length else if i=5 ∨ i=11 then 1 else 0) ∧
      r.steps≤budget a b := by
  obtain ⟨left,hl,hls,hlo,hlh,hlt⟩ := ValueField.value_field_run [] a (frame b++tail)
  have hl' : runFrom ValueField.machine (ValueField.budget a)
      (ValueField.input ValueField.machine.start (source a b tail) 0)=some left := by
    simpa only [source,List.nil_append,List.append_assoc,List.length_nil] using hl
  have hfirst := TapeEmbedding.run_embed ValueField.machine (fun _ : Fin 6 => 0) (fun _ : Fin 6 => [])
    _ _ left hl'
  let first := TapeEmbedding.receipt (fun _ : Fin 6 => 0) (fun _ : Fin 6 => []) left
  have hi : TapeEmbedding.config (fun _ : Fin 6 => 0) (fun _ : Fin 6 => [])
      (ValueField.input ValueField.machine.start (source a b tail) 0)=
      initialConfiguration firstProgram (input (source a b tail)) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at hfirst
  obtain ⟨right,hr,hrs,hro,hrh,hrt⟩ := ValueField.value_field_run (frame a) b tail
  obtain ⟨last,hlast,hlf,hlt'⟩ := RecoveryFocus.run_config secondSlots (by decide) ValueField.machine
    first.final.heads first.final.tapes _ _ right hr
  have hmiddle : RecoveryFocus.config secondSlots first.final.heads first.final.tapes
      (ValueField.input ValueField.machine.start (frame a++frame b++tail) (frame a).length)=
      Composition.restart first.final secondProgram.start := by
    apply TransitionEvent.focused_eq secondSlots (by decide) (Composition.restart first.final secondProgram.start)
    · rfl
    · intro j; fin_cases j
      · have hh := hlh 0
        simpa [first,TapeEmbedding.receipt,TapeEmbedding.config,ValueField.input,Composition.restart,
          secondSlots,frame_length,Fin.addCases] using hh.symm
      all_goals rfl
    · intro j; fin_cases j
      · simpa [first,TapeEmbedding.receipt,TapeEmbedding.config,ValueField.input,Composition.restart,
          secondSlots,source,List.append_assoc,Fin.addCases] using hls.symm
      all_goals rfl
    · intro i _; rfl
    · intro i _; rfl
  rw [hmiddle] at hlast
  have hj := Composition.run_join firstProgram secondProgram _ _ _ first last hfirst hlast
  have hselectedHead (j : Fin 7) : last.final.heads (secondSlots j)=
      if j=0 then (frame a).length+2*b.length+1 else if j=5 then 1 else 0 := by
    rw [hlf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot secondSlots (by decide)] using hrh j
  have hselectedTape (j : Fin 7) : last.final.tapes (secondSlots j)=right.final.tapes j := by
    simp [hlf,RecoveryFocus.config,RecoveryFocus.pick_slot secondSlots (by decide)]
  have houtsideHead (i : Fin 13) (hi : ∀ j,secondSlots j≠i) : last.final.heads i=first.final.heads i := by
    have hp : RecoveryFocus.pick secondSlots i=none := by simp [RecoveryFocus.pick,show ¬∃ j,secondSlots j=i by simpa using hi]
    simp [hlf,RecoveryFocus.config,hp]
  have houtsideTape (i : Fin 13) (hi : ∀ j,secondSlots j≠i) : last.final.tapes i=first.final.tapes i := by
    have hp : RecoveryFocus.pick secondSlots i=none := by simp [RecoveryFocus.pick,show ¬∃ j,secondSlots j=i by simpa using hi]
    simp [hlf,RecoveryFocus.config,hp]
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_,?_,?_,?_⟩
  · exact (hselectedTape 0).trans hrs
  · change last.final.tapes 5=_
    rw [houtsideTape 5 (by decide)]
    exact hlo
  · exact (hselectedTape 5).trans hro
  · intro i
    change last.final.heads i=_
    fin_cases i
    · simpa [secondSlots,frame_length,List.length_append,Nat.add_assoc] using hselectedHead 0
    · change last.final.heads (1 : Fin 13)=0
      rw [houtsideHead 1 (by decide)]
      simpa [first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using hlh 1
    · change last.final.heads (2 : Fin 13)=0
      rw [houtsideHead 2 (by decide)]
      simpa [first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using hlh 2
    · change last.final.heads (3 : Fin 13)=0
      rw [houtsideHead 3 (by decide)]
      simpa [first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using hlh 3
    · change last.final.heads (4 : Fin 13)=0
      rw [houtsideHead 4 (by decide)]
      simpa [first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using hlh 4
    · change last.final.heads (5 : Fin 13)=1
      rw [houtsideHead 5 (by decide)]
      simpa [first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using hlh 5
    · change last.final.heads (6 : Fin 13)=0
      rw [houtsideHead 6 (by decide)]
      simpa [first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using hlh 6
    · simpa [secondSlots] using hselectedHead 1
    · simpa [secondSlots] using hselectedHead 2
    · simpa [secondSlots] using hselectedHead 3
    · simpa [secondSlots] using hselectedHead 4
    · simpa [secondSlots] using hselectedHead 5
    · simpa [secondSlots] using hselectedHead 6
  · change first.steps+1+last.steps≤budget a b
    change left.steps+1+last.steps≤budget a b
    dsimp only [budget]
    omega

end NearCubicWires.RepairSource.ProjectionNormalization.Header
