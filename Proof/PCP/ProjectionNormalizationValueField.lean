import Proof.PCP.ProjectionNormalizationUnary

/-! A raw source dimension field supplies its own counted driver: physically
copy the field, reset that copy only, and run the cold binary-to-unary
producer. The original source advances exactly over its framed field. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.ValueField
open LocalBitMultitape RepairOrdinary RecoveryExecution RadixSemantics VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 2) : Bool := decide (i=1)
def copyProgram := TapeEmbedding.machine 4 (MaskedReset.machine Field.machine selected)
def unarySlots : Fin 5 → Fin 7 := ![1,3,4,5,6]
noncomputable def unaryProgram := RecoveryFocus.machine unarySlots Unary.machine
noncomputable def machine := Composition.machine copyProgram unaryProgram
def input {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ) : Configuration 7 s :=
  ⟨q,![pos,0,0,0,0,0,0],![source,[],[],[],[],[],[]]⟩
def prepared {s : ℕ} (q : Fin s) (source bits : List Bool) (pos : ℕ) : Configuration 7 s :=
  ⟨q,![pos,0,0,0,0,0,0],![source,frame bits,List.replicate (2*bits.length+1) false,[],[],[],[]]⟩

theorem copy_run (pre bits suffix : List Bool) :
    ∃ r,runFrom copyProgram (4*bits.length+4)
      (input copyProgram.start (pre++frame bits++suffix) pre.length)=some r ∧
      r.final=prepared 4 (pre++frame bits++suffix) bits (pre.length+2*bits.length+1) ∧
      r.steps=4*bits.length+4 := by
  obtain ⟨base,hb,hf,hs⟩ := Field.copy_run pre bits suffix []
  obtain ⟨a,ha,haf,hat,_⟩ := MaskedReset.reset_run Field.machine selected _ _ base hb (by
    intro i hi
    have he : i=1 := of_decide_eq_true hi
    subst i
    rw [hf,hs]
    simp [Field.cfg,frame_length])
  have h := TapeEmbedding.run_embed (MaskedReset.machine Field.machine selected)
    (fun _ : Fin 4 => 0) (fun _ : Fin 4 => []) _ _ a ha
  have he : 2*base.steps+2=4*bits.length+4 := by omega
  rw [he] at h
  have hi : TapeEmbedding.config (fun _ : Fin 4 => 0) (fun _ : Fin 4 => [])
      (Rewind.recording (Field.cfg 0 (pre++frame bits++suffix) pre.length []) 0)=
      input copyProgram.start (pre++frame bits++suffix) pre.length := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at h
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 4 => 0) (fun _ : Fin 4 => []) a,h,?_,?_⟩
  · change TapeEmbedding.config _ _ a.final=_
    rw [haf,hf,hs]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,SelectiveReset.finished,Rewind.config,
        Field.cfg,selected,prepared,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,SelectiveReset.finished,Rewind.config,
        Field.cfg,prepared,Fin.addCases]
  · change a.steps=4*bits.length+4
    omega

theorem unary_entry (source bits : List Bool) (pos : ℕ) :
    RecoveryFocus.config unarySlots (prepared unaryProgram.start source bits pos).heads
      (prepared unaryProgram.start source bits pos).tapes (initialConfiguration Unary.machine (Unary.input bits))=
      prepared unaryProgram.start source bits pos := by
  apply TransitionEvent.focused_eq unarySlots (by decide) (prepared unaryProgram.start source bits pos)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i _; rfl
  · intro i _; rfl

theorem unary_run (source bits : List Bool) (pos : ℕ) :
    ∃ r,runFrom unaryProgram (Unary.budget bits) (prepared unaryProgram.start source bits pos)=some r ∧
      r.final.tapes 0=source ∧ r.final.tapes 5=CompareMachine.word (value bits) ∧
      (∀ i,r.final.heads i=if i=0 then pos else if i=5 then 1 else 0) ∧ r.steps≤Unary.budget bits := by
  obtain ⟨base,hb,hout,hh,ht⟩ := Unary.unary_run bits
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config unarySlots (by decide) Unary.machine
    (prepared unaryProgram.start source bits pos).heads (prepared unaryProgram.start source bits pos).tapes _ _ base hb
  rw [unary_entry] at hr
  have hp0 : RecoveryFocus.pick unarySlots 0=none := by
    simp [RecoveryFocus.pick,unarySlots,Fin.exists_fin_succ]
  have hp2 : RecoveryFocus.pick unarySlots 2=none := by
    simp [RecoveryFocus.pick,unarySlots,Fin.exists_fin_succ]
  have hp (j : Fin 5) := RecoveryFocus.pick_slot unarySlots (by decide) j
  refine ⟨r,hr,?_,?_,?_,hs.le.trans ht⟩
  · simp only [hf,RecoveryFocus.config,hp0,prepared]
    rfl
  · have h5 : RecoveryFocus.pick unarySlots 5=some 3 := hp 3
    simpa only [hf,RecoveryFocus.config,h5] using hout
  · intro i
    fin_cases i
    · simp [hf,RecoveryFocus.config,hp0,prepared]
    · have hj : RecoveryFocus.pick unarySlots 1=some 0 := hp 0
      simp [hf,RecoveryFocus.config,hj,hh]
    · simp [hf,RecoveryFocus.config,hp2,prepared]
    · have hj : RecoveryFocus.pick unarySlots 3=some 1 := hp 1
      simp [hf,RecoveryFocus.config,hj,hh]
    · have hj : RecoveryFocus.pick unarySlots 4=some 2 := hp 2
      simp [hf,RecoveryFocus.config,hj,hh]
    · have hj : RecoveryFocus.pick unarySlots 5=some 3 := hp 3
      simp [hf,RecoveryFocus.config,hj,hh]
    · have hj : RecoveryFocus.pick unarySlots 6=some 4 := hp 4
      simp [hf,RecoveryFocus.config,hj,hh]

def budget (bits : List Bool) := 32*(value bits+1)*(bits.length+1)

theorem value_field_run (pre bits suffix : List Bool) :
    ∃ r,runFrom machine (budget bits) (input machine.start (pre++frame bits++suffix) pre.length)=some r ∧
      r.final.tapes 0=pre++frame bits++suffix ∧ r.final.tapes 5=CompareMachine.word (value bits) ∧
      (∀ i,r.final.heads i=if i=0 then pre.length+2*bits.length+1 else if i=5 then 1 else 0) ∧
      r.steps≤budget bits := by
  obtain ⟨a,ha,haf,hat⟩ := copy_run pre bits suffix
  obtain ⟨b,hb,hsource,hout,hh,ht⟩ := unary_run (pre++frame bits++suffix) bits (pre.length+2*bits.length+1)
  have hmid : Composition.restart a.final unaryProgram.start=
      prepared unaryProgram.start (pre++frame bits++suffix) bits (pre.length+2*bits.length+1) := by rw [haf]; rfl
  rw [←hmid] at hb
  have h := Composition.run_join copyProgram unaryProgram _ _ _ a b ha hb
  have hbound : (4*bits.length+4)+1+Unary.budget bits≤budget bits := by
    dsimp only [budget,Unary.budget]
    nlinarith
  have hm := runFrom_moreFuel machine _ (budget bits-((4*bits.length+4)+1+Unary.budget bits))
    _ (Composition.joinedReceipt a b) h
  rw [Nat.add_sub_of_le hbound] at hm
  refine ⟨Composition.joinedReceipt a b,hm,hsource,hout,hh,?_⟩
  change a.steps+1+b.steps≤budget bits
  omega

end NearCubicWires.RepairSource.ProjectionNormalization.ValueField
