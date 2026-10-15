import Proof.PCP.ProjectionNormalizationConstants

/-! One actual normalized query row: copy all native source fields, then
append the fixed zero-projection field for each physical padding count.
Both counters are restored and both stream cursors are retained. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Row
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool)
    (native padding : ℕ) : Configuration 4 s :=
  ⟨q,![pos,out.length,1,1],![source,out,CompareMachine.word native,CompareMachine.word padding]⟩
def copySlots : Fin 3 → Fin 4 := ![0,1,2]
def padSlots : Fin 2 → Fin 4 := ![1,3]
noncomputable def copyProgram := RecoveryFocus.machine copySlots FieldList.machine
noncomputable def padProgram := RecoveryFocus.machine padSlots Constants.machine
noncomputable def machine := Composition.machine copyProgram padProgram
noncomputable def finalState :=
  (RepeatMachine.phaseCode (Constants.zeroField.length+1) 3).natAdd (Fintype.card (RepeatMachine.Control 3))

theorem copy_place (q : Fin (Fintype.card (RepeatMachine.Control 3)))
    (phase : Fin 5) (source oldOut out : List Bool) (oldPos pos native padding : ℕ) :
    RecoveryFocus.config copySlots
      (cfg q source oldPos oldOut native padding).heads
      (cfg q source oldPos oldOut native padding).tapes
      (FieldList.cfg phase source pos out native 1)=
    cfg (RepeatMachine.phaseCode 3 phase) source pos out native padding := by
  apply TransitionEvent.focused_eq copySlots (by decide)
    (cfg q source oldPos oldOut native padding)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;>
      first | rfl | exact False.elim (h 0 rfl) | exact False.elim (h 1 rfl)
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 1 rfl)

theorem pad_place (q : Fin (Fintype.card (RepeatMachine.Control (Constants.zeroField.length+1))))
    (phase : Fin 5) (source oldOut out : List Bool) (pos native padding : ℕ) :
    RecoveryFocus.config padSlots
      (cfg q source pos oldOut native padding).heads
      (cfg q source pos oldOut native padding).tapes
      (RepeatMachine.cfg phase (Constants.cfg Constants.zeroField out 0 (by omega)) padding 1)=
    cfg (RepeatMachine.phaseCode (Constants.zeroField.length+1) phase) source pos out native padding := by
  apply TransitionEvent.focused_eq padSlots (by decide)
    (cfg q source pos oldOut native padding)
  · rfl
  · intro j; fin_cases j <;> simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Constants.cfg,cfg,padSlots,Fin.addCases]
  · intro j; fin_cases j <;> simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Constants.cfg,cfg,padSlots,Fin.addCases]
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 0 rfl)
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 0 rfl)

theorem copy_run (pre : List Bool) (fields : List (List Bool)) (suffix out : List Bool) (padding : ℕ) :
    ∃ r,runFrom copyProgram ((FieldList.stream fields).length+3*fields.length+3)
      (cfg copyProgram.start (pre++FieldList.stream fields++suffix) pre.length out fields.length padding)=some r ∧
      r.final=cfg (RepeatMachine.phaseCode 3 3) (pre++FieldList.stream fields++suffix)
        (pre.length+(FieldList.stream fields).length) (out++FieldList.stream fields) fields.length padding ∧
      r.steps=(FieldList.stream fields).length+3*fields.length+3 := by
  obtain ⟨base,hb,hf,hs⟩ := FieldList.copy_run pre fields suffix out
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config copySlots (by decide) FieldList.machine
    (cfg copyProgram.start (pre++FieldList.stream fields++suffix) pre.length out fields.length padding).heads
    (cfg copyProgram.start (pre++FieldList.stream fields++suffix) pre.length out fields.length padding).tapes
    _ _ base hb
  rw [copy_place] at hr
  refine ⟨r,hr,?_,hrs.trans hs⟩
  rw [hrf,hf]
  exact copy_place _ 3 _ _ _ _ _ _ _

theorem padding_run (source out : List Bool) (pos native padding : ℕ) :
    ∃ r,runFrom padProgram (10*padding+3) (cfg padProgram.start source pos out native padding)=some r ∧
      r.final=cfg (RepeatMachine.phaseCode (Constants.zeroField.length+1) 3) source pos
        (out++(List.replicate padding Constants.zeroField).flatten) native padding ∧ r.steps≤10*padding+3 := by
  obtain ⟨base,hb,hs,hf⟩ := Constants.pad_run out padding
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config padSlots (by decide) Constants.machine
    (cfg padProgram.start source pos out native padding).heads
    (cfg padProgram.start source pos out native padding).tapes _ _ base hb
  change runFrom padProgram (10*padding+3)
    (RecoveryFocus.config padSlots _ _
      (RepeatMachine.cfg 0 (Constants.cfg Constants.zeroField out 0 (by omega)) padding 1))=some r at hr
  rw [pad_place] at hr
  refine ⟨r,hr,?_,hrs.le.trans hs⟩
  rw [hrf,hf]
  exact pad_place _ 3 _ _ _ _ _ _

def paddedFields (fields : List (List Bool)) (padding : ℕ) :=
  fields++List.replicate padding zeroCode.bits

theorem padded_stream (fields : List (List Bool)) (padding : ℕ) :
    FieldList.stream (paddedFields fields padding)=
      FieldList.stream fields++(List.replicate padding Constants.zeroField).flatten := by
  simp [FieldList.stream,paddedFields,List.map_replicate,Constants.zeroField]

theorem row_run (pre : List Bool) (fields : List (List Bool)) (suffix out : List Bool) (padding : ℕ) :
    ∃ r,runFrom machine ((FieldList.stream fields).length+3*fields.length+10*padding+7)
      (cfg machine.start (pre++FieldList.stream fields++suffix) pre.length out fields.length padding)=some r ∧
      r.final=cfg finalState (pre++FieldList.stream fields++suffix)
        (pre.length+(FieldList.stream fields).length) (out++FieldList.stream (paddedFields fields padding))
        fields.length padding ∧ r.steps≤(FieldList.stream fields).length+3*fields.length+10*padding+7 := by
  obtain ⟨a,ha,haf,hat⟩ := copy_run pre fields suffix out padding
  obtain ⟨b,hb,hbf,hbt⟩ := padding_run (pre++FieldList.stream fields++suffix)
    (out++FieldList.stream fields) (pre.length+(FieldList.stream fields).length) fields.length padding
  have hmid : Composition.restart a.final padProgram.start=
      cfg padProgram.start (pre++FieldList.stream fields++suffix)
        (pre.length+(FieldList.stream fields).length) (out++FieldList.stream fields) fields.length padding := by
    rw [haf]
    rfl
  rw [←hmid] at hb
  have h := Composition.run_join copyProgram padProgram _ _ _ a b ha hb
  have he : ((FieldList.stream fields).length+3*fields.length+3)+1+(10*padding+3)=
      (FieldList.stream fields).length+3*fields.length+10*padding+7 := by omega
  rw [he] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_⟩
  · change Composition.rightConfig _ b.final=_
    rw [hbf,padded_stream]
    simp only [List.append_assoc]
    rfl
  · change a.steps+1+b.steps≤_
    omega

end NearCubicWires.RepairSource.ProjectionNormalization.Row
