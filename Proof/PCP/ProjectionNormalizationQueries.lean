import Proof.PCP.ProjectionNormalizationRows

/-! Complete prepared projection stream: native queries are copied and widened;
unused query coordinates are emitted by a physically supplied product driver.
No input-dependent word is put into the finite control of this machine. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Queries
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool)
    (native padding queries extra : ℕ) : Configuration 6 s :=
  ⟨q,![pos,out.length,1,1,1,1],![source,out,CompareMachine.word native,CompareMachine.word padding,
    CompareMachine.word queries,CompareMachine.word extra]⟩
def copySlots : Fin 5 → Fin 6 := ![0,1,2,3,4]
def padSlots : Fin 2 → Fin 6 := ![1,5]
noncomputable def copyProgram := RecoveryFocus.machine copySlots Rows.machine
noncomputable def padProgram := RecoveryFocus.machine padSlots Constants.machine
noncomputable def machine := Composition.machine copyProgram padProgram
noncomputable def finalState :=
  (RepeatMachine.phaseCode (Constants.zeroField.length+1) 3).natAdd
    (Fintype.card (RepeatMachine.Control (Fintype.card (RepeatMachine.Control 3)+
      Fintype.card (RepeatMachine.Control (Constants.zeroField.length+1)))))

theorem copy_place (q : Fin (Fintype.card (RepeatMachine.Control (Fintype.card (RepeatMachine.Control 3)+
      Fintype.card (RepeatMachine.Control (Constants.zeroField.length+1))))))
    (phase : Fin 5) (source oldOut out : List Bool) (oldPos pos native padding queries extra : ℕ) :
    RecoveryFocus.config copySlots (cfg q source oldPos oldOut native padding queries extra).heads
      (cfg q source oldPos oldOut native padding queries extra).tapes
      (Rows.cfg phase source pos out native padding queries 1)=
      cfg (Rows.cfg phase source pos out native padding queries 1).control source pos out native padding queries extra := by
  apply TransitionEvent.focused_eq copySlots (by decide) (cfg q source oldPos oldOut native padding queries extra)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 0 rfl) | exact False.elim (h 1 rfl)
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 1 rfl)

theorem pad_place (q : Fin (Fintype.card (RepeatMachine.Control (Constants.zeroField.length+1))))
    (phase : Fin 5) (source oldOut out : List Bool) (pos native padding queries extra : ℕ) :
    RecoveryFocus.config padSlots (cfg q source pos oldOut native padding queries extra).heads
      (cfg q source pos oldOut native padding queries extra).tapes
      (RepeatMachine.cfg phase (Constants.cfg Constants.zeroField out 0 (by omega)) extra 1)=
      cfg (RepeatMachine.phaseCode (Constants.zeroField.length+1) phase) source pos out native padding queries extra := by
  apply TransitionEvent.focused_eq padSlots (by decide) (cfg q source pos oldOut native padding queries extra)
  · rfl
  · intro j; fin_cases j <;> simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Constants.cfg,cfg,padSlots,Fin.addCases]
  · intro j; fin_cases j <;> simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Constants.cfg,cfg,padSlots,Fin.addCases]
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 0 rfl)
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 0 rfl)

theorem copy_run (pre : List Bool) (rows : List (List (List Bool))) (suffix out : List Bool)
    (native padding extra : ℕ) (hrows : ∀ row∈rows,row.length=native) :
    ∃ r,runFrom copyProgram ((Rows.stream rows).length+rows.length*(3*native+10*padding+10)+3)
      (cfg copyProgram.start (pre++Rows.stream rows++suffix) pre.length out native padding rows.length extra)=some r ∧
      r.final=cfg (Rows.cfg 3 [] 0 [] native padding rows.length 1).control
        (pre++Rows.stream rows++suffix) (pre.length+(Rows.stream rows).length)
        (out++Rows.stream (Rows.padded rows padding)) native padding rows.length extra ∧
      r.steps≤(Rows.stream rows).length+rows.length*(3*native+10*padding+10)+3 := by
  obtain ⟨base,hb,hs,hf⟩ := Rows.rows_run pre rows suffix out native padding hrows
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config copySlots (by decide) Rows.machine
    (cfg copyProgram.start (pre++Rows.stream rows++suffix) pre.length out native padding rows.length extra).heads
    (cfg copyProgram.start (pre++Rows.stream rows++suffix) pre.length out native padding rows.length extra).tapes
    _ _ base hb
  rw [copy_place] at hr
  refine ⟨r,hr,?_,hrs.le.trans hs⟩
  rw [hrf,hf]
  exact copy_place _ 3 _ _ _ _ _ _ _ _ _

theorem padding_run (source out : List Bool) (pos native padding queries extra : ℕ) :
    ∃ r,runFrom padProgram (10*extra+3) (cfg padProgram.start source pos out native padding queries extra)=some r ∧
      r.final=cfg (RepeatMachine.phaseCode (Constants.zeroField.length+1) 3) source pos
        (out++(List.replicate extra Constants.zeroField).flatten) native padding queries extra ∧ r.steps≤10*extra+3 := by
  obtain ⟨base,hb,hs,hf⟩ := Constants.pad_run out extra
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config padSlots (by decide) Constants.machine
    (cfg padProgram.start source pos out native padding queries extra).heads
    (cfg padProgram.start source pos out native padding queries extra).tapes _ _ base hb
  change runFrom padProgram (10*extra+3) (RecoveryFocus.config padSlots _ _
    (RepeatMachine.cfg 0 (Constants.cfg Constants.zeroField out 0 (by omega)) extra 1))=some r at hr
  rw [pad_place] at hr
  refine ⟨r,hr,?_,hrs.le.trans hs⟩
  rw [hrf,hf]
  exact pad_place _ 3 _ _ _ _ _ _ _ _

def output (rows : List (List (List Bool))) (padding extra : ℕ) :=
  Rows.stream (Rows.padded rows padding)++(List.replicate extra Constants.zeroField).flatten

theorem queries_run (pre : List Bool) (rows : List (List (List Bool))) (suffix out : List Bool)
    (native padding extra : ℕ) (hrows : ∀ row∈rows,row.length=native) :
    ∃ r,runFrom machine ((Rows.stream rows).length+rows.length*(3*native+10*padding+10)+10*extra+7)
      (cfg machine.start (pre++Rows.stream rows++suffix) pre.length out native padding rows.length extra)=some r ∧
      r.final=cfg finalState (pre++Rows.stream rows++suffix) (pre.length+(Rows.stream rows).length)
        (out++output rows padding extra) native padding rows.length extra ∧
      r.steps≤(Rows.stream rows).length+rows.length*(3*native+10*padding+10)+10*extra+7 := by
  obtain ⟨a,ha,haf,hat⟩ := copy_run pre rows suffix out native padding extra hrows
  obtain ⟨b,hb,hbf,hbt⟩ := padding_run (pre++Rows.stream rows++suffix)
    (out++Rows.stream (Rows.padded rows padding)) (pre.length+(Rows.stream rows).length)
    native padding rows.length extra
  have hmid : Composition.restart a.final padProgram.start=
      cfg padProgram.start (pre++Rows.stream rows++suffix) (pre.length+(Rows.stream rows).length)
        (out++Rows.stream (Rows.padded rows padding)) native padding rows.length extra := by rw [haf]; rfl
  rw [←hmid] at hb
  have h := Composition.run_join copyProgram padProgram _ _ _ a b ha hb
  have he : ((Rows.stream rows).length+rows.length*(3*native+10*padding+10)+3)+1+(10*extra+3)=
      (Rows.stream rows).length+rows.length*(3*native+10*padding+10)+10*extra+7 := by omega
  rw [he] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_⟩
  · change Composition.rightConfig _ b.final=_
    rw [hbf]
    simp only [output,List.append_assoc]
    rfl
  · change a.steps+1+b.steps≤_
    omega

end NearCubicWires.RepairSource.ProjectionNormalization.Queries
