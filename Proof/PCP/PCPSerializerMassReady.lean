import Proof.PCP.PCPSerializerMassLoop
import Proof.PCP.ProjectionNormalizationSuffixRestore

/-! The actual counted field scan is followed by two paid selective resets.
The original source cursor and the count sentinel return to their entry
positions, while a fresh tape contains the raw unary byte mass at head zero. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerCapacity.MassReady
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev scanSize := Fintype.card (RepeatMachine.Control 3)
abbrev size := scanSize+2+2
noncomputable def sourceReset := CursorRestore.machine MassLoop.machine 0
noncomputable def machine := CursorRestore.machine sourceReset 1
noncomputable def finalCode : Fin size := (1 : Fin 2).natAdd (scanSize+2)
def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos mass count sourceLog massLog : ℕ) : Configuration 5 s :=
  ⟨q,![pos,0,1,0,0],![source,List.replicate mass true,CompareMachine.word count,
    List.replicate sourceLog false,List.replicate massLog false]⟩

theorem source_forward : CursorRestore.NoLeft MassLoop.machine 0 :=
  CursorRestore.repeat_forward FieldCount.machine (fun _ _ => true) (0 : Fin 2) (FieldCount.noLeft 0)
theorem mass_forward : CursorRestore.NoLeft sourceReset 1 :=
  CursorRestore.other_forward MassLoop.machine 0 (1 : Fin 3) (by decide)
    (CursorRestore.repeat_forward FieldCount.machine (fun _ _ => true) (1 : Fin 2) (FieldCount.noLeft 1))

theorem input_eq (source : List Bool) (pos count : ℕ) :
    Rewind.recording (Rewind.recording (MassLoop.cfg 0 source pos [] count 1) 0) 0=
      cfg machine.start source pos 0 count 0 0 := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;>
      simp [Rewind.recording,Rewind.config,MassLoop.cfg,RepeatMachine.cfg,controlConfig,
        TapeEmbedding.config,FieldCount.cfg,cfg,Fin.addCases]
  · funext i; fin_cases i <;>
      simp [Rewind.recording,Rewind.config,MassLoop.cfg,RepeatMachine.cfg,controlConfig,
        TapeEmbedding.config,FieldCount.cfg,cfg,Fin.addCases]

theorem mass_run (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool) :
    ∃ r sourceLog massLog,runFrom machine (4*((FieldList.stream fields).length+3*fields.length+3)+6)
      (cfg machine.start (pre++FieldList.stream fields++suffix) pre.length 0 fields.length 0 0)=some r ∧
      sourceLog ≤ (FieldList.stream fields).length+3*fields.length+3 ∧
      massLog ≤ 2*((FieldList.stream fields).length+3*fields.length+3)+2 ∧
      r.steps ≤ 4*((FieldList.stream fields).length+3*fields.length+3)+6 ∧
      r.final=cfg finalCode (pre++FieldList.stream fields++suffix) pre.length
        (FieldList.stream fields).length fields.length sourceLog massLog := by
  obtain ⟨base,hb,hbf,hbs⟩ := MassLoop.count_run pre fields suffix []
  obtain ⟨a,sourceLog,ha,hsl,has,haf⟩ := CursorRestore.restore_run MassLoop.machine 0 source_forward _ _ base hb
  obtain ⟨r,massLog,hr,hml,hrs,hrf⟩ := CursorRestore.restore_run sourceReset 1 mass_forward _ _ a ha
  change runFrom machine (2*a.steps+2)
    (Rewind.recording (Rewind.recording (MassLoop.cfg _ _ _ _ _ _) 0) 0)=some r at hr
  rw [input_eq] at hr
  have htime : 2*a.steps+2 ≤ 4*((FieldList.stream fields).length+3*fields.length+3)+6 := by omega
  have hm := runFrom_moreFuel machine _
    (4*((FieldList.stream fields).length+3*fields.length+3)+6-(2*a.steps+2)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨r,sourceLog,massLog,hm,by omega,by omega,by omega,?_⟩
  rw [hrf,haf,hbf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;>
      simp [SelectiveReset.finished,Rewind.config,Rewind.recording,MassLoop.cfg,RepeatMachine.cfg,
        controlConfig,TapeEmbedding.config,FieldCount.cfg,cfg,Fin.addCases]
  · funext i; fin_cases i <;>
      simp [SelectiveReset.finished,Rewind.config,MassLoop.cfg,RepeatMachine.cfg,
        controlConfig,TapeEmbedding.config,FieldCount.cfg,cfg,Fin.addCases]

theorem count_le_mass (fields : List (List Bool)) : fields.length ≤ (FieldList.stream fields).length := by
  induction fields with
  | nil => simp
  | cons bits fields ih =>
    simp only [List.length_cons,FieldList.stream_cons,List.length_append,frame_length]
    omega

theorem bounded_run (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool) :
    ∃ r sourceLog massLog,runFrom machine (16*(FieldList.stream fields).length+18)
      (cfg machine.start (pre++FieldList.stream fields++suffix) pre.length 0 fields.length 0 0)=some r ∧
      r.steps ≤ 16*(FieldList.stream fields).length+18 ∧
      r.final=cfg finalCode (pre++FieldList.stream fields++suffix) pre.length
        (FieldList.stream fields).length fields.length sourceLog massLog := by
  obtain ⟨r,sl,ml,hr,_,_,hs,hf⟩ := mass_run pre fields suffix
  have hcount := count_le_mass fields
  have hb : 4*((FieldList.stream fields).length+3*fields.length+3)+6 ≤
      16*(FieldList.stream fields).length+18 := by omega
  have hmore := runFrom_moreFuel machine _
    (16*(FieldList.stream fields).length+18-(4*((FieldList.stream fields).length+3*fields.length+3)+6)) _ r hr
  rw [Nat.add_sub_of_le hb] at hmore
  exact ⟨r,sl,ml,hmore,by omega,hf⟩

end NearCubicWires.RepairOrdinary.PCPSerializerCapacity.MassReady
