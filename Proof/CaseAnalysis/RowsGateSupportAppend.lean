import Proof.CaseAnalysis.RowsGateSupportReady
import Proof.PCP.ProjectionNormalizationSuffixRestore

/-! The same support loop appends immediately after the native arity.
No second copy of the filtered weight list or output-length tape is needed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
open LocalBitMultitape RecoveryExecution RadixSemantics
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def appendInput (fields : List (Bool×List Bool)) (membership out : List Bool) : Configuration 6 2 :=
  ⟨0,![0,0,out.length,0,0,0],
    ![fields.flatMap fieldWord,[],out,frame membership,[],CompareMachine.word fields.length]⟩
def appendBooted (fields : List (Bool×List Bool)) (membership out : List Bool) : Configuration 6 2 :=
  ⟨1,![0,0,out.length,0,0,1],
    ![fields.flatMap fieldWord,[],out,frame membership,[true],CompareMachine.word fields.length]⟩
noncomputable def appendEntry (_compressed : Bool) (fields : List (Bool×List Bool))
    (membership out : List Bool) :=
  Composition.leftConfig 10 (appendInput fields membership out)

theorem append_bootstrap (fields : List (Bool×List Bool)) (membership out : List Bool) : ∃ actual,
    runFrom bootstrap 1 (appendInput fields membership out)=some actual ∧
      actual.final=appendBooted fields membership out ∧ actual.steps=1 := by
  have hs : step bootstrap (appendInput fields membership out)=some (appendBooted fields membership out) := by
    simp [step,bootstrap,appendInput]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem append_run (compressed : Bool) (fields : List (Bool×List Bool))
    (membership out : List Bool) (w : ℕ) (hw : ∀ field∈fields,field.2.length ≤ w) : ∃ actual,
    runFrom (preparedMachine compressed) (preparedBudget w fields.length)
      (appendEntry compressed fields membership out)=some actual ∧
      actual.steps ≤ preparedBudget w fields.length ∧
      actual.final.tapes 2=out++(List.range fields.length).flatMap (emission compressed fields membership) ∧
      actual.final.heads 2=(out++(List.range fields.length).flatMap (emission compressed fields membership)).length ∧
      actual.final.tapes 4=[validity fields membership true fields.length] := by
  obtain ⟨a,ha,af,as⟩ := append_bootstrap fields membership out
  obtain ⟨b,hb,bf,bs⟩ := loop_run compressed fields membership [] out [] [] true w hw
  have hi : RepeatMachine.cfg 0 (entry fields membership [] [] [] true 0 out) fields.length 1=
      Composition.restart a.final (loop compressed).start := by
    rw [af]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> simp [RepeatMachine.cfg,controlConfig,entry,cfg,scratch,validity,appendBooted,
        TapeEmbedding.config,Composition.restart,Fin.addCases]
  rw [hi] at hb
  have h := Composition.run_join bootstrap (loop compressed) _ _ _ a b ha hb
  have he : 1+1+loopBudget w fields.length=preparedBudget w fields.length := by unfold preparedBudget;omega
  rw [he] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    unfold preparedBudget
    omega
  all_goals first | change b.final.tapes _=_ | change b.final.heads _=_
  all_goals rw [bf]
  all_goals simp [RepeatMachine.cfg,controlConfig,entry,cfg,TapeEmbedding.config,Fin.addCases]

theorem append_forward (compressed : Bool) : CursorRestore.NoLeft (preparedMachine compressed) 2 := by
  apply CursorRestore.composition_forward
  · intro q bits a ha
    simp only [bootstrap] at ha
    split at ha
    · cases ha;simp
    · contradiction
  · refine CursorRestore.repeat_forward (machine compressed) (fun _ _ => true) (2 : Fin 5) ?_
    intro q bits a ha
    simp only [machine] at ha
    split_ifs at ha <;> cases ha <;> simp

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
