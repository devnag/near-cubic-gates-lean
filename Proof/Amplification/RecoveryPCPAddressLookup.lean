import Proof.Amplification.RecoverySourceLiteralDriver
import Proof.PCP.ProjectionNormalizationFieldList

/-! Select an actual framed query address using the original source literal's
physical unary driver. The existing field copier and repeater do all scans;
the existing rewind machine restores every head for the clause encoder. -/
namespace NearCubicWires.RepairSource.RecoveryPCPAddressLookup
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def skipSlots : Fin 3 -> Fin 4 := ![0,1,2]
def copySlots : Fin 2 -> Fin 4 := ![0,3]
theorem skip_injective : Function.Injective skipSlots := by decide
theorem copy_injective : Function.Injective copySlots := by decide
def position : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val=1
  rule := fun q _ => if q.val=0 then some
    ⟨1,fun _ => none,fun i => if i=2 then .right else .stay⟩ else none
def positioned (data : Fin 4 -> List Bool) : Configuration 4 2 :=
  ⟨1,![0,0,1,0],data⟩
theorem position_step (data : Fin 4 -> List Bool) :
    step position (initialConfiguration position data)=some (positioned data) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

noncomputable def skip := RecoveryFocus.machine skipSlots FieldList.machine
noncomputable def copy := RecoveryFocus.machine copySlots Field.machine
noncomputable def raw := Composition.machine (Composition.machine position skip) copy
noncomputable def machine := Rewind.machine raw
def source (skipped : List (List Bool)) (bits suffix : List Bool) :=
  FieldList.stream skipped++frame bits++suffix
def input (skipped : List (List Bool)) (bits suffix : List Bool) : Fin 4 -> List Bool :=
  ![source skipped bits suffix,[],CompareMachine.word skipped.length,[]]
def output (skipped : List (List Bool)) (bits suffix : List Bool) : Fin 4 -> List Bool :=
  ![source skipped bits suffix,FieldList.stream skipped,CompareMachine.word skipped.length,frame bits]
def rawBudget (skipped : List (List Bool)) (bits : List Bool) :=
  (FieldList.stream skipped).length+3*skipped.length+2*bits.length+7
def budget (skipped : List (List Bool)) (bits : List Bool) := 2*rawBudget skipped bits+2

theorem raw_run (skipped : List (List Bool)) (bits suffix : List Bool) :
    ∃ r,run raw (rawBudget skipped bits) (input skipped bits suffix)=some r ∧
      r.final.tapes=output skipped bits suffix ∧ r.steps=rawBudget skipped bits := by
  obtain ⟨first,hfirst,ff,fs⟩ := (Timed.single (by rfl)
    (position_step (input skipped bits suffix))).run (by rfl)
  obtain ⟨base,hbase,bf,bs⟩ := FieldList.copy_run [] skipped (frame bits++suffix) []
  obtain ⟨second,hsecond,_sc,ss,sh,st,keepS⟩ := RecoveryFocus.dock skipSlots skip_injective
    FieldList.machine _ first.final.heads first.final.tapes _
    (by intro i; rw [ff]; fin_cases i <;> rfl)
    (by intro i; rw [ff]; fin_cases i
        · simp only [positioned,input,source,List.nil_append,List.append_assoc]; rfl
        all_goals rfl) base hbase
  obtain ⟨field,hfield,fieldF,fieldS⟩ := Field.copy_run (FieldList.stream skipped) bits suffix []
  obtain ⟨last,hlast,_lc,ls,_lh,lt,keepL⟩ := RecoveryFocus.dock copySlots copy_injective
    Field.machine _ second.final.heads second.final.tapes _
    (by intro i; fin_cases i
        · have h := sh 0; rw [bf] at h
          change second.final.heads 0=0+(FieldList.stream skipped).length at h
          change second.final.heads 0=(FieldList.stream skipped).length
          omega
        · have h := (keepS 3 (by decide)).1; rw [ff] at h; exact h)
    (by intro i; fin_cases i
        · have h := st 0; rw [bf] at h
          change second.final.tapes 0=[]++FieldList.stream skipped++(frame bits++suffix) at h
          change second.final.tapes 0=FieldList.stream skipped++frame bits++suffix
          simpa only [List.nil_append,List.append_assoc] using h
        · have h := (keepS 3 (by decide)).2; rw [ff] at h; exact h) field hfield
  have firstRun := Composition.run_join position skip _ _ _ first second hfirst hsecond
  have combined := Composition.run_join (Composition.machine position skip) copy _ _ _
    (Composition.joinedReceipt first second) last firstRun hlast
  have htime : (1+1+((FieldList.stream skipped).length+3*skipped.length+3))+1+
      (2*bits.length+1)=rawBudget skipped bits := by unfold rawBudget; omega
  rw [htime] at combined
  refine ⟨_,combined,?_,?_⟩
  · change last.final.tapes=output skipped bits suffix
    funext i; fin_cases i
    · change last.final.tapes 0=source skipped bits suffix
      have h := lt 0; rw [fieldF] at h; exact h
    · change last.final.tapes 1=FieldList.stream skipped
      rw [(keepL 1 (by decide)).2]
      have h := st 1; rw [bf] at h
      exact h
    · change last.final.tapes 2=CompareMachine.word skipped.length
      rw [(keepL 2 (by decide)).2]
      have h := st 2; rw [bf] at h; exact h
    · change last.final.tapes 3=frame bits
      have h := lt 1; rw [fieldF] at h
      change last.final.tapes 3=[]++frame bits at h
      simpa only [List.nil_append] using h
  · change (first.steps+1+second.steps)+1+last.steps=_
    rw [fs,ss,bs,ls,fieldS]
    exact htime

theorem ready_run (skipped : List (List Bool)) (bits suffix : List Bool) (logCap : Nat) :
    ClockJoin.ReadyRun machine (budget skipped bits)
      (Fin.addCases (input skipped bits suffix) (fun _ : Fin 1 => List.replicate logCap false))
      (Fin.addCases (output skipped bits suffix)
        (fun _ : Fin 1 => List.replicate (max logCap (rawBudget skipped bits)) false)) := by
  obtain ⟨base,hbase,bt,bs⟩ := raw_run skipped bits suffix
  obtain ⟨r,hr,rt,rc,rh,rs,_peak⟩ := Rewind.Workspace.reset_workspace raw _ _ base hbase logCap
  rw [bs] at hr rs rc
  refine ⟨r,hr,?_,rh,rs.le⟩
  funext i
  refine Fin.addCases (m:=4) (n:=1) (fun j => ?_) (fun j => ?_) i
  · rw [rt j,bt]; simp only [Fin.addCases_left]
  · fin_cases j; exact rc

end NearCubicWires.RepairSource.RecoveryPCPAddressLookup
