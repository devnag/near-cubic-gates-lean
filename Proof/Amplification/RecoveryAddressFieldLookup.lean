import Proof.Amplification.RecoveryFormulaValueFields
import Proof.PCP.ProjectionNormalizationFieldList

/-! A physical unary-indexed address lookup. Existing counted field copying
and selected-field copying execute the lookup; the existing logger restores
all six heads, retaining the address stream and produced index driver. -/
namespace NearCubicWires.RepairSource.RecoveryAddressFieldLookup
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (source : List Bool) (count : Nat) (i : Fin 5) :=
  if i=0 then source else if i=2 then CompareMachine.word count else []
def heads (pos : Nat) (i : Fin 5) := if i=0 then pos else if i=2 then 1 else 0
def position : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun i=>if i=2 then .right else .stay⟩ else none

theorem position_step (source : List Bool) (count : Nat) :
    step position (initialConfiguration position (input source count))=
      some ⟨1,heads 0,input source count⟩ := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

def skipSlots : Fin 3→Fin 5 := ![0,1,2]
def copySlots : Fin 3→Fin 5 := ![0,3,4]
noncomputable def skipMachine := RecoveryFocus.machine skipSlots FieldList.machine
noncomputable def copyMachine := RecoveryFocus.machine copySlots PCPFieldMoves.advanceMachine
noncomputable def raw := Composition.machine (Composition.machine position skipMachine) copyMachine
noncomputable def machine := Rewind.machine raw
def rawBudget (skipped : List (List Bool)) (bits : List Bool) :=
  (FieldList.stream skipped).length+3*skipped.length+4*bits.length+10
def budget (skipped : List (List Bool)) (bits : List Bool) := 2*rawBudget skipped bits+2

theorem raw_run (skipped : List (List Bool)) (bits suffix : List Bool) : ∃ r,
    run raw (rawBudget skipped bits) (input (FieldList.stream skipped++RepairOrdinary.frame bits++suffix) skipped.length)=some r ∧
      r.final.tapes 0=FieldList.stream skipped++RepairOrdinary.frame bits++suffix ∧
      r.final.tapes 2=CompareMachine.word skipped.length ∧ r.final.tapes 3=RepairOrdinary.frame bits ∧
      r.steps≤rawBudget skipped bits := by
  let source:=FieldList.stream skipped++RepairOrdinary.frame bits++suffix
  obtain ⟨pos,hpos,pf,ps⟩ := (Timed.single (by rfl) (position_step source skipped.length)).run (by rfl)
  obtain ⟨sk,hsk,skf,sks⟩ := FieldList.copy_run [] skipped (RepairOrdinary.frame bits++suffix) []
  obtain ⟨first,hfirst,_fc,firstSteps,firstHeads,firstTapes,firstKeep⟩ := RecoveryFocus.dock skipSlots (by decide)
    FieldList.machine _ (heads 0) (input source skipped.length) _
    (by intro i; fin_cases i <;> rfl)
    (by intro i; fin_cases i
        · simp only [source,input,List.nil_append,List.append_assoc]; rfl
        all_goals rfl) sk hsk
  have hp : Composition.restart pos.final skipMachine.start=
      (⟨FieldList.machine.start,heads 0,input source skipped.length⟩ : Configuration 5 _) := by rw [pf]; rfl
  change runFrom skipMachine _ ⟨FieldList.machine.start,heads 0,input source skipped.length⟩=some first at hfirst
  rw [←hp] at hfirst
  have hprefix := Composition.run_join position skipMachine 1 _ _ pos first hpos hfirst
  obtain ⟨cp,hcp,cpt,cph,cps⟩ := PCPFieldMoves.advance_run (FieldList.stream skipped) bits suffix 0 0
  obtain ⟨last,hlast,_lc,lastSteps,_lastHeads,lastTapes,lastKeep⟩ := RecoveryFocus.dock copySlots (by decide)
    PCPFieldMoves.advanceMachine _ first.final.heads first.final.tapes _
    (by intro i; fin_cases i
        · have h:=firstHeads 0
          rw [skf] at h
          change first.final.heads 0=0+(FieldList.stream skipped).length at h
          change first.final.heads 0=(FieldList.stream skipped).length
          simpa only [Nat.zero_add] using h
        · exact (firstKeep 3 (by decide)).1
        · exact (firstKeep 4 (by decide)).1)
    (by intro i; fin_cases i
        · have h:=firstTapes 0
          rw [skf] at h
          change first.final.tapes 0=[]++FieldList.stream skipped++(RepairOrdinary.frame bits++suffix) at h
          change first.final.tapes 0=ZeroPadding.pad 0 (FieldList.stream skipped++RepairOrdinary.frame bits++suffix)
          simpa only [List.nil_append,List.append_assoc,ZeroPadding.pad_zero] using h
        · exact (firstKeep 3 (by decide)).2
        · exact (firstKeep 4 (by decide)).2) cp hcp
  have hall := Composition.run_join (Composition.machine position skipMachine) copyMachine _ _ _
    (Composition.joinedReceipt pos first) last hprefix hlast
  have ht : (1+1+((FieldList.stream skipped).length+3*skipped.length+3))+1+(4*bits.length+4)=rawBudget skipped bits := by
    unfold rawBudget; omega
  rw [ht] at hall
  refine ⟨_,hall,?_,?_,?_,?_⟩
  · change last.final.tapes (copySlots 0)=_
    rw [lastTapes,cpt]
    rfl
  · change last.final.tapes 2=_
    rw [(lastKeep 2 (by decide)).2]
    change first.final.tapes (skipSlots 2)=_
    rw [firstTapes,skf]
    rfl
  · change last.final.tapes (copySlots 1)=_
    rw [lastTapes,cpt]
    exact ZeroPadding.pad_zero _
  · change (pos.steps+1+first.steps)+1+last.steps≤_
    unfold rawBudget
    omega

theorem lookup_ready (skipped : List (List Bool)) (bits suffix : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget skipped bits)
      (fun i=>Fin.addCases (m:=5) (n:=1) (motive:=fun _=>List Bool)
        (input (FieldList.stream skipped++RepairOrdinary.frame bits++suffix) skipped.length) (fun _=>[]) i) out ∧
      out 0=FieldList.stream skipped++RepairOrdinary.frame bits++suffix ∧
      out 2=CompareMachine.word skipped.length ∧ out 3=RepairOrdinary.frame bits := by
  obtain ⟨base,hbase,b0,b2,b3,bs⟩ := raw_run skipped bits suffix
  obtain ⟨r,hr,rt,_rc,rh,rs,_peak⟩ := Rewind.Workspace.reset_workspace raw _ _ base hbase 0
  have hb : 2*base.steps+2≤budget skipped bits := by unfold budget; omega
  have hm := run_moreFuel machine _ (budget skipped bits-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r.final.tapes,⟨r,hm,rfl,rh,by omega⟩,(rt 0).trans b0,(rt 2).trans b2,(rt 3).trans b3⟩

end NearCubicWires.RepairSource.RecoveryAddressFieldLookup
