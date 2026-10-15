import Proof.CaseAnalysis.RecoveryQueryMeaning

/-! The actual query-count driver executes the literal original query list.
Every output reference is appended in its original order, with one shared
description-variable block and the same retained graph throughout. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQueries
open LocalBitMultitape RepairRepresentation RepairSource.VerifierDecoding RecoveryExecution
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RepeatMachine.machine RecoveryBoundedQuery.machine (fun _ _=>true)
def budget (queries W : ℕ):=queries*(RecoveryBoundedQuery.budget W+2)+queries+3
noncomputable def configuration {n bound : ℕ} (phase : Fin 5)
    (b : BooleanDAGBuilder (descriptionWidth n bound)) (total W D L : ℕ)
    (out pre source refs : List Bool) (queries driver : ℕ):=
  RepeatMachine.cfg phase (entry b total W D L out pre source refs) queries driver

private theorem cfg_data {t s : ℕ} (phase : Fin 5) (c d : Configuration t s) (total driver : ℕ)
    (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total driver=RepeatMachine.cfg phase d total driver := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem repeat_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total W D L queries pos : ℕ) (out pre tail refs : List Bool)
    (addresses : List (BitInput n)) (ht : total ≤ bound) (hpos : pos+addresses.length=queries)
    (hfits : Fits b total W ht addresses) (hn : n ≤ W)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let source:=pre++addressWord addresses++tail
    let compiled:=compileUniversalOutputs b total ht addresses
    ∃ r,runFrom machine (addresses.length*(RecoveryBoundedQuery.budget W+2)+queries+3)
      (configuration 0 b total W D L out pre source refs queries (pos+1))=some r ∧
      r.final=configuration 3 compiled.final total W D L (out++native b total ht addresses)
        (pre++addressWord addresses) source (refs++sourceWord (references b total ht addresses)) queries 1 ∧
      r.steps ≤ addresses.length*(RecoveryBoundedQuery.budget W+2)+queries+3 := by
  induction addresses generalizing b pos out pre refs with
  | nil=>
    have hoff : pos=queries:=by simpa only [List.length_nil,Nat.add_zero] using hpos
    obtain ⟨r,hr,rf,rs⟩:=(RepeatMachine.exhaust RecoveryBoundedQuery.machine (fun _ _=>true)
      (entry b total W D L out pre (pre++tail) refs) queries).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,?_,?_⟩
    · simpa only [machine,configuration,addressWord,List.flatMap_nil,List.append_nil,hoff,List.length_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [configuration,native,references,compileUniversalOutputs,addressWord,sourceWord,
        BooleanDAGExtension.refl,List.flatMap_nil,List.map_nil,List.append_nil] using rf
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using rs.le
  | cons address addresses ih=>
    let source:=pre++addressWord (address::addresses)++tail
    let head:=compileUniversalOutput b address total ht
    let nextOut:=out++head.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let nextPre:=pre++List.ofFn address
    let nextRefs:=refs++frame (List.replicate head.compiled.output.val true)
    have sourceEq : pre++List.ofFn address++(addressWord addresses++tail)=source := by
      simp only [source,addressWord_cons,List.append_assoc]
    rcases hfits with ⟨hTable,hOutput,hRest⟩
    obtain ⟨first,fr,fs,fh,ft⟩:=query_step b address total W D L out pre (addressWord addresses++tail) refs ht hTable hOutput hn hD hL
    rw [sourceEq] at fr fh ft
    have hp : pos < queries:=by simp only [List.length_cons] at hpos;omega
    have hiteration:=RepeatMachine.iteration RecoveryBoundedQuery.machine (fun _ _=>true)
      (entry b total W D L out pre source refs) queries pos first rfl hp fr
    change Timed machine (first.steps+2)
      (configuration 0 b total W D L out pre source refs queries (pos+1))
      (RepeatMachine.cfg 0 first.final queries (pos+2)) at hiteration
    rw [cfg_data 0 first.final (entry head.compiled.final total W D L nextOut nextPre source nextRefs)
      queries (pos+2) fh ft] at hiteration
    obtain ⟨last,lr,lf,ls⟩:=ih head.compiled.final (pos+1) nextOut nextPre nextRefs
      (by simp only [List.length_cons] at hpos;omega) hRest
    have nextSource : nextPre++addressWord addresses++tail=source := by
      simp only [nextPre,source,addressWord_cons,List.append_assoc]
    rw [nextSource] at lr lf
    change runFrom machine _
      (configuration 0 head.compiled.final total W D L nextOut nextPre source nextRefs queries (pos+2))=some last at lr
    rcases hiteration with ⟨space,hprefix⟩
    obtain ⟨r,hr,rf,rs,_⟩:=hprefix.followedBy last lr
    have hbudget : first.steps+2+(addresses.length*(RecoveryBoundedQuery.budget W+2)+queries+3) ≤
        (address::addresses).length*(RecoveryBoundedQuery.budget W+2)+queries+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have more:=runFrom_moreFuel machine _
      ((address::addresses).length*(RecoveryBoundedQuery.budget W+2)+queries+3-
        (first.steps+2+(addresses.length*(RecoveryBoundedQuery.budget W+2)+queries+3))) _ r hr
    rw [Nat.add_sub_of_le hbudget] at more
    refine ⟨r,more,?_,?_⟩
    · exact rf.trans (lf.trans (congrArg (fun c=>RepeatMachine.cfg 3 c queries 1)
        (final_entry_cons b total W D L out pre source refs ht address addresses)))
    · rw [rs]
      omega

theorem queries_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total W D L : ℕ) (out pre tail refs : List Bool) (addresses : List (BitInput n)) (ht : total ≤ bound)
    (hfits : Fits b total W ht addresses) (hn : n ≤ W)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let source:=pre++addressWord addresses++tail
    let compiled:=compileUniversalOutputs b total ht addresses
    ∃ r,runFrom machine (budget addresses.length W)
      (configuration 0 b total W D L out pre source refs addresses.length 1)=some r ∧
      r.final=configuration 3 compiled.final total W D L (out++native b total ht addresses)
        (pre++addressWord addresses) source (refs++sourceWord (references b total ht addresses)) addresses.length 1 ∧
      r.steps ≤ budget addresses.length W := by
  exact repeat_run b total W D L addresses.length 0 out pre tail refs addresses ht (by omega) hfits hn hD hL

end NearCubicWires.RepairOrdinary.RecoveryBoundedQueries
