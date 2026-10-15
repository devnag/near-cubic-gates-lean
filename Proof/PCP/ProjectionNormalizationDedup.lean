import Proof.PCP.ProjectionNormalizationDedupBounds

/-! Cold raw-clause producer. All auxiliary tapes start blank; the flags and
kept-count sentinel are written physically. Zero padding is removed from the
whole actual loop, leaving its exact emitted stream and actual count intact. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DedupCold
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def entry {s : ℕ} (q : Fin s) (source : List Bool) (pos count : ℕ) : Configuration 12 s where
  control := q
  heads := fun i => if i=0 then pos else if i=3 then 1 else 0
  tapes := fun i => if i=0 then source else if i=3 then CompareMachine.word count else []
def capacities (rows : List SuffixScan.Clause) : Fin 12 → ℕ := fun i =>
  if i=6 then Dedup.pairCap rows else if i=7 then Dedup.scanCapacity rows else
  if i=8 then Dedup.scanCapacity rows else if i=9 then Dedup.copyCapacity rows else 0
def emptyStore (source : List Bool) (pos : ℕ) (rows : List SuffixScan.Clause) :=
  {Dedup.initialStore source pos rows with cap:=0,scanCap:=0,copyCap:=0}
def boot : Machine 12 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i=4 ∨ i=5 ∨ i=11 then some false else none,
      fun i => if i=11 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine boot Dedup.machine

def budget (source : List Bool) (pos : ℕ) (rows : List SuffixScan.Clause) :=
  Dedup.loopBudget (Dedup.initialStore source pos rows) rows+2

theorem boot_run (source : List Bool) (pos : ℕ) (rows : List SuffixScan.Clause) :
    ∃ r,runFrom boot 1 (entry 0 source pos rows.length)=some r ∧
      r.final=Dedup.cfg 1 (emptyStore source pos rows) ∧ r.steps=1 := by
  have h : step boot (entry 0 source pos rows.length)=some (Dedup.cfg 1 (emptyStore source pos rows)) := by
    change some (applyAction (entry 0 source pos rows.length)
      ⟨1,(fun i => if i=4 ∨ i=5 ∨ i=11 then some false else none),
        (fun i => if i=11 then .right else .stay)⟩)=_
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem padded_store {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ) (rows : List SuffixScan.Clause) :
    ZeroPadding.config (capacities rows) (Dedup.cfg q (emptyStore source pos rows))=
      Dedup.cfg q (Dedup.initialStore source pos rows) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;>
      simp [ZeroPadding.config,capacities,Dedup.cfg,emptyStore,Dedup.initialStore,ZeroPadding.pad]

theorem logical_run (pre suffix : List Bool) (rows : List SuffixScan.Clause) :
    ∃ r,runFrom machine (budget (pre++SuffixScan.stream rows++suffix) pre.length rows)
      (ZeroPadding.config (capacities rows) (entry machine.start (pre++SuffixScan.stream rows++suffix) pre.length rows.length))=some r ∧
      r.steps ≤ budget (pre++SuffixScan.stream rows++suffix) pre.length rows ∧
      r.final=Composition.rightConfig 2
        (Dedup.loopCfg 1 (Dedup.process rows (Dedup.initialStore (pre++SuffixScan.stream rows++suffix) pre.length rows))) := by
  obtain ⟨base,hb,hbf,hbs⟩ := boot_run (pre++SuffixScan.stream rows++suffix) pre.length rows
  obtain ⟨a,ha,haf,hat,_⟩ := ZeroPadding.run_config boot (capacities rows) _ _ base hb
  rw [hbf,padded_store] at haf
  obtain ⟨b,hb,hbt,hbf⟩ := Dedup.initial_run pre suffix rows
  have he : Composition.restart a.final Dedup.machine.start=
      Dedup.loopCfg 0 (Dedup.initialStore (pre++SuffixScan.stream rows++suffix) pre.length rows) := by
    rw [haf]
    rfl
  rw [←he] at hb
  have h := Composition.run_join boot Dedup.machine _ _ _ a b ha hb
  have ht : 1+1+Dedup.loopBudget (Dedup.initialStore (pre++SuffixScan.stream rows++suffix) pre.length rows) rows=
      budget (pre++SuffixScan.stream rows++suffix) pre.length rows := by dsimp [budget]; omega
  rw [ht] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    dsimp only [budget]
    omega
  · change Composition.rightConfig 2 b.final=_
    rw [hbf]

theorem cold_run (pre suffix : List Bool) (rows : List SuffixScan.Clause) :
    ∃ r,runFrom machine (budget (pre++SuffixScan.stream rows++suffix) pre.length rows)
      (entry machine.start (pre++SuffixScan.stream rows++suffix) pre.length rows.length)=some r ∧
      r.steps ≤ budget (pre++SuffixScan.stream rows++suffix) pre.length rows ∧
      r.final.tapes 2=SuffixScan.stream rows.dedup ∧
      r.final.tapes 11=CompareMachine.word rows.dedup.length ∧
      r.final.heads 2=(SuffixScan.stream rows.dedup).length ∧
      r.final.heads 11=rows.dedup.length+1 := by
  classical
  obtain ⟨base,hb,hbs,hbf⟩ := logical_run pre suffix rows
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_unpad machine (capacities rows) _ _ base hb
  rw [hbf] at hrf
  refine ⟨r,hr,hrs.le.trans hbs,?_,?_,?_,?_⟩
  · have h := congrArg (fun c => c.tapes 2) hrf
    simpa [ZeroPadding.config,capacities,Composition.rightConfig,Dedup.loopCfg,Dedup.cfg,
      Dedup.process_out,Dedup.initialStore] using h
  · have h := congrArg (fun c => c.tapes 11) hrf
    simpa [ZeroPadding.config,capacities,Composition.rightConfig,Dedup.loopCfg,Dedup.cfg,
      Dedup.process_kept,Dedup.initialStore] using h
  · have h := congrArg (fun c => c.heads 2) hrf
    simpa [ZeroPadding.config,Composition.rightConfig,Dedup.loopCfg,Dedup.cfg,
      Dedup.process_out,Dedup.initialStore] using h
  · have h := congrArg (fun c => c.heads 11) hrf
    simpa [ZeroPadding.config,Composition.rightConfig,Dedup.loopCfg,Dedup.cfg,
      Dedup.process_kept,Dedup.initialStore] using h

end NearCubicWires.RepairSource.ProjectionNormalization.DedupCold
