import Proof.PCP.ProjectionNormalizationStreamPrepare

/-! End-to-end raw header, driver production and padded query emission. The
actual total-field counter and the next source cursor are retained. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.StreamQueries
open SourceInterfaces ExecutableInterfaces LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 7 → Fin 31 := ![0,29,5,21,11,27,30]
noncomputable def prepare := TapeEmbedding.machine 2 StreamPrepare.machine
def selected (i : Fin 31) : Prop := i=5 ∨ i=11 ∨ i=21 ∨ i=25 ∨ i=27
instance (i : Fin 31) : Decidable (selected i) := inferInstanceAs (Decidable (i=5 ∨ i=11 ∨ i=21 ∨ i=25 ∨ i=27))
def advance : Machine 31 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,
    fun i => if selected i then .right else .stay⟩ else none
noncomputable def prefixMachine := Composition.machine prepare advance
noncomputable def queryProgram := RecoveryFocus.machine slots QueryReady.machine
noncomputable def machine := Composition.machine prefixMachine queryProgram
noncomputable def input (p : RawProjectionPCP) (R Q : ℕ) : Fin 31 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (29+2) => List Bool) (StreamPrepare.input p R Q) (fun _ : Fin 2 => [])
def budget (p : RawProjectionPCP) (R Q : ℕ) := StreamPrepare.budget p R Q+3+QueryReady.budget p R Q

theorem entry_heads (p : RawProjectionPCP) (R Q : ℕ) :
    (QueryReady.entry p R Q).heads= ![(QueryBytes.header p).length,0,1,1,1,1,0] := by
  funext i; fin_cases i <;> rfl
theorem entry_tapes (p : RawProjectionPCP) (R Q : ℕ) :
    (QueryReady.entry p R Q).tapes= ![p.word,[],CompareMachine.word p.width,UnaryTemplate.tape (R-p.width),
      CompareMachine.word p.queries,CompareMachine.word ((Q-p.queries)*R),[]] := by
  funext i; fin_cases i <;>
    simp [QueryReady.entry,Rewind.recording,Rewind.config,ZeroPadding.config,QueryReady.capacities,
      Queries.cfg,Fin.addCases,Difference.padded_word]

theorem advance_run (c : Configuration 31 2) (hc : c.control=0) :
    ∃ r,runFrom advance 1 c=some r ∧ r.final.tapes=c.tapes ∧
      (∀ i,r.final.heads i=if selected i then c.heads i+1 else c.heads i) ∧ r.steps=1 := by
  let f : Configuration 31 2 := ⟨1,(fun i => if selected i then c.heads i+1 else c.heads i),c.tapes⟩
  have h : step advance c=some f := by
    simp [step,advance,hc]
    apply configuration_ext
    · rfl
    · funext i; by_cases hi : selected i <;> simp [applyAction,HeadMove.apply,f,hi]
    · rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by simp [advance,hc]) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],hs⟩

def sourceHeads (pos : ℕ) : Fin 31 → ℕ := fun i => if i=0 then pos else 0
def advancedHeads (pos : ℕ) : Fin 31 → ℕ := fun i => if i=0 then pos else if selected i then 1 else 0
theorem heads_embed (pos : ℕ) :
    Fin.addCases (motive := fun _ : Fin (29+2) => ℕ) (StreamPrepare.sourceHeads pos) (fun _ : Fin 2 => 0)=sourceHeads pos := by
  funext i; fin_cases i <;> rfl
theorem heads_advance (pos : ℕ) :
    (fun i : Fin 31 => if selected i then sourceHeads pos i+1 else sourceHeads pos i)=advancedHeads pos := by
  funext i; fin_cases i <;> rfl

theorem queries_run (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q) :
    ∃ r,run machine (budget p R Q) (input p R Q)=some r ∧ r.steps ≤ budget p R Q ∧
      r.final.tapes 0=p.word ∧ r.final.tapes 29=QueryReady.output p R Q ∧
      r.final.tapes 25=CompareMachine.word (R*Q) ∧
      r.final.heads 0=QueryReady.sourcePos p ∧ r.final.heads 29=0 ∧ r.final.heads 25=1 := by
  obtain ⟨base,hbase,hsteps,⟨hsource,_,_,hnative,hqueries,hpadding,hcount,hextra⟩,hheads⟩ :=
    StreamPrepare.prepare_run p R Q hr hq
  let a := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) base
  have ha := TapeEmbedding.run_embed StreamPrepare.machine (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) _ _ base hbase
  rw [StreamPrepare.embed_initial] at ha
  have haheads : a.final.heads=sourceHeads (QueryBytes.header p).length := by
    have hh : base.final.heads=StreamPrepare.sourceHeads (QueryBytes.header p).length := funext hheads
    change Fin.addCases (motive := fun _ : Fin (29+2) => ℕ) base.final.heads (fun _ : Fin 2 => 0)=_
    rw [hh]
    exact heads_embed _
  obtain ⟨b,hb,hbt,hbh,hbs⟩ := advance_run (Composition.restart a.final advance.start) rfl
  have hAB := Composition.run_join prepare advance _ 1 _ a b ha hb
  let ab := Composition.joinedReceipt a b
  have habhead (i : Fin 31) : ab.final.heads i=
      if i=0 then (QueryBytes.header p).length else if selected i then 1 else 0 := by
    change b.final.heads i=_
    rw [hbh]
    change (if selected i then a.final.heads i+1 else a.final.heads i)=_
    rw [haheads]
    exact congrFun (heads_advance _) i
  obtain ⟨localRun,hl,hls,hlo,hlout,hlh⟩ := QueryReady.query_run p R Q
  obtain ⟨c,hc,hcf,hcs⟩ := RecoveryFocus.run_config slots (by decide) QueryReady.machine
    ab.final.heads ab.final.tapes _ _ localRun hl
  have he : RecoveryFocus.config slots ab.final.heads ab.final.tapes (QueryReady.entry p R Q)=
      Composition.restart ab.final queryProgram.start := by
    apply TransitionEvent.focused_eq slots (by decide) (Composition.restart ab.final queryProgram.start)
    · rfl
    · intro i
      change (QueryReady.entry p R Q).heads i=ab.final.heads (slots i)
      rw [entry_heads,habhead]
      fin_cases i <;> rfl
    · intro i
      change (QueryReady.entry p R Q).tapes i=b.final.tapes (slots i)
      rw [entry_tapes,hbt]
      fin_cases i
      · exact hsource.symm
      · rfl
      · exact hnative.symm
      · exact hpadding.symm
      · exact hqueries.symm
      · exact hextra.symm
      · rfl
    · intro i _; rfl
    · intro i _; rfl
  rw [he] at hc
  have h := Composition.run_join prefixMachine queryProgram _ _ _ ab c hAB hc
  have htime : (StreamPrepare.budget p R Q+1+1)+1+QueryReady.budget p R Q=budget p R Q := by rfl
  rw [htime] at h
  have hct (j : Fin 7) : c.final.tapes (slots j)=localRun.final.tapes j := by
    simp [hcf,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have hch (j : Fin 7) : c.final.heads (slots j)=localRun.final.heads j := by
    simp [hcf,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have hp : RecoveryFocus.pick slots 25=none := by
    simp [RecoveryFocus.pick,show ¬∃ i,slots i=25 by decide]
  refine ⟨Composition.joinedReceipt ab c,h,?_,(hct 0).trans hlo,(hct 1).trans hlout,?_,?_,?_,?_⟩
  · change (base.steps+1+b.steps)+1+c.steps ≤ _
    dsimp only [budget]
    omega
  · change c.final.tapes 25=_
    simp only [hcf,RecoveryFocus.config,hp]
    change b.final.tapes 25=_
    rw [hbt]
    exact hcount
  · exact (hch 0).trans (by simpa using hlh 0)
  · exact (hch 1).trans (by simpa using hlh 1)
  · change c.final.heads 25=1
    simp only [hcf,RecoveryFocus.config,hp]
    exact habhead 25

end NearCubicWires.RepairSource.ProjectionNormalization.StreamQueries
