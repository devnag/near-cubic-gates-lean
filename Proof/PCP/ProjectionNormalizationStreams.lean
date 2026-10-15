import Proof.PCP.ProjectionNormalizationStreamQueries

/-! The complete raw-PCP normalization stream producer. Both serializer
counts and both streams are actual outputs of one fixed ordinary machine. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Streams
open SourceInterfaces ExecutableInterfaces LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clausePrefix (p : RawProjectionPCP) := QueryBytes.header p++Rows.stream (QueryBytes.rowsBits (queryRows p))
def slots : Fin 18 → Fin 48 := ![0,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47]
noncomputable def first := TapeEmbedding.machine 17 StreamQueries.machine
noncomputable def second := RecoveryFocus.machine slots Clauses.machine
noncomputable def machine := Composition.machine first second
noncomputable def input (p : RawProjectionPCP) (R Q : ℕ) : Fin 48 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (31+17) => List Bool) (StreamQueries.input p R Q) (fun _ : Fin 17 => [])
def budget (p : RawProjectionPCP) (R Q : ℕ) := StreamQueries.budget p R Q+1+Clauses.budget (DedupBytes.rows p)

theorem raw_word (p : RawProjectionPCP) :
    p.word=clausePrefix p++frame (DedupBytes.rows p).length.bits++SuffixScan.stream (DedupBytes.rows p) := by
  rw [QueryBytes.source_split p,DedupBytes.suffix_fields]
  simp only [clausePrefix,DedupBytes.rows,List.length_map,List.append_assoc]

theorem clause_entry_heads (p : RawProjectionPCP) :
    (Clauses.entry p.word (QueryReady.sourcePos p)).heads=
      (fun i => if i=0 then QueryReady.sourcePos p else 0) := by
  funext i; fin_cases i <;> rfl
theorem clause_entry_tapes (p : RawProjectionPCP) :
    (Clauses.entry p.word (QueryReady.sourcePos p)).tapes=(fun i => if i=0 then p.word else []) := by
  funext i; fin_cases i <;> rfl

theorem streams_run (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q) :
    ∃ r,run machine (budget p R Q) (input p R Q)=some r ∧ r.steps ≤ budget p R Q ∧
      r.final.tapes 29=QueryBytes.framedCodes (normalizedRows p R Q).flatten ∧
      r.final.tapes 25=CompareMachine.word (R*Q) ∧
      r.final.tapes 38=DedupBytes.fields p ∧ r.final.tapes 46=CompareMachine.word (Codec.clauses p).length ∧
      r.final.heads 29=0 ∧ r.final.heads 25=1 ∧ r.final.heads 38=0 ∧ r.final.heads 46=1 := by
  obtain ⟨base,hbase,hbs,hsource,hqueries,hcount,hpos,houtpos,hcountpos⟩ := StreamQueries.queries_run p R Q hr hq
  let a := TapeEmbedding.receipt (fun _ : Fin 17 => 0) (fun _ : Fin 17 => []) base
  have ha := TapeEmbedding.run_embed StreamQueries.machine (fun _ : Fin 17 => 0) (fun _ : Fin 17 => []) _ _ base hbase
  rw [StreamPrepare.embed_initial] at ha
  obtain ⟨localRun,hl,hls,hlo,hlc,hlh,hlk⟩ := Clauses.rows_run (clausePrefix p) (DedupBytes.rows p)
  rw [←raw_word p] at hl
  have hpre : (clausePrefix p).length=QueryReady.sourcePos p := by simp [clausePrefix,QueryReady.sourcePos]
  rw [hpre] at hl
  obtain ⟨b,hb,hbf,hbt⟩ := RecoveryFocus.run_config slots (by decide) Clauses.machine a.final.heads a.final.tapes _ _ localRun hl
  have he : RecoveryFocus.config slots a.final.heads a.final.tapes
      (Clauses.entry p.word (QueryReady.sourcePos p))=Composition.restart a.final second.start := by
    apply TransitionEvent.focused_eq slots (by decide) (Composition.restart a.final second.start)
    · rfl
    · intro i
      change (Clauses.entry p.word (QueryReady.sourcePos p)).heads i=a.final.heads (slots i)
      rw [clause_entry_heads]
      fin_cases i
      · exact hpos.symm
      all_goals rfl
    · intro i
      change (Clauses.entry p.word (QueryReady.sourcePos p)).tapes i=a.final.tapes (slots i)
      rw [clause_entry_tapes]
      fin_cases i
      · exact hsource.symm
      all_goals rfl
    · intro i _; rfl
    · intro i _; rfl
  rw [he] at hb
  have h := Composition.run_join first second _ _ _ a b ha hb
  have hselectedTape (i : Fin 18) : b.final.tapes (slots i)=localRun.final.tapes i := by
    simp [hbf,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have hselectedHead (i : Fin 18) : b.final.heads (slots i)=localRun.final.heads i := by
    simp [hbf,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have h29 : RecoveryFocus.pick slots 29=none := by simp [RecoveryFocus.pick,show ¬∃ i,slots i=29 by decide]
  have h25 : RecoveryFocus.pick slots 25=none := by simp [RecoveryFocus.pick,show ¬∃ i,slots i=25 by decide]
  refine ⟨Composition.joinedReceipt a b,h,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change base.steps+1+b.steps ≤ _
    dsimp only [budget]
    omega
  · change b.final.tapes 29=_
    simp only [hbf,RecoveryFocus.config,h29]
    exact hqueries
  · change b.final.tapes 25=_
    simp only [hbf,RecoveryFocus.config,h25]
    exact hcount
  · exact (hselectedTape 8).trans (hlo.trans (DedupBytes.output_fields p))
  · exact (hselectedTape 16).trans (by simpa only [DedupBytes.output_count] using hlc)
  · change b.final.heads 29=0
    simp only [hbf,RecoveryFocus.config,h29]
    exact houtpos
  · change b.final.heads 25=1
    simp only [hbf,RecoveryFocus.config,h25]
    exact hcountpos
  · exact (hselectedHead 8).trans hlh
  · exact (hselectedHead 16).trans hlk

end NearCubicWires.RepairSource.ProjectionNormalization.Streams
