import Proof.CaseAnalysis.RecoveryHierarchyDockCountTail

/-! The complete original hierarchy/source/normalization prefix followed by
its paid count extraction into scalar157. All original streams remain exact. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdHierarchyDock.Count
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

structure Fields {s : ℕ} (k CH Cpad : ℕ) (code x bound : List Bool)
    (c : Configuration (tapes source k) s) : Prop where
  input : c.tapes (prior source k (inputPort source k))=frame x++frame bound
  inputHead : c.heads (prior source k (inputPort source k))=0
  width : c.tapes (prior source k (rBitsPort source k))=frame (HierarchyStreams.R source k CH Cpad code x).bits
  widthHead : c.heads (prior source k (rBitsPort source k))=0
  queries : c.tapes (prior source k (qBitsPort source k))=frame (HierarchyStreams.Q source k CH Cpad code x).bits
  queriesHead : c.heads (prior source k (qBitsPort source k))=0
  queryStream : c.tapes (old source k 106)=QueryBytes.framedCodes
    (normalizedRows (source.output (HierarchyStreams.request k CH Cpad code x))
      (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x)).flatten
  queryStreamHead : c.heads (old source k 106)=0
  queryCount : c.tapes (prior source k (queryCountPort source k))=CompareMachine.word
    (HierarchyStreams.R source k CH Cpad code x*HierarchyStreams.Q source k CH Cpad code x)
  queryCountHead : c.heads (prior source k (queryCountPort source k))=1
  clauseStream : c.tapes (old source k 70)=DedupBytes.fields (source.output (HierarchyStreams.request k CH Cpad code x))
  clauseStreamHead : c.heads (old source k 70)=0
  clauseCount : c.tapes (counter source k)=CompareMachine.word (clauses source k CH Cpad code x)
  clauseCountHead : c.heads (counter source k)=0
  rawClauses : c.tapes (old source k 157)=List.replicate (clauses source k CH Cpad code x) true
  rawClausesHead : c.heads (old source k 157)=0

private theorem original_ne_count (k : ℕ) (i : Fin (HierarchyStreams.base source k)) :
    HierarchyStreams.old source k i≠HierarchyStreams.slots source k 46:=by
  intro he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  simp only [HierarchyStreams.old,HierarchyStreams.slots,
    show (46 : Fin 48)≠0 by decide,show (46 : Fin 48)≠13 by decide,
    show (46 : Fin 48)≠14 by decide,if_false,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem stream_ne_count (k : ℕ) (i : Fin 48) (hi : i≠46) :
    HierarchyStreams.slots source k i≠HierarchyStreams.slots source k 46:=
  fun he=>hi (HierarchyStreams.slots_injective source k he)

theorem run (k CH Cpad : ℕ) (code x bound : List Bool) (hpad : k+3≤Cpad)
    (A : Fin 158→List Bool) (H : Fin 158→ℕ)
    (h70 : A 70=[]) (h106 : A 106=[]) (h157 : A 157=[])
    (hh70 : H 70=0) (hh106 : H 106=0) (hh157 : H 157=0) :
    ∃ r,runFrom (machine source k CH Cpad code) (budget source k CH Cpad code x)
      ⟨(machine source k CH Cpad code).start,heads source k H,input source k A (frame x++frame bound)⟩=some r ∧
      r.steps≤budget source k CH Cpad code x ∧ Fields source k CH Cpad code x bound r.final ∧
      ∀ i : Fin 158,i≠70→i≠106→i≠157→
        r.final.heads (old source k i)=H i ∧ r.final.tapes (old source k i)=A i:=by
  obtain ⟨baseRun,hbase,hbs,hf,hret⟩:=RecoveryBoundedColdHierarchyDock.scalar_run
    source k CH Cpad code x bound hpad A H h70 h106 hh70 hh106
  let firstRun:=TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _ : Fin 1=>[]) baseRun
  have hfirst:=TapeEmbedding.run_embed (RecoveryBoundedColdHierarchyDock.machine source k CH Cpad code)
    (fun _ : Fin 1=>0) (fun _ : Fin 1=>[]) _ _ baseRun hbase
  have ho:=hret 157 (by decide) (by decide)
  obtain ⟨lastRun,hl,hls,hraw,hrawHead,hcounterHead,htapes,hheads⟩:=tail_run source baseRun.final
    (clauses source k CH Cpad code x) hf.clauseCount hf.clauseCountHead
    (ho.2.trans h157) (ho.1.trans hh157)
  have hlast : runFrom (last source k) (RecoveryBoundedColdClauseCount.budget (clauses source k CH Cpad code x))
      (Composition.restart firstRun.final (last source k).start)=some lastRun:=hl
  have ht (j : Fin (HierarchyStreams.tapes source k)) :
      lastRun.final.tapes (prior source k (RecoveryBoundedColdHierarchyDock.slots source k j))=
        baseRun.final.tapes (RecoveryBoundedColdHierarchyDock.slots source k j):=
    htapes _ (slots_other source k 157 (by decide) (by decide) j)
  have hh (j : Fin (HierarchyStreams.tapes source k)) (hj : j≠HierarchyStreams.slots source k 46) :
      lastRun.final.heads (prior source k (RecoveryBoundedColdHierarchyDock.slots source k j))=
        baseRun.final.heads (RecoveryBoundedColdHierarchyDock.slots source k j):=
    hheads _ (slots_other source k 157 (by decide) (by decide) j)
      (fun he=>hj (RecoveryBoundedColdHierarchyDock.slots_injective source k he))
  refine ⟨Composition.joinedReceipt firstRun lastRun,
    Composition.run_join _ _ _ _ _ firstRun lastRun hfirst hlast,?_,?_,?_⟩
  · change baseRun.steps+1+lastRun.steps≤budget source k CH Cpad code x
    unfold budget
    omega
  · refine ⟨(ht _).trans hf.input,(hh _ (original_ne_count source k _)).trans hf.inputHead,
      (ht _).trans hf.width,(hh _ (original_ne_count source k _)).trans hf.widthHead,
      (ht _).trans hf.queries,(hh _ (original_ne_count source k _)).trans hf.queriesHead,?_,?_,
      (ht _).trans hf.queryCount,(hh _ (stream_ne_count source k 25 (by decide))).trans hf.queryCountHead,
      ?_,?_,(ht _).trans hf.clauseCount,hcounterHead,hraw,hrawHead⟩
    · change lastRun.final.tapes (old source k 106)=_
      simpa only [query_slot,old] using (ht (HierarchyStreams.slots source k 29)).trans hf.queryStream
    · change lastRun.final.heads (old source k 106)=0
      simpa only [query_slot,old] using
        (hh _ (stream_ne_count source k 29 (by decide))).trans hf.queryStreamHead
    · change lastRun.final.tapes (old source k 70)=_
      simpa only [clause_slot,old] using (ht (HierarchyStreams.slots source k 38)).trans hf.clauseStream
    · change lastRun.final.heads (old source k 70)=0
      simpa only [clause_slot,old] using
        (hh _ (stream_ne_count source k 38 (by decide))).trans hf.clauseStreamHead
  · intro i hi70 hi106 hi157
    have hn : RecoveryBoundedColdHierarchyDock.old source k i≠RecoveryBoundedColdHierarchyDock.old source k 157:=by
      intro he
      exact hi157 (Fin.ext (congrArg (fun j : Fin (RecoveryBoundedColdHierarchyDock.tapes source k)=>j.val) he))
    exact ⟨(hheads _ hn (Ne.symm (slots_other source k i hi70 hi106 _))).trans (hret i hi70 hi106).1,
      (htapes _ hn).trans (hret i hi70 hi106).2⟩

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdHierarchyDock.Count
