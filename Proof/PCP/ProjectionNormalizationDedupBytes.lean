import Proof.PCP.ProjectionNormalizationDedupReady

/-! Literal raw-PCP clause fields agree with the exact same-source codec,
including canonical binary equality and keep-last ordering. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DedupBytes
open SourceInterfaces ExecutableInterfaces LocalBitMultitape RepairOrdinary VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def row {q : ℕ} (c : Fin 3 → Literal q) : SuffixScan.Clause := fun i => (literalCode (c i)).bits
def rows (p : RawProjectionPCP) := p.decision.clauses.map row
def fields (p : RawProjectionPCP) := ((Codec.clauses p).map QueryBytes.framedCodes).flatten

theorem row_injective {q : ℕ} : Function.Injective (row (q := q)) := by
  intro a b h
  funext i
  apply literal_injective
  have he := congrArg (fun c : SuffixScan.Clause => CanonicalBinary.bitsValue (c i)) h
  simpa only [row,CanonicalBinary.bitsValue_natBits] using he

theorem row_stream {q : ℕ} (c : Fin 3 → Literal q) :
    ClauseEquality.stream (row c)=QueryBytes.framedCodes (clauseCodes c) := by
  simp [ClauseEquality.stream,row,QueryBytes.framedCodes,clauseCodes,
    FieldList.stream,List.ofFn_succ]

theorem output_fields (p : RawProjectionPCP) : SuffixScan.stream (rows p).dedup=fields p := by
  rw [rows,List.dedup_map_of_injective row_injective]
  simp only [SuffixScan.stream,List.map_map,Function.comp_def,row_stream]
  rw [fields,Codec.clauses,List.dedup_map_of_injective clauseCodes_injective]
  simp only [List.map_map,Function.comp_def]

theorem output_count (p : RawProjectionPCP) : (rows p).dedup.length=(Codec.clauses p).length := by
  rw [rows,List.dedup_map_of_injective row_injective,Codec.clauses,
    List.dedup_map_of_injective clauseCodes_injective]
  simp

theorem suffix_fields (p : RawProjectionPCP) :
    QueryBytes.suffix p=frame p.decision.clauses.length.bits++SuffixScan.stream (rows p) := by
  simp only [QueryBytes.suffix,SuffixScan.stream,rows,List.map_map,Function.comp_def]
  simp [ClauseEquality.stream,row,List.ofFn_succ]

theorem ready_run (p : RawProjectionPCP) (pre suffix : List Bool) :
    ∃ r,runFrom DedupReady.machine (DedupReady.budget (rows p))
      (DedupReady.entry (pre++SuffixScan.stream (rows p)++suffix) pre.length p.decision.clauses.length)=some r ∧
      r.steps ≤ DedupReady.budget (rows p) ∧ r.final.tapes 2=fields p ∧
      r.final.tapes 11=CompareMachine.word (Codec.clauses p).length ∧
      r.final.heads 2=0 ∧ r.final.heads 11=1 := by
  obtain ⟨r,hr,hs,ho,hc,hh,hk⟩ := DedupReady.ready_run pre suffix (rows p)
  refine ⟨r,?_,hs,?_,?_,hh,hk⟩
  · simpa only [rows,List.length_map] using hr
  · exact ho.trans (output_fields p)
  · simpa only [output_count] using hc

end NearCubicWires.RepairSource.ProjectionNormalization.DedupBytes
