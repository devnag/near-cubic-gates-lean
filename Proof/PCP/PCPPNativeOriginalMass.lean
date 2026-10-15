import Proof.PCP.PCPPNativeTripleMass

/-! The measured triple stream is the original selected compact clause
stream, with precisely the count produced by the hierarchy deduplicator. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeOriginalMass
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem triple_source (rows : List (Fin 3 → List Bool)) :
    PCPPNativeTripleMass.source rows=SuffixScan.stream rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [PCPPNativeTripleMass.source,PCPPNativeTripleMass.fields,FieldList.stream,
      List.flatMap_cons,List.map_append,List.flatten_append,SuffixScan.stream_cons] at ih ⊢
    rw [ih]
    simp [List.ofFn_succ,ClauseEquality.stream,List.append_assoc]

theorem clause_run (p : RawProjectionPCP) : ∃ result,
    run PCPPNativeTripleMass.machine (PCPPNativeTripleMass.budget (DedupBytes.rows p).dedup)
      (PCPPNativeTripleMass.data (DedupBytes.fields p) (Codec.clauses p).length 0)=some result ∧
    result.steps ≤ PCPPNativeTripleMass.budget (DedupBytes.rows p).dedup ∧
    result.final.heads 4=0 ∧ result.final.tapes 4=DedupBytes.fields p ∧
    result.final.heads 5=0 ∧ result.final.tapes 5=List.replicate (DedupBytes.fields p).length true ∧
    result.final.heads 0=0 ∧ result.final.tapes 0=List.replicate (Codec.clauses p).length true := by
  have h:=PCPPNativeTripleMass.mass_run (DedupBytes.rows p).dedup
  simpa only [triple_source,DedupBytes.output_fields,DedupBytes.output_count] using h

end NearCubicWires.RepairOrdinary.PCPPNativeOriginalMass
