import Proof.Amplification.RecoverySourceClauseList
import Proof.Amplification.RecoveryPCPFormulaResumeFields
import Proof.Amplification.RecoveryProjectionRowsRewind

/-! The clause-list machine consumes the SAME normalized source fields and
its actual projected-address batch, producing the original row formula words. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseList
open LocalBitMultitape RepairOrdinary SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clause_source {Q : Nat} (clause : Fin 3→Literal Q) :
    clauseFields clause=QueryBytes.framedCodes (clauseCodes clause) := by
  simp [clauseFields,RecoverySourceClauseRead.prefixes,QueryBytes.framedCodes,clauseCodes,
    FieldList.stream,List.ofFn_succ,List.append_assoc]

theorem source_codes {Q : Nat} (clauses : List (Fin 3→Literal Q)) :
    sourceFields clauses=((clauses.map clauseCodes).map QueryBytes.framedCodes).flatten := by
  simp only [sourceFields,List.flatMap,List.map_map,Function.comp_def]
  exact congrArg List.flatten (congrArg (fun f=>clauses.map f) (funext clause_source))

theorem original_source (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) :
    sourceFields ((compactProjectionPCP (p.normalized R Q hr hq)).decision x randomness).clauses=
      DedupBytes.fields p := by
  rw [source_codes,Codec.decision_codes]
  rfl

theorem original_addresses (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) :
    RecoverySourceLiteralMeaning.fields (compactProjectionPCP (p.normalized R Q hr hq)) x randomness=
      RecoveryProjectionRows.addressFields p R Q hr hq x randomness := rfl

theorem emitted_words {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) :
    emitted pcp x randomness (pcp.decision x randomness).clauses=
      FieldList.stream (RecoveryPCPFormulaResume.rowWords pcp x randomness) := by
  simp only [emitted,RecoveryPCPFormulaResume.rowWords,FieldList.stream,List.flatMap,List.map_map,Function.comp_def]

theorem original_row_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) (cap : Nat) (pre suffix out : List Bool)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap) : ∃ r,
    runFrom machine ((Codec.clauses p).length*(5*cap+12)+3)
      (cfg 0 cap (pre++DedupBytes.fields p++suffix)
        (FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness))
        out pre.length (Codec.clauses p).length 1)=some r ∧
      r.final=cfg 3 cap (pre++DedupBytes.fields p++suffix)
        (FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness))
        (out++FieldList.stream (RecoveryPCPFormulaResume.rowWords
          (compactProjectionPCP (p.normalized R Q hr hq)) x randomness))
        (pre++DedupBytes.fields p).length (Codec.clauses p).length 1 ∧
      r.steps≤(Codec.clauses p).length*(5*cap+12)+3 := by
  have hcount := congrArg List.length (Codec.decision_codes p R Q hr hq x randomness)
  simp only [List.length_map] at hcount
  have h:=list_run (compactProjectionPCP (p.normalized R Q hr hq)) x randomness cap
    ((compactProjectionPCP (p.normalized R Q hr hq)).decision x randomness).clauses pre suffix out hc
  simpa only [original_source,original_addresses,emitted_words,hcount] using h

end NearCubicWires.RepairSource.RecoverySourceClauseList
