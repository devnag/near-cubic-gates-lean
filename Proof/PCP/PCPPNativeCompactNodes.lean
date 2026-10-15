import Proof.PCP.PCPPNativeClauseOracleRun
import Proof.PCP.PCPPNativeCounters

/-! The literal measured compact fields are exactly the decision clauses
of the same normalized PCPP used by the query emitter. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCompactNodes
open LocalBitMultitape SourceInterfaces RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clauses (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) : List (Fin 3→Literal Q) :=
  ((compactProjectionPCP (p.normalized R Q hR hQ)).decision x (fun _ : Fin R=>false)).clauses

theorem codes (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) : (clauses p R Q hR hQ x).map clauseCodes=Codec.clauses p := by
  change (compactThreeCNF ⟨p.decision.clauses.map (fun c j=>liftQueryLiteral hQ (c j))⟩).clauses.map clauseCodes=_
  exact compact_clause_codes hQ p.decision

theorem count (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) : (clauses p R Q hR hQ x).length=(Codec.clauses p).length := by
  have h:=congrArg List.length (codes p R Q hR hQ x)
  simpa only [List.length_map] using h

theorem fields (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) :
    PCPPNativeClauseLoop.sourceFields (clauses p R Q hR hQ x)=DedupBytes.fields p := by
  rw [PCPPNativeClauseOriginal.source_fields]
  simp only [SuffixScan.stream,List.map_map,Function.comp_def,DedupBytes.row_stream]
  have h:=congrArg (fun codes : List (List ℕ)=>(codes.map QueryBytes.framedCodes).flatten)
    (codes p R Q hR hQ x)
  simpa only [DedupBytes.fields,List.map_map,Function.comp_def] using h

def nodes (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) :=
  PCPPNative.substitutedNodes oracle ((p.normalized R Q hR hQ).queryAddressBits x) (clauses p R Q hR hQ x)

end NearCubicWires.RepairOrdinary.PCPPNativeCompactNodes
