import Proof.PCP.ProjectionNormalizationValueField

/-! Exact target for the remaining duplicate filter and balanced serializer.
This identifies the ordinary producer's four lists with pcpWord of the
same selected normalized witness, retaining the target's clause order. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Codec
open SourceInterfaces ExecutableInterfaces ProjectionPCPPadding CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clauses (p : RawProjectionPCP) : List (List ℕ) := (p.decision.clauses.map clauseCodes).dedup
def word (p : RawProjectionPCP) (R Q : ℕ) : List Bool :=
  (encodeBalancedList [R,Q,encodeBalancedList (normalizedRows p R Q).flatten,
    encodeBalancedList ((clauses p).map encodeBalancedList)]).bits

theorem decision_codes (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (randomness : BitInput R) :
    (((compactProjectionPCP (p.normalized R Q hr hq)).decision x randomness).clauses.map clauseCodes)=clauses p := by
  change (compactThreeCNF ⟨p.decision.clauses.map (fun c j => liftQueryLiteral hq (c j))⟩).clauses.map clauseCodes=_
  exact compact_clause_codes hq p.decision

theorem pcp_word (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : ℕ} (x : BitInput n) :
    pcpWord (compactProjectionPCP (p.normalized R Q hr hq)) x=word p R Q := by
  let qs := List.ofFn fun j : Fin Q => List.ofFn fun i : Fin R =>
    projectionCode ((p.normalized R Q hr hq).queryAddressBits x j i)
  let cs := ((compactProjectionPCP (p.normalized R Q hr hq)).decision x (fun _ => false)).clauses
  change (encodeBalancedList [R,Q,encodeBalancedList qs.flatten,
    encodeBalancedList (cs.map (fun c => encodeBalancedList (clauseCodes c)))]).bits=word p R Q
  have hqcodes : qs=normalizedRows p R Q := normalized_rows p R Q hr hq x
  have hccodes : cs.map clauseCodes=clauses p := decision_codes p R Q hr hq x (fun _ => false)
  have hmap : cs.map (fun c => encodeBalancedList (clauseCodes c))=(clauses p).map encodeBalancedList := by
    simpa only [List.map_map,Function.comp_def] using congrArg (List.map encodeBalancedList) hccodes
  rw [hqcodes,hmap]
  rfl

theorem source_word {v : OrdinaryVerifier} {T U : ℕ → ℕ}
    (source : ProjectionSourceAlgorithm v U) (H : OrdinaryHierarchy T)
    (encode : InputRequest → InputRequest) (R Q : ℕ → ℕ)
    (hr : ∀ r : InputRequest,(source.output (encode r)).width≤R r.1)
    (hq : ∀ r : InputRequest,(source.output (encode r)).queries≤Q r.1) (r : InputRequest) :
    pcpWord (normalizedSourcePCP source H encode R Q hr hq) r.2=
      word (source.output (encode r)) (R r.1) (Q r.1) := by
  exact pcp_word (source.output (encode r)) (R r.1) (Q r.1) (hr r) (hq r) r.2

theorem clauses_length (p : RawProjectionPCP) : (clauses p).length≤(2*p.queries)^3 := by
  have he : clauses p=(compactThreeCNF p.decision).clauses.map clauseCodes := by
    exact List.dedup_map_of_injective clauseCodes_injective _
  rw [he,List.length_map]
  exact compactThreeCNF_clauses p.decision

end NearCubicWires.RepairSource.ProjectionNormalization.Codec
