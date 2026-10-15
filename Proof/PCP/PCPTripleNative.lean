import Proof.PCP.PCPTripleData

/-! Exact source-code identity for the physical consecutive triples. The
native literal codes, duplicate order and canonical Nat.bits are unchanged. -/
namespace NearCubicWires.RepairOrdinary.PCPTripleNative
open CanonicalBinary PCPSerializerMass
open RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def groups (p : RawProjectionPCP) : List (List (List Bool)) :=
  (Codec.clauses p).map (fun codes => codes.map Nat.bits)

theorem code_values (codes : List ℕ) :
    PCPTraversal.code (codes.map Nat.bits)=encodeBalancedList codes := by
  unfold PCPTraversal.code values
  simp only [List.map_map,Function.comp_def,CanonicalPositiveOutput.nat_bits_value]
  change encodeBalancedList (codes.map id)=encodeBalancedList codes
  rw [List.map_id]

theorem group_count (p : RawProjectionPCP) : (groups p).length=(Codec.clauses p).length := by
  simp only [groups,List.length_map]

theorem group_three (p : RawProjectionPCP) : ∀ fields∈groups p,fields.length=3 := by
  intro fields hf
  obtain ⟨codes,hcodes,rfl⟩ := List.mem_map.mp hf
  rw [List.length_map]
  have hm : codes∈p.decision.clauses.map clauseCodes := by
    simpa only [Codec.clauses,List.mem_dedup] using hcodes
  obtain ⟨c,_hc,rfl⟩ := List.mem_map.mp hm
  simp only [clauseCodes,List.length_ofFn]

theorem group_stream (p : RawProjectionPCP) : PCPTripleLoop.stream (groups p)=DedupBytes.fields p := by
  simp only [PCPTripleLoop.stream,groups,DedupBytes.fields,
    List.map_map,Function.comp_def]
  rfl

theorem encoded_stream (p : RawProjectionPCP) :
    PCPTripleLoop.encoded (groups p)=QueryBytes.framedCodes ((Codec.clauses p).map encodeBalancedList) := by
  simp only [PCPTripleLoop.encoded,groups,QueryBytes.framedCodes,List.map_map,Function.comp_def,code_values]

theorem query_code (p : RawProjectionPCP) (R Q : ℕ) :
    PCPTraversal.code ((normalizedRows p R Q).flatten.map Nat.bits)=
      encodeBalancedList (normalizedRows p R Q).flatten := code_values _

theorem clause_list_code (p : RawProjectionPCP) :
    PCPTraversal.code (((Codec.clauses p).map encodeBalancedList).map Nat.bits)=
      encodeBalancedList ((Codec.clauses p).map encodeBalancedList) := code_values _

theorem outer_code (p : RawProjectionPCP) (R Q : ℕ) :
    (PCPTraversal.code [R.bits,Q.bits,
      (encodeBalancedList (normalizedRows p R Q).flatten).bits,
      (encodeBalancedList ((Codec.clauses p).map encodeBalancedList)).bits]).bits=Codec.word p R Q := by
  have h := code_values [R,Q,encodeBalancedList (normalizedRows p R Q).flatten,
    encodeBalancedList ((Codec.clauses p).map encodeBalancedList)]
  exact congrArg Nat.bits h

end NearCubicWires.RepairOrdinary.PCPTripleNative
