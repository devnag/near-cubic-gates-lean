import Proof.PCP.PCPPNativeClauseLoop

/-! Apply the complete clause emitter to the original oracle and clause
fields. Shared measured byte/count bounds discharge every per-clause premise. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseOriginal
open LocalBitMultitape SourceInterfaces RepairSource PCPPNativeClauseLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem literal_length {q : ℕ} (clause : Fin 3→Literal q) (j : Fin 3) :
    (PCPPNativeClauseTyped.bits clause j).length≤(PCPPNativeClauseTyped.fields clause).length := by
  fin_cases j
  all_goals first
    | change (PCPPNativeClauseTyped.bits clause 0).length≤_
    | change (PCPPNativeClauseTyped.bits clause 1).length≤_
    | change (PCPPNativeClauseTyped.bits clause 2).length≤_
  all_goals simp only [PCPPNativeClauseTyped.fields,PCPPNativeClauseTriple.fields,List.length_append,frame_length]
  all_goals omega

theorem field_length {q : ℕ} (clauses : List (Fin 3→Literal q))
    (clause : Fin 3→Literal q) (hc : clause∈clauses) (j : Fin 3) :
    (PCPPNativeClauseTyped.bits clause j).length≤(sourceFields clauses).length := by
  induction clauses with
  | nil => simp at hc
  | cons head tail ih =>
    rcases List.mem_cons.mp hc with rfl|ht
    · have h:=literal_length clause j
      simp only [sourceFields,List.flatMap_cons,List.length_append]
      omega
    · have h:=ih ht
      change (PCPPNativeClauseTyped.bits clause j).length≤(List.flatMap PCPPNativeClauseTyped.fields tail).length at h
      simp only [sourceFields,List.flatMap_cons,List.length_append]
      omega

theorem literal_reference {n q : ℕ} (oracle : BooleanCircuit n) (literal : Literal q) :
    PCPPNativeClauseTyped.reference (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size) literal=
      PCPPNative.literalAddress oracle literal := by
  rw [PCPPNativeClauseTyped.query_reference]
  cases literal <;> rfl

theorem literal_bound {n q : ℕ} (r : ℕ) (oracle : BooleanCircuit n) (literal : Literal q) :
    PCPPNativeClauseTyped.reference (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size) literal<q*(2*oracle.size+1) := by
  have h:=PCPPSubstitution.queryAddress_lt (BooleanDAGBuilder.empty r) oracle q
    (PCPPNativeClauseTyped.index literal) (PCPPNativeClauseTyped.index_lt literal) (PCPPNativeClauseTyped.negative literal)
  simpa only [PCPPNativeClauseTyped.query_reference,BooleanDAGBuilder.empty,List.length_nil,Nat.zero_add] using h

theorem source_fields {q : ℕ} (clauses : List (Fin 3→Literal q)) :
    sourceFields clauses=ProjectionNormalization.SuffixScan.stream (clauses.map ProjectionNormalization.DedupBytes.row) := by
  simp only [sourceFields,List.flatMap_def,ProjectionNormalization.SuffixScan.stream,List.map_map,
    Function.comp_def]
  rfl

theorem compact_source_fields (raw : RawProjectionPCP) :
    sourceFields raw.decision.clauses.dedup=ProjectionNormalization.DedupBytes.fields raw := by
  have h:=ProjectionNormalization.DedupBytes.output_fields raw
  rw [source_fields]
  simpa only [ProjectionNormalization.DedupBytes.rows,
    List.dedup_map_of_injective ProjectionNormalization.DedupBytes.row_injective] using h

theorem accumulator_value (base count : ℕ) :
    finalAccumulator (base+1) base count=base+3*count := by
  unfold finalAccumulator
  split_ifs <;> omega

theorem original_run {n q : ℕ} (r W C : ℕ) (oracle : BooleanCircuit n)
    (clauses : List (Fin 3→Literal q)) (pre suffix out : List Bool)
    (hstride : 2*oracle.size+1≤W) (hsize : q*(2*oracle.size+1)+3*clauses.length+1≤W)
    (hbytes : (sourceFields clauses).length≤W) (hC : 16384*(W+1)^2≤C) :
    ∃ result,runFrom machine (clauses.length*(48*C+131)+3)
      (cfg 0 (pre++sourceFields clauses++suffix) pre.length (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size) C
        (q*(2*oracle.size+1)+1) (q*(2*oracle.size+1)) out clauses.length 1)=some result ∧
      result.final=cfg 3 (pre++sourceFields clauses++suffix) (pre++sourceFields clauses).length
        (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size) C
        (q*(2*oracle.size+1)+3*clauses.length+1) (q*(2*oracle.size+1)+3*clauses.length)
        (out++(PCPPNative.clauseStreamNodes (r:=r) (q*(2*oracle.size+1)+1) (q*(2*oracle.size+1))
          (PCPPNative.literalAddress oracle) clauses).flatMap PCPPRequestNodeSchema.native) clauses.length 1 ∧
      result.steps≤clauses.length*(48*C+131)+3 := by
  have hout : oracle.output.val<oracle.size:=oracle.output.isLt
  have hq : q≤W := by nlinarith [Nat.zero_le (q*oracle.size)]
  have hl (clause : Fin 3→Literal q) (hc : clause∈clauses) (j : Fin 3) :=
    (field_length clauses clause hc j).trans hbytes
  have href (clause : Fin 3→Literal q) (_hc : clause∈clauses) (j : Fin 3) :
      PCPPNativeClauseTyped.refs (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size) clause j≤W := by
    have h:=literal_bound r oracle (clause j)
    change PCPPNativeClauseTyped.reference _ _ _ _≤W
    omega
  have h:=list_run r (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size) W C
    hq hstride (by omega) (by omega) hC clauses hl href pre suffix out
    (q*(2*oracle.size+1)+1) (q*(2*oracle.size+1)) (by omega) (by omega)
  have hrefeq : PCPPNativeClauseTyped.reference (q:=q) (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size)=
      PCPPNative.literalAddress oracle := funext (literal_reference oracle)
  have hbase : (q*(2*oracle.size+1)+1)+3*clauses.length=q*(2*oracle.size+1)+3*clauses.length+1 := by omega
  simp only [emitted,hrefeq,hbase,accumulator_value] at h
  exact h

end NearCubicWires.RepairOrdinary.PCPPNativeClauseOriginal
