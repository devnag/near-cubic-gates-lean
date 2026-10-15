import Proof.PCP.ProjectionNormalizationStreams

/-! The complete stream producer has an explicit polynomial bound in the
actual raw source-output length and the physically produced dimensions. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Streams
open SourceInterfaces ExecutableInterfaces LocalBitMultitape RepairOrdinary VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_literal (p : RawProjectionPCP) (R Q : ℕ) :
    input p R Q=(fun i => if i=0 then p.word else if i=13 then List.replicate R true else
      if i=14 then List.replicate Q true else []) := by
  funext i
  fin_cases i <;> rfl

theorem clause_width (p : RawProjectionPCP) (row : List ℕ) (hrow : row∈Codec.clauses p) : row.length=3 := by
  have hm : row∈p.decision.clauses.map clauseCodes := by simpa only [Codec.clauses,List.mem_dedup] using hrow
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp hm
  simp [clauseCodes]

theorem source_sizes (p : RawProjectionPCP) :
    p.width.bits.length ≤ p.word.length ∧ p.queries.bits.length ≤ p.word.length ∧
    (Rows.stream (QueryBytes.rowsBits (queryRows p))).length ≤ p.word.length ∧
    (SuffixScan.stream (DedupBytes.rows p)).length ≤ p.word.length ∧
    (DedupBytes.rows p).length.bits.length ≤ p.word.length ∧
    (DedupBytes.rows p).length ≤ p.word.length := by
  have hfirst := congrArg List.length (QueryBytes.source_split p)
  simp only [List.length_append,QueryBytes.header,frame_length] at hfirst
  have hlast := congrArg List.length (raw_word p)
  simp only [List.length_append,frame_length] at hlast
  have hc := Dedup.count_le_bytes (DedupBytes.rows p)
  omega

theorem query_count (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q) :
    (normalizedRows p R Q).flatten.length=R*Q := by
  have h := congrArg (fun xs : List (List ℕ) => xs.flatten.length)
    (normalized_rows p R Q hr hq (fun _ : Fin 0 => false))
  simpa [List.length_flatten,List.map_ofFn,Function.comp_def,List.ofFn_const,Nat.mul_comm] using h.symm

theorem clause_count (p : RawProjectionPCP) (Q : ℕ) (hq : p.queries ≤ Q) :
    (Codec.clauses p).length ≤ (2*Q)^3 := by
  exact (Codec.clauses_length p).trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hq) 3)

theorem budget_bound (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q) :
    budget p R Q ≤ 1024*(p.word.length+R+Q+1)^3 := by
  let z := p.word.length+R+Q+1
  have hz : 1 ≤ z := by dsimp [z]; omega
  obtain ⟨hwidth,hqueries,hnative,hclauses,hcountbits,hcount⟩ := source_sizes p
  have hR : R ≤ z := by dsimp [z]; omega
  have hQ : Q ≤ z := by dsimp [z]; omega
  have hw1 : p.width+1 ≤ z := by dsimp [z]; omega
  have hq1 : p.queries+1 ≤ z := by dsimp [z]; omega
  have hwbits : p.width.bits.length+1 ≤ z := by dsimp [z]; omega
  have hqbits : p.queries.bits.length+1 ≤ z := by dsimp [z]; omega
  have hmulw := Nat.mul_le_mul hw1 hwbits
  have hmulq := Nat.mul_le_mul hq1 hqbits
  have hheader : Header.budget p.width.bits p.queries.bits ≤ 65*z^2 := by
    dsimp [Header.budget,ValueField.budget]
    rw [RecoveryUnpair.bits_value,RecoveryUnpair.bits_value]
    nlinarith
  have hdriver : Drivers.budget R Q p.queries ≤ 128*z^2 := by
    have ht := Drivers.budget_bound R Q p.queries
    have hz' : R+Q+1 ≤ z := by dsimp [z]; omega
    exact ht.trans (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hz' 2))
  have hpad : R-p.width ≤ z := (Nat.sub_le R _).trans hR
  have hextra := Nat.mul_le_mul ((Nat.sub_le Q p.queries).trans hQ) hR
  have hrow : 3*p.width+10*(R-p.width)+10 ≤ 13*z+10 := by omega
  have hrows := Nat.mul_le_mul (hq.trans hQ) hrow
  have hquery : QueryReady.budget p R Q ≤ 84*z^2 := by
    have hn : (Rows.stream (QueryBytes.rowsBits (queryRows p))).length ≤ z := by dsimp [z]; omega
    dsimp [QueryReady.budget,QueryBytes.budget]
    nlinarith
  have hm1 : (DedupBytes.rows p).length+1 ≤ z := by dsimp [z]; omega
  have hmbits : (DedupBytes.rows p).length.bits.length+1 ≤ z := by dsimp [z]; omega
  have hmmul := Nat.mul_le_mul hm1 hmbits
  have hclause1 : (SuffixScan.stream (DedupBytes.rows p)).length+1 ≤ z := by dsimp [z]; omega
  have hcube := Nat.pow_le_pow_left hclause1 3
  have hclause : Clauses.budget (DedupBytes.rows p) ≤ 32*z^2+128*z^3+1 := by
    dsimp [Clauses.budget,ValueField.budget,DedupReady.budget]
    rw [RecoveryUnpair.bits_value]
    nlinarith
  have hsq : z^2 ≤ z^3 := by
    have hm := Nat.mul_le_mul_left (z^2) hz
    simpa [pow_succ] using hm
  change budget p R Q ≤ 1024*z^3
  dsimp only [budget,StreamQueries.budget,StreamPrepare.budget]
  nlinarith

end NearCubicWires.RepairSource.ProjectionNormalization.Streams
