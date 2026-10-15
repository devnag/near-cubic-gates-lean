import Proof.Amplification.RecoveryCertificateTableBounds

/-! All indices in the shared valuation fit the original payload. Counts
remain binary scalars and cause no expansion into prefix clauses. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
open CanonicalBinary BalancedCNFSATEncoding BalancedCertificate
open private decodeClauseCodes from StatementSupport
open private faithful_list faithful_prod faithful_bool faithful_nat from Proof.Amplification.RecoveryCompactSize
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clause_literal_le (code : Nat) (literal : Bool×Nat)
    (hm : literal∈(Encodable.decode (α := List (Bool×Nat)) code).getD []) : literal.2≤code := by
  cases hd : Encodable.decode (α := List (Bool×Nat)) code with
  | none => simp [hd] at hm
  | some clause =>
    have he : Encodable.encode clause=code :=
      faithful_list (faithful_prod faithful_bool faithful_nat) code clause hd
    have hl : literal∈clause := by simpa only [hd,Option.getD_some] using hm
    exact (Nat.right_le_pair (Encodable.encode literal.1) literal.2).trans
      ((RawSyntaxCertificate.member_code_le literal clause hl).trans_eq he)

theorem clause_variables_le (codes : List Nat) (committed count ceiling : Nat)
    (hc : ∀ code∈codes,code≤ceiling) (index : Nat)
    (hi : index∈(⟨decodeClauseCodes codes,committed,count⟩ : CompactRequest).variables) : index≤ceiling := by
  simp only [CompactRequest.variables,List.mem_eraseDups,List.mem_map] at hi
  obtain ⟨literal,hl,rfl⟩ := hi
  obtain ⟨clause,hclause,hl⟩ := List.mem_flatten.mp hl
  obtain ⟨code,hcode,rfl⟩ := List.mem_map.mp hclause
  exact (clause_literal_le code literal hl).trans (hc code hcode)

theorem chunks_member_le {chunks codes : List Nat}
    (hd : decodeBalancedClauseChunks chunks=some codes) (ceiling : Nat)
    (hc : ∀ chunk∈chunks,chunk≤ceiling) (code : Nat) (hm : code∈codes) : code≤ceiling := by
  induction chunks generalizing codes with
  | nil => simp [decodeBalancedClauseChunks] at hd; subst codes; simp at hm
  | cons chunk rest ih =>
    cases hh : decodeBalancedList chunk with
    | none => simp [decodeBalancedClauseChunks,hh] at hd
    | some head =>
      cases ht : decodeBalancedClauseChunks rest with
      | none => simp [decodeBalancedClauseChunks,hh,ht] at hd
      | some tail =>
        have he : head++tail=codes := by simpa [decodeBalancedClauseChunks,hh,ht] using hd
        rw [← he] at hm
        rcases List.mem_append.mp hm with hm|hm
        · exact (decoded_member_le hh code hm).trans (hc chunk (by simp))
        · exact ih ht (by intro c hm; exact hc c (by simp [hm])) hm

theorem nested_member_le {payload : Nat} {codes : List Nat}
    (hd : decodeNestedBalancedCNFPayload payload=some codes) (code : Nat) (hm : code∈codes) : code≤payload := by
  cases hh : decodeBalancedList payload with
  | none => simp [decodeNestedBalancedCNFPayload,hh] at hd
  | some chunks =>
    have hd' : decodeBalancedClauseChunks chunks=some codes := by
      simpa [decodeNestedBalancedCNFPayload,hh] using hd
    exact chunks_member_le hd' payload (fun c hc => decoded_member_le hh c hc) code hm

def DataFits (code : Nat) (table : FiniteValuation.Table) (inner outer : List Row) : Prop :=
  table.length≤3*natBitLength code ∧ (∀ entry∈table,entry.1≤code) ∧
    inner.length≤3*natBitLength code ∧ outer.length≤2*natBitLength code+1 ∧
    ∀ row∈inner++outer,RowFits code (natBitLength code) row

theorem DataFits.mono {small large : Nat} {table : FiniteValuation.Table} {inner outer : List Row}
    (h : DataFits small table inner outer) (hl : small≤large) : DataFits large table inner outer := by
  have hw := RawSyntaxCertificate.width_mono hl
  refine ⟨h.1.trans (Nat.mul_le_mul_left 3 hw),fun entry he => (h.2.1 entry he).trans hl,
    h.2.2.1.trans (Nat.mul_le_mul_left 3 hw),h.2.2.2.1.trans (by omega),?_⟩
  intro row hm
  have hf := h.2.2.2.2 row hm
  exact ⟨hf.1.trans hl,hf.2.1.trans hl,hf.2.2.1.trans hw,hf.2.2.2⟩

theorem bounded_flat_payload (payload committed count : Nat)
    (hs : ∃ table rows,rootCheck (clausePredicate committed count table) rows payload=true) :
    ∃ table outer,rootCheck (clausePredicate committed count table) outer payload=true ∧
      DataFits payload table [] outer := by
  obtain ⟨codes,hd,hm⟩ := (flat_payload_iff payload committed count).mp hs
  obtain ⟨table,ht,hs,hf⟩ := FiniteValuation.bounded_table _ hm
  have hn := decoded_balanced_length hd
  obtain ⟨outer,ho,hos,hof⟩ := bounded_rootCheck (clausePredicate committed count table) hd
    ((clause_codes_check codes committed count table).symm ▸ ht)
  refine ⟨table,outer,ho,?_,?_,by simp,hos,by simpa using hof⟩
  · simp only [decodeClauseCodes,List.length_map] at hs
    exact hs.trans (Nat.mul_le_mul_left 3 hn)
  · intro entry he
    exact clause_variables_le codes committed count payload (fun c hc => decoded_member_le hd c hc)
      entry.1 (hf entry he)

theorem bounded_nested_payload (payload committed count : Nat)
    (hs : ∃ table inner outer,nestedCheck (clausePredicate committed count table) inner outer payload=true) :
    ∃ table inner outer,nestedCheck (clausePredicate committed count table) inner outer payload=true ∧
      DataFits payload table inner outer := by
  obtain ⟨codes,hd,hm⟩ := (nested_payload_iff payload committed count).mp hs
  obtain ⟨table,ht,hs,hf⟩ := FiniteValuation.bounded_table _ hm
  have hn := decoded_nested_length hd
  obtain ⟨inner,outer,ho,his,hos,hof⟩ := bounded_nestedCheck (clausePredicate committed count table) hd
    ((clause_codes_check codes committed count table).symm ▸ ht)
  refine ⟨table,inner,outer,ho,?_,?_,his,hos,hof⟩
  · simp only [decodeClauseCodes,List.length_map] at hs
    exact hs.trans (Nat.mul_le_mul_left 3 hn)
  · intro entry he
    exact clause_variables_le codes committed count payload (fun c hc => nested_member_le hd c hc)
      entry.1 (hf entry he)

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
