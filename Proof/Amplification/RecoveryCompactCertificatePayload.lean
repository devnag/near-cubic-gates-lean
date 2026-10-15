import Proof.Amplification.RecoveryBalancedCertificatePredicate
import Proof.Amplification.RecoveryFiniteValuation

namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
open CanonicalBinary BalancedCNFSATEncoding TseitinCNF BalancedCertificate
open private decodeClauseCodes from StatementSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clausePredicate (committed count : Nat) (table : FiniteValuation.Table)
    (code : Nat) : Bool :=
  let clause := (Encodable.decode (α := List (Bool×Nat)) code).getD []
  decide (clause.length=3) && clauseEval (FiniteValuation.assignment committed count table) clause

theorem clause_codes_check (codes : List Nat) (committed count : Nat)
    (table : FiniteValuation.Table) :
    codes.all (clausePredicate committed count table)=
      FiniteValuation.check ⟨decodeClauseCodes codes,committed,count⟩ table := by
  apply Bool.eq_iff_iff.mpr
  simp [FiniteValuation.check,decodeClauseCodes,formulaEval,List.all_eq_true,clausePredicate,forall_and]

def hasRoot (rows : List Row) (code : Nat) : Bool := rows.any fun row => row.code==code
def nestedCheck (P : Nat → Bool) (inner outer : List Row) (payload : Nat) : Bool :=
  checkFrom [] inner && inner.all (leafCheck P) && rootCheck (hasRoot inner) outer payload

theorem chunks_predicate_iff (P : Nat → Bool) (chunks : List Nat) :
    (∀ chunk∈chunks,∃ codes,decodeBalancedList chunk=some codes ∧ codes.all P=true) ↔
      ∃ codes,decodeBalancedClauseChunks chunks=some codes ∧ codes.all P=true := by
  induction chunks with
  | nil => simp [decodeBalancedClauseChunks]
  | cons chunk rest ih =>
    constructor
    · intro h
      obtain ⟨head,hh,hp⟩ := h chunk (by simp)
      obtain ⟨tail,ht,hq⟩ := ih.mp (by intro c hc; exact h c (by simp [hc]))
      exact ⟨head++tail,by simp [decodeBalancedClauseChunks,hh,ht],by simp [hp,hq]⟩
    · rintro ⟨codes,hd,hp⟩
      cases hh : decodeBalancedList chunk with
      | none => simp [decodeBalancedClauseChunks,hh] at hd
      | some head =>
        cases ht : decodeBalancedClauseChunks rest with
        | none => simp [decodeBalancedClauseChunks,hh,ht] at hd
        | some tail =>
          have he : head++tail=codes := by simpa [decodeBalancedClauseChunks,hh,ht] using hd
          rw [← he,List.all_append,Bool.and_eq_true] at hp
          intro c hc
          rcases List.mem_cons.mp hc with rfl|hc
          · exact ⟨head,hh,hp.1⟩
          · exact ih.mpr ⟨tail,ht,hp.2⟩ c hc

theorem checked_root (P : Nat → Bool) (rows : List Row) (code : Nat)
    (hc : checkFrom [] rows=true) (hp : rows.all (leafCheck P)=true)
    (hr : hasRoot rows code=true) :
    ∃ codes,decodeBalancedList code=some codes ∧ codes.all P=true := by
  apply rootCheck_sound P rows code
  simp only [rootCheck,hc,hp,hasRoot] at hr ⊢
  exact hr

theorem chunk_tables (P : Nat → Bool) (chunks : List Nat)
    (hh : ∀ chunk∈chunks,∃ codes,decodeBalancedList chunk=some codes ∧ codes.all P=true) :
    ∃ rows,checkFrom [] rows=true ∧ rows.all (leafCheck P)=true ∧ chunks.all (hasRoot rows)=true := by
  induction chunks with
  | nil => exact ⟨[],rfl,rfl,rfl⟩
  | cons chunk rest ih =>
    obtain ⟨head,hd,hp⟩ := hh chunk (by simp)
    obtain ⟨w⟩ := exists_witness head
    have hw := witness_rootCheck head w P hp
    rw [encodeBalancedList_of_decode hd] at hw
    simp only [rootCheck,Bool.and_eq_true] at hw
    obtain ⟨tail,ht,hl,hr⟩ := ih (by intro c hc; exact hh c (by simp [hc]))
    refine ⟨w.rows++tail,?_,by simp [hw.1.2,hl],?_⟩
    · rw [check_append]
      simp only [List.nil_append,hw.1.1,Bool.true_and]
      exact check_mono [] w.rows tail (by simp) ht
    · rw [List.all_cons,Bool.and_eq_true]
      constructor
      · simp only [hasRoot,List.any_append,hw.2,Bool.true_or]
      · rw [List.all_eq_true] at hr ⊢
        intro c hc
        simp only [hasRoot,List.any_append]
        rw [show tail.any (fun row => row.code==c)=true from hr c hc]
        exact Bool.or_true _

theorem nestedCheck_iff (P : Nat → Bool) (payload : Nat) :
    (∃ inner outer,nestedCheck P inner outer payload=true) ↔
      ∃ codes,decodeNestedBalancedCNFPayload payload=some codes ∧ codes.all P=true := by
  constructor
  · rintro ⟨inner,outer,hc⟩
    simp only [nestedCheck,Bool.and_eq_true] at hc
    obtain ⟨chunks,hd,hroots⟩ := rootCheck_sound (hasRoot inner) outer payload hc.2
    have hchunks : ∀ chunk∈chunks,∃ codes,decodeBalancedList chunk=some codes ∧ codes.all P=true := by
      intro chunk hm
      exact checked_root P inner chunk hc.1.1 hc.1.2 (List.all_eq_true.mp hroots chunk hm)
    obtain ⟨codes,hcodes,hp⟩ := (chunks_predicate_iff P chunks).mp hchunks
    exact ⟨codes,by simp [decodeNestedBalancedCNFPayload,hd,hcodes],hp⟩
  · rintro ⟨codes,hd,hp⟩
    cases hh : decodeBalancedList payload with
    | none => simp [decodeNestedBalancedCNFPayload,hh] at hd
    | some chunks =>
      have hchunks : decodeBalancedClauseChunks chunks=some codes := by
        simpa [decodeNestedBalancedCNFPayload,hh] using hd
      obtain ⟨inner,hi,hl,hr⟩ := chunk_tables P chunks ((chunks_predicate_iff P chunks).mpr ⟨codes,hchunks,hp⟩)
      obtain ⟨outer,ho⟩ := (rootCheck_iff (hasRoot inner) payload).mpr ⟨chunks,hh,hr⟩
      exact ⟨inner,outer,by simp [nestedCheck,hi,hl,ho]⟩

theorem flat_payload_iff (payload committed count : Nat) :
    (∃ table rows,rootCheck (clausePredicate committed count table) rows payload=true) ↔
      ∃ codes,decodeBalancedList payload=some codes ∧
        compactMeaning ⟨decodeClauseCodes codes,committed,count⟩ := by
  constructor
  · rintro ⟨table,rows,hc⟩
    obtain ⟨codes,hd,hp⟩ := rootCheck_sound (clausePredicate committed count table) rows payload hc
    exact ⟨codes,hd,FiniteValuation.check_sound _ table ((clause_codes_check codes committed count table) ▸ hp)⟩
  · rintro ⟨codes,hd,hm⟩
    obtain ⟨table,ht⟩ := (FiniteValuation.check_iff _).mpr hm
    obtain ⟨rows,hr⟩ := (rootCheck_iff (clausePredicate committed count table) payload).mpr
      ⟨codes,hd,(clause_codes_check codes committed count table).symm ▸ ht⟩
    exact ⟨table,rows,hr⟩

theorem nested_payload_iff (payload committed count : Nat) :
    (∃ table inner outer,nestedCheck (clausePredicate committed count table) inner outer payload=true) ↔
      ∃ codes,decodeNestedBalancedCNFPayload payload=some codes ∧
        compactMeaning ⟨decodeClauseCodes codes,committed,count⟩ := by
  constructor
  · rintro ⟨table,inner,outer,hc⟩
    obtain ⟨codes,hd,hp⟩ := (nestedCheck_iff (clausePredicate committed count table) payload).mp ⟨inner,outer,hc⟩
    exact ⟨codes,hd,FiniteValuation.check_sound _ table ((clause_codes_check codes committed count table) ▸ hp)⟩
  · rintro ⟨codes,hd,hm⟩
    obtain ⟨table,ht⟩ := (FiniteValuation.check_iff _).mpr hm
    obtain ⟨inner,outer,hr⟩ := (nestedCheck_iff (clausePredicate committed count table) payload).mpr
      ⟨codes,hd,(clause_codes_check codes committed count table).symm ▸ ht⟩
    exact ⟨table,inner,outer,hr⟩

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
