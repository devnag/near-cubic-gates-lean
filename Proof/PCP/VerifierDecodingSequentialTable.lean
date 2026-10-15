import Proof.PCP.VerifierDecodingSequentialRecords

/-! The successful table validator and literal flags reconstruct exactly
the table and flags of the decoder's returned verifier. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Sequential
open LocalBitMultitape VerifierEncoding RepairOrdinary SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pair_reencode (bits : List Bool) (h : bits.length=2) : [bits.getD 0 false,bits.getD 1 false]=bits := by
  cases bits with
  | nil => simp at h
  | cons a bs =>
    cases bs with
    | nil => simp at h
    | cons b cs =>
      have hc : cs=[] := by
        have hz : cs.length=0 := by simp only [List.length_cons] at h; omega
        simpa using hz
      subst cs
      rfl

theorem flags_fromParts (t s : ℕ) (ht : 2≤t) (start : Fin s) (flagWord tableWord : List Bool)
    (h : flagWord.length=2*s) : flags (fromParts t s ht start flagWord tableWord)=flagWord := by
  change (List.ofFn fun i : Fin s => [flagAt flagWord i.val false,flagAt flagWord i.val true]).flatten=flagWord
  have he : (fun i : Fin s => [flagAt flagWord i.val false,flagAt flagWord i.val true])=
      fun i : Fin s => slice flagWord (i.val*2) 2 := by
    funext i
    apply pair_reencode
    apply slice_length
    omega
  rw [he]
  exact flat_slices_exact s 2 flagWord (by omega)

theorem table_fromParts (t s : ℕ) (ht : 2≤t) (start : Fin s) (flagWord tableWord : List Bool)
    (hv : TableValidation.valid (binary (natBitLength s) s) t (s*2^t) tableWord=true) :
    table (fromParts t s ht start flagWord tableWord)=tableWord := by
  let j := natBitLength s
  let W := entryWidth t s
  let P := 2^t
  have hs : s<2^j := Nat.lt_pow_succ_log_self (by decide) s
  simp only [TableValidation.valid,Bool.and_eq_true,decide_eq_true_eq] at hv
  obtain ⟨hscan,hlen⟩ := hv
  have hlen' : tableWord.length=s*(P*W) := by
    have hh : W*(s*P)=tableWord.length := by
      simpa only [RecordsMachine.width,binary_length,W,P,entryWidth] using hlen
    rw [←hh]
    ring
  have hall := (records_tests_iff (binary j s) t (s*P) tableWord).mp hscan
  have hwidth : RecordsMachine.width (binary j s) t=W := by simp [RecordsMachine.width,W,j,entryWidth]
  rw [hwidth] at hall
  have hrow (row : Fin s) :
      (List.ofFn fun mask : Fin P => actionCode j
        (ruleAt tableWord row (fun i : Fin t => mask.val.testBit i.val))).flatten=
      slice tableWord (row.val*(P*W)) (P*W) := by
    let word := slice tableWord (row.val*(P*W)) (P*W)
    have hrowBound : row.val*(P*W)+P*W≤tableWord.length := by
      have hi := Nat.mul_le_mul_right (P*W) row.isLt
      rw [Nat.succ_mul] at hi
      omega
    have hword : word.length=P*W := slice_length _ _ _ hrowBound
    have he : (fun mask : Fin P => actionCode j
        (ruleAt tableWord row (fun i : Fin t => mask.val.testBit i.val)))=
        fun mask : Fin P => slice word (mask.val*W) W := by
      funext mask
      have hm : value (List.ofFn fun i : Fin t => mask.val.testBit i.val)=mask.val :=
        fixedBits_value t mask.val mask.isLt
      change actionCode j (decodeAction j (slice word
        (value (List.ofFn fun i : Fin t => mask.val.testBit i.val)*W) W))=_
      rw [hm]
      have hidx : row.val*P+mask.val<s*P := by
        have hi := Nat.mul_le_mul_right P row.isLt
        rw [Nat.succ_mul] at hi
        omega
      let idx : Fin (s*P) := ⟨row.val*P+mask.val,hidx⟩
      have hc := record_prefix_reencode j (tableWord.drop (idx.val*W)) hs (hall idx)
      have hoff : idx.val*W=row.val*(P*W)+mask.val*W := by dsimp [idx]; ring
      change actionCode j (decodeAction j (slice tableWord (idx.val*W) W))=slice tableWord (idx.val*W) W at hc
      rw [hoff] at hc
      have hb : mask.val*W+W≤P*W := by
        have hi := Nat.mul_le_mul_right W mask.isLt
        simpa only [Nat.succ_mul] using hi
      rw [←slice_slice tableWord (row.val*(P*W)) (P*W) (mask.val*W) W hb] at hc
      exact hc
    rw [he]
    exact flat_slices_exact P W word hword
  change (List.ofFn fun row : Fin s =>
    (List.ofFn fun mask : Fin P => actionCode j (ruleAt tableWord row (fun i : Fin t => mask.val.testBit i.val))).flatten).flatten=tableWord
  simp_rw [hrow]
  exact flat_slices_exact s (P*W) tableWord hlen'

end NearCubicWires.RepairSource.VerifierDecoding.Sequential
