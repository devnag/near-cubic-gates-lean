import Proof.PCP.VerifierDecodingWhole
import Proof.PCP.VerifierDecodingSequential

/-! The actual decoder's physical Boolean is exactly canonical semantic
decoding. Its table-size guard follows from successful sequential validation,
so the executable guard adds no restriction to the encoded machine domain. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Whole
open LocalBitMultitape RepairOrdinary VerifierEncoding SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bound_value (s : ℕ) : value (Front.bound s)=s := by
  exact fixedBits_value (natBitLength s) s (Nat.lt_pow_succ_log_self (by decide) s)

theorem sequential_fields (t s : ℕ) (fields : List Bool) :
    SequentialValid t s fields ↔ (2≤t ∧ 0<s) ∧
      StartFlags.valid fields (Front.bound s) s=true ∧
      TableValidation.valid (Front.bound s) t (2^t*s) (FrontTable.tableState fields t s).bits=true := by
  have hb : value (binary (natBitLength s) s)=s := by
    simpa [Front.bound,fixedBits_binary] using bound_value s
  simp [SequentialValid,StartFlags.valid,RecordMachine.rangeValid,
    TagScan.flags_test,FrontTable.tableState,Front.bound,fixedBits_binary,hb,Nat.mul_comm,and_assoc]

theorem valid_parts_iff (word fields : List Bool) (limit t s : ℕ)
    (hp : HeaderMachine.parts word=some (t,s,fields)) :
    valid word limit=true ↔ word.length≤limit ∧ SequentialValid t s fields := by
  have hraw : valid word limit=true ↔
      ((word.length≤limit ∧ (2≤t ∧ 0<s)) ∧ StartFlags.valid fields (Front.bound s) s=true) ∧
      (2^t*s ≤ word.length ∧
        TableValidation.valid (Front.bound s) t (2^t*s) (FrontTable.tableState fields t s).bits=true) := by
    simp [valid,Front.valid,GuardedPreparation.valid,GuardedPreparation.headerValid,
      GuardedPreparation.dimensions,hp,tableValid]
  rw [hraw]
  constructor
  · rintro ⟨⟨⟨hlimit,hdim⟩,hstart⟩,_,htable⟩
    exact ⟨hlimit,(sequential_fields t s fields).mpr ⟨hdim,hstart,htable⟩⟩
  · rintro ⟨hlimit,hseq⟩
    obtain ⟨hdim,hstart,htable⟩ := (sequential_fields t s fields).mp hseq
    have hfit := sequential_countsFit t s fields hseq
    have hw := HeaderMachine.parts_decomposition hp
    have he : 2^t*s ≤ word.length := by
      rw [hw,Nat.mul_comm]
      exact hfit.2.2.2.1
    exact ⟨⟨⟨hlimit,hdim⟩,hstart⟩,he,htable⟩

theorem valid_decode_iff (N : ℕ) (word : List Bool) :
    valid word (Nat.log 2 N)=true ↔ ∃ v,decode N word=some v := by
  constructor
  · intro hv
    cases hp : HeaderMachine.parts word with
    | none => simp [valid,Front.valid,GuardedPreparation.valid,GuardedPreparation.headerValid,hp] at hv
    | some triple =>
      rcases triple with ⟨t,s,fields⟩
      have he := (valid_parts_iff word fields (Nat.log 2 N) t s hp).mp hv
      have hw := HeaderMachine.parts_decomposition hp
      rw [hw] at he ⊢
      exact (sequential_decode_iff N t s fields).mp he
  · rintro ⟨v,hv⟩
    obtain ⟨hlen,hcode⟩ := decode_code_length hv
    have hp : HeaderMachine.parts word=some (v.tapeCount,v.stateCount,codeFields v) := by
      rw [←hcode]
      exact parts_code v
    exact (valid_parts_iff word (codeFields v) (Nat.log 2 N) v.tapeCount v.stateCount hp).mpr
      ⟨hlen,sequential_code v⟩

theorem decoder_run (N : ℕ) (word : List Bool) :
    ∃ r, runFrom machine (budget word.length) (blankEntry word (Nat.log 2 N))=some r ∧
      r.steps≤budget word.length ∧
      (r.final.scanned 19=true ↔ ∃ v,decode N word=some v) ∧
      Outcome word (Nat.log 2 N) (ZeroPadding.config (inputCapacity word) r.final) := by
  obtain ⟨r,hr,hs,hbit,hout⟩ := whole_run word (Nat.log 2 N)
  exact ⟨r,hr,hs,by rw [hbit,valid_decode_iff],hout⟩

end NearCubicWires.RepairSource.VerifierDecoding.Whole
