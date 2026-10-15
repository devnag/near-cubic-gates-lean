import Proof.PCP.VerifierDecodingSequentialTable

/-! The exact semantic result of the sequential decoder pipeline. All
canonical re-encoding and dimension guards follow from the executed tests. -/
namespace NearCubicWires.RepairSource.VerifierDecoding
open LocalBitMultitape VerifierEncoding RepairOrdinary SignedSortKey RadixSemantics Sequential
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def SequentialValid (t s : ℕ) (fields : List Bool) : Prop :=
  let j := natBitLength s
  2≤t ∧ 0<s ∧ j≤fields.length ∧ value (fields.take j)<s ∧
    TagScan.tests 2 (fun _ => true) s (fields.drop j)=true ∧
    TableValidation.valid (binary j s) t (s*2^t) (fields.drop (j+2*s))=true

def checkedVerifier (t s : ℕ) (fields : List Bool) (h : SequentialValid t s fields) : OrdinaryVerifier :=
  fromParts t s h.1 ⟨value (fields.take (natBitLength s)),h.2.2.2.1⟩
    (slice fields (natBitLength s) (2*s)) (fields.drop (natBitLength s+2*s))

theorem sequential_reencode (t s : ℕ) (fields : List Bool) (h : SequentialValid t s fields) :
    code (checkedVerifier t s fields h)=HeaderMachine.word t s fields := by
  let j := natBitLength s
  obtain ⟨ht,_,hj,hi,hflags,htable⟩ := h
  have hflagsBound : 2*s≤(fields.drop j).length := by
    simpa only [TagScan.flags_test,decide_eq_true_eq] using hflags
  have hflagLength : (slice fields j (2*s)).length=2*s := by
    apply slice_length
    simp only [List.length_drop] at hflagsBound
    omega
  have hstart : fixedBits j (value (fields.take j))=fields.take j := by
    rw [fixedBits_binary]
    have he := binary_value_word (fields.take j)
    have hj' : j≤fields.length := hj
    simpa only [List.length_take,Nat.min_eq_left hj'] using he
  have hparts : fields.take j++slice fields j (2*s)++fields.drop (j+2*s)=fields := by
    have he := List.take_append_drop (j+2*s) fields
    rw [List.take_add] at he
    exact he
  rw [code_split]
  change HeaderMachine.word t s (fixedBits j (value (fields.take j))++
    flags (fromParts t s ht ⟨value (fields.take j),hi⟩ (slice fields j (2*s)) (fields.drop (j+2*s)))++
    table (fromParts t s ht ⟨value (fields.take j),hi⟩ (slice fields j (2*s)) (fields.drop (j+2*s))))=_
  rw [hstart,flags_fromParts t s ht _ _ _ hflagLength,table_fromParts t s ht _ _ _ htable,hparts]

theorem sequential_countsFit (t s : ℕ) (fields : List Bool) (h : SequentialValid t s fields) :
    CountsFit (HeaderMachine.word t s fields).length t s := by
  have hc := countsFit_code (checkedVerifier t s fields h)
  change CountsFit (code (checkedVerifier t s fields h)).length t s at hc
  rw [sequential_reencode] at hc
  exact hc

def codeFields (v : OrdinaryVerifier) : List Bool :=
  fixedBits (natBitLength v.stateCount) v.machine.start.val++flags v++table v

theorem parts_code (v : OrdinaryVerifier) :
    HeaderMachine.parts (code v)=some (v.tapeCount,v.stateCount,codeFields v) := by
  rw [code_split]
  exact HeaderMachine.parts_word _ _ _

theorem sequential_code (v : OrdinaryVerifier) :
    SequentialValid v.tapeCount v.stateCount (codeFields v) := by
  let j := natBitLength v.stateCount
  have ht : (codeFields v).take j=fixedBits j v.machine.start.val := by
    have he := List.take_left (l₁:=fixedBits j v.machine.start.val) (l₂:=flags v++table v)
    simpa only [fixedBits_length,codeFields,List.append_assoc] using he
  have hd : (codeFields v).drop j=flags v++table v := by
    have he := List.drop_left (l₁:=fixedBits j v.machine.start.val) (l₂:=flags v++table v)
    simpa only [fixedBits_length,codeFields,List.append_assoc] using he
  have htable : (codeFields v).drop (j+2*v.stateCount)=table v := by
    have he := List.drop_left (l₁:=fixedBits j v.machine.start.val++flags v) (l₂:=table v)
    simpa only [fixedBits_length,flags_length,List.length_append,codeFields] using he
  refine ⟨v.twoTapes,Nat.zero_lt_of_lt v.machine.start.isLt,?_,?_,?_,?_⟩
  · simp [codeFields]
  · rw [ht,fixedBits_value j _ (v.machine.start.isLt.trans (Nat.lt_pow_succ_log_self (by decide) v.stateCount))]
    exact v.machine.start.isLt
  · rw [hd,TagScan.flags_test]
    apply decide_eq_true
    simp [flags_length]
  · rw [htable]
    exact table_tests_encoded v

theorem sequential_iff_code (t s : ℕ) (fields : List Bool) :
    SequentialValid t s fields ↔ ∃ v,code v=HeaderMachine.word t s fields := by
  constructor
  · intro h
    exact ⟨checkedVerifier t s fields h,sequential_reencode t s fields h⟩
  · rintro ⟨v,hcode⟩
    have hp : HeaderMachine.parts (code v)=some (t,s,fields) := by
      rw [hcode]
      exact HeaderMachine.parts_word _ _ _
    rw [parts_code] at hp
    simp only [Option.some.injEq,Prod.mk.injEq] at hp
    rcases hp with ⟨ht,hs,hfields⟩
    subst t
    subst s
    subst fields
    exact sequential_code v

theorem sequential_decodeHeader_iff (t s : ℕ) (fields : List Bool) :
    SequentialValid t s fields ↔ ∃ v,decodeHeader (HeaderMachine.word t s fields)=some v ∧
      code v=HeaderMachine.word t s fields := by
  rw [sequential_iff_code]
  constructor
  · rintro ⟨v,hcode⟩
    refine ⟨canonical v,?_,by simpa only [code_canonical] using hcode⟩
    rw [←hcode]
    exact decodeHeader_code v
  · rintro ⟨v,_,hcode⟩
    exact ⟨v,hcode⟩

theorem sequential_decode_iff (N t s : ℕ) (fields : List Bool) :
    ((HeaderMachine.word t s fields).length≤Nat.log 2 N ∧ SequentialValid t s fields) ↔
      ∃ v,decode N (HeaderMachine.word t s fields)=some v := by
  constructor
  · rintro ⟨hlen,hvalid⟩
    obtain ⟨v,hcode⟩ := (sequential_iff_code t s fields).mp hvalid
    refine ⟨canonical v,?_⟩
    rw [←hcode]
    exact decode_code v N (by rw [hcode]; exact hlen)
  · rintro ⟨v,hdecode⟩
    obtain ⟨hlen,hcode⟩ := decode_code_length hdecode
    exact ⟨hlen,(sequential_iff_code t s fields).mpr ⟨v,hcode⟩⟩

end NearCubicWires.RepairSource.VerifierDecoding
