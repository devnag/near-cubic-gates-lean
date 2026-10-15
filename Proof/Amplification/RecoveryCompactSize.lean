import Proof.Amplification.RecoveryCompactVerifier

/-! Encoded-length ledger for the compact SAT checker.  These bounds concern
the data actually parsed, rather than the possibly enormous binary prefix
count. They are the size preconditions for its local ordinary implementation. -/
namespace NearCubicWires.RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open CanonicalBinary BalancedCNFSATEncoding

private theorem pair_product (left right : Nat) :
    (left + 1) * (right + 1) ≤ Nat.pair left right + 1 := by
  unfold Nat.pair
  split <;> nlinarith

/-- Each atom's binary width is paid for by the enclosing balanced code. -/
theorem balanced_atoms_pow (values : List Nat) :
    2 ^ (values.map natBitLength).sum ≤ encodeBalancedList values + 1 := by
  induction values using encodeBalancedList.induct with
  | case1 => simp [encodeBalancedList]
  | case2 value =>
    have hv := Nat.pow_log_le_add_one 2 value
    have hp := pair_product 1 value
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, encodeBalancedList, natBitLength, pow_succ]
    nlinarith
  | case3 first second rest values leftLength left right ihleft ihright =>
    have hsum : (values.map natBitLength).sum =
        (left.map natBitLength).sum + (right.map natBitLength).sum := by
      rw [← List.sum_append, ← List.map_append]
      simp only [left, right, List.take_append_drop]
    rw [encodeBalancedList.eq_def]
    change 2 ^ (values.map natBitLength).sum ≤
      Nat.pair 2 (Nat.pair (encodeBalancedList left) (encodeBalancedList right)) + 1
    rw [hsum, pow_add]
    exact (Nat.mul_le_mul ihleft ihright).trans
      ((pair_product _ _).trans
        (Nat.add_le_add_right (Nat.right_le_pair _ _) 1))

theorem balanced_atoms_bits (values : List Nat) :
    (values.map natBitLength).sum ≤ natBitLength (encodeBalancedList values) := by
  have hp := balanced_atoms_pow values
  have hc : encodeBalancedList values <
      2 ^ natBitLength (encodeBalancedList values) :=
    Nat.lt_pow_succ_log_self (by omega) _
  by_contra h
  have hlt := Nat.pow_lt_pow_right (by omega : 1 < (2 : Nat))
    (show natBitLength (encodeBalancedList values) <
      (values.map natBitLength).sum by omega)
  omega

theorem list_length_le_atom_bits (values : List Nat) :
    values.length ≤ (values.map natBitLength).sum := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have : 1 ≤ natBitLength value := by unfold natBitLength; omega
    omega

theorem decoded_balanced_atoms_bits {code : Nat} {values : List Nat}
    (hdecode : decodeBalancedList code = some values) :
    (values.map natBitLength).sum ≤ natBitLength code := by
  rw [← encodeBalancedList_of_decode hdecode]
  exact balanced_atoms_bits values

theorem decoded_balanced_length {code : Nat} {values : List Nat}
    (hdecode : decodeBalancedList code = some values) :
    values.length ≤ natBitLength code :=
  (list_length_le_atom_bits values).trans (decoded_balanced_atoms_bits hdecode)

theorem decoded_chunks_length {chunks values : List Nat}
    (hdecode : decodeBalancedClauseChunks chunks = some values) :
    values.length ≤ (chunks.map natBitLength).sum := by
  induction chunks generalizing values with
  | nil => simp [decodeBalancedClauseChunks] at hdecode; subst values; simp
  | cons chunk rest ih =>
    simp only [decodeBalancedClauseChunks] at hdecode
    cases hc : decodeBalancedList chunk with
    | none => simp [hc] at hdecode
    | some head =>
      cases hr : decodeBalancedClauseChunks rest with
      | none => simp [hc, hr] at hdecode
      | some tail =>
        simp [hc, hr] at hdecode
        subst values
        simpa using Nat.add_le_add (decoded_balanced_length hc) (ih hr)

theorem decoded_nested_length {code : Nat} {values : List Nat}
    (hdecode : decodeNestedBalancedCNFPayload code = some values) :
    values.length ≤ natBitLength code := by
  unfold decodeNestedBalancedCNFPayload at hdecode
  cases hc : decodeBalancedList code with
  | none => simp [hc] at hdecode
  | some chunks =>
    simp only [hc] at hdecode
    exact (decoded_chunks_length hdecode).trans (decoded_balanced_atoms_bits hc)

private def FaithfulDecode (α : Type) [Encodable α] : Prop :=
  ∀ (code : Nat) (value : α), Encodable.decode code = some value → Encodable.encode value = code

private theorem faithful_bool : FaithfulDecode Bool := by
  intro code value hdecode
  cases code with
  | zero => simpa using (Option.some.inj hdecode).symm ▸ (rfl : Encodable.encode false = 0)
  | succ code =>
    cases code with
    | zero => simpa using (Option.some.inj hdecode).symm ▸ (rfl : Encodable.encode true = 1)
    | succ code => simp [Encodable.decode_ge_two (code + 2) (by omega)] at hdecode

private theorem faithful_nat : FaithfulDecode Nat := by
  intro code value hdecode
  simpa using (Option.some.inj hdecode).symm

private theorem faithful_prod {α β : Type} [Encodable α] [Encodable β]
    (ha : FaithfulDecode α) (hb : FaithfulDecode β) : FaithfulDecode (α × β) := by
  intro code value hdecode
  rw [Encodable.decode_prod_val] at hdecode
  cases hl : Encodable.decode (α := α) (Nat.unpair code).1 with
  | none => simp [hl] at hdecode
  | some left =>
    cases hr : Encodable.decode (α := β) (Nat.unpair code).2 with
    | none => simp [hl, hr] at hdecode
    | some right =>
      simp [hl, hr] at hdecode
      subst value
      simp only [Encodable.encode_prod_val, ha _ _ hl, hb _ _ hr, Nat.pair_unpair]

private theorem faithful_list {α : Type} [Encodable α]
    (ha : FaithfulDecode α) : FaithfulDecode (List α) := by
  intro code
  induction code using Nat.strong_induction_on with
  | h code ih =>
    intro value hdecode
    cases code with
    | zero => simp at hdecode; subst value; rfl
    | succ code =>
      rw [Encodable.decode_list_succ] at hdecode
      cases hl : Encodable.decode (α := α) (Nat.unpair code).1 with
      | none =>
        simp only [hl] at hdecode
        change (none : Option (List α)) = some value at hdecode
        contradiction
      | some head =>
        cases hr : Encodable.decode (α := List α) (Nat.unpair code).2 with
        | none =>
          simp only [hl, hr] at hdecode
          change (none : Option (List α)) = some value at hdecode
          contradiction
        | some tail =>
          simp [hl, hr] at hdecode
          subst value
          rw [Encodable.encode_list_cons, ha _ _ hl,
            ih _ (Nat.lt_succ_of_le (Nat.unpair_right_le code)) _ hr,
            Nat.pair_unpair]

theorem encode_of_decodeCNF {code : Nat} {formula : EncodedCNF}
    (hdecode : Encodable.decode code = some formula) : Encodable.encode formula = code :=
  faithful_list (faithful_list (faithful_prod faithful_bool faithful_nat)) code formula hdecode

private theorem member_code_le {α : Type} [Encodable α]
    {value : α} {values : List α} (hmem : value ∈ values) :
    Encodable.encode value ≤ Encodable.encode values := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
    rcases List.mem_cons.mp hmem with rfl | htail
    · exact (Nat.left_le_pair _ _).trans (Nat.le_succ _)
    · exact (ih htail).trans ((Nat.right_le_pair _ _).trans (Nat.le_succ _))

/-- Every binary field retained from a decoded marker fits in the input code. -/
theorem raw_literal_le_code {code : Nat} {clause : List (Bool × Nat)}
    {literal : Bool × Nat} (hc : clause ∈ decodeCNF code) (hl : literal ∈ clause) :
    literal.2 ≤ code := by
  unfold decodeCNF at hc
  cases hd : Encodable.decode (α := EncodedCNF) code with
  | none => simp [hd] at hc
  | some formula =>
    simp only [hd] at hc
    rw [← encode_of_decodeCNF hd]
    exact (Nat.right_le_pair (Encodable.encode literal.1) literal.2).trans
      ((member_code_le hl).trans (member_code_le hc))

private theorem bitLength_mono {a b : Nat} (h : a ≤ b) : natBitLength a ≤ natBitLength b :=
  Nat.add_le_add_right (Nat.log_mono_right h) 1

open private decodeClauseCodes from StatementSupport

theorem flatCompact_base_length {code : Nat} {request : CompactRequest}
    (hdecode : decodeFlatCompact code = some request) :
    request.base.length ≤ natBitLength code := by
  unfold decodeFlatCompact at hdecode
  split at hdecode
  next payload hmarker =>
    cases hp : decodeBalancedList payload with
    | none => simp [hp] at hdecode
    | some clauses =>
      simp only [hp, Option.map_some, Option.some.injEq] at hdecode
      subst request
      simp only [decodeClauseCodes, List.length_map]
      apply (decoded_balanced_length hp).trans
      apply bitLength_mono
      exact raw_literal_le_code (literal := (true, payload))
        (clause := [(true, payload)]) (by rw [hmarker]; simp) (by simp)
  next payload assignment count hmarker =>
    cases hp : decodeBalancedList payload with
    | none => simp [hp] at hdecode
    | some clauses =>
      simp only [hp, Option.map_some, Option.some.injEq] at hdecode
      subst request
      simp only [decodeClauseCodes, List.length_map]
      apply (decoded_balanced_length hp).trans
      apply bitLength_mono
      exact raw_literal_le_code (literal := (true, payload))
        (clause := [(true, payload)]) (by rw [hmarker]; simp) (by simp)
  next => simp at hdecode

theorem nestedCompact_base_length {code : Nat} {request : CompactRequest}
    (hdecode : decodeNestedCompact code = some request) :
    request.base.length ≤ natBitLength code := by
  unfold decodeNestedCompact at hdecode
  split at hdecode
  next payload hmarker =>
    cases hp : decodeNestedBalancedCNFPayload payload with
    | none => simp [hp] at hdecode
    | some clauses =>
      simp only [hp, Option.map_some, Option.some.injEq] at hdecode
      subst request
      simp only [decodeClauseCodes, List.length_map]
      apply (decoded_nested_length hp).trans
      apply bitLength_mono
      exact raw_literal_le_code (literal := (false, payload))
        (clause := [(false, payload)]) (by rw [hmarker]; simp) (by simp)
  next payload assignment count hmarker =>
    cases hp : decodeNestedBalancedCNFPayload payload with
    | none => simp [hp] at hdecode
    | some clauses =>
      simp only [hp, Option.map_some, Option.some.injEq] at hdecode
      subst request
      simp only [decodeClauseCodes, List.length_map]
      apply (decoded_nested_length hp).trans
      apply bitLength_mono
      exact raw_literal_le_code (literal := (false, payload))
        (clause := [(false, payload)]) (by rw [hmarker]; simp) (by simp)
  next => simp at hdecode

private theorem eraseDups_length_bound (values : List Nat) :
    values.eraseDups.length ≤ values.length := by
  have hloop : ∀ left right : List Nat,
      (List.eraseDupsBy.loop (fun a b => a == b) left right).length ≤
        left.length + right.length := by
    intro left
    induction left with
    | nil => intro right; simp [List.eraseDupsBy.loop]
    | cons head tail ih =>
      intro right
      rw [List.eraseDupsBy.loop.eq_def]
      cases hseen : right.any (fun b => head == b)
      · have ht := ih (head :: right)
        simpa only [hseen, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
      · simp only [hseen]
        exact (ih right).trans (by simp only [List.length_cons]; omega)
  simpa only [List.eraseDups, List.eraseDupsBy, List.length_nil, Nat.add_zero] using hloop values []

theorem compact_witness_length {request : CompactRequest} {witness : List Bool}
    (haccept : compactVerifier request witness = true) :
    witness.length ≤ 3 * request.base.length := by
  simp only [compactVerifier, Bool.and_eq_true, decide_eq_true_eq] at haccept
  have hflatten : ∀ (formula : EncodedCNF),
      formula.all (fun clause => clause.length = 3) = true →
      formula.flatten.length = 3 * formula.length := by
    intro formula
    induction formula with
    | nil => simp
    | cons clause tail ih =>
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq,
        List.flatten_cons, List.length_append, List.length_cons]
      rintro ⟨hc, ht⟩
      rw [hc, ih ht]
      omega
  rw [haccept.1.1]
  apply (eraseDups_length_bound _).trans
  simp only [List.length_map, hflatten request.base haccept.1.2]
  exact le_rfl

/-- Uniform witness bound for every accepting query, including raw/malformed
codes and both compact marker formats. Numeric prefix counts never occur. -/
theorem corrected_witness_length {code : Nat} {witness : List Bool}
    (haccept : correctedWitnessVerifier code witness = true) :
    witness.length ≤ 3 * natBitLength code := by
  unfold correctedWitnessVerifier at haccept
  split at haccept
  next hraw =>
    have hw := compact_witness_length haccept
    have hc : (decodeCNF code).length ≤ natBitLength code := by
      simp only [wellSizedCNFEncoding, Bool.and_eq_true, decide_eq_true_eq] at hraw
      exact hraw.1
    exact hw.trans (Nat.mul_le_mul_left 3 hc)
  next =>
    cases hf : decodeFlatCompact code with
    | some request =>
      simp only [hf] at haccept
      exact (compact_witness_length haccept).trans
        (Nat.mul_le_mul_left 3 (flatCompact_base_length hf))
    | none =>
      simp only [hf] at haccept
      cases hn : decodeNestedCompact code with
      | some request =>
        simp only [hn] at haccept
        exact (compact_witness_length haccept).trans
          (Nat.mul_le_mul_left 3 (nestedCompact_base_length hn))
      | none => simp [hn] at haccept

theorem correctedSat_bounded_witness (code : Nat) :
    correctedSat code = true ↔
      ∃ witness : List Bool, witness.length ≤ 3 * natBitLength code ∧
        correctedWitnessVerifier code witness = true := by
  rw [← correctedWitnessVerifier_iff]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, corrected_witness_length hw, hw⟩,
    fun ⟨w, _, hw⟩ => ⟨w, hw⟩⟩

end NearCubicWires.RepairSource.RecoveryOracle
