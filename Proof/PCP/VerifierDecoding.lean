import Proof.PCP.VerifierDecodingLookup

/-! Guarded canonical flat verifier decoding. Unary dimensions are read from
the bounded word itself. Dimension and exact-size guards precede table
enumeration; final canonical re-encoding rejects every noncanonical tag,
padding field or out-of-range state without expanding an unchecked count. -/
namespace NearCubicWires.RepairSource.VerifierDecoding
open LocalBitMultitape VerifierEncoding RepairOrdinary.RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def expectedLength (t s : ℕ) : ℕ :=
  t+s+2+natBitLength s+2*s+s*2^t*entryWidth t s

def CountsFit (c t s : ℕ) : Prop :=
  2 ≤ t ∧ 0 < s ∧ 2^t ≤ c ∧ s*2^t ≤ c ∧ expectedLength t s = c
instance (c t s : ℕ) : Decidable (CountsFit c t s) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def fromParts (t s : ℕ) (ht : 2 ≤ t) (start : Fin s)
    (flagWord tableWord : List Bool) : OrdinaryVerifier where
  tapeCount := t
  stateCount := s
  twoTapes := ht
  machine :=
    { descriptionBits := 0
      start := start
      halted := fun state => flagAt flagWord state.val false
      rule := ruleAt tableWord }
  accepting := fun state => flagAt flagWord state.val true

def canonical (v : OrdinaryVerifier) : OrdinaryVerifier :=
  { v with machine := { v.machine with descriptionBits := 0 } }

theorem fromParts_encoded (v : OrdinaryVerifier) :
    fromParts v.tapeCount v.stateCount v.twoTapes v.machine.start (flags v) (table v) = canonical v := by
  have hh : (fun state : Fin v.stateCount => flagAt (flags v) state.val false) = v.machine.halted := by
    funext state
    exact (literal_lookup v state (fun _ => false)).1
  have ha : (fun state : Fin v.stateCount => flagAt (flags v) state.val true) = v.accepting := by
    funext state
    exact (literal_lookup v state (fun _ => false)).2.1
  have hr : (ruleAt (table v) : Fin v.stateCount → (Fin v.tapeCount → Bool) → _) = v.machine.rule := by
    funext state scanned
    exact ruleAt_table v state scanned
  unfold fromParts canonical
  rw [hh, ha, hr]

@[simp] theorem code_canonical (v : OrdinaryVerifier) : code (canonical v) = code v := rfl

theorem countsFit_code (v : OrdinaryVerifier) : CountsFit (code v).length v.tapeCount v.stateCount := by
  have hs : 0 < v.stateCount := Nat.zero_lt_of_lt v.machine.start.isLt
  have he : expectedLength v.tapeCount v.stateCount = (code v).length := (code_length v).symm
  have hw : 1 ≤ entryWidth v.tapeCount v.stateCount := by unfold entryWidth; omega
  have hentries : v.stateCount*2^v.tapeCount ≤ (code v).length := by
    have hm := Nat.le_mul_of_pos_right (v.stateCount*2^v.tapeCount) hw
    rw [code_length]
    dsimp [entryWidth] at hm
    omega
  have hp : 2^v.tapeCount ≤ v.stateCount*2^v.tapeCount := Nat.le_mul_of_pos_left _ hs
  exact ⟨v.twoTapes, hs, hp.trans hentries, hentries, he⟩

def decodeHeader (word : List Bool) : Option OrdinaryVerifier :=
  match unary word with
  | none => none
  | some (t, tail) =>
    match unary tail with
    | none => none
    | some (s, fields) =>
      if h : CountsFit word.length t s then
        let width := natBitLength s
        let start := value (fields.take width)
        if hi : start < s then
          some (fromParts t s h.1 ⟨start, hi⟩
            (slice fields width (2*s)) (fields.drop (width+2*s)))
        else none
      else none

/-- The first guard belongs before any dimension arithmetic. Canonical
validation then scans only a table already bounded by the literal code. -/
def decode (inputLength : ℕ) (word : List Bool) : Option OrdinaryVerifier :=
  if word.length ≤ Nat.log 2 inputLength then
    (decodeHeader word).bind fun v => if code v = word then some v else none
  else none

theorem decodeHeader_code (v : OrdinaryVerifier) : decodeHeader (code v) = some (canonical v) := by
  let fields := fixedBits (natBitLength v.stateCount) v.machine.start.val ++ flags v ++ table v
  have hp : unary (code v) = some (v.tapeCount, List.replicate v.stateCount true ++ false :: fields) := by
    rw [code_split]
    exact unary_encoded _ _
  have hs : unary (List.replicate v.stateCount true ++ false :: fields) = some (v.stateCount, fields) :=
    unary_encoded _ _
  have hstart : value (fields.take (natBitLength v.stateCount)) = v.machine.start.val := by
    have ht := List.take_left (l₁ := fixedBits (natBitLength v.stateCount) v.machine.start.val)
      (l₂ := flags v ++ table v)
    simp only [fixedBits_length] at ht
    have he : fields.take (natBitLength v.stateCount) = fixedBits (natBitLength v.stateCount) v.machine.start.val := by
      simpa only [fields, List.append_assoc] using ht
    rw [he]
    exact fixedBits_value _ _ (v.machine.start.isLt.trans_le
      (Nat.lt_pow_succ_log_self (by decide) v.stateCount).le)
  have hi : value (fields.take (natBitLength v.stateCount)) < v.stateCount := by rw [hstart]; exact v.machine.start.isLt
  have hf : slice fields (natBitLength v.stateCount) (2*v.stateCount) = flags v := by
    have hd := List.drop_left (l₁ := fixedBits (natBitLength v.stateCount) v.machine.start.val)
      (l₂ := flags v ++ table v)
    simp only [fixedBits_length] at hd
    have ht := List.take_left (l₁ := flags v) (l₂ := table v)
    simp only [flags_length] at ht
    simpa only [slice, fields, List.append_assoc, hd] using ht
  have ht : fields.drop (natBitLength v.stateCount+2*v.stateCount) = table v := by
    have hd := List.drop_left (l₁ := fixedBits (natBitLength v.stateCount) v.machine.start.val ++ flags v)
      (l₂ := table v)
    simpa only [fields, List.length_append, fixedBits_length, flags_length] using hd
  have hfin : (⟨value (fields.take (natBitLength v.stateCount)), hi⟩ : Fin v.stateCount) = v.machine.start := Fin.ext hstart
  simp only [decodeHeader, hp, hs, dif_pos (countsFit_code v), dif_pos hi]
  rw [hfin, hf, ht, fromParts_encoded]

theorem decode_code (v : OrdinaryVerifier) (N : ℕ) (hc : (code v).length ≤ Nat.log 2 N) :
    decode N (code v) = some (canonical v) := by
  simp only [decode, hc, ↓reduceIte, decodeHeader_code, Option.bind_some, code_canonical]

theorem decode_code_length {N : ℕ} {word : List Bool} {v : OrdinaryVerifier}
    (h : decode N word = some v) : word.length ≤ Nat.log 2 N ∧ code v = word := by
  unfold decode at h
  split at h
  · next hlength =>
    cases hd : decodeHeader word with
    | none => simp [hd] at h
    | some found =>
      simp only [hd, Option.bind_some] at h
      split at h
      · next he => cases h; exact ⟨hlength, he⟩
      · contradiction
  · contradiction

/-- Every post-validation enumeration is bounded by the supplied code; these
are the actual dimensions of the returned verifier, not claimed input tags. -/
theorem decode_table_bound {N : ℕ} {word : List Bool} {v : OrdinaryVerifier}
    (h : decode N word = some v) :
    v.tapeCount ≤ word.length ∧ v.stateCount ≤ word.length ∧
      2^v.tapeCount ≤ word.length ∧ v.stateCount*2^v.tapeCount ≤ word.length ∧
      (table v).length ≤ word.length := by
  obtain ⟨_, he⟩ := decode_code_length h
  have hf := countsFit_code v
  rw [he] at hf
  have hl := code_length v
  rw [he] at hl
  rw [table_length]
  dsimp [CountsFit] at hf
  refine ⟨?_, ?_, hf.2.2.1, hf.2.2.2.1, ?_⟩
  · omega
  · omega
  · unfold entryWidth
    omega

end NearCubicWires.RepairSource.VerifierDecoding
