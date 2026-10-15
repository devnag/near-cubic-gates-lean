import Proof.CaseAnalysis.WitnessAliases

/-! Move the fixed rational bit policy ahead of canonical reduction. The
early test reads only the original integer/natural fields. Exact re-encoding
proves that no accepted canonical coefficient is lost on any raw code. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalGuard
open CanonicalBinary CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (raw : ℕ) : Option (ℤ × ℕ) :=
  match decodeTaggedList raw with
  | some [a, b] => do
      let numerator ← decodeInt a
      let denominator ← decodeNat b
      pure (numerator, denominator)
  | _ => none

def Within (bits : ℕ) (a : ℤ) (b : ℕ) : Prop :=
  natBitLength a.natAbs ≤ bits ∧ natBitLength b ≤ bits
instance (bits : ℕ) (a : ℤ) (b : ℕ) : Decidable (Within bits a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

def early (bits raw : ℕ) : Bool :=
  match fields raw with
  | some (a, b) => decide (0 < b ∧ Within bits a b)
  | none => false

def boundedDecode (bits raw : ℕ) : Option ℚ :=
  (decodeCanonicalRational raw).bind fun c =>
    if Within bits c.num c.den then some c else none

def guardedDecode (bits raw : ℕ) : Option ℚ :=
  if early bits raw then boundedDecode bits raw else none

theorem fields_encode (c : ℚ) : fields (encodeCanonicalRational c) = some (c.num, c.den) := by
  simp [fields, encodeCanonicalRational]

theorem early_encode (bits : ℕ) (c : ℚ) :
    early bits (encodeCanonicalRational c) = decide (Within bits c.num c.den) := by
  simp [early, fields_encode, c.pos]

theorem early_of_boundedDecode {bits raw : ℕ} {c : ℚ}
    (h : boundedDecode bits raw = some c) : early bits raw = true := by
  unfold boundedDecode at h
  cases hd : decodeCanonicalRational raw with
  | none => simp [hd] at h
  | some decoded =>
    simp only [hd, Option.bind_some] at h
    split at h
    · rename_i hb
      cases Option.some.inj h
      rw [← encodeCanonicalRational_of_decode hd, early_encode]
      exact decide_eq_true hb
    · simp at h

theorem guardedDecode_eq (bits raw : ℕ) : guardedDecode bits raw = boundedDecode bits raw := by
  unfold guardedDecode
  cases h : boundedDecode bits raw with
  | none => simp
  | some c => rw [early_of_boundedDecode h]; rfl

theorem encoded_guardedDecode (bits : ℕ) (c : ℚ) (h : Within bits c.num c.den) :
    guardedDecode bits (encodeCanonicalRational c) = some c := by
  rw [guardedDecode_eq]
  simp [boundedDecode, decodeCanonicalRational_encode, h]

theorem bit_cap_numeric (C a : ℕ) (hC : 0 < C)
    (h : natBitLength a ≤ natBitLength C) : a < 2 * C := by
  have hp : 2 ^ natBitLength C ≤ 2 * C := by
    unfold natBitLength
    rw [pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hC.ne')
  exact (Nat.lt_pow_succ_log_self Nat.one_lt_two a).trans_le
    ((Nat.pow_le_pow_right (by decide : 0 < 2) h).trans hp)

theorem early_fields_numeric {C raw : ℕ} {a : ℤ} {b : ℕ} (hC : 0 < C)
    (hf : fields raw = some (a, b)) (h : early (natBitLength C) raw = true) :
    0 < b ∧ a.natAbs < 2 * C ∧ b < 2 * C := by
  rw [early, hf, decide_eq_true_eq] at h
  exact ⟨h.1, bit_cap_numeric C a.natAbs hC h.2.1, bit_cap_numeric C b hC h.2.2⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalGuard
