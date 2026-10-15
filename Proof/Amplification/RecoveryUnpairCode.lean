import Proof.Amplification.RecoveryUnpair

/-! The shared scalar supplier at the literal EncodedNPVerifier input ABI.
The clock is polynomial in encoded bit length, including code zero. -/
namespace NearCubicWires.RepairOrdinary.RecoveryUnpair
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bits_value (code : Nat) : value code.bits = code := by
  have h (bits : List Bool) : value bits = CanonicalBinary.bitsValue bits := by
    induction bits with
    | nil => rfl
    | cons b bits ih => simp only [value, CanonicalBinary.bitsValue, ih]
  exact (h code.bits).trans (CanonicalBinary.bitsValue_natBits code)

theorem bits_length (code : Nat) : code.bits.length ≤ natBitLength code := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  simpa [natBitLength, Nat.succ_eq_add_one] using
    (Nat.lt_pow_succ_log_self (b := 2) (by omega) code)

def codeBudget (code : Nat) := 2048 * (natBitLength code + 1) ^ 2

theorem unpair_code_run (code : Nat) :
    ∃ r : ExecutionReceipt 16 (Fintype.card (RecoveryCalls.Control sizes) + 2),
      run machine (codeBudget code) (fun i => if i.val = 0 then frame code.bits else []) = some r ∧
      r.final.tapes 2 = frame (SignedSortKey.binary (3 + 2 * code.bits.length) (Nat.unpair code).1) ∧
      r.final.tapes 3 = frame (SignedSortKey.binary (3 + 2 * code.bits.length) (Nat.unpair code).2) ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps ≤ codeBudget code := by
  obtain ⟨r, hr, hl, hrout, hh, hs⟩ := unpair_run code.bits
  have ht : budget code.bits ≤ codeBudget code := by
    unfold budget codeBudget
    exact Nat.mul_le_mul_left 2048 (Nat.pow_le_pow_left (by have h := bits_length code; omega) 2)
  have hmore := run_moreFuel machine (budget code.bits) (codeBudget code - budget code.bits) _ r hr
  rw [Nat.add_sub_of_le ht] at hmore
  simp only [leftWord, rightWord, bits_value] at hl hrout
  exact ⟨r, hmore, hl, hrout, hh, hs.trans ht⟩

theorem code_component_width (code : Nat) :
    3 + 2 * code.bits.length ≤ 3 + 2 * natBitLength code := by
  have h := bits_length code
  omega

end NearCubicWires.RepairOrdinary.RecoveryUnpair
