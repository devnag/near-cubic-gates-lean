import Proof.PCP.ProjectionDimensionWidth

namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionProducer
open RepairOrdinary RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bits_value (n : ℕ) : value n.bits=n := by
  have h (bits : List Bool) : value bits=CanonicalBinary.bitsValue bits := by
    induction bits with
    | nil => rfl
    | cons b bits ih => simp only [value,CanonicalBinary.bitsValue,ih]
  exact (h n.bits).trans (CanonicalBinary.bitsValue_natBits n)

theorem bits_length (n : ℕ) (hn : 0<n) : n.bits.length=natBitLength n := by
  rw [Nat.size_eq_bits_len]
  have hlo : Nat.log 2 n < n.size := Nat.lt_size.mpr (Nat.pow_log_le_self 2 (Nat.ne_of_gt hn))
  have hhi : n.size ≤ Nat.log 2 n+1 := Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide) n)
  dsimp [natBitLength]
  omega

theorem binary_bits (n : ℕ) (hn : 0<n) : SignedSortKey.binary (natBitLength n) n=n.bits := by
  have h := BoundedCounter.binary_of_value n.bits
  rw [bits_value,bits_length n hn] at h
  exact h

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionProducer
