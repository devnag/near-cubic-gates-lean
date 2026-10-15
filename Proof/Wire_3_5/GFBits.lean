import Proof.Wire_3_5.GF2Refs

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.GF
open Polynomial

theorem toPoly_shiftLeft (a i : ℕ) : toPoly (a <<< i) = X ^ i * toPoly a := by
  rw [Nat.shiftLeft_eq, mul_comm, toPoly_two_pow_mul]

/-- Adding the next low bit. -/
theorem toPoly_mod_two_pow_succ (a j : ℕ) :
    toPoly (a % 2 ^ (j + 1)) = toPoly (a % 2 ^ j) + if a.testBit j then X ^ j else 0 := by
  ext i
  rw [coeff_add, coeff_toPoly, coeff_toPoly, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : i < j + 1 := by omega
    have h2 : i ≠ j := by omega
    split_ifs <;> simp [h, h1, h2, coeff_X_pow]
  · split_ifs with hb <;> simp [hb, bitF]
  · have h1 : ¬ i < j + 1 := by omega
    have h2 : ¬ i < j := by omega
    have h3 : i ≠ j := by omega
    split_ifs <;> simp [h1, h2, h3, coeff_X_pow, bitF]

end NearCubicWires.WireExponent3_5.GF
