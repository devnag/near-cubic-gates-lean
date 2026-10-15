import Mathlib

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared

theorem choose_two_pow_mod_two (x h : ℕ) :
    Nat.choose x (2 ^ h) % 2 = if x.testBit h then 1 else 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction h generalizing x with
  | zero =>
    simp only [pow_zero, Nat.choose_one_right, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> simp [hx]
  | succ h ih =>
    have hl := @Choose.choose_modEq_choose_mod_mul_choose_div_nat x (2 ^ (h + 1)) 2 _
    have h1 : 2 ^ (h + 1) % 2 = 0 := by rw [pow_succ]; simp
    have h2 : 2 ^ (h + 1) / 2 = 2 ^ h := by rw [pow_succ]; simp
    rw [h1, h2, Nat.choose_zero_right, one_mul] at hl
    rw [hl, ih (x / 2), Nat.testBit_div_two]

end NearCubicWires.WireExponent3_5.Shared
