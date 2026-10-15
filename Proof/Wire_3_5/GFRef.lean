import Proof.Wire_3_5.GFBits

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.GF
open Polynomial NearCubicWires.WireExponent3_5.GF2

/-- One step of the shift-and-xor multiplier (the body of `fmulShift`). -/
def mulStep (p ℓ y : ℕ) (st : ℕ × ℕ) (i : ℕ) : ℕ × ℕ :=
  (if y.testBit i then st.1 ^^^ st.2 else st.1, lfsr p ℓ st.2)

theorem mulStep_fst (p ℓ y : ℕ) (st : ℕ × ℕ) (i : ℕ) :
    (mulStep p ℓ y st i).1 = if y.testBit i then st.1 ^^^ st.2 else st.1 := rfl

theorem mulStep_snd (p ℓ y : ℕ) (st : ℕ × ℕ) (i : ℕ) : (mulStep p ℓ y st i).2 = lfsr p ℓ st.2 := rfl

theorem fmulShift_eq (p ℓ x y : ℕ) : fmulShift p ℓ x y = ((List.range ℓ).foldl (mulStep p ℓ y) (0, x)).1 := rfl

theorem mulStep_fold (p ℓ x y : ℕ) (hp : ModulusOk p ℓ) (hx : x < 2 ^ ℓ) (n : ℕ) :
    ((List.range n).foldl (mulStep p ℓ y) (0, x)).1 < 2 ^ ℓ ∧
      ((List.range n).foldl (mulStep p ℓ y) (0, x)).2 < 2 ^ ℓ ∧
      rep p ((List.range n).foldl (mulStep p ℓ y) (0, x)).1 =
        rep p x * AdjoinRoot.mk (toPoly p) (toPoly (y % 2 ^ n)) ∧
      rep p ((List.range n).foldl (mulStep p ℓ y) (0, x)).2 = rep p x * xRoot p ^ n := by
  induction n with
  | zero => simp [hx, Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨h1, h2, h3, h4⟩ := ih
    obtain ⟨h5, h6⟩ := lfsr_spec p ℓ _ hp h2
    rw [mulStep_fst, mulStep_snd]
    refine ⟨?_, h5, ?_, ?_⟩
    · split_ifs
      · exact Nat.xor_lt_two_pow h1 h2
      · exact h1
    · rw [toPoly_mod_two_pow_succ, map_add]
      split_ifs with hb
      · rw [rep_xor, h3, h4, mul_add, map_pow, AdjoinRoot.mk_X]
      · rw [h3, map_zero, add_zero]
    · rw [h6, h4, pow_succ]; ring

/-- **The shift-and-xor multiplier is the field product.** -/
theorem fmulShift_spec (p ℓ x y : ℕ) (hp : ModulusOk p ℓ) (hx : x < 2 ^ ℓ) (hy : y < 2 ^ ℓ) :
    fmulShift p ℓ x y < 2 ^ ℓ ∧ rep p (fmulShift p ℓ x y) = rep p x * rep p y := by
  obtain ⟨h1, _, h3, _⟩ := mulStep_fold p ℓ x y hp hx ℓ
  rw [fmulShift_eq]
  refine ⟨h1, ?_⟩
  rw [h3, Nat.mod_eq_of_lt hy]
  rfl

end NearCubicWires.WireExponent3_5.GF
