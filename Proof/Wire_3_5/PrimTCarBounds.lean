import Proof.Wire_3_5.PrimTCarFold

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.CarBounds
open NearCubicWires NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.CarFold

/-- The capacity polynomial's coefficient. -/
abbrev cC2 : ℕ := 1000000000000000000000000000000000000000000000000

/-- The per-atom native word bound. -/
def gateB (W : ℕ) : ℕ := 4000000000000000000001002 * (W + 2) ^ 26 + 2 * W + 2

/-- **The bank capacity dominates the atom loop's needs.** -/
theorem capacity_ok (W c T' : ℕ)
    (hc : c * (2 * W + 1) ≤ max (2 * W + 1) (16 * 1000000000000000000 * (W + 1) ^ 24 + 1))
    (hT' : T' ≤ c * gateB W) :
    c ≤ cC2 * (W + 2) ^ 50 ∧ c * (2 * W + 1) ≤ cC2 * (W + 2) ^ 50 ∧ 4 + T' ≤ cC2 * (W + 2) ^ 50 ∧
      foldCw W c T' + 1 ≤ cC2 * (W + 2) ^ 50 := by
  set P := (W + 2) ^ 24 with hP
  set Q := (W + 2) ^ 26 with hQ
  have hPQ : (W + 2) ^ 50 = P * Q := by rw [hP, hQ, ← pow_add]
  have hP1 : (W + 1) ^ 24 ≤ P := Nat.pow_le_pow_left (by omega) _
  have hPW : W + 2 ≤ P := Nat.le_self_pow (by norm_num) _
  have hQW : W + 2 ≤ Q := Nat.le_self_pow (by norm_num) _
  have hP0 : 1 ≤ P := by omega
  have hQ0 : 1 ≤ Q := by omega
  -- the atom count
  have hcP : c ≤ 17000000000000000000 * P := by
    rcases le_max_iff.mp (show c * (2 * W + 1) ≤ max _ _ from hc) |>.elim (fun h => Or.inl h) (fun h => Or.inr h)
      with h | h
    · have : c ≤ 1 := by
        by_contra hc1
        have : 2 * (2 * W + 1) ≤ c * (2 * W + 1) := Nat.mul_le_mul_right _ (by omega)
        omega
      omega
    · have : c ≤ c * (2 * W + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  have hS : c * (2 * W + 1) ≤ 17000000000000000000 * P := by
    rcases le_max_iff.mp hc with h | h <;> omega
  -- products with `Q`
  have hcQ : c * Q ≤ 17000000000000000000 * (P * Q) := by
    have := Nat.mul_le_mul_right Q hcP; rw [Nat.mul_assoc] at this; exact this
  have hcW : c * W ≤ c * Q := Nat.mul_le_mul_left _ (by omega)
  have hgate : T' ≤ 4000000000000000000001002 * (c * Q) + 2 * (c * Q) + 2 * c := by
    have e : c * gateB W = 4000000000000000000001002 * (c * Q) + 2 * (c * W) + 2 * c := by
      unfold gateB; rw [← hQ]; ring
    omega
  have hR : P ≤ P * Q := Nat.le_mul_of_pos_right _ (by omega)
  have hRQ : Q ≤ P * Q := Nat.le_mul_of_pos_left _ (by omega)
  rw [hPQ, show cC2 = 1000000000000000000000000000000000000000000000000 from rfl]
  refine ⟨by omega, by omega, by omega, ?_⟩
  have e : foldCw W c T' = 1 + 1 + ((2 * (5 * (c * W) + 8 * c + 14 * W + 10) + 2) + 1 +
      (4000000000000000000001002 * Q + 1 + (2 * (18 * T' + 20) + 2))) := by
    unfold foldCw; rw [← hQ]; ring
  rw [e]
  omega

end NearCubicWires.WireExponent3_5.PrimT.CarBounds
