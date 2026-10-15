import Proof.Wire_3_5.ListMachinePrintLoop

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.WireExponent3_5

theorem goods_length_le (L d : ℕ) : (Interp.goods L d).length ≤ (L + 1) ^ d := by
  have h := Interp.length_supports_le L d (Interp.monos L d) (Interp.monos_nodup L d)
    (fun S hS => ⟨(Interp.mem_monos hS).2.1, (Interp.mem_monos hS).2.2⟩)
  rwa [Interp.monos_eq_goods, List.length_map] at h

theorem recInnerCost_le (xs : List Bool) : recInnerCost xs ≤ 4 * xs.length ^ 2 + 30 * xs.length + 10 := by
  have hb : ∀ i ∈ List.range xs.length, bodyCostR i + 2 ≤ 4 * xs.length + 30 := by
    intro i hi
    have := List.mem_range.mp hi
    simp [bodyCostR, armCost]; omega
  have hs := List.sum_le_card_nsmul _ _ (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hb i hi)
  simp only [List.length_map, List.length_range, smul_eq_mul] at hs
  simp only [recInnerCost, loopCostR]
  nlinarith

theorem outerPassCost_le {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (d : ℕ) (hd : 1 ≤ d) (k : ℕ)
    (hk : k < (Interp.goods L d).length) :
    outerPassCost E d k ≤ 2 ^ d * (E.cost + 8 * L + 14) + 8 * L ^ 2 + 76 * L + 56 := by
  have hl := xsAt_length L d k
  have hp : 2 ^ Interp.pop (xsAt L d k) ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (xsAt_pop L d hd k hk)
  have hr := recInnerCost_le (xsAt L d k)
  rw [hl] at hr
  have hm : 2 ^ Interp.pop (xsAt L d k) * (innerPassCost E L + 2) ≤ 2 ^ d * (E.cost + 8 * L + 14) := by
    apply Nat.mul_le_mul hp
    simp [innerPassCost, innerRestCost]; omega
  simp only [outerPassCost, outerRestCost, hl]
  nlinarith

/-- **The printer's cost**: `(L+1)^d` supports, `2^d` evaluations each, `O(L²)` bookkeeping. -/
theorem printCost_le {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (d : ℕ) (hd : 1 ≤ d) :
    printCost E d ≤ (L + 1) ^ d * 2 ^ d * (E.cost + 100 * (L + 1) ^ 2) + 3 := by
  have hb : ∀ x ∈ (List.range (Interp.goods L d).length).map (fun k => outerPassCost E d k + 2),
      x ≤ 2 ^ d * (E.cost + 100 * (L + 1) ^ 2) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have h1 := outerPassCost_le E d hd k (List.mem_range.mp hk)
    have h2 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    nlinarith
  have hs := List.sum_le_card_nsmul _ _ hb
  simp only [List.length_map, List.length_range, smul_eq_mul] at hs
  have hg := goods_length_le L d
  unfold printCost
  calc _ ≤ (Interp.goods L d).length * (2 ^ d * (E.cost + 100 * (L + 1) ^ 2)) + 3 := by omega
    _ ≤ (L + 1) ^ d * (2 ^ d * (E.cost + 100 * (L + 1) ^ 2)) + 3 := by
      have := Nat.mul_le_mul_right (2 ^ d * (E.cost + 100 * (L + 1) ^ 2)) hg
      omega
    _ = (L + 1) ^ d * 2 ^ d * (E.cost + 100 * (L + 1) ^ 2) + 3 := by ring

end NearCubicWires.WireExponent3_5.ListMachine.Print
