import Proof.Wire_3_5.Shared.S0

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires

/-- The integer score `Σ w_i x_i` of a normalized gate (REL `NormalizedThresholdGate.eval`). -/
def gateScore {n : ℕ} (g : NormalizedThresholdGate n) (x : BitInput n) : ℤ :=
  ∑ i, g.weight i * if x i then 1 else 0

theorem eval_eq_decide {n : ℕ} (g : NormalizedThresholdGate n) (x : BitInput n) :
    g.eval x = decide (g.threshold ≤ gateScore g x) := rfl

theorem diagonal_sums {n : ℕ} (g : NormalizedThresholdGate n) (c u v : BitInput n)
    (hdisj : ∀ i, ¬(u i = true ∧ v i = true)) :
    gateScore g (xorInput (xorInput c u) v) + gateScore g c =
      gateScore g (xorInput c u) + gateScore g (xorInput c v) := by
  unfold gateScore
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := hdisj i
  simp only [xorInput]
  by_cases hc : c i = true <;> by_cases hu : u i = true <;> by_cases hv : v i = true <;> simp_all

theorem mixedDifference_range {n : ℕ} (g : NormalizedThresholdGate n) (c u v : BitInput n)
    (hdisj : ∀ i, ¬(u i = true ∧ v i = true)) :
    mixedDifference g.eval c u v ∈ ({-1, 0, 1} : Finset ℤ) := by
  have hd := diagonal_sums g c u v hdisj
  simp only [mixedDifference, eval_eq_decide, bitZ]
  by_cases h4 : g.threshold ≤ gateScore g (xorInput (xorInput c u) v) <;>
    by_cases h2 : g.threshold ≤ gateScore g (xorInput c u) <;>
    by_cases h3 : g.threshold ≤ gateScore g (xorInput c v) <;>
    by_cases h1 : g.threshold ≤ gateScore g c <;>
    simp [h1, h2, h3, h4] <;> omega

theorem errorVector_disjoint (P : StarParams) (u v : P.Errors) (i : Fin P.n) :
    ¬(P.errorVector P.leftBlock u i = true ∧ P.errorVector P.rightBlock v i = true) := by
  rintro ⟨hl, hr⟩
  simp only [StarParams.errorVector, decide_eq_true_eq] at hl hr
  obtain ⟨j, a, -, hj⟩ := hl
  obtain ⟨j', a', -, hj'⟩ := hr
  have hv := congrArg Fin.val (hj.trans hj'.symm)
  simp only [StarParams.blockCoord, StarParams.leftBlock, StarParams.rightBlock] at hv
  have hja := j.isLt; have hj'a := j'.isLt; have haa := a.isLt; have ha'a := a'.isLt
  have hr2 : P.r / 2 * 2 = P.r := Nat.div_mul_cancel (even_iff_two_dvd.mp P.r_even)
  -- j*b + a = (r/2 + j')*b + a' with a, a' < b forces j = r/2 + j' ≥ r/2 > j
  have hlt : j.val * P.b + a.val < (j.val + 1) * P.b := by nlinarith
  have hge : (P.r / 2 + j'.val) * P.b ≤ (P.r / 2 + j'.val) * P.b + a'.val := Nat.le_add_right _ _
  have hmono : (j.val + 1) * P.b ≤ (P.r / 2 + j'.val) * P.b :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- `star:range` at the star parametrization: every gate's mixed residual at every cell point is in
`{−1,0,1}`; this is the type the population bound (`star:population`) and `row:identity` consume. -/
theorem star_range (P : StarParams) (g : NormalizedThresholdGate P.n) (c : BitInput P.n) (u v : P.Errors) :
    mixedDifference g.eval c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) ∈
      ({-1, 0, 1} : Finset ℤ) :=
  mixedDifference_range g c _ _ (errorVector_disjoint P u v)

end NearCubicWires.WireExponent3_5.Shared
