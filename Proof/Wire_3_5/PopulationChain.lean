import Proof.Wire_3_5.Population

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires Finset

theorem min_one_le_sqrt {t : ℝ} (ht : 0 ≤ t) : min 1 t ≤ Real.sqrt t := by
  rcases le_total t 1 with h | h
  · rw [min_eq_right h]; exact Real.le_sqrt_of_sq_le (by nlinarith)
  · rw [min_eq_left h]; exact Real.one_le_sqrt.mpr h

theorem star_bound_second {IL f fR b1 : ℝ} (hb : 0 < b1) (hIL : IL ≤ Real.sqrt f)
    (hfR0 : 0 ≤ fR) (hfR : fR ≤ f) :
    2 * IL / b1 * min 1 (fR / b1) ≤ 2 * f / (b1 * Real.sqrt b1) := by
  have hf0 : 0 ≤ f := hfR0.trans hfR
  have hm : min 1 (fR / b1) ≤ Real.sqrt f / Real.sqrt b1 := by
    calc min 1 (fR / b1) ≤ Real.sqrt (fR / b1) := min_one_le_sqrt (div_nonneg hfR0 hb.le)
      _ ≤ Real.sqrt (f / b1) := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hfR hb.le)
      _ = Real.sqrt f / Real.sqrt b1 := Real.sqrt_div' _ hb.le
  have hsb : 0 < Real.sqrt b1 := Real.sqrt_pos.mpr hb
  have hmin0 : 0 ≤ min 1 (fR / b1) := le_min zero_le_one (div_nonneg hfR0 hb.le)
  calc 2 * IL / b1 * min 1 (fR / b1) ≤ 2 * Real.sqrt f / b1 * (Real.sqrt f / Real.sqrt b1) := by
        apply mul_le_mul (div_le_div_of_nonneg_right (by linarith) hb.le) hm hmin0 (by positivity)
    _ = 2 * (Real.sqrt f * Real.sqrt f) / (b1 * Real.sqrt b1) := by field_simp
    _ = 2 * f / (b1 * Real.sqrt b1) := by rw [Real.mul_self_sqrt hf0]

theorem star_bound_third {f n r b1 : ℝ} (hf : 0 ≤ f) (hn : 0 < n) (hr : 0 < r) (hb : 0 < b1)
    (hnr : n + r < 2 * b1 * r) :
    2 * f / (b1 * Real.sqrt b1) ≤ 4 * Real.sqrt 2 * (r * Real.sqrt r) * f / (n * Real.sqrt n) := by
  have hb' : n / (2 * r) ≤ b1 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have hx : 0 < n / (2 * r) := by positivity
  have hsq : Real.sqrt (n / (2 * r)) ≤ Real.sqrt b1 := Real.sqrt_le_sqrt hb'
  have hkey : n / (2 * r) * Real.sqrt (n / (2 * r)) ≤ b1 * Real.sqrt b1 :=
    mul_le_mul hb' hsq (Real.sqrt_nonneg _) hb.le
  have hpos : 0 < n / (2 * r) * Real.sqrt (n / (2 * r)) := by positivity
  have hsplit : Real.sqrt (n / (2 * r)) = Real.sqrt n / (Real.sqrt 2 * Real.sqrt r) := by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by norm_num)]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  calc 2 * f / (b1 * Real.sqrt b1) ≤ 2 * f / (n / (2 * r) * Real.sqrt (n / (2 * r))) :=
        div_le_div_of_nonneg_left (by positivity) hpos hkey
    _ = 4 * Real.sqrt 2 * (r * Real.sqrt r) * f / (n * Real.sqrt n) := by
        rw [hsplit]; field_simp; ring

def StarPopulation : Prop :=
  ∀ (P : StarParams) (g : NormalizedThresholdGate P.n),
    ((∑ u : P.Errors, ∑ v : P.Errors,
        (univ.filter fun c : BitInput P.n =>
          mixedDifference g.eval c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) ≠ 0).card : ℕ) : ℝ) /
      (2 ^ P.n * (Fintype.card P.Errors : ℝ) ^ 2) ≤
    4 * Real.sqrt 2 * (P.r * Real.sqrt P.r) * (gateSupport g).card / (P.n * Real.sqrt P.n)

end NearCubicWires.WireExponent3_5.Shared
