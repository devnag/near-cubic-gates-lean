import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Uniform margins for a finite threshold classification

For `lem:integer`, ties are classified positively. A small positive shift
preserves every negative value in a finite family and makes all positive values
strict. A common positive dilation then gives margin one.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Normalization

variable {ι : Type*} [Fintype ι]

theorem exists_positive_shift (s : ι → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, s i < 0 → s i + δ < 0 := by
  classical
  let J := Finset.univ.filter fun i => s i < 0
  by_cases hJ : J.Nonempty
  · obtain ⟨j, hj, hmin⟩ := J.exists_min_image (fun i => -s i) hJ
    have hj' : s j < 0 := by simpa [J] using hj
    refine ⟨-s j / 2, div_pos (neg_pos.mpr hj') (by norm_num), ?_⟩
    intro i hi
    have hm := hmin i (by simpa [J] using hi)
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro i hi
    exact False.elim (hJ ⟨i, by simpa [J] using hi⟩)

theorem exists_unit_dilation (s : ι → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, 1 ≤ c * s i := by
  classical
  by_cases hι : Nonempty ι
  · letI := hι
    obtain ⟨j, _, hmin⟩ := Finset.univ.exists_min_image s Finset.univ_nonempty
    refine ⟨1 / s j, one_div_pos.mpr (hs j), ?_⟩
    intro i
    have hm := hmin i (Finset.mem_univ i)
    rw [div_mul_eq_mul_div, one_mul]
    exact (one_le_div (hs j)).mpr hm
  · refine ⟨1, by norm_num, ?_⟩
    intro i
    exact False.elim (hι ⟨i⟩)

/-- The signs of a finite family, with zero counted positively, admit a single
positive shift and dilation giving unit signed margins. -/
theorem exists_signed_unit_margin (s : ι → ℝ) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ i, 1 ≤ (if 0 ≤ s i then (1 : ℝ) else -1) * (c * (s i + δ)) := by
  classical
  obtain ⟨δ, hδ, hneg⟩ := exists_positive_shift s
  let a : ι → ℝ := fun i => (if 0 ≤ s i then 1 else -1) * (s i + δ)
  have ha (i : ι) : 0 < a i := by
    by_cases hi : 0 ≤ s i
    · simp only [a, if_pos hi, one_mul]
      linarith
    · simp only [a, if_neg hi, neg_one_mul]
      exact neg_pos.mpr (hneg i (lt_of_not_ge hi))
  obtain ⟨c, hc, hmargin⟩ := exists_unit_dilation a ha
  refine ⟨δ, c, hδ, hc, ?_⟩
  intro i
  simpa only [a, mul_left_comm] using hmargin i

end NearCubicGates.Adapters.Normalization
