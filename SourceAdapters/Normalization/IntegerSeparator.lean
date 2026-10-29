import SourceAdapters.Normalization.ActiveBasis
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Data.Real.Basic

/-!
# Small integer separators by Cramer's rule

The integer normalization in `lem:integer` clears the denominator of a basic
feasible solution. Each resulting coordinate is a determinant. The elementary
Leibniz determinant bound suffices for the stated, deliberately loose bound.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Normalization

open Matrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Cramer's vector of a consistent square system is its determinant times the
solution, even before assuming that the determinant is nonzero. -/
theorem cramer_eq_det_smul {R : Type*} [CommRing R] (M : Matrix κ κ R)
    (x b : κ → R) (hx : M *ᵥ x = b) : M.cramer b = M.det • x := by
  rw [← hx, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem intCast_cramer (M : Matrix κ κ ℤ) (b : κ → ℤ) (j : κ) :
    (M.cramer b j : ℝ) = (M.map (fun z => (z : ℝ))).cramer (fun i => (b i : ℝ)) j := by
  simp only [Matrix.cramer_apply, Int.cast_det, Matrix.map_updateCol, Function.comp_def]

theorem abs_cramer_one_le_factorial (M : Matrix κ κ ℤ)
    (hM : ∀ i j, |M i j| ≤ 1) (j : κ) :
    |M.cramer (fun _ => 1) j| ≤ (Nat.factorial (Fintype.card κ) : ℤ) := by
  rw [Matrix.cramer_apply]
  have h := Matrix.det_le (A := M.updateCol j (fun _ => 1))
    (abv := AbsoluteValue.abs) (x := (1 : ℤ)) (by
      intro i k
      by_cases hk : k = j
      · simp [hk]
      · simpa [Matrix.updateCol_apply, hk] using hM i k)
  simpa using h

/-- A pointed unit-margin system with integer coefficients in `[-1,1]` has a
strictly positive integer separator with every coordinate bounded by `d!`.
The finite system may have arbitrarily many inequalities. -/
theorem exists_integer_separator {ι : Type*} [Fintype ι] (A : Matrix ι κ ℤ)
    (hA : ∀ i j, |A i j| ≤ 1)
    (hsep : ∀ v : κ → ℝ, (∀ i, (fun j => (A i j : ℝ)) ⬝ᵥ v = 0) → v = 0)
    (hne : ∃ x : κ → ℝ, ∀ i, 1 ≤ (fun j => (A i j : ℝ)) ⬝ᵥ x) :
    ∃ z : κ → ℤ, (∀ i, 0 < A i ⬝ᵥ z) ∧
      ∀ j, |z j| ≤ (Nat.factorial (Fintype.card κ) : ℤ) := by
  classical
  let Ar : Matrix ι κ ℝ := A.map (fun z => (z : ℝ))
  obtain ⟨x, pick, hx, htight, hdet⟩ := exists_active_basis Ar (fun _ => 1) hsep hne
  let M : Matrix κ κ ℤ := fun i j => A (pick i) j
  let Mr : Matrix κ κ ℝ := M.map (fun z => (z : ℝ))
  have hMr : Mr *ᵥ x = (fun _ => 1) := funext htight
  have hd : (M.det : ℝ) ≠ 0 := by
    rw [Int.cast_det]
    exact hdet
  let z : κ → ℤ := M.cramer (fun _ => 1)
  have hz (j : κ) : (z j : ℝ) = (M.det : ℝ) * x j := by
    have h := congrFun (cramer_eq_det_smul Mr x (fun _ => 1) hMr) j
    have he : (z j : ℝ) = Mr.cramer (fun _ => 1) j := by
      simpa only [z, Mr, Int.cast_one] using intCast_cramer M (fun _ => 1) j
    rw [he, h]
    simp only [Pi.smul_apply, smul_eq_mul, Mr, Int.cast_det]
  have hb (j : κ) : |z j| ≤ (Nat.factorial (Fintype.card κ) : ℤ) :=
    abs_cramer_one_le_factorial M (fun i j => hA (pick i) j) j
  have hp (i : ι) : ((A i ⬝ᵥ z : ℤ) : ℝ) = (M.det : ℝ) * (Ar i ⬝ᵥ x) := by
    simp only [dotProduct, Int.cast_sum, Int.cast_mul, hz]
    simp only [Ar, Matrix.map_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · refine ⟨-z, ?_, fun j => by simpa using hb j⟩
    intro i
    have hxi : 0 < Ar i ⬝ᵥ x := lt_of_lt_of_le zero_lt_one (hx i)
    have hpi : ((A i ⬝ᵥ z : ℤ) : ℝ) < 0 := by rw [hp]; exact mul_neg_of_neg_of_pos hneg hxi
    have hi : A i ⬝ᵥ z < 0 := by exact_mod_cast hpi
    simpa only [dotProduct_neg] using neg_pos.mpr hi
  · refine ⟨z, ?_, hb⟩
    intro i
    have hxi : 0 < Ar i ⬝ᵥ x := lt_of_lt_of_le zero_lt_one (hx i)
    have hpi : 0 < ((A i ⬝ᵥ z : ℤ) : ℝ) := by rw [hp]; exact mul_pos hpos hxi
    exact_mod_cast hpi

end NearCubicGates.Adapters.Normalization
