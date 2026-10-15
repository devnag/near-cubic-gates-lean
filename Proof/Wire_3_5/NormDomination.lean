import Mathlib

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open Matrix Finset

variable {N : ℕ}

theorem dot_cs (x y : Fin N → ℝ) : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  simp only [dotProduct]
  have := Finset.sum_mul_sq_le_sq_mul_sq univ x y
  simpa [sq] using this

theorem dot_self_nonneg' (x : Fin N → ℝ) : 0 ≤ x ⬝ᵥ x := by
  simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- `(Av)·(Av) = v·(AᵀA v)`. -/
theorem mulVec_dot_mulVec (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ ((Aᵀ * A) *ᵥ v) := by
  symm
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v Aᵀ (A *ᵥ v), Matrix.vecMul_transpose]

/-- One Cauchy–Schwarz step for a symmetric matrix: `(v·Sv)² ≤ (v·v)(v·S²v)`. -/
theorem quad_sq_le (S : Matrix (Fin N) (Fin N) ℝ) (hS : Sᵀ = S) (v : Fin N → ℝ) :
    (v ⬝ᵥ (S *ᵥ v)) ^ 2 ≤ (v ⬝ᵥ v) * (v ⬝ᵥ ((S * S) *ᵥ v)) := by
  have h := dot_cs v (S *ᵥ v)
  have h2 : (S *ᵥ v) ⬝ᵥ (S *ᵥ v) = v ⬝ᵥ ((S * S) *ᵥ v) := by
    rw [mulVec_dot_mulVec, hS]
  rwa [h2] at h

/-- Frobenius step: `v·(SᵀS v) ≤ tr(SᵀS)·(v·v)`. -/
theorem quad_le_trace (S : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) :
    v ⬝ᵥ ((Sᵀ * S) *ᵥ v) ≤ Matrix.trace (Sᵀ * S) * (v ⬝ᵥ v) := by
  rw [← mulVec_dot_mulVec]
  have hrow : ∀ i, ((S *ᵥ v) i) ^ 2 ≤ (∑ j, S i j ^ 2) * (v ⬝ᵥ v) := by
    intro i
    have := dot_cs (fun j => S i j) v
    simpa [Matrix.mulVec, dotProduct, sq] using this
  have htr : Matrix.trace (Sᵀ * S) = ∑ i, ∑ j, S i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
    rw [Finset.sum_comm]
  calc (S *ᵥ v) ⬝ᵥ (S *ᵥ v) = ∑ i, ((S *ᵥ v) i) ^ 2 := by simp [dotProduct, sq]
    _ ≤ ∑ i, (∑ j, S i j ^ 2) * (v ⬝ᵥ v) := Finset.sum_le_sum fun i _ => hrow i
    _ = Matrix.trace (Sᵀ * S) * (v ⬝ᵥ v) := by rw [htr, Finset.sum_mul]

/-- The domination used by the direct sampler (h = 4). -/
theorem bilinear_pow8_le (E : Matrix (Fin N) (Fin N) ℝ) (a b : Fin N → ℝ) :
    (a ⬝ᵥ (E *ᵥ b)) ^ 8 ≤ (a ⬝ᵥ a) ^ 4 * (b ⬝ᵥ b) ^ 4 * Matrix.trace ((Eᵀ * E) ^ 4) := by
  set M := Eᵀ * E with hMdef
  have hM : Mᵀ = M := by rw [hMdef, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hM2 : (M * M)ᵀ = M * M := by rw [Matrix.transpose_mul, hM]
  set s := a ⬝ᵥ a; set t := b ⬝ᵥ b
  set q1 := b ⬝ᵥ (M *ᵥ b); set q2 := b ⬝ᵥ ((M * M) *ᵥ b); set q4 := b ⬝ᵥ (((M * M) * (M * M)) *ᵥ b)
  have hs : 0 ≤ s := dot_self_nonneg' a
  have ht : 0 ≤ t := dot_self_nonneg' b
  have hq1 : 0 ≤ q1 := by
    have := dot_self_nonneg' (E *ᵥ b); rwa [mulVec_dot_mulVec] at this
  have hq2 : 0 ≤ q2 := by
    have := dot_self_nonneg' (M *ᵥ b); rwa [mulVec_dot_mulVec, hM] at this
  -- the four inequalities
  have i1 : (a ⬝ᵥ (E *ᵥ b)) ^ 2 ≤ s * q1 := by
    have := dot_cs a (E *ᵥ b); rwa [mulVec_dot_mulVec] at this
  have i2 : q1 ^ 2 ≤ t * q2 := quad_sq_le M hM b
  have i3 : q2 ^ 2 ≤ t * q4 := quad_sq_le (M * M) hM2 b
  have i4 : q4 ≤ Matrix.trace ((M * M) * (M * M)) * t := by
    have := quad_le_trace (M * M) b; rwa [hM2] at this
  have htr : Matrix.trace (M ^ 4) = Matrix.trace ((M * M) * (M * M)) := by
    congr 1; rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  rw [htr]
  set T := Matrix.trace ((M * M) * (M * M))
  have hx2 : 0 ≤ (a ⬝ᵥ (E *ᵥ b)) ^ 2 := sq_nonneg _
  calc (a ⬝ᵥ (E *ᵥ b)) ^ 8 = ((a ⬝ᵥ (E *ᵥ b)) ^ 2) ^ 4 := by ring
    _ ≤ (s * q1) ^ 4 := pow_le_pow_left₀ hx2 i1 4
    _ = s ^ 4 * (q1 ^ 2) ^ 2 := by ring
    _ ≤ s ^ 4 * (t * q2) ^ 2 := by
        apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) i2 2) (pow_nonneg hs 4)
    _ = s ^ 4 * t ^ 2 * q2 ^ 2 := by ring
    _ ≤ s ^ 4 * t ^ 2 * (t * q4) := mul_le_mul_of_nonneg_left i3 (by positivity)
    _ ≤ s ^ 4 * t ^ 2 * (t * (T * t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left i4 ht) (by positivity)
    _ = s ^ 4 * t ^ 4 * T := by ring

end NearCubicWires.WireExponent3_5.Shared
