import Mathlib

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open scoped Matrix.Norms.L2Operator
open Matrix

theorem bilinear_le_opNorm {N : ℕ} (E : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) :
    ‖∑ u, a u * (E *ᵥ b) u‖ ≤ ‖E‖ * N := by
  set w : EuclideanSpace ℂ (Fin N) := (EuclideanSpace.equiv (Fin N) ℂ).symm b
  have hw : ∀ i, w i = b i := fun i => rfl
  have hwN : ‖w‖ ≤ Real.sqrt N := by
    rw [← Real.sqrt_sq (norm_nonneg w), EuclideanSpace.norm_sq_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          rw [hw]; nlinarith [hb i, norm_nonneg (b i)]
      _ = N := by simp
  have hop := Matrix.l2_opNorm_mulVec E w
  set y : EuclideanSpace ℂ (Fin N) := (EuclideanSpace.equiv (Fin N) ℂ).symm (E *ᵥ w.ofLp)
  have hy : ∀ u, y u = (E *ᵥ b) u := fun u => rfl
  have hcs : (∑ u, ‖y u‖) ^ 2 ≤ N * ‖y‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun u => ‖y u‖)
    simpa [EuclideanSpace.norm_sq_eq] using this
  have hsum : ∑ u, ‖y u‖ ≤ Real.sqrt N * ‖y‖ := by
    rw [← Real.sqrt_sq (Finset.sum_nonneg fun u _ => norm_nonneg (y u)),
      ← Real.sqrt_sq (norm_nonneg y), ← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt hcs
  calc ‖∑ u, a u * (E *ᵥ b) u‖ ≤ ∑ u, ‖a u * (E *ᵥ b) u‖ := norm_sum_le _ _
    _ ≤ ∑ u, ‖y u‖ := Finset.sum_le_sum fun u _ => by
        rw [norm_mul, ← hy]; nlinarith [ha u, norm_nonneg (y u), norm_nonneg (a u)]
    _ ≤ Real.sqrt N * ‖y‖ := hsum
    _ ≤ Real.sqrt N * (‖E‖ * ‖w‖) := mul_le_mul_of_nonneg_left hop (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt N * (‖E‖ * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwN (norm_nonneg _)) (Real.sqrt_nonneg _)
    _ = ‖E‖ * N := by rw [mul_comm, mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]

def sampleError {N Q : ℕ} (D : Fin N → Fin N → ℂ) (S : Fin Q → Fin N × Fin N) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun u v => (Q : ℂ) * D u v - (N : ℂ) ^ 2 * ∑ j, if S j = (u, v) then D u v else 0

theorem sample_estimate_error {N Q : ℕ} (hN : 0 < N) (hQ : 0 < Q) (D : Fin N → Fin N → ℂ)
    (S : Fin Q → Fin N × Fin N) (a b : Fin N → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) :
    ‖(∑ u, a u * (Matrix.of D *ᵥ b) u) / (N : ℂ) ^ 2 -
        (∑ j, a (S j).1 * b (S j).2 * D (S j).1 (S j).2) / (Q : ℂ)‖ ≤
      ‖sampleError D S‖ / (Q * N) := by
  have hkey : (∑ u, a u * (sampleError D S *ᵥ b) u) =
      (Q : ℂ) * ∑ u, a u * (Matrix.of D *ᵥ b) u - (N : ℂ) ^ 2 * ∑ j, a (S j).1 * b (S j).2 * D (S j).1 (S j).2 := by
    have hmv : ∀ (M : Matrix (Fin N) (Fin N) ℂ) (u : Fin N), (M *ᵥ b) u = ∑ v, M u v * b v :=
      fun M u => rfl
    simp only [hmv, sampleError, Matrix.of_apply, Finset.mul_sum, Finset.sum_sub_distrib, sub_mul, mul_sub]
    congr 1
    · apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _; ring
    · have h1 : ∀ u v, a u * ((∑ j, (N : ℂ) ^ 2 * if S j = (u, v) then D u v else 0) * b v) =
          ∑ j, if S j = (u, v) then (N : ℂ) ^ 2 * (a u * b v * D u v) else 0 := by
        intro u v; rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; split_ifs <;> ring
      simp only [h1]
      rw [← Fintype.sum_prod_type' (f := fun u v =>
        ∑ j, if S j = (u, v) then (N : ℂ) ^ 2 * (a u * b v * D u v) else 0)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_ite_eq Finset.univ (S j) (fun p => (N : ℂ) ^ 2 * (a p.1 * b p.2 * D p.1 p.2))]
      simp
  have hb' := bilinear_le_opNorm (sampleError D S) a b ha hb
  rw [hkey] at hb'
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hQc : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hQN : (0 : ℝ) < Q * N := by positivity
  rw [le_div_iff₀ hQN]
  have : (∑ u, a u * (Matrix.of D *ᵥ b) u) / (N : ℂ) ^ 2 - (∑ j, a (S j).1 * b (S j).2 * D (S j).1 (S j).2) / (Q : ℂ) =
      ((Q : ℂ) * ∑ u, a u * (Matrix.of D *ᵥ b) u - (N : ℂ) ^ 2 * ∑ j, a (S j).1 * b (S j).2 * D (S j).1 (S j).2) /
        ((Q : ℂ) * (N : ℂ) ^ 2) := by field_simp
  rw [this, norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
  have hN2 : (0 : ℝ) < (Q : ℝ) * (N : ℝ) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hN2]
  nlinarith [hb', norm_nonneg (sampleError D S)]

end NearCubicWires.WireExponent3_5.Shared
