import Mathlib

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.Shared
open Finset Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- `(−1)^{Tr x}`. -/
def psi (Tr : K →+ ZMod 2) (x : K) : ℤ := if Tr x = 0 then 1 else -1

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

omit [Fintype K] [DecidableEq K] in
theorem psi_add (Tr : K →+ ZMod 2) (x y : K) : psi Tr (x + y) = psi Tr x * psi Tr y := by
  unfold psi; rw [map_add]
  rcases zmod2_cases (Tr x) with hx | hx <;> rcases zmod2_cases (Tr y) with hy | hy <;> simp [hx, hy] <;> decide

/-- Orthogonality: a nontrivial additive character sums to zero. -/
theorem sum_psi_eq_zero (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0) : ∑ x, psi Tr x = 0 := by
  obtain ⟨b, hb⟩ := hTr
  have hb1 : psi Tr b = -1 := by unfold psi; simp [hb]
  have hshift : ∑ x, psi Tr x = ∑ x, psi Tr (x + b) :=
    (Equiv.sum_comp (Equiv.addRight b) (fun x => psi Tr x)).symm
  simp only [psi_add, hb1, mul_neg, mul_one, Finset.sum_neg_distrib] at hshift
  linarith

theorem sum_psi_mul (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0) (y : K) :
    ∑ u, psi Tr (u * y) = if y = 0 then (Fintype.card K : ℤ) else 0 := by
  split_ifs with hy
  · subst hy; simp [psi]
  · rw [← sum_psi_eq_zero Tr hTr]
    exact Equiv.sum_comp (Equiv.mulRight₀ y hy) (fun x => psi Tr x)

noncomputable def selectorPoly (J : Finset ℕ) : K[X] := ∑ i ∈ J, X ^ i

omit [Fintype K] [DecidableEq K] in
theorem selectorPoly_ne_zero (J : Finset ℕ) (hJ : J.Nonempty) : selectorPoly (K := K) J ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := hJ
  have hc := congrArg (fun p : K[X] => p.coeff i) h
  simp only [selectorPoly, finsetSum_coeff, coeff_X_pow, coeff_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simp [hi] at hc

omit [Fintype K] [DecidableEq K] in
theorem selectorPoly_natDegree_le (J : Finset ℕ) (M : ℕ) (hJM : ∀ i ∈ J, i ≤ M) :
    (selectorPoly (K := K) J).natDegree ≤ M := by
  unfold selectorPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi; exact (natDegree_X_pow_le i).trans (hJM i hi)

theorem card_zeros_le (J : Finset ℕ) (hJ : J.Nonempty) (M : ℕ) (hJM : ∀ i ∈ J, i ≤ M) :
    (univ.filter fun v : K => (selectorPoly J).eval v = 0).card ≤ M := by
  have hne := selectorPoly_ne_zero (K := K) J hJ
  calc (univ.filter fun v : K => (selectorPoly J).eval v = 0).card
      ≤ (selectorPoly (K := K) J).roots.toFinset.card := by
        apply Finset.card_le_card; intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        rw [Multiset.mem_toFinset, mem_roots hne]; exact hv
    _ ≤ Multiset.card (selectorPoly (K := K) J).roots := Multiset.toFinset_card_le _
    _ ≤ (selectorPoly (K := K) J).natDegree := card_roots' _
    _ ≤ M := selectorPoly_natDegree_le J M hJM

theorem parity_bias (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0) (J : Finset ℕ) (hJ : J.Nonempty) (M : ℕ)
    (hJM : ∀ i ∈ J, i ≤ M) :
    (∑ u, ∑ v, psi Tr (∑ i ∈ J, u * v ^ i)) =
        (Fintype.card K : ℤ) * (univ.filter fun v : K => (selectorPoly J).eval v = 0).card ∧
      (univ.filter fun v : K => (selectorPoly J).eval v = 0).card ≤ M := by
  refine ⟨?_, card_zeros_le J hJ M hJM⟩
  have hfac : ∀ u v : K, (∑ i ∈ J, u * v ^ i) = u * (selectorPoly J).eval v := by
    intro u v; simp [selectorPoly, eval_finsetSum, Finset.mul_sum]
  simp only [hfac]
  rw [Finset.sum_comm]
  simp only [sum_psi_mul Tr hTr]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem algebraTrace_nontrivial (F : Type) [Field F] [Finite F] [Algebra (ZMod (ringChar F)) F] :
    ∃ b, Algebra.trace (ZMod (ringChar F)) F b ≠ 0 := by
  obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate F (a := (1 : F)) one_ne_zero
  exact ⟨b, by simpa using hb⟩

end NearCubicWires.WireExponent3_5.Shared
