import SourceAdapters.ACSP.Affine
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The degree of every composition (the paragraph after `def:acsp`)

"If `deg A < 2^{m_H}`, then `B_A(X) = P(X, A(N_1(X)), …, A(N_{c_N}(X)))` has degree at most `d_B`: substituting
`A ∘ N_ν`, of degree at most `2^{m_H} − 1`, raises no monomial above its weight. … The weighted bound `4 d_B ≤ 2^f`
implies its degree condition (3) and, as just shown, bounds every composition `B_A`; we use this stronger sufficient
condition."

This is a one-way implication: from the weighted bound of `def:acsp` (`Instance.HasDegreeBound`) to the bound on
every composition that the soundness argument of Step 2 of the proof of `thm:short-pcp-ours` uses (Case 4, "`B'` of
degree at most `d_B`"). The converse fails (over `F_16` with `m_H = 2`, two identity neighbors and
`P = Y_1² + Y_2²`, every composition vanishes while `P` has weighted degree `6 > 16/4`).
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ACSP.Affine

open Polynomial

/-- Substituting univariate polynomials of degrees `≤ w j` into `P` gives degree at most the `w`-weighted total
degree of `P`. -/
theorem natDegree_aeval_le_weighted {σ R : Type} [Fintype σ] [CommSemiring R] (w : σ → ℕ) (g : σ → R[X])
    (hg : ∀ j, (g j).natDegree ≤ w j) (P : MvPolynomial σ R) :
    (MvPolynomial.aeval g P).natDegree ≤ MvPolynomial.weightedTotalDegree w P := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have hsum : ∑ i, (g i ^ d i).natDegree ≤ ∑ i, d i * w i :=
    Finset.sum_le_sum fun i _ => (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ (hg i))
  refine hsum.trans ?_
  have hw : ∑ i, d i * w i = Finsupp.weight w d := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [smul_eq_mul]
  rw [hw]
  exact MvPolynomial.le_weightedTotalDegree w hd

namespace Instance

/-- **The bound on every composition** (the paragraph after `def:acsp`): "If `deg A < 2^{m_H}`, then `B_A(X)` has
degree at most `d_B`." -/
theorem composed_natDegree_le (c : Instance) {dB : ℕ} (hB : c.HasDegreeBound dB) (A : c.Fld[X])
    (hA : A.degree < (2 ^ c.mH : ℕ)) : (c.composed A).natDegree ≤ dB := by
  have hAd : A.natDegree ≤ 2 ^ c.mH - 1 := by
    by_cases h0 : A = 0
    · rw [h0, Polynomial.natDegree_zero]; exact Nat.zero_le _
    · have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hA
      omega
  refine (natDegree_aeval_le_weighted c.weight _ ?_ c.consPoly).trans ?_
  · intro j
    refine Fin.cases ?_ (fun ν => ?_) j
    · simp only [Fin.cons_zero, weight, Fin.val_zero, if_true]
      exact Polynomial.natDegree_X_le
    · simp only [Fin.cons_succ, weight, Fin.val_succ, Nat.add_one_ne_zero, if_false]
      refine (Polynomial.natDegree_comp_le).trans ?_
      have hq : (Polynomial.C (c.slope ν.val) * X + Polynomial.C (c.shift ν.val) : c.Fld[X]).natDegree ≤ 1 :=
        Polynomial.natDegree_linear_le
      calc A.natDegree * (Polynomial.C (c.slope ν.val) * X + Polynomial.C (c.shift ν.val)).natDegree
          ≤ A.natDegree * 1 := Nat.mul_le_mul_left _ hq
        _ ≤ 2 ^ c.mH - 1 := by omega
  · exact Finset.sup_le fun s hs => hB s hs

/-- **The form Step 2 uses** (proof of `thm:short-pcp-ours`, "Base soundness", Case 4: "`B_A` … of degree at most
`d_B ≤ |F|/4`"): from `def:acsp`, a single `d_B` with `4 d_B ≤ 2^f` bounding every composition. -/
theorem degB_of_isValid (c : Instance) (h : c.IsValid) :
    ∃ dB : ℕ, dB * 4 ≤ 2 ^ c.f ∧ ∀ A : c.Fld[X], A.degree < ((2 ^ c.mH : ℕ) : WithBot ℕ) →
      (c.composed A).natDegree ≤ dB := by
  obtain ⟨-, -, -, -, dB, hB, h4⟩ := h
  exact ⟨dB, by omega, fun A hA => composed_natDegree_le c hB A hA⟩

end Instance

end NearCubicGates.Adapters.ACSP.Affine
