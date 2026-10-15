import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The literal Beigel--Tarui modulus-amplifying polynomial

The polynomial is exactly the one in `lem:amp`. Its two divisibilities and
prime-power congruences are proved, not imported. The power-series inverse
used in the proof is a proved theorem from mathlib, not a new assumption.
-/

namespace NearCubicGates.PrimePowerLifting

open scoped BigOperators Polynomial PowerSeries

/-- The finite binomial series appearing in the manuscript. -/
noncomputable def binomialTrunc (e : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range e,
    Polynomial.C ((Nat.choose (e - 1 + j) j : ℕ) : ℤ) * Polynomial.X ^ j

/-- `1 - (1-t)^e * Σ_{j<e} choose(e-1+j,j) t^j`. -/
noncomputable def amplifier (e : ℕ) : ℤ[X] :=
  1 - (1 - Polynomial.X) ^ e * binomialTrunc e

theorem binomialTrunc_coeff (e j : ℕ) (hj : j < e) :
    (binomialTrunc e).coeff j = ((e - 1 + j).choose j : ℤ) := by
  classical
  simp only [binomialTrunc, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Ne.symm hij]
  · simp [Finset.mem_range.mpr hj]

theorem binomialTrunc_eq (e : ℕ) (he : 1 ≤ e) :
    binomialTrunc e =
      PowerSeries.trunc e (PowerSeries.invOneSubPow ℤ e).val := by
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ e (by omega),
    PowerSeries.trunc_apply, Nat.Ico_zero_eq_range]
  unfold binomialTrunc
  apply Finset.sum_congr rfl
  intro j _
  rw [PowerSeries.coeff_mk, Nat.choose_symm_add]
  simp only [Polynomial.C_mul_X_pow_eq_monomial]

theorem amplifier_X_pow_dvd (e : ℕ) (he : 1 ≤ e) :
    (Polynomial.X : ℤ[X]) ^ e ∣ amplifier e := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro n hn
  let A : ℤ⟦X⟧ := (1 - PowerSeries.X) ^ e
  let G : ℤ⟦X⟧ := (PowerSeries.invOneSubPow ℤ e).val
  have hAG : A * G = 1 := by
    dsimp only [A, G]
    rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow ℤ e]
    exact (PowerSeries.invOneSubPow ℤ e).inv_val
  have hc := congrArg (fun P : ℤ[X] => P.coeff n)
    (PowerSeries.trunc_mul_trunc (n := e) A G)
  simp only [PowerSeries.coeff_trunc, if_pos hn] at hc
  have hcoef : PowerSeries.coeff n (A * (binomialTrunc e : ℤ⟦X⟧)) =
      PowerSeries.coeff n (1 : ℤ⟦X⟧) := by
    rw [binomialTrunc_eq e he]
    exact hc.trans (congrArg (fun s : ℤ⟦X⟧ => PowerSeries.coeff n s) hAG)
  have hseries : (amplifier e : ℤ⟦X⟧) =
      1 - A * (binomialTrunc e : ℤ⟦X⟧) := by
    simp [amplifier, A]
  rw [← Polynomial.coeff_coe, hseries, map_sub, hcoef, sub_self]

theorem amplifier_one_sub_pow_dvd (e : ℕ) :
    (1 - Polynomial.X : ℤ[X]) ^ e ∣ 1 - amplifier e := by
  refine ⟨binomialTrunc e, ?_⟩
  simp [amplifier]

theorem binomialTrunc_natDegree_lt (e : ℕ) (he : 1 ≤ e) :
    (binomialTrunc e).natDegree < e := by
  rw [binomialTrunc_eq e he]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  exact PowerSeries.natDegree_trunc_lt _ d

/-- The quantitative degree bound needed by the tabulation guard. -/
theorem amplifier_natDegree_le (e : ℕ) (he : 1 ≤ e) :
    (amplifier e).natDegree ≤ 2 * e - 1 := by
  have hR := binomialTrunc_natDegree_lt e he
  have hbase : (1 - Polynomial.X : ℤ[X]).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp
  have hpow : ((1 - Polynomial.X : ℤ[X]) ^ e).natDegree ≤ e := by
    simpa using Polynomial.natDegree_pow_le_of_le e hbase
  have hprod := Polynomial.natDegree_mul_le_of_le hpow (Nat.le_pred_of_lt hR)
  have hsub := Polynomial.natDegree_sub_le (1 : ℤ[X])
    ((1 - Polynomial.X) ^ e * binomialTrunc e)
  unfold amplifier
  apply hsub.trans
  simp only [Polynomial.natDegree_one, zero_le, max_eq_right]
  have hprod' : ((1 - Polynomial.X : ℤ[X]) ^ e * binomialTrunc e).natDegree ≤ e + (e - 1) := by
    simpa only [Nat.pred_eq_sub_one] using hprod
  omega

/-- The degree is exactly `2e-1`, including the endpoint `e=1`. -/
theorem amplifier_natDegree_eq (e : ℕ) (he : 1 ≤ e) :
    (amplifier e).natDegree = 2 * e - 1 := by
  have hcoeff : (binomialTrunc e).coeff (e - 1) ≠ 0 := by
    rw [binomialTrunc_coeff e (e - 1) (by omega)]
    exact_mod_cast (Nat.choose_pos (by omega : e - 1 ≤ e - 1 + (e - 1))).ne'
  have hR : (binomialTrunc e).natDegree = e - 1 := by
    have hlt := binomialTrunc_natDegree_lt e he
    have hle := Polynomial.le_natDegree_of_ne_zero hcoeff
    omega
  have hR0 : binomialTrunc e ≠ 0 := by
    intro h
    rw [h, Polynomial.coeff_zero] at hcoeff
    exact hcoeff rfl
  have hbase : (1 - Polynomial.X : ℤ[X]).natDegree = 1 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · apply (Polynomial.natDegree_sub_le _ _).trans
      simp
    · norm_num [Polynomial.coeff_one]
  have hbase0 : (1 - Polynomial.X : ℤ[X]) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hbase
    omega
  have hproduct : ((1 - Polynomial.X : ℤ[X]) ^ e * binomialTrunc e).natDegree =
      e + (e - 1) := by
    rw [Polynomial.natDegree_mul (pow_ne_zero e hbase0) hR0,
      Polynomial.natDegree_pow, hbase, hR, Nat.mul_one]
  unfold amplifier
  rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt
    (by rw [Polynomial.natDegree_one, hproduct]; omega), hproduct]
  omega

/-- The zero branch is sound for arbitrary integer arguments, including negatives. -/
theorem amplifier_mod_zero (e : ℕ) (he : 1 ≤ e) (p t : ℤ) (ht : p ∣ t) :
    p ^ e ∣ (amplifier e).eval t := by
  obtain ⟨P, hP⟩ := amplifier_X_pow_dvd e he
  have hv := congrArg (fun Q : ℤ[X] => Q.eval t) hP
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hv
  rw [hv]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd ht e) _

/-- The one branch is sound for arbitrary integer arguments. -/
theorem amplifier_mod_one (e : ℕ) (p t : ℤ) (ht : p ∣ t - 1) :
    p ^ e ∣ (amplifier e).eval t - 1 := by
  obtain ⟨P, hP⟩ := amplifier_one_sub_pow_dvd e
  have hv := congrArg (fun Q : ℤ[X] => Q.eval t) hP
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X] at hv
  have hd : p ^ e ∣ (1 - t) ^ e :=
    pow_dvd_pow_of_dvd (by simpa only [neg_sub] using dvd_neg.mpr ht) e
  have hres : p ^ e ∣ 1 - (amplifier e).eval t := by
    rw [hv]
    exact dvd_mul_of_dvd_left hd _
  simpa only [neg_sub] using dvd_neg.mpr hres

theorem amplifier_modEq_zero (e : ℕ) (he : 1 ≤ e) (p t : ℤ)
    (ht : t ≡ 0 [ZMOD p]) : (amplifier e).eval t ≡ 0 [ZMOD p ^ e] :=
  Int.modEq_zero_iff_dvd.mpr (amplifier_mod_zero e he p t (Int.modEq_zero_iff_dvd.mp ht))

theorem amplifier_modEq_one (e : ℕ) (p t : ℤ) (ht : t ≡ 1 [ZMOD p]) :
    (amplifier e).eval t ≡ 1 [ZMOD p ^ e] := by
  apply Int.modEq_iff_dvd.mpr
  have h : p ∣ t - 1 := by simpa only [neg_sub] using dvd_neg.mpr ht.dvd
  simpa only [neg_sub] using dvd_neg.mpr (amplifier_mod_one e p t h)

end NearCubicGates.PrimePowerLifting
