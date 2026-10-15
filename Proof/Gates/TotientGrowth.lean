import Proof.Gates.TomographyDirections
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Elementary quantitative totient growth. A coarse positive constant is
    sufficient for the headline's unspecified budget constant. The proof uses
    finite Möbius inversion and an elementary inverse-square bound; it does
    not add a summatory-totient literature assumption. -/

set_option autoImplicit false

namespace NearCubicGates.TotientGrowth

open scoped BigOperators
open ArithmeticFunction ArithmeticFunction.Moebius TomographyDirections

theorem square_sum (q : ℕ) :
    (∑ i ∈ Finset.Icc 1 q, (i : ℝ) ^ 2) =
      (q : ℝ) ^ 3 / 3 + (q : ℝ) ^ 2 / 2 + (q : ℝ) / 6 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hs : Finset.Icc 1 (q + 1) = insert (q + 1) (Finset.Icc 1 q) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hs, Finset.sum_insert (by simp), ih]
    push_cast
    ring

theorem divisor_hyperbola_sum (q : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 q, ∑ p ∈ m.divisorsAntidiagonal, f p.1 p.2) =
      ∑ d ∈ Finset.Icc 1 q, ∑ e ∈ Finset.Icc 1 (q / d), f d e := by
  classical
  rw [Finset.sum_sigma' (Finset.Icc 1 q) (fun m => m.divisorsAntidiagonal)
    (fun _ p => f p.1 p.2),
    Finset.sum_sigma' (Finset.Icc 1 q) (fun d => Finset.Icc 1 (q / d)) f]
  apply Finset.sum_bij (fun p _ => ⟨p.2.1, p.2.2⟩)
  · rintro ⟨m, d, e⟩ hp
    obtain ⟨hm, hde⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hprod, hm0⟩ := Nat.mem_divisorsAntidiagonal.mp hde
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hm2 := (Finset.mem_Icc.mp hm).2
    have hd : 0 < d := Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hde)
    have he : 0 < e := Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hde)
    change d * e = m at hprod
    simp only [Finset.mem_sigma, Finset.mem_Icc]
    have hdle : d ≤ q := by nlinarith
    have hele : e ≤ q / d := (Nat.le_div_iff_mul_le hd).mpr (by nlinarith)
    exact ⟨⟨hd, hdle⟩, he, hele⟩
  · rintro ⟨m, d, e⟩ hp ⟨m', d', e'⟩ hp' heq
    have h := congrArg Sigma.fst heq
    have h' := congrArg (fun p : Σ _ : ℕ, ℕ => p.2) heq
    dsimp at h h'
    subst d'
    subst e'
    have hm := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hp).2).1
    have hm' := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hp').2).1
    change d * e = m at hm
    change d * e = m' at hm'
    have hmm : m = m' := hm.symm.trans hm'
    exact congrArg (fun v : ℕ => (⟨v, (d, e)⟩ : Σ _ : ℕ, ℕ × ℕ)) hmm
  · rintro ⟨d, e⟩ hp
    obtain ⟨hd, he⟩ := Finset.mem_sigma.mp hp
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    have he0 : 0 < e := (Finset.mem_Icc.mp he).1
    have hm : d * e ≤ q := by
      have h := (Nat.le_div_iff_mul_le hd0).mp (Finset.mem_Icc.mp he).2
      nlinarith
    refine ⟨⟨d * e, d, e⟩, ?_, rfl⟩
    apply Finset.mem_sigma.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd0 he0, hm⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.ne_of_gt (Nat.mul_pos hd0 he0)⟩⟩
  · intro p _
    rfl

theorem weighted_totient_moebius (m : ℕ) (hm : 0 < m) :
    ((m * Nat.totient m : ℕ) : ℝ) =
      ∑ p ∈ m.divisorsAntidiagonal, (μ p.1 : ℝ) * p.1 * (p.2 : ℝ) ^ 2 := by
  have hsum : ∀ n : ℕ, 0 < n → ∑ i ∈ n.divisors, (Nat.totient i : ℝ) = (n : ℝ) := by
    intro n _
    exact_mod_cast Nat.sum_totient n
  have h := sum_eq_iff_sum_mul_moebius_eq.mp hsum m hm
  rw [Nat.cast_mul, ← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have he' : (m : ℝ) = (p.1 : ℝ) * p.2 := by exact_mod_cast he.symm
  rw [he']
  ring

theorem degreeSum_moebius (q : ℕ) :
    (degreeSum q : ℝ) =
      ∑ d ∈ Finset.Icc 1 q, (μ d : ℝ) * d *
        (∑ e ∈ Finset.Icc 1 (q / d), (e : ℝ) ^ 2) := by
  unfold degreeSum
  push_cast
  have h : (∑ m ∈ Finset.Icc 1 q, ((m : ℝ) * Nat.totient m)) =
      ∑ m ∈ Finset.Icc 1 q,
        ∑ p ∈ m.divisorsAntidiagonal, (μ p.1 : ℝ) * p.1 * (p.2 : ℝ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro m hm
    simpa using weighted_totient_moebius m (Finset.mem_Icc.mp hm).1
  rw [h, divisor_hyperbola_sum q (fun d e => (μ d : ℝ) * d * (e : ℝ) ^ 2)]
  simp_rw [Finset.mul_sum]

theorem inverse_square_tail_bound (q : ℕ) :
    (∑ d ∈ Finset.Icc 2 q, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 3 / 4 := by
  have hstrong : ∀ q : ℕ, 2 ≤ q →
      (∑ d ∈ Finset.Icc 2 q, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 3 / 4 - 1 / q := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base => norm_num
    | succ q hq ih =>
      have hs : Finset.Icc 2 (q + 1) = insert (q + 1) (Finset.Icc 2 q) := by
        ext d
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hs, Finset.sum_insert (by simp)]
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hq1 : (0 : ℝ) < q + 1 := by linarith
      have hterm : (1 : ℝ) / ((q : ℝ) + 1) ^ 2 ≤ 1 / q - 1 / ((q : ℝ) + 1) := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((q : ℝ) + 1) ^ 2)).mpr
        field_simp
        nlinarith
      push_cast
      linarith
  by_cases hq : 2 ≤ q
  · have h := hstrong q hq
    have h0 : (0 : ℝ) ≤ 1 / q := by positivity
    linarith
  · have hset : Finset.Icc 2 q = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [hset, Finset.sum_empty]
    norm_num

theorem moebius_truncated_positive (q : ℕ) (hq : 1 ≤ q) :
    (1 : ℝ) / 4 ≤ ∑ d ∈ Finset.Icc 1 q, (μ d : ℝ) / (d : ℝ) ^ 2 := by
  have hs : Finset.Icc 1 q = insert 1 (Finset.Icc 2 q) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hs, Finset.sum_insert (by simp)]
  have hl : -(∑ d ∈ Finset.Icc 2 q, (1 : ℝ) / (d : ℝ) ^ 2) ≤
      ∑ d ∈ Finset.Icc 2 q, (μ d : ℝ) / (d : ℝ) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro d _
    have hm : -(1 : ℝ) ≤ μ d := by
      have h := abs_moebius_le_one (n := d)
      have h' := (abs_le.mp h).1
      exact_mod_cast h'
    simpa only [neg_div] using div_le_div_of_nonneg_right hm (sq_nonneg (d : ℝ))
  have ht := inverse_square_tail_bound q
  norm_num at *
  linarith

theorem square_sum_division_error (q d : ℕ) (hd : 1 ≤ d) (hdq : d ≤ q) :
    |(∑ e ∈ Finset.Icc 1 (q / d), (e : ℝ) ^ 2) - ((q : ℝ) / d) ^ 3 / 3| ≤
      ((q : ℝ) / d) ^ 2 := by
  let y : ℝ := (q : ℝ) / d
  let z : ℝ := (q / d : ℕ)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hy1 : 1 ≤ y := by
    dsimp [y]
    apply (le_div_iff₀ hd0).mpr
    rw [one_mul]
    exact_mod_cast hdq
  have hz0 : 0 ≤ z := by positivity
  have hzy : z ≤ y := by
    dsimp [y, z]
    apply (le_div_iff₀ hd0).mpr
    exact_mod_cast Nat.div_mul_le_self q d
  have hyz : y - 1 ≤ z := by
    have hq : q < (q / d + 1) * d := by
      have h := Nat.mod_add_div q d
      have hmod := Nat.mod_lt q (by omega : 0 < d)
      nlinarith
    have hr : (q : ℝ) < ((q / d : ℕ) + 1) * (d : ℝ) := by exact_mod_cast hq
    have hr' : y < z + 1 := by
      dsimp [y, z]
      exact (div_lt_iff₀ hd0).mpr hr
    linarith
  have hz3 : (y - 1) ^ 3 ≤ z ^ 3 := pow_le_pow_left₀ (by linarith) hyz 3
  have hz3' : z ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hz0 hzy 3
  have hz2 : z ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hz0 hzy 2
  rw [square_sum, abs_le]
  change -y ^ 2 ≤ z ^ 3 / 3 + z ^ 2 / 2 + z / 6 - y ^ 3 / 3 ∧
    z ^ 3 / 3 + z ^ 2 / 2 + z / 6 - y ^ 3 / 3 ≤ y ^ 2
  constructor <;> nlinarith [sq_nonneg z, sq_nonneg (y - 1)]

theorem weighted_square_lower (q d : ℕ) (hd : 1 ≤ d) (hdq : d ≤ q) :
    (q : ℝ) ^ 3 / 3 * ((μ d : ℝ) / (d : ℝ) ^ 2) - (q : ℝ) ^ 2 / d ≤
      (μ d : ℝ) * d * (∑ e ∈ Finset.Icc 1 (q / d), (e : ℝ) ^ 2) := by
  let E : ℝ := (∑ e ∈ Finset.Icc 1 (q / d), (e : ℝ) ^ 2) - ((q : ℝ) / d) ^ 3 / 3
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hm : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
  have herr : |E| ≤ ((q : ℝ) / d) ^ 2 := square_sum_division_error q d hd hdq
  have hmul : |(μ d : ℝ) * E| ≤ ((q : ℝ) / d) ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ 1 * ((q : ℝ) / d) ^ 2 := mul_le_mul hm herr (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hlow := (abs_le.mp hmul).1
  have hdE := mul_le_mul_of_nonneg_left hlow (le_of_lt hd0)
  have hid : (μ d : ℝ) * d * (∑ e ∈ Finset.Icc 1 (q / d), (e : ℝ) ^ 2) =
      (q : ℝ) ^ 3 / 3 * ((μ d : ℝ) / (d : ℝ) ^ 2) + (d : ℝ) * ((μ d : ℝ) * E) := by
    dsimp [E]
    field_simp
    ring
  have hid2 : (d : ℝ) * (-((q : ℝ) / d) ^ 2) = -(q : ℝ) ^ 2 / d := by
    field_simp
  rw [hid]
  rw [hid2] at hdE
  rw [neg_div] at hdE
  linarith

/-- A fully finite cubic lower bound, with the explicit harmonic error term.
    The weaker constant avoids needing the Euler product for zeta(2). -/
theorem degreeSum_cubic_lower (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) ^ 3 / 12 - (q : ℝ) ^ 2 * (1 + Real.log q) ≤ (degreeSum q : ℝ) := by
  have hs : (q : ℝ) ^ 3 / 3 *
      (∑ d ∈ Finset.Icc 1 q, (μ d : ℝ) / (d : ℝ) ^ 2) -
      (q : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 q, (1 : ℝ) / d) ≤ (degreeSum q : ℝ) := by
    rw [degreeSum_moebius, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro d hd
    simpa only [mul_one_div] using weighted_square_lower q d
      (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
  have hp := mul_le_mul_of_nonneg_left (moebius_truncated_positive q hq)
    (by positivity : 0 ≤ (q : ℝ) ^ 3 / 3)
  have hh : (∑ d ∈ Finset.Icc 1 q, (1 : ℝ) / d) ≤ 1 + Real.log q := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      one_div] using harmonic_le_one_add_log q
  have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg (q : ℝ))
  nlinarith

theorem degreeSum_cubic_upper (q : ℕ) :
    (degreeSum q : ℝ) ≤ (q : ℝ) ^ 3 / 3 + (q : ℝ) ^ 2 / 2 + (q : ℝ) / 6 := by
  rw [← square_sum]
  unfold degreeSum
  push_cast
  apply Finset.sum_le_sum
  intro m _
  have hm : (Nat.totient m : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  nlinarith

theorem degreeSum_eventually_cubic_lower :
    ∃ onset : ℕ, ∀ q : ℕ, onset ≤ q → (q : ℝ) ^ 3 / 24 ≤ (degreeSum q : ℝ) := by
  have hl := Real.isLittleO_log_id_atTop.def (by norm_num : (0 : ℝ) < 1 / 48)
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp hl
  refine ⟨max 48 ⌈b⌉₊, ?_⟩
  intro q hq
  have hq1 : 1 ≤ q := by omega
  have hq48 : (48 : ℝ) ≤ q := by exact_mod_cast (show 48 ≤ q by omega)
  have hbq : b ≤ (q : ℝ) := by
    exact (Nat.le_ceil b).trans (by exact_mod_cast (show ⌈b⌉₊ ≤ q by omega))
  have hh := hb (q : ℝ) hbq
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ q)] at hh
  have hlog := (le_abs_self (Real.log q)).trans hh
  have hsum : 1 + Real.log q ≤ (q : ℝ) / 24 := by linarith
  have hg := degreeSum_cubic_lower q hq1
  have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg (q : ℝ))
  nlinarith

end NearCubicGates.TotientGrowth
