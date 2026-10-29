import Proof.Gates.Certificates
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp

/-! The square-root acceleration is the high-risk part of the public rate
    chain: multiplying the rate by a fixed constant would cost too many
    stages. These definitions follow the literal floor rule of `lem:chain`. -/

set_option autoImplicit false

namespace NearCubicGates.NestedRateChain

noncomputable def factor (x : ℝ) : ℕ := ⌊1 / (4 * Real.sqrt x)⌋₊
noncomputable def next (x : ℝ) : ℝ := (factor x : ℝ) * x

theorem step_bounds (x : ℝ) (hx : 0 < x) (hsmall : x < 1 / 256) :
    4 ≤ factor x ∧ Real.sqrt x / 8 ≤ next x ∧
      0 < next x ∧ next x < 1 / 64 ∧ next x ^ 2 ≥ x / 64 := by
  let s := Real.sqrt x
  have hs : 0 < s := Real.sqrt_pos.mpr hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hs16 : s < 1 / 16 := by nlinarith
  have hd : 0 < 4 * s := by positivity
  have hi : 4 < 1 / (4 * s) := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  have ha : 4 ≤ factor x := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ 1 / (4 * s))).mpr
    exact hi.le
  have hf : (factor x : ℝ) ≤ 1 / (4 * s) := Nat.floor_le (by positivity)
  have hlt : 1 / (4 * s) < (factor x : ℝ) + 1 := Nat.lt_floor_add_one _
  have ha4 : (4 : ℝ) ≤ factor x := by exact_mod_cast ha
  have hup : (factor x : ℝ) * s ≤ 1 / 4 := by
    have h := (le_div_iff₀ hd).mp hf
    nlinarith
  have hlo : 1 / 8 ≤ (factor x : ℝ) * s := by
    have h := (div_lt_iff₀ hd).mp hlt
    nlinarith
  have hnlo : s / 8 ≤ next x := by
    dsimp [next]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) hs.le]
  have hnpos : 0 < next x := lt_of_lt_of_le (by positivity) hnlo
  have hnup : next x < 1 / 64 := by
    dsimp [next]
    nlinarith [mul_nonneg (sub_nonneg.mpr hup) hs.le]
  refine ⟨ha, hnlo, hnpos, hnup, ?_⟩
  nlinarith [sq_nonneg (next x - s / 8)]

theorem step_growth (x : ℝ) (hx : 0 < x) (hsmall : x < 1 / 256) :
    x ≤ next x := by
  have ha : (4 : ℝ) ≤ factor x := by exact_mod_cast (step_bounds x hx hsmall).1
  dsimp [next]
  nlinarith

noncomputable def rateRatio (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | j + 1 => if rateRatio x₀ j < 1 / 256 then next (rateRatio x₀ j) else rateRatio x₀ j

theorem ratio_positive (x₀ : ℝ) (hx : 0 < x₀) : ∀ j, 0 < rateRatio x₀ j := by
  intro j
  induction j with
  | zero => exact hx
  | succ j ih =>
      simp only [rateRatio]
      split_ifs with h
      · exact (step_bounds _ ih h).2.2.1
      · exact ih

theorem ratio_step_mono (x₀ : ℝ) (hx : 0 < x₀) (j : ℕ) :
    rateRatio x₀ j ≤ rateRatio x₀ (j + 1) := by
  simp only [rateRatio]
  split_ifs with h
  · exact step_growth _ (ratio_positive x₀ hx j) h
  · exact le_refl _

theorem ratio_mono (x₀ : ℝ) (hx : 0 < x₀) : Monotone (rateRatio x₀) :=
  monotone_nat_of_le_succ (ratio_step_mono x₀ hx)

theorem ratio_upper (x₀ : ℝ) (hx : 0 < x₀) (hupper : x₀ ≤ 1 / 32) :
    ∀ j, rateRatio x₀ j ≤ 1 / 32 := by
  intro j
  induction j with
  | zero => exact hupper
  | succ j ih =>
      simp only [rateRatio]
      split_ifs with h
      · have h' := (step_bounds _ (ratio_positive x₀ hx j) h).2.2.2.1
        linarith
      · exact ih

noncomputable def reciprocal (x : ℝ) : ℝ := 1 / (64 * x)

theorem reciprocal_square_step (x : ℝ) (hx : 0 < x) (hsmall : x < 1 / 256) :
    reciprocal (next x) ^ 2 ≤ reciprocal x := by
  have hb := step_bounds x hx hsmall
  have hn := hb.2.2.1
  have hsq := hb.2.2.2.2
  unfold reciprocal
  rw [div_pow, one_pow]
  apply (div_le_div_iff₀ (by positivity : 0 < (64 * next x) ^ 2)
    (by positivity : 0 < 64 * x)).mpr
  nlinarith

theorem iterated_square_contraction (x₀ : ℝ) (hx : 0 < x₀) (j : ℕ)
    (hactive : rateRatio x₀ j < 1 / 256) :
    reciprocal (rateRatio x₀ j) ^ (2 ^ j) ≤ reciprocal x₀ := by
  induction j with
  | zero => simp [rateRatio]
  | succ j ih =>
      have ha : rateRatio x₀ j < 1 / 256 :=
        lt_of_le_of_lt (ratio_step_mono x₀ hx j) hactive
      have hstep : rateRatio x₀ (j + 1) = next (rateRatio x₀ j) := by
        simp only [rateRatio, if_pos ha]
      have hsq := reciprocal_square_step _ (ratio_positive x₀ hx j) ha
      calc
        _ = (reciprocal (next (rateRatio x₀ j)) ^ 2) ^ (2 ^ j) := by
          rw [hstep, ← pow_mul, Nat.pow_succ]
          congr 1
          omega
        _ ≤ reciprocal (rateRatio x₀ j) ^ (2 ^ j) :=
          pow_le_pow_left₀ (sq_nonneg _) hsq _
        _ ≤ reciprocal x₀ := ih ha

/-- A finite, double-exponential bound forces the actual public recursion to
    stop. This does not use an assumed chain-length estimate. -/
theorem stopped_by (x₀ : ℝ) (hx : 0 < x₀) (j : ℕ)
    (hbound : reciprocal x₀ ≤ (4 : ℝ) ^ (2 ^ j)) :
    1 / 256 ≤ rateRatio x₀ j := by
  by_contra h
  have ha : rateRatio x₀ j < 1 / 256 := lt_of_not_ge h
  have hp := ratio_positive x₀ hx j
  have hz : 4 < reciprocal (rateRatio x₀ j) := by
    unfold reciprocal
    apply (lt_div_iff₀ (by positivity : 0 < 64 * rateRatio x₀ j)).mpr
    linarith
  have hstrict : (4 : ℝ) ^ (2 ^ j) < reciprocal (rateRatio x₀ j) ^ (2 ^ j) :=
    pow_lt_pow_left₀ hz (by norm_num) (by positivity)
  have hsmall := iterated_square_contraction x₀ hx j ha
  linarith

def stageCap (bound : ℕ) : ℕ := Nat.clog 2 (Nat.clog 4 bound)

theorem stopped_at_double_log (x₀ : ℝ) (hx : 0 < x₀) (bound : ℕ)
    (hbound : reciprocal x₀ ≤ bound) :
    1 / 256 ≤ rateRatio x₀ (stageCap bound) := by
  apply stopped_by x₀ hx
  have h1 : bound ≤ 4 ^ Nat.clog 4 bound := Nat.le_pow_clog (by omega) bound
  have h2 : Nat.clog 4 bound ≤ 2 ^ stageCap bound := Nat.le_pow_clog (by omega) _
  have h3 : (4 : ℕ) ^ Nat.clog 4 bound ≤ 4 ^ (2 ^ stageCap bound) :=
    Nat.pow_le_pow_right (by omega) h2
  have h4 : (bound : ℝ) ≤ (4 : ℝ) ^ (2 ^ stageCap bound) := by
    exact_mod_cast h1.trans h3
  exact hbound.trans h4

noncomputable def stoppingIndex (x₀ : ℝ) (hx : 0 < x₀) (bound : ℕ)
    (hbound : reciprocal x₀ ≤ bound) : ℕ :=
  Nat.find (show ∃ j : ℕ, (1 : ℝ) / 256 ≤ rateRatio x₀ j from
    ⟨stageCap bound, stopped_at_double_log x₀ hx bound hbound⟩)

theorem stoppingIndex_spec (x₀ : ℝ) (hx : 0 < x₀) (bound : ℕ)
    (hbound : reciprocal x₀ ≤ bound) :
    stoppingIndex x₀ hx bound hbound ≤ stageCap bound ∧
      1 / 256 ≤ rateRatio x₀ (stoppingIndex x₀ hx bound hbound) ∧
      ∀ j, j < stoppingIndex x₀ hx bound hbound → rateRatio x₀ j < 1 / 256 := by
  let hex : ∃ j : ℕ, (1 : ℝ) / 256 ≤ rateRatio x₀ j :=
    ⟨stageCap bound, stopped_at_double_log x₀ hx bound hbound⟩
  change Nat.find hex ≤ stageCap bound ∧
    (1 : ℝ) / 256 ≤ rateRatio x₀ (Nat.find hex) ∧ _
  refine ⟨Nat.find_min' hex (stopped_at_double_log x₀ hx bound hbound), Nat.find_spec hex, ?_⟩
  intro j hj
  exact lt_of_not_ge (Nat.find_min hex hj)

noncomputable def multiplier (x₀ : ℝ) (j : ℕ) : ℕ :=
  if rateRatio x₀ j < 1 / 256 then factor (rateRatio x₀ j) else 1

noncomputable def product (x₀ : ℝ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => multiplier x₀ j * product x₀ j

theorem ratio_is_integer_multiple (x₀ : ℝ) (j : ℕ) :
    rateRatio x₀ j = x₀ * (product x₀ j : ℝ) := by
  induction j with
  | zero => simp [rateRatio, product]
  | succ j ih =>
      unfold product multiplier
      simp only [Nat.cast_mul, rateRatio]
      split_ifs with h
      · calc
          _ = (factor (rateRatio x₀ j) : ℝ) * (x₀ * (product x₀ j : ℝ)) :=
            congrArg (fun u => (factor (rateRatio x₀ j) : ℝ) * u) ih
          _ = _ := by ring
      · simp [ih]

theorem product_positive (x₀ : ℝ) (hx : 0 < x₀) (j : ℕ) : 0 < product x₀ j := by
  have h := ratio_positive x₀ hx j
  rw [ratio_is_integer_multiple] at h
  by_contra hn
  have hz : product x₀ j = 0 := by omega
  simp [hz] at h

theorem stageCap_le_iterated_binary_log (bound n : ℕ) (h : bound ≤ n) :
    stageCap bound ≤ Nat.clog 2 (Nat.clog 2 n) := by
  apply Nat.clog_mono_right 2
  exact Nat.clog_mono (by omega) (by omega) h

theorem factor_sqrt_bounds (x : ℝ) (hx : 0 < x) :
    (factor x : ℝ) * Real.sqrt x ≤ 1 / 4 := by
  have h := Nat.floor_le (by positivity : 0 ≤ 1 / (4 * Real.sqrt x))
  have hd : 0 < 4 * Real.sqrt x := by positivity
  have hm := (le_div_iff₀ hd).mp h
  change (factor x : ℝ) * Real.sqrt x ≤ 1 / 4
  dsimp [factor]
  nlinarith

/-- The floor rule is exactly an integer power comparison. This is the
    criterion used to implement it on rational inputs without real roots. -/
theorem factor_integer_comparison (x : ℝ) (hx : 0 < x) (a : ℕ) :
    a ≤ factor x ↔ 16 * (a : ℝ) ^ 2 * x ≤ 1 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hd : 0 < 4 * Real.sqrt x := by positivity
  have heq : 16 * (a : ℝ) ^ 2 * x = (4 * (a : ℝ) * Real.sqrt x) ^ 2 := by
    calc
      _ = 16 * (a : ℝ) ^ 2 * Real.sqrt x ^ 2 := by rw [hs2]
      _ = _ := by ring
  unfold factor
  rw [Nat.le_floor_iff (by positivity : 0 ≤ 1 / (4 * Real.sqrt x)),
    le_div_iff₀ hd, heq]
  constructor
  · intro h
    nlinarith [mul_nonneg (by positivity : 0 ≤ (a : ℝ) * (4 * Real.sqrt x))
      (sub_nonneg.mpr h)]
  · intro h
    nlinarith

end NearCubicGates.NestedRateChain
