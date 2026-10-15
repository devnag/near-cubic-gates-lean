import Proof.Foundations.ScheduleArithmetic

/-!
# Smooth polynomial schedules

The source-facing recovery objects have fixed polynomial envelopes in the
source exponent.  This module proves that one canonical smooth envelope has a
first half-crossing whose predecessor is within the manuscript's one-sixth
jump.  The jump hypothesis is used only below the crossing; requiring it at
all later sources would be false for every polynomial of degree at least two.
-/

namespace NearCubicWires.PolynomialSchedule

open NearCubicWires.RecoveryPipeline
open NearCubicWires.ScheduleArithmetic
open NearCubicWires.SourceInterfaces

def polynomialCore (coefficient degree source : ℕ) : ℕ :=
  coefficient * (source + 1) ^ degree

structure PolynomialEnvelope (function : ℕ → ℕ) where
  coefficient : ℕ
  degree : ℕ
  coefficientPositive : 0 < coefficient
  bound : ∀ n, function n ≤ coefficient * (n + 1) ^ degree

theorem polynomiallyBounded_iff_nonemptyEnvelope
    {function : ℕ → ℕ} :
    PolynomiallyBounded function ↔
      Nonempty (PolynomialEnvelope function) := by
  constructor
  · rintro ⟨coefficient, degree, hcoefficient, hbound⟩
    exact ⟨⟨coefficient, degree, hcoefficient, hbound⟩⟩
  · rintro ⟨envelope⟩
    exact
      ⟨envelope.coefficient, envelope.degree,
        envelope.coefficientPositive, envelope.bound⟩

theorem polynomiallyBounded_mono
    {smaller larger : ℕ → ℕ}
    (hle : ∀ n, smaller n ≤ larger n)
    (hlarger : PolynomiallyBounded larger) :
    PolynomiallyBounded smaller := by
  rcases hlarger with
    ⟨coefficient, degree, hcoefficient, hbound⟩
  exact
    ⟨coefficient, degree, hcoefficient,
      fun n => (hle n).trans (hbound n)⟩

theorem polynomiallyBounded_constant (constant : ℕ) :
    PolynomiallyBounded (fun _ => constant) := by
  exact ⟨constant + 1, 0, by omega, by
    intro n
    simp⟩

theorem polynomiallyBounded_id :
    PolynomiallyBounded (fun n : ℕ => n) := by
  exact ⟨1, 1, by omega, by
    intro n
    simp⟩

theorem polynomiallyBounded_add
    {left right : ℕ → ℕ}
    (hleft : PolynomiallyBounded left)
    (hright : PolynomiallyBounded right) :
    PolynomiallyBounded (fun n => left n + right n) := by
  rcases hleft with
    ⟨leftCoefficient, leftDegree, hleftCoefficient, hleft⟩
  rcases hright with
    ⟨rightCoefficient, rightDegree, hrightCoefficient, hright⟩
  refine
    ⟨leftCoefficient + rightCoefficient,
      max leftDegree rightDegree, by omega, ?_⟩
  intro n
  calc
    left n + right n ≤
        leftCoefficient * (n + 1) ^ leftDegree +
          rightCoefficient * (n + 1) ^ rightDegree :=
      Nat.add_le_add (hleft n) (hright n)
    _ ≤
        leftCoefficient * (n + 1) ^ max leftDegree rightDegree +
          rightCoefficient * (n + 1) ^ max leftDegree rightDegree := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left _ <|
          Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      · exact Nat.mul_le_mul_left _ <|
          Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    _ =
        (leftCoefficient + rightCoefficient) *
          (n + 1) ^ max leftDegree rightDegree := by ring

theorem polynomiallyBounded_mul
    {left right : ℕ → ℕ}
    (hleft : PolynomiallyBounded left)
    (hright : PolynomiallyBounded right) :
    PolynomiallyBounded (fun n => left n * right n) := by
  rcases hleft with
    ⟨leftCoefficient, leftDegree, hleftCoefficient, hleft⟩
  rcases hright with
    ⟨rightCoefficient, rightDegree, hrightCoefficient, hright⟩
  refine
    ⟨leftCoefficient * rightCoefficient,
      leftDegree + rightDegree,
      Nat.mul_pos hleftCoefficient hrightCoefficient, ?_⟩
  intro n
  calc
    left n * right n ≤
        (leftCoefficient * (n + 1) ^ leftDegree) *
          (rightCoefficient * (n + 1) ^ rightDegree) := by
      exact Nat.mul_le_mul (hleft n) (hright n)
    _ =
        (leftCoefficient * rightCoefficient) *
          (n + 1) ^ (leftDegree + rightDegree) := by
      rw [pow_add]
      ring

theorem polynomiallyBounded_max
    {left right : ℕ → ℕ}
    (hleft : PolynomiallyBounded left)
    (hright : PolynomiallyBounded right) :
    PolynomiallyBounded (fun n => max (left n) (right n)) := by
  apply polynomiallyBounded_mono
    (larger := fun n => left n + right n)
  · intro n
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  · exact polynomiallyBounded_add hleft hright

theorem polynomiallyBounded_pow
    {function : ℕ → ℕ} (hfunction : PolynomiallyBounded function)
    (exponent : ℕ) :
    PolynomiallyBounded (fun n => function n ^ exponent) := by
  rcases hfunction with
    ⟨coefficient, degree, hcoefficient, hbound⟩
  refine
    ⟨coefficient ^ exponent + 1, degree * exponent, by omega, ?_⟩
  intro n
  calc
    function n ^ exponent ≤
        (coefficient * (n + 1) ^ degree) ^ exponent :=
      Nat.pow_le_pow_left (hbound n) _
    _ =
        coefficient ^ exponent *
          (n + 1) ^ (degree * exponent) := by
      rw [mul_pow, pow_mul]
    _ ≤
        (coefficient ^ exponent + 1) *
          (n + 1) ^ (degree * exponent) := by
      exact Nat.mul_le_mul_right _
        (Nat.le_add_right (coefficient ^ exponent) 1)

theorem polynomiallyBounded_comp
    {outer inner : ℕ → ℕ}
    (houter : PolynomiallyBounded outer)
    (hinner : PolynomiallyBounded inner) :
    PolynomiallyBounded (fun n => outer (inner n)) := by
  rcases houter with
    ⟨outerCoefficient, outerDegree, houterCoefficient, houter⟩
  rcases hinner with
    ⟨innerCoefficient, innerDegree, hinnerCoefficient, hinner⟩
  refine
    ⟨outerCoefficient * (innerCoefficient + 1) ^ outerDegree,
      innerDegree * outerDegree, by positivity, ?_⟩
  intro n
  have hone :
      1 ≤ (n + 1) ^ innerDegree := by
    exact Nat.one_le_pow innerDegree _ (by omega)
  have hinnerSucc :
      inner n + 1 ≤
        (innerCoefficient + 1) * (n + 1) ^ innerDegree := by
    calc
      inner n + 1 ≤
          innerCoefficient * (n + 1) ^ innerDegree + 1 :=
        Nat.add_le_add_right (hinner n) 1
      _ ≤
          innerCoefficient * (n + 1) ^ innerDegree +
            (n + 1) ^ innerDegree := by
        gcongr
      _ =
          (innerCoefficient + 1) * (n + 1) ^ innerDegree := by ring
  calc
    outer (inner n) ≤
        outerCoefficient * (inner n + 1) ^ outerDegree :=
      houter (inner n)
    _ ≤
        outerCoefficient *
          ((innerCoefficient + 1) *
            (n + 1) ^ innerDegree) ^ outerDegree := by
      gcongr
    _ =
        (outerCoefficient * (innerCoefficient + 1) ^ outerDegree) *
          (n + 1) ^ (innerDegree * outerDegree) := by
      rw [mul_pow, pow_mul]
      ring

/-- Every fixed polynomial envelope eventually fits in one sixteenth of the
canonical exponential source length.  The factor is charged explicitly so
downstream witness-width proofs do not hide a capacity assumption. -/
theorem polynomiallyBounded_eventually_le_sixteenth_exponential
    {function : ℕ → ℕ}
    (hfunction : PolynomiallyBounded function) :
    ∃ onset, ∀ n, onset ≤ n →
      function n ≤ 2 ^ (n + 1) / 16 := by
  rcases hfunction with
    ⟨coefficient, degree, hcoefficient, hbound⟩
  have hlittle :
      (fun n : ℕ => (n : ℝ) ^ degree) =o[Filter.atTop]
        (fun n : ℕ => (2 : ℝ) ^ n) :=
    isLittleO_pow_const_const_pow_of_one_lt degree (by norm_num)
  let scale : ℝ := 16 * coefficient * 2 ^ degree
  have hscale : 0 < scale := by
    dsimp only [scale]
    positivity
  have heventually := hlittle.bound (one_div_pos.mpr hscale)
  rw [Filter.eventually_atTop] at heventually
  rcases heventually with ⟨onset, heventually⟩
  refine ⟨max 1 onset, fun n hn => ?_⟩
  have hone : 1 ≤ n := (le_max_left 1 onset).trans hn
  have honset : onset ≤ n := (le_max_right 1 onset).trans hn
  have hsucc : n + 1 ≤ 2 * n := by omega
  have hpower :
      (n + 1) ^ degree ≤ 2 ^ degree * n ^ degree := by
    calc
      (n + 1) ^ degree ≤ (2 * n) ^ degree :=
        Nat.pow_le_pow_left hsucc degree
      _ = 2 ^ degree * n ^ degree := by rw [Nat.mul_pow]
  have hsmall := heventually n honset
  have hnnonnegative : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have htwoNonnegative : (0 : ℝ) ≤ 2 := by norm_num
  simp only [Real.norm_eq_abs, abs_pow,
    abs_of_nonneg hnnonnegative,
    abs_of_nonneg htwoNonnegative] at hsmall
  have hscaledReal :
      ((16 * function n : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    calc
      ((16 * function n : ℕ) : ℝ) ≤
          ((16 * (coefficient * (n + 1) ^ degree) : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 16 (hbound n)
      _ ≤
          ((16 * (coefficient *
            (2 ^ degree * n ^ degree)) : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 16
          (Nat.mul_le_mul_left coefficient hpower)
      _ = scale * (n : ℝ) ^ degree := by
        dsimp only [scale]
        push_cast
        ring
      _ ≤ (2 : ℝ) ^ n := by
        calc
          scale * (n : ℝ) ^ degree ≤
              scale * ((1 / scale) * (2 : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left hsmall hscale.le
          _ = (2 : ℝ) ^ n := by field_simp
  have hscaled : 16 * function n ≤ 2 ^ n := by
    exact_mod_cast hscaledReal
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 16)).2
  calc
    function n * 16 = 16 * function n := by omega
    _ ≤ 2 ^ n := hscaled
    _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)

theorem polynomialCore_monotone (coefficient degree : ℕ) :
    Monotone (polynomialCore coefficient degree) := by
  intro left right hle
  unfold polynomialCore
  gcongr

/-- Discrete mean-value bound for natural powers. -/
theorem pow_increment_le
    (value degree : ℕ) :
    (value + 1) ^ degree ≤
      value ^ degree +
        degree * (value + 1) ^ (degree - 1) := by
  have hmono :
      value ^ degree ≤ (value + 1) ^ degree :=
    Nat.pow_le_pow_left (by omega) degree
  have hdiffNonnegative :
      (0 : ℤ) ≤
        ((value + 1 : ℕ) : ℤ) ^ degree -
          (value : ℤ) ^ degree := by
    apply sub_nonneg.mpr
    exact_mod_cast hmono
  have hbound :=
    abs_pow_sub_pow_le
      (a := ((value + 1 : ℕ) : ℤ))
      (b := (value : ℤ)) degree
  rw [abs_of_nonneg hdiffNonnegative] at hbound
  have habsDifference :
      |(((value + 1 : ℕ) : ℤ) - (value : ℤ))| = 1 := by
    norm_num
  have hmax :
      max |((value + 1 : ℕ) : ℤ)| |(value : ℤ)| =
        ((value + 1 : ℕ) : ℤ) := by
    rw [show (((value + 1 : ℕ) : ℤ)) = (value : ℤ) + 1 by omega]
    rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (value : ℤ) + 1)]
    rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (value : ℤ))]
    exact max_eq_left (by omega)
  rw [habsDifference, hmax] at hbound
  norm_num at hbound
  have hinteger :
      ((value + 1 : ℕ) : ℤ) ^ degree ≤
        (value : ℤ) ^ degree +
          degree * ((value + 1 : ℕ) : ℤ) ^ (degree - 1) := by
    simpa [add_comm] using hbound
  exact_mod_cast hinteger

/-- Once `value` dominates the fixed derivative coefficient, one polynomial
step increases by at most one third of the current value. -/
theorem three_mul_next_pow_le_four_mul_pow
    {value degree : ℕ} (hvalue : 0 < value)
    (honset : 3 * degree * 2 ^ (degree - 1) ≤ value) :
    3 * (value + 1) ^ degree ≤ 4 * value ^ degree := by
  cases degree with
  | zero =>
      simp
  | succ degree =>
    simp only [Nat.succ_sub_one] at honset ⊢
    have hbase : value + 1 ≤ 2 * value := by
      omega
    have hpower :
        (value + 1) ^ degree ≤
          2 ^ degree * value ^ degree := by
      calc
        (value + 1) ^ degree ≤
            (2 * value) ^ degree :=
          Nat.pow_le_pow_left hbase _
        _ = 2 ^ degree * value ^ degree := by
          rw [mul_pow]
    have hderivative :
        3 * ((degree + 1) * (value + 1) ^ degree) ≤
          value ^ (degree + 1) := by
      calc
        3 * ((degree + 1) * (value + 1) ^ degree) ≤
            3 * ((degree + 1) *
              (2 ^ degree * value ^ degree)) := by
          gcongr
        _ =
            (3 * (degree + 1) * 2 ^ degree) *
              value ^ degree := by ring
        _ ≤ value * value ^ degree :=
          Nat.mul_le_mul_right _ honset
        _ = value ^ (degree + 1) := by
          simp [pow_succ, Nat.mul_comm]
    have hincrement := pow_increment_le value (degree + 1)
    simp only [Nat.add_sub_cancel] at hincrement
    calc
      3 * (value + 1) ^ (degree + 1) ≤
          3 * (value ^ (degree + 1) +
            (degree + 1) * (value + 1) ^ degree) :=
        Nat.mul_le_mul_left 3 hincrement
      _ = 3 * value ^ (degree + 1) +
          3 * ((degree + 1) * (value + 1) ^ degree) := by ring
      _ ≤ 3 * value ^ (degree + 1) + value ^ (degree + 1) := by
        gcongr
      _ = 4 * value ^ (degree + 1) := by ring

theorem polynomialCore_adjacent_of_belowHalf
    {coefficient degree source target : ℕ}
    (hsource :
      3 * degree * 2 ^ (degree - 1) ≤ source)
    (hbelow :
      2 * polynomialCore coefficient degree source ≤ target) :
    6 * polynomialCore coefficient degree (source + 1) ≤
      6 * polynomialCore coefficient degree source + target := by
  have hratio :=
    three_mul_next_pow_le_four_mul_pow
      (value := source + 1) (degree := degree)
      (by omega)
      (hsource.trans (by omega))
  have hscaled :=
    Nat.mul_le_mul_left (2 * coefficient) hratio
  unfold polynomialCore at hbelow ⊢
  calc
    6 * (coefficient * (source + 1 + 1) ^ degree) =
        (2 * coefficient) *
          (3 * ((source + 1) + 1) ^ degree) := by ring
    _ ≤ (2 * coefficient) *
          (4 * (source + 1) ^ degree) := hscaled
    _ =
        6 * (coefficient * (source + 1) ^ degree) +
          2 * (coefficient * (source + 1) ^ degree) := by ring
    _ ≤
        6 * (coefficient * (source + 1) ^ degree) + target := by
      gcongr

def polynomialSourceOnset (degree : ℕ) : ℕ :=
  3 * degree * 2 ^ (degree - 1)

/-- The generic existence proof uses the target itself as a concrete search
limit.  Keeping that witness visible lets the executable selector charge a
finite unary loop without importing an independent halting certificate. -/
theorem polynomialCore_crosses_at_target
    {coefficient degree target sourceOnset : ℕ}
    (hcoefficient : 0 < coefficient) (hdegree : 0 < degree) :
    target <
      2 * polynomialCore coefficient degree
        (sourceOnset + target) := by
  unfold polynomialCore
  have hbase :
      target < sourceOnset + target + 1 := by omega
  have hpow :
      sourceOnset + target + 1 ≤
        (sourceOnset + target + 1) ^ degree := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right
        (by omega : 0 < sourceOnset + target + 1) hdegree
  have hcoefficientOne : 1 ≤ coefficient := hcoefficient
  calc
    target < sourceOnset + target + 1 := hbase
    _ ≤ (sourceOnset + target + 1) ^ degree := hpow
    _ ≤ coefficient * (sourceOnset + target + 1) ^ degree := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right
          ((sourceOnset + target + 1) ^ degree) hcoefficientOne
    _ < 2 *
        (coefficient * (sourceOnset + target + 1) ^ degree) := by
      have hpositive :
          0 < coefficient *
            (sourceOnset + target + 1) ^ degree := by positivity
      omega

theorem polynomialCore_crossingExists
    {coefficient degree target sourceOnset : ℕ}
    (hcoefficient : 0 < coefficient) (hdegree : 0 < degree) :
    ∃ offset,
      target <
        2 * polynomialCore coefficient degree
          (sourceOnset + offset) := by
  refine ⟨target, polynomialCore_crosses_at_target
    hcoefficient hdegree⟩

/-- Canonical semantic first-crossing data for a fixed polynomial envelope. -/
def polynomialFirstCrossingData
    (coefficient degree target : ℕ)
    (hcoefficient : 0 < coefficient)
    (hdegree : 0 < degree)
    (htarget :
      2 * polynomialCore coefficient degree
        (polynomialSourceOnset degree) ≤ target) :
    FirstCrossingData
      (polynomialCore coefficient degree) target where
  sourceOnset := polynomialSourceOnset degree
  monotone := polynomialCore_monotone coefficient degree
  belowAtOnset := htarget
  crossingExists :=
    polynomialCore_crossingExists hcoefficient hdegree
  adjacentJump := by
    intro source hsource hbelow
    exact polynomialCore_adjacent_of_belowHalf
      (by simpa [polynomialSourceOnset] using hsource) hbelow

theorem polynomialFirstCrossingData_nextOffset_le_target
    (coefficient degree target : ℕ)
    (hcoefficient : 0 < coefficient)
    (hdegree : 0 < degree)
    (htarget :
      2 * polynomialCore coefficient degree
        (polynomialSourceOnset degree) ≤ target) :
    (polynomialFirstCrossingData coefficient degree target
      hcoefficient hdegree htarget).nextOffset ≤ target := by
  apply Nat.find_min'
  exact polynomialCore_crosses_at_target hcoefficient hdegree

end NearCubicWires.PolynomialSchedule
