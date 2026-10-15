import Proof.Foundations.PolynomialSchedule

namespace NearCubicWires.SupplierCapacity

open NearCubicWires.PolynomialSchedule
open NearCubicWires.SourceInterfaces

theorem coefficient_mul_logScale_eventually_le (coefficient : ℕ) :
    ∃ onset, ∀ q, onset ≤ q →
      coefficient * logScale q ≤ q := by
  let positiveCoefficient := coefficient + 1
  have hcoefficient : 0 < positiveCoefficient := by
    dsimp only [positiveCoefficient]
    omega
  let envelope : ℕ → ℕ :=
    fun n => positiveCoefficient * (n + 2) + 2
  have henvelope : PolynomiallyBounded envelope := by
    refine ⟨2 * positiveCoefficient + 2, 1, by omega, ?_⟩
    intro n
    dsimp only [envelope]
    simp only [pow_one]
    nlinarith
  rcases polynomiallyBounded_eventually_le_sixteenth_exponential
      henvelope with
    ⟨exponentialOnset, hexponential⟩
  refine ⟨positiveCoefficient * (exponentialOnset + 1), ?_⟩
  intro q hq
  let quotient := q / positiveCoefficient
  have hquotientLower : quotient * positiveCoefficient ≤ q := by
    apply (Nat.le_div_iff_mul_le hcoefficient).mp
    exact le_rfl
  have hquotientOnset : exponentialOnset + 1 ≤ quotient := by
    apply (Nat.le_div_iff_mul_le hcoefficient).2
    simpa [Nat.mul_comm] using hq
  have hquotientPositive : 0 < quotient := by omega
  have hquotientUpper :
      q < (quotient + 1) * positiveCoefficient := by
    apply (Nat.div_lt_iff_lt_mul hcoefficient).mp
    omega
  have henvelopeBound :=
    hexponential (quotient - 1) (by omega)
  have hargument :
      quotient - 1 + 2 = quotient + 1 := by omega
  have hexponent :
      quotient - 1 + 1 = quotient := by omega
  have hqEnvelope : q + 2 ≤ envelope (quotient - 1) := by
    dsimp only [envelope]
    rw [hargument, Nat.mul_comm]
    omega
  have hqPower : q + 2 ≤ 2 ^ quotient := by
    rw [hexponent] at henvelopeBound
    exact hqEnvelope.trans
      (henvelopeBound.trans (Nat.div_le_self _ _))
  have hlog : logScale q ≤ quotient := by
    unfold logScale
    exact Nat.clog_le_of_le_pow hqPower
  calc
    coefficient * logScale q ≤
        positiveCoefficient * logScale q := by
      apply Nat.mul_le_mul_right
      dsimp only [positiveCoefficient]
      omega
    _ ≤ positiveCoefficient * quotient :=
      Nat.mul_le_mul_left positiveCoefficient hlog
    _ = quotient * positiveCoefficient := Nat.mul_comm _ _
    _ ≤ q := hquotientLower

/-- Every fixed polynomial in the canonical binary logarithm is eventually
sublinear in the source arity.  This packages the recurring conversion from a
polynomial seed/branch ledger to one finite source-size onset. -/
theorem polynomiallyBounded_logScale_eventually_le_id
    {function : ℕ → ℕ}
    (hfunction : PolynomiallyBounded function) :
    ∃ onset, ∀ q, onset ≤ q →
      function (logScale q) ≤ q := by
  rcases polynomiallyBounded_eventually_le_sixteenth_exponential
      hfunction with
    ⟨logOnset, hlog⟩
  refine ⟨max 1 (2 ^ logOnset), ?_⟩
  intro q hq
  have hqPositive : 0 < q := (le_max_left 1 (2 ^ logOnset)).trans hq
  have hpowOnset : 2 ^ logOnset ≤ q :=
    (le_max_right 1 (2 ^ logOnset)).trans hq
  have hlogOnset : logOnset ≤ logScale q := by
    apply Nat.le_of_lt
    unfold logScale
    rw [Nat.lt_clog_iff_pow_lt (by omega)]
    omega
  have hfunctionBound := hlog (logScale q) hlogOnset
  have hclogPower :
      2 ^ logScale q ≤ 2 * (q + 2) := by
    unfold logScale
    by_cases hsmall : q + 2 ≤ 1
    · omega
    · have hpred :
          2 ^ (Nat.clog 2 (q + 2)).pred < q + 2 :=
        Nat.pow_pred_clog_lt_self (by omega) (by omega)
      have hclogPositive : 0 < Nat.clog 2 (q + 2) :=
        Nat.clog_pos (by omega) (by omega)
      have hpredSucc :
          (Nat.clog 2 (q + 2)).pred + 1 =
            Nat.clog 2 (q + 2) :=
        Nat.succ_pred_eq_of_pos hclogPositive
      calc
        2 ^ Nat.clog 2 (q + 2) =
            2 ^ ((Nat.clog 2 (q + 2)).pred + 1) := by
          rw [hpredSucc]
        _ = 2 ^ (Nat.clog 2 (q + 2)).pred * 2 := by
          rw [pow_succ]
        _ ≤ 2 * (q + 2) := by nlinarith
  calc
    function (logScale q) ≤
        2 ^ (logScale q + 1) / 16 :=
      hfunctionBound
    _ ≤ (4 * (q + 2)) / 16 := by
      apply Nat.div_le_div_right
      rw [pow_succ]
      nlinarith
    _ ≤ q := by omega

/-- Concrete power specialization used for logarithmic row and selector
ledgers. -/
theorem coefficient_mul_logScale_pow_eventually_le
    (coefficient degree : ℕ) :
    ∃ onset, ∀ q, onset ≤ q →
      coefficient * (logScale q) ^ degree ≤ q := by
  apply polynomiallyBounded_logScale_eventually_le_id
    (function := fun n => coefficient * n ^ degree)
  refine ⟨coefficient + 1, degree, by omega, ?_⟩
  intro n
  exact Nat.mul_le_mul
    (Nat.le_add_right coefficient 1)
    (Nat.pow_le_pow_left (by omega) degree)

/-- A twentieth-power gate bound is exactly the finite condition needed to
fit the squared stable-layout gate dimension inside `⌈U^(1/10)⌉`. -/
theorem gateSquare_le_rectangularInnerDimension_of_pow_le
    {U Gates : ℕ} (hgate : Gates ^ 20 ≤ U) :
    Gates * Gates ≤ rectangularInnerDimension U := by
  rw [show Gates * Gates = Gates ^ 2 by ring]
  apply le_integerCeilRoot (degree := 10) (by norm_num)
  calc
    (Gates ^ 2) ^ 10 = Gates ^ (2 * 10) := by
      exact (pow_mul Gates 2 10).symm
    _ = Gates ^ 20 := by norm_num
    _ ≤ U := hgate

end NearCubicWires.SupplierCapacity
