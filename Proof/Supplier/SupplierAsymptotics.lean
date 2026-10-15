import Proof.Foundations.AsymptoticAdapters
import Proof.Foundations.SupplierPipeline
import Proof.MachineModel.SupplierRuntime

/-!
# Supplier asymptotic closure

The supplier implementation proves concrete error and integer step bounds.
This module performs the only quantifier and asymptotic packaging needed by
the published A.1/A.2 interfaces: it combines finite onsets, weakens caps in
the safe direction, and converts a master integer saving inequality into the
real-valued runtime envelope.  It introduces no alternate supplier or runner.
-/

namespace NearCubicWires.SupplierAsymptotics

open NearCubicWires
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierRuntime

theorem supplierRuntimeEnvelope_mono_coefficient
    {smaller larger savingExponent : ℝ} {degree q description : ℕ}
    (hcoefficient : smaller ≤ larger) (hq : 0 < q) :
    supplierRuntimeEnvelope smaller degree savingExponent q description ≤
      supplierRuntimeEnvelope larger degree savingExponent q description := by
  unfold supplierRuntimeEnvelope
  have hdenominator :
      0 < Real.rpow (q : ℝ) savingExponent :=
    Real.rpow_pos_of_pos (by exact_mod_cast hq) _
  apply (div_le_div_iff_of_pos_right hdenominator).2
  gcongr

theorem supplierRegisterEnvelope_mono_coefficient
    {smaller larger : ℝ} {degree q description : ℕ}
    (hcoefficient : smaller ≤ larger) :
    supplierRegisterEnvelope smaller degree q description ≤
      supplierRegisterEnvelope larger degree q description := by
  unfold supplierRegisterEnvelope
  gcongr

theorem supplierRuntimeEnvelope_mono_degree
    {coefficient savingExponent : ℝ} {smallerDegree largerDegree q description : ℕ}
    (hcoefficient : 0 ≤ coefficient)
    (hdegree : smallerDegree ≤ largerDegree) (hq : 0 < q) :
    supplierRuntimeEnvelope coefficient smallerDegree savingExponent q description ≤
      supplierRuntimeEnvelope coefficient largerDegree savingExponent q description := by
  unfold supplierRuntimeEnvelope
  have hdenominator :
      0 < Real.rpow (q : ℝ) savingExponent :=
    Real.rpow_pos_of_pos (by exact_mod_cast hq) _
  apply (div_le_div_iff_of_pos_right hdenominator).2
  have hbase : (1 : ℝ) ≤ (description + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le description)
  gcongr

theorem supplierRuntimeEnvelope_add_le
    {firstCoefficient secondCoefficient savingExponent : ℝ}
    {firstDegree secondDegree q description : ℕ}
    (hfirstCoefficient : 0 ≤ firstCoefficient)
    (hsecondCoefficient : 0 ≤ secondCoefficient)
    (hq : 0 < q) :
    supplierRuntimeEnvelope firstCoefficient firstDegree savingExponent
        q description +
      supplierRuntimeEnvelope secondCoefficient secondDegree savingExponent
        q description ≤
      supplierRuntimeEnvelope (firstCoefficient + secondCoefficient)
        (max firstDegree secondDegree) savingExponent q description := by
  calc
    _ ≤
        supplierRuntimeEnvelope firstCoefficient
            (max firstDegree secondDegree) savingExponent q description +
          supplierRuntimeEnvelope secondCoefficient
            (max firstDegree secondDegree) savingExponent q description :=
      add_le_add
        (supplierRuntimeEnvelope_mono_degree hfirstCoefficient
          (le_max_left _ _) hq)
        (supplierRuntimeEnvelope_mono_degree hsecondCoefficient
          (le_max_right _ _) hq)
    _ = _ := by
      unfold supplierRuntimeEnvelope
      ring

theorem additiveSteps_le_supplierRuntimeEnvelope
    {firstSteps secondSteps description : ℕ}
    {firstCoefficient secondCoefficient savingExponent : ℝ}
    {firstDegree secondDegree q : ℕ}
    (hfirstCoefficient : 0 ≤ firstCoefficient)
    (hsecondCoefficient : 0 ≤ secondCoefficient)
    (hq : 0 < q)
    (hfirst :
      (firstSteps : ℝ) ≤
        supplierRuntimeEnvelope firstCoefficient firstDegree savingExponent
          q description)
    (hsecond :
      (secondSteps : ℝ) ≤
        supplierRuntimeEnvelope secondCoefficient secondDegree savingExponent
          q description) :
    (firstSteps + secondSteps : ℕ) ≤
      supplierRuntimeEnvelope (firstCoefficient + secondCoefficient)
        (max firstDegree secondDegree) savingExponent q description := by
  exact_mod_cast
    (add_le_add hfirst hsecond |>.trans
      (supplierRuntimeEnvelope_add_le hfirstCoefficient
        hsecondCoefficient hq))

theorem eventualAdditiveRuntimeClosure
    {firstSteps secondSteps description : ℕ → ℕ}
    {firstCoefficient secondCoefficient savingExponent : ℝ}
    {firstDegree secondDegree firstOnset secondOnset : ℕ}
    (hfirstCoefficient : 0 ≤ firstCoefficient)
    (hsecondCoefficient : 0 ≤ secondCoefficient)
    (hfirst :
      ∀ q, firstOnset ≤ q → 0 < q →
        (firstSteps q : ℝ) ≤
          supplierRuntimeEnvelope firstCoefficient firstDegree savingExponent
            q (description q))
    (hsecond :
      ∀ q, secondOnset ≤ q → 0 < q →
        (secondSteps q : ℝ) ≤
          supplierRuntimeEnvelope secondCoefficient secondDegree savingExponent
            q (description q)) :
    ∀ q, max firstOnset secondOnset ≤ q → 0 < q →
      (firstSteps q + secondSteps q : ℕ) ≤
        supplierRuntimeEnvelope (firstCoefficient + secondCoefficient)
          (max firstDegree secondDegree) savingExponent q (description q) := by
  intro q hq hqPositive
  exact additiveSteps_le_supplierRuntimeEnvelope
    hfirstCoefficient hsecondCoefficient hqPositive
    (hfirst q ((le_max_left _ _).trans hq) hqPositive)
    (hsecond q ((le_max_right _ _).trans hq) hqPositive)

/-- A concrete row ledger is sufficient for the supplier envelope.  This is
the exact bridge from the interpreter's natural-number budget to the real
`2^q / q^savingExponent` statement; the description polynomial and runtime
coefficient can only enlarge that envelope. -/
theorem runtimeEnvelope_of_masterBudget
    {steps savingPower q description degree : ℕ}
    {runtimeCoefficient savingExponent : ℝ}
    (hq : 0 < q) (hruntimeCoefficient : 1 ≤ runtimeCoefficient)
    (hmaster : steps * savingPower ≤ 2 ^ q)
    (hsaving :
      Real.rpow (q : ℝ) savingExponent ≤ savingPower) :
    (steps : ℝ) ≤
      supplierRuntimeEnvelope runtimeCoefficient degree savingExponent
        q description := by
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hdenominator :
      0 < Real.rpow (q : ℝ) savingExponent :=
    Real.rpow_pos_of_pos hqReal _
  have hmasterReal :
      (steps : ℝ) * savingPower ≤ (2 : ℝ) ^ q := by
    exact_mod_cast hmaster
  have hscaled :
      (steps : ℝ) * Real.rpow (q : ℝ) savingExponent ≤
        (2 : ℝ) ^ q := by
    calc
      (steps : ℝ) * Real.rpow (q : ℝ) savingExponent ≤
          (steps : ℝ) * savingPower := by
        gcongr
      _ ≤ (2 : ℝ) ^ q := hmasterReal
  apply (le_div_iff₀ hdenominator).2
  apply hscaled.trans
  have hdescription : (1 : ℝ) ≤ (description + 1 : ℕ) ^ degree := by
    have : (1 : ℝ) ≤ (description + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le description)
    exact one_le_pow₀ this
  have htwo : (0 : ℝ) ≤ (2 : ℝ) ^ q := by positivity
  calc
    (2 : ℝ) ^ q = 1 * (2 : ℝ) ^ q * 1 := by ring
    _ ≤ runtimeCoefficient * (2 : ℝ) ^ q *
        (description + 1 : ℕ) ^ degree := by
      gcongr

theorem masterBudget_of_additive_rows
    {steps preprocessing columnCost savingPower q : ℕ}
    (hq : 0 < q)
    (hsteps : steps ≤ preprocessing + columnCost)
    (hpreprocessing :
      preprocessing * savingPower ≤ 2 ^ (q - 1))
    (hcolumns :
      columnCost * savingPower ≤ 2 ^ (q - 1)) :
    steps * savingPower ≤ 2 ^ q := by
  exact (Nat.mul_le_mul_right savingPower hsteps).trans
    (two_half_budgets_add hq hpreprocessing hcolumns)

theorem supplierLogExponentLedger :
    (∀ logarithm : ℕ,
      logarithm ^ 3 * logarithm ^ 2 = logarithm ^ 5) ∧
    (∀ logarithm : ℕ,
      logarithm ^ 3 * logarithm ^ 2 * logarithm ^ 2 =
        logarithm ^ 7) ∧
    (∀ logarithm : ℕ,
      logarithm ^ 3 * logarithm ^ 2 * logarithm ^ 2 * logarithm ^ 2 =
        logarithm ^ 9) :=
  ⟨directPrinterExponent, walkedPrinterExponent, thresholdPrinterExponent⟩

end NearCubicWires.SupplierAsymptotics
