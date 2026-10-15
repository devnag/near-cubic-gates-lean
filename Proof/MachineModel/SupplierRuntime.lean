import Proof.Foundations.SupplierPrinter
import Proof.Supplier.SupplierWalk

/-!
# Supplier runtime ledger

This module kernel-checks the exact arithmetic used to turn a `K`-bit live
restriction into a polynomial saving.  External rows multiply the
`2^(q-K)` column scan; preprocessing remains an additive charge.  The lemmas
state the finite inequalities needed by a concrete parameter instantiation
and do not hide asymptotic notation or introduce a second cost model.
-/

namespace NearCubicWires.SupplierRuntime

def columnPhaseCost
    (q liveBits externalRows perColumn : ℕ) : ℕ :=
  externalRows * (2 ^ (q - liveBits) * perColumn)

theorem columnPhase_mul_saving_le
    {q liveBits externalRows perColumn savingPower : ℕ}
    (hlive : liveBits ≤ q)
    (hbudget :
      externalRows * perColumn * savingPower ≤ 2 ^ liveBits) :
    columnPhaseCost q liveBits externalRows perColumn * savingPower ≤
      2 ^ q := by
  calc
    columnPhaseCost q liveBits externalRows perColumn * savingPower =
        2 ^ (q - liveBits) *
          (externalRows * perColumn * savingPower) := by
      simp only [columnPhaseCost]
      ring
    _ ≤ 2 ^ (q - liveBits) * 2 ^ liveBits :=
      Nat.mul_le_mul_left _ hbudget
    _ = 2 ^ q := by
      rw [← pow_add, Nat.sub_add_cancel hlive]

theorem columnPhase_le_quotient
    {q liveBits externalRows perColumn savingPower : ℕ}
    (hlive : liveBits ≤ q) (hsaving : 0 < savingPower)
    (hbudget :
      externalRows * perColumn * savingPower ≤ 2 ^ liveBits) :
    columnPhaseCost q liveBits externalRows perColumn ≤
      2 ^ q / savingPower := by
  apply (Nat.le_div_iff_mul_le hsaving).2
  exact columnPhase_mul_saving_le hlive hbudget

theorem two_half_budgets_add
    {q leftCost rightCost savingPower : ℕ}
    (hq : 0 < q)
    (hleft : leftCost * savingPower ≤ 2 ^ (q - 1))
    (hright : rightCost * savingPower ≤ 2 ^ (q - 1)) :
    (leftCost + rightCost) * savingPower ≤ 2 ^ q := by
  calc
    (leftCost + rightCost) * savingPower =
        leftCost * savingPower + rightCost * savingPower := by ring
    _ ≤ 2 ^ (q - 1) + 2 ^ (q - 1) :=
      Nat.add_le_add hleft hright
    _ = 2 ^ q := by
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hq)
      simp [pow_succ]
      ring

theorem additiveLedger_le_quotient
    {q preprocessing columnCost savingPower : ℕ}
    (hq : 0 < q) (hsaving : 0 < savingPower)
    (hpreprocessing :
      preprocessing * savingPower ≤ 2 ^ (q - 1))
    (hcolumns :
      columnCost * savingPower ≤ 2 ^ (q - 1)) :
    preprocessing + columnCost ≤ 2 ^ q / savingPower := by
  apply (Nat.le_div_iff_mul_le hsaving).2
  exact two_half_budgets_add hq hpreprocessing hcolumns

theorem polynomialRowBudget_closes
    {q liveBits rowExponent savingExponent overhead : ℕ}
    (hq : 0 < q) (hlive : liveBits ≤ q)
    (hpower :
      q ^ rowExponent * overhead * q ^ savingExponent ≤
        2 ^ liveBits) :
    columnPhaseCost q liveBits (q ^ rowExponent) overhead ≤
      2 ^ q / q ^ savingExponent := by
  apply columnPhase_le_quotient hlive
    (pow_pos hq _)
  exact hpower

/-! ## Exact exponent bookkeeping for the three supplier regimes -/

theorem directPrinterExponent (logarithm : ℕ) :
    logarithm ^ 3 * logarithm ^ 2 = logarithm ^ 5 := by
  ring

theorem walkedPrinterExponent (logarithm : ℕ) :
    logarithm ^ 3 * logarithm ^ 2 * logarithm ^ 2 =
      logarithm ^ 7 := by
  ring

theorem thresholdPrinterExponent (logarithm : ℕ) :
    logarithm ^ 3 * logarithm ^ 2 *
        logarithm ^ 2 * logarithm ^ 2 =
      logarithm ^ 9 := by
  ring

theorem minimalModulus_strictly_exceeds_liveCount (liveBits : ℕ) :
    2 ^ liveBits < 2 ^ (liveBits + 1) := by
  exact Nat.pow_lt_pow_right (by omega) (by omega)

theorem externalAndPreprocessingRemainAdditive
    (externalRows preprocessing scanPerRow : ℕ) :
    preprocessing + externalRows * scanPerRow =
      externalRows * scanPerRow + preprocessing := by
  exact Nat.add_comm _ _

end NearCubicWires.SupplierRuntime
