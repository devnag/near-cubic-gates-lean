import Proof.CaseAnalysis.RawRowsDegree

/-! The existing additive logarithmic census for the actual raw recurrence.
Windows are summed at their own levels, as in the paper. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierListPolynomial SupplierListSchedule
open SupplierToeplitz SupplierToeplitzCore SupplierEstimator
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def terminalCoordinateLogBudget
    (population terminalWindow : ℕ) : ℕ :=
  2 * natBitLength (terminalWindow + 1) +
    terminalWindow * natBitLength (population + 1) + 2

def deltaCoordinateLogBudget
    (population windowWidth : ℕ) : ℕ :=
  2 * natBitLength (2 * windowWidth + 1) +
    (2 * windowWidth) * natBitLength (2 * population + 1) + 2

theorem terminalCoordinateRawLedger_bitLength_le
    (population terminalWindow : ℕ) :
    natBitLength (terminalCoordinateRawLedger population terminalWindow) ≤
      terminalCoordinateLogBudget population terminalWindow := by
  unfold terminalCoordinateRawLedger terminalCoordinateLogBudget
  calc
    natBitLength
        ((terminalWindow + 1) ^ 2 *
          (population + 1) ^ terminalWindow) ≤
      natBitLength ((terminalWindow + 1) ^ 2) +
        natBitLength ((population + 1) ^ terminalWindow) :=
      ValidatorPolynomialDomination.natBitLength_mul_le _ _
    _ ≤ (2 * natBitLength (terminalWindow + 1) + 1) +
        (terminalWindow * natBitLength (population + 1) + 1) :=
      Nat.add_le_add
        (ValidatorPolynomialDomination.natBitLength_pow_le _ _)
        (ValidatorPolynomialDomination.natBitLength_pow_le _ _)
    _ = 2 * natBitLength (terminalWindow + 1) +
        terminalWindow * natBitLength (population + 1) + 2 := by ring

theorem deltaCoordinateRawLedger_bitLength_le
    (population windowWidth : ℕ) :
    natBitLength (deltaCoordinateRawLedger population windowWidth) ≤
      deltaCoordinateLogBudget population windowWidth := by
  unfold deltaCoordinateRawLedger deltaCoordinateLogBudget
  calc
    natBitLength
        ((2 * windowWidth + 1) ^ 2 *
          (2 * population + 1) ^ (2 * windowWidth)) ≤
      natBitLength ((2 * windowWidth + 1) ^ 2) +
        natBitLength ((2 * population + 1) ^ (2 * windowWidth)) :=
      ValidatorPolynomialDomination.natBitLength_mul_le _ _
    _ ≤ (2 * natBitLength (2 * windowWidth + 1) + 1) +
        ((2 * windowWidth) * natBitLength (2 * population + 1) + 1) :=
      Nat.add_le_add
        (ValidatorPolynomialDomination.natBitLength_pow_le _ _)
        (ValidatorPolynomialDomination.natBitLength_pow_le _ _)
    _ = 2 * natBitLength (2 * windowWidth + 1) +
        (2 * windowWidth) * natBitLength (2 * population + 1) + 2 := by ring

/-- Constructor-for-constructor logarithmic ledger.  Products in the raw
substitution ledger have become sums, so this is the form used by the
manuscript log budget. -/
def structuralListCoordinateLogLedgerFrom
    (depth population : ℕ) (window : Fin depth → ℕ)
    (terminalWindow level : ℕ) : ℕ :=
  if hlevel : level < depth then
    natBitLength (population + 1) +
      structuralListCoordinateLogLedgerFrom depth population window
        terminalWindow (level + 1) +
      deltaCoordinateLogBudget population (window ⟨level, hlevel⟩)
  else
    terminalCoordinateLogBudget population terminalWindow
termination_by depth - level
decreasing_by omega

theorem structuralListCoordinateRawLedgerFrom_bitLength_le
    (depth population : ℕ) (window : Fin depth → ℕ)
    (terminalWindow level : ℕ) :
    natBitLength
        (structuralListCoordinateRawLedgerFrom depth population window
          terminalWindow level) ≤
      structuralListCoordinateLogLedgerFrom depth population window
        terminalWindow level := by
  rw [structuralListCoordinateRawLedgerFrom,
    structuralListCoordinateLogLedgerFrom]
  by_cases hlevel : level < depth
  · rw [dif_pos hlevel, dif_pos hlevel]
    have houter := ValidatorPolynomialDomination.natBitLength_mul_le
      (population + 1)
      (structuralListCoordinateRawLedgerFrom depth population window
          terminalWindow (level + 1) *
        deltaCoordinateRawLedger population (window ⟨level, hlevel⟩))
    have hinner := ValidatorPolynomialDomination.natBitLength_mul_le
      (structuralListCoordinateRawLedgerFrom depth population window
        terminalWindow (level + 1))
      (deltaCoordinateRawLedger population (window ⟨level, hlevel⟩))
    have hrecursive :=
      structuralListCoordinateRawLedgerFrom_bitLength_le depth population
        window terminalWindow (level + 1)
    have hdelta := deltaCoordinateRawLedger_bitLength_le population
      (window ⟨level, hlevel⟩)
    omega
  · rw [dif_neg hlevel, dif_neg hlevel]
    exact terminalCoordinateRawLedger_bitLength_le population terminalWindow
termination_by depth - level
decreasing_by omega

def structuralListCoordinateLogLedger
    (depth population : ℕ) (window : Fin depth → ℕ)
    (terminalWindow : ℕ) : ℕ :=
  structuralListCoordinateLogLedgerFrom depth population window terminalWindow 0

theorem structuralListCoordinateRawLedger_bitLength_le
    (depth population : ℕ) (window : Fin depth → ℕ)
    (terminalWindow : ℕ) :
    natBitLength
        (structuralListCoordinateRawLedger depth population window
          terminalWindow) ≤
      structuralListCoordinateLogLedger depth population window
        terminalWindow := by
  unfold structuralListCoordinateRawLedger structuralListCoordinateLogLedger
  exact structuralListCoordinateRawLedgerFrom_bitLength_le depth population
    window terminalWindow 0

/-! The recursive logarithmic ledger is an additive fold over the graded
windows.  Exposing that fold is the key uniformity step: using only the
largest window would introduce an unnecessary extra factor of the depth. -/

private theorem capBlind_natBitLength_le_succ (value : ℕ) :
    natBitLength value ≤ value + 1 := by
  unfold natBitLength
  exact Nat.succ_le_succ (Nat.log_le_self 2 value)

theorem deltaCoordinateLogBudget_le_windowCharge
    (population windowWidth : ℕ) :
    deltaCoordinateLogBudget population windowWidth ≤
      6 * (windowWidth + 1) *
        (natBitLength (2 * population + 1) + 2) := by
  have hwindowBits := capBlind_natBitLength_le_succ (2 * windowWidth + 1)
  unfold deltaCoordinateLogBudget
  nlinarith

theorem structuralListCoordinateLogLedgerFrom_eq_sum
    {depth : ℕ} (population : ℕ) (window : Fin depth → ℕ)
    (terminalWindow level : ℕ) (hlevel : level ≤ depth) :
    structuralListCoordinateLogLedgerFrom depth population window
        terminalWindow level =
      terminalCoordinateLogBudget population terminalWindow +
        ∑ index ∈ Finset.Ico level depth,
          (natBitLength (population + 1) +
            deltaCoordinateLogBudget population
              (listWindowAt window index)) := by
  rw [structuralListCoordinateLogLedgerFrom]
  by_cases hnext : level < depth
  · rw [dif_pos hnext]
    rw [structuralListCoordinateLogLedgerFrom_eq_sum population window
      terminalWindow (level + 1) (by omega)]
    rw [← Finset.insert_Ico_add_one_left_eq_Ico hnext]
    rw [Finset.sum_insert (by simp)]
    rw [listWindowAt_of_lt window level hnext]
    omega
  · rw [dif_neg hnext]
    have hequal : level = depth := by omega
    subst level
    simp
termination_by depth - level
decreasing_by omega

theorem structuralListCoordinateLogLedger_eq_sum
    (depth population : ℕ) (window : Fin depth → ℕ)
    (terminalWindow : ℕ) :
    structuralListCoordinateLogLedger depth population window terminalWindow =
      terminalCoordinateLogBudget population terminalWindow +
        ∑ level : Fin depth,
          (natBitLength (population + 1) +
            deltaCoordinateLogBudget population (window level)) := by
  unfold structuralListCoordinateLogLedger
  rw [structuralListCoordinateLogLedgerFrom_eq_sum population window
    terminalWindow 0 (Nat.zero_le depth)]
  rw [Nat.Ico_zero_eq_range]
  congr 1
  calc
    (∑ index ∈ Finset.range depth,
        (natBitLength (population + 1) +
          deltaCoordinateLogBudget population (listWindowAt window index))) =
        ∑ level : Fin depth,
          (natBitLength (population + 1) +
            deltaCoordinateLogBudget population
              (listWindowAt window level.val)) := by
      exact (Fin.sum_univ_eq_sum_range
        (fun index : ℕ => natBitLength (population + 1) +
          deltaCoordinateLogBudget population (listWindowAt window index))
        depth).symm
    _ = ∑ level : Fin depth,
          (natBitLength (population + 1) +
            deltaCoordinateLogBudget population (window level)) := by
      apply Finset.sum_congr rfl
      intro level _
      rw [listWindowAt_of_lt window level.val level.isLt]

theorem structuralListCoordinateLogLedger_le_windowSum
    (depth population : ℕ) (window : Fin depth → ℕ) :
    structuralListCoordinateLogLedger depth population window 0 ≤
      4 + depth * natBitLength (population + 1) +
        6 * ((∑ level : Fin depth, window level) + depth) *
          (natBitLength (2 * population + 1) + 2) := by
  rw [structuralListCoordinateLogLedger_eq_sum]
  unfold terminalCoordinateLogBudget
  norm_num only [Nat.zero_add, Nat.zero_mul, Nat.mul_zero,
    Nat.cast_zero, natBitLength]
  have hdelta :
      (∑ level : Fin depth,
          deltaCoordinateLogBudget population (window level)) ≤
        ∑ level : Fin depth,
          6 * (window level + 1) *
            (natBitLength (2 * population + 1) + 2) := by
    exact Finset.sum_le_sum fun level _ =>
      deltaCoordinateLogBudget_le_windowCharge population (window level)
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  calc
    4 + (depth * natBitLength (population + 1) +
        ∑ level : Fin depth,
          deltaCoordinateLogBudget population (window level)) ≤
      4 + (depth * natBitLength (population + 1) +
        ∑ level : Fin depth,
          6 * (window level + 1) *
            (natBitLength (2 * population + 1) + 2)) := by omega
    _ = 4 + depth * natBitLength (population + 1) +
        6 * ((∑ level : Fin depth, window level) + depth) *
          (natBitLength (2 * population + 1) + 2) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id,
        Nat.mul_one]
      omega
    _ = 4 + depth * natBitLength (population + 1) +
        6 * ((∑ level : Fin depth, window level) + depth) *
          (natBitLength (2 * population + 1) + 2) := rfl

end
end NearCubicWires.RepairSource.CloseoutRawRows
