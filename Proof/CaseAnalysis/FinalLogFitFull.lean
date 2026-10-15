import Proof.CaseAnalysis.FinalLogFit

namespace NearCubicWires.RepairSource.CloseoutFinal.C10LogFitFull

open NearCubicWires.RepairSource.CloseoutFinal.C10LogFit

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fullOnset (kappa : ℕ) : ℕ := logFit_onset kappa + 2

theorem logFit_onset_le_fullOnset (kappa : ℕ) : logFit_onset kappa ≤ fullOnset kappa := by
  unfold fullOnset
  omega

theorem two_le_fullOnset (kappa : ℕ) : 2 ≤ fullOnset kappa := by
  unfold fullOnset
  omega

theorem hlog_of_onset (kappa : ℕ) :
    ∀ w, fullOnset kappa ≤ w → w + 1 ≤ 2 ^ (Nat.log 2 w + 1) := by
  intro w _
  have h : w < 2 ^ (Nat.log 2 w + 1) := Nat.lt_pow_succ_log_self (by decide) w
  exact h

/-- **Hypothesis 10 (`hfit`)**, at `fullOnset`.  This is `C10LogFit.hfit_of_onset`
transported up the onset; it is not re-proved. -/
theorem hfit_full (kappa : ℕ) :
    ∀ w, fullOnset kappa ≤ w → kappa * (Nat.log 2 w + 1) ≤ w := by
  intro w hw
  exact hfit_of_onset kappa w (Nat.le_trans (logFit_onset_le_fullOnset kappa) hw)

/-- **Hypothesis 11 (`hlogTwo`)**, the fact S6 §4(a) found load-bearing for
`hot_absorb`'s six-phase step. -/
theorem hlogTwo_of_onset (kappa : ℕ) :
    ∀ w, fullOnset kappa ≤ w → 2 ≤ Nat.log 2 w + 1 := by
  intro w hw
  have h2 : 2 ≤ w := Nat.le_trans (two_le_fullOnset kappa) hw
  have hpos : 0 < Nat.log 2 w := Nat.log_pos (by decide) h2
  omega

theorem logFit_full (kappa : ℕ) :
    ∀ w, fullOnset kappa ≤ w →
      (w + 1 ≤ 2 ^ (Nat.log 2 w + 1)) ∧ (kappa * (Nat.log 2 w + 1) ≤ w) ∧
        (2 ≤ Nat.log 2 w + 1) := by
  intro w hw
  exact ⟨hlog_of_onset kappa w hw, hfit_full kappa w hw, hlogTwo_of_onset kappa w hw⟩

end NearCubicWires.RepairSource.CloseoutFinal.C10LogFitFull
