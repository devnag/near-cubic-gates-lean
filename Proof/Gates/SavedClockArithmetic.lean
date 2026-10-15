import Proof.Gates.MainBudgetDilation
import Mathlib.Tactic.Positivity

/-! Exact integer arithmetic for the counter's saved clock and for its
    transfer to the hierarchy clock. These theorems do not assert that an
    ordinary machine realizes the operation-count premise. -/

set_option autoImplicit false

namespace NearCubicGates.SavedClockArithmetic

open Target

def innerWidth (n stages reserve : ℕ) : ℕ :=
  (2 * stages + reserve + mu n) * lambda n

def savedClock (n : ℕ) : ℕ := 2 ^ n / n ^ mu n

theorem width_saving (n stages reserve : ℕ) :
    n ^ (2 * stages + reserve + mu n) ≤ 2 ^ innerWidth n stages reserve := by
  have h := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) n)
    (2 * stages + reserve + mu n)
  simpa [innerWidth, lambda, ← pow_mul, Nat.mul_comm] using h

theorem workload_fits_clock {n stages reserve overhead multiplier : ℕ}
    (hn : 0 < n) (hk : innerWidth n stages reserve ≤ n)
    (hr : overhead + 2 ≤ reserve) (hm : multiplier ≤ n ^ 2) :
    multiplier * (2 ^ (n - innerWidth n stages reserve) * n ^ (2 * stages + overhead)) ≤
      savedClock n := by
  have hsave := width_saving n stages reserve
  have he : 2 * stages + overhead + 2 + mu n ≤ 2 * stages + reserve + mu n := by omega
  have hp : multiplier * n ^ (2 * stages + overhead) * n ^ mu n ≤
      2 ^ innerWidth n stages reserve := by
    calc
      _ ≤ n ^ 2 * n ^ (2 * stages + overhead) * n ^ mu n := by gcongr
      _ = n ^ (2 * stages + overhead + 2 + mu n) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ n ^ (2 * stages + reserve + mu n) := Nat.pow_le_pow_right hn he
      _ ≤ _ := hsave
  unfold savedClock
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < n ^ mu n)).mpr
  calc
    _ = 2 ^ (n - innerWidth n stages reserve) *
      (multiplier * n ^ (2 * stages + overhead) * n ^ mu n) := by ring
    _ ≤ 2 ^ (n - innerWidth n stages reserve) * 2 ^ innerWidth n stages reserve :=
      Nat.mul_le_mul_left _ hp
    _ = 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel hk]

theorem mu_large {r n : ℕ} (hn : 2 ^ (2 ^ r) ≤ n) : r ≤ mu n := by
  have h := mu_mono hn
  simpa [mu, lambda, Nat.clog_pow, show 1 < 2 by decide] using h

/-- A complete polynomial workload is negligible relative to the hierarchy
    clock once the saved exponent dominates both fixed polynomial tariffs. -/
theorem hierarchy_workload_bound {q T work sourceTariff callTariff multiplier : ℕ}
    (hq : 0 < q)
    (hsource : 2 ^ q ≤ T * q ^ sourceTariff)
    (hwork : work * q ^ mu q ≤ 2 ^ q * q ^ callTariff)
    (hexponent : sourceTariff + callTariff + 2 ≤ mu q)
    (hm : multiplier ≤ q ^ 2) : multiplier * work ≤ T := by
  have hpow : q ^ (sourceTariff + callTariff + 2) ≤ q ^ mu q :=
    Nat.pow_le_pow_right hq hexponent
  have h : work * q ^ (sourceTariff + callTariff + 2) ≤
      T * q ^ (sourceTariff + callTariff) := by
    calc
      _ ≤ work * q ^ mu q := Nat.mul_le_mul_left _ hpow
      _ ≤ 2 ^ q * q ^ callTariff := hwork
      _ ≤ (T * q ^ sourceTariff) * q ^ callTariff := Nat.mul_le_mul_right _ hsource
      _ = _ := by rw [mul_assoc, ← pow_add]
  have hmwork : (multiplier * work) * q ^ (sourceTariff + callTariff) ≤
      T * q ^ (sourceTariff + callTariff) := by
    calc
      _ ≤ (q ^ 2 * work) * q ^ (sourceTariff + callTariff) := by gcongr
      _ = work * q ^ (sourceTariff + callTariff + 2) := by rw [pow_add]; ring
      _ ≤ _ := h
  exact Nat.le_of_mul_le_mul_right hmwork (by positivity)

theorem hierarchy_little_o (q T work : ℕ → ℕ) (sourceTariff callTariff : ℕ)
    (hunbounded : ∀ bound, ∃ onset, ∀ N, onset ≤ N → bound ≤ q N)
    (hsource : ∃ onset, ∀ N, onset ≤ N →
      2 ^ q N ≤ T N * q N ^ sourceTariff)
    (hwork : ∃ onset, ∀ N, onset ≤ N →
      work N * q N ^ mu (q N) ≤ 2 ^ q N * q N ^ callTariff) :
    ∀ multiplier : ℕ, 0 < multiplier →
      ∃ onset, ∀ N, onset ≤ N → multiplier * work N ≤ T N := by
  intro multiplier hm
  obtain ⟨a, ha⟩ := hunbounded (max multiplier (2 ^ (2 ^ (sourceTariff + callTariff + 2))))
  obtain ⟨b, hb⟩ := hsource
  obtain ⟨c, hc⟩ := hwork
  refine ⟨max a (max b c), ?_⟩
  intro N hN
  have hq := ha N (le_trans (le_max_left _ _) hN)
  have hqm : multiplier ≤ q N := le_trans (le_max_left _ _) hq
  have hqt : 2 ^ (2 ^ (sourceTariff + callTariff + 2)) ≤ q N :=
    le_trans (le_max_right _ _) hq
  apply hierarchy_workload_bound (by omega : 0 < q N)
    (hb N (by omega)) (hc N (by omega)) (mu_large hqt)
  exact hqm.trans (by
    simpa [pow_two] using Nat.mul_le_mul_left (q N) (by omega : 1 ≤ q N))

end NearCubicGates.SavedClockArithmetic
