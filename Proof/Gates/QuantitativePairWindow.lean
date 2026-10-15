import Proof.Gates.TotientGrowth
import Proof.Gates.PairReconstruction
import Mathlib.Data.Nat.Sqrt

/-! A computable integer window of order D^(3/4), obtained from the proved
    cubic totient estimate. The constant is deliberately conservative; the
    headline permits an unspecified constant. No window-growth input is added. -/

set_option autoImplicit false

namespace NearCubicGates.QuantitativePairWindow

open scoped BigOperators
open TomographyDirections TotientGrowth Reconstruction ScalarWindow

def fourthRoot (D : ℕ) : ℕ := Nat.sqrt (Nat.sqrt D)
def side (D : ℕ) : ℕ := fourthRoot D ^ 3 / 24

theorem fourthRoot_bounds (D : ℕ) : fourthRoot D ^ 4 ≤ D ∧ D < (fourthRoot D + 1) ^ 4 := by
  have h1 := Nat.sqrt_le' D
  have h2 := Nat.sqrt_le' (Nat.sqrt D)
  have h3 := Nat.lt_succ_sqrt' D
  have h4 := Nat.lt_succ_sqrt' (Nat.sqrt D)
  simp only [Nat.succ_eq_add_one] at h3 h4
  dsimp [fourthRoot]
  constructor
  · have hp := Nat.pow_le_pow_left h2 2
    rw [← pow_mul] at hp
    exact hp.trans h1
  · have hs : Nat.sqrt D + 1 ≤ (Nat.sqrt (Nat.sqrt D) + 1) ^ 2 := by omega
    have hp := Nat.pow_le_pow_left hs 2
    rw [← pow_mul] at hp
    exact h3.trans_le hp

theorem fourthRoot_large {D a : ℕ} (h : a ^ 4 ≤ D) : a ≤ fourthRoot D := by
  unfold fourthRoot
  apply Nat.le_sqrt'.mpr
  apply Nat.le_sqrt'.mpr
  simpa only [← pow_mul] using h

theorem degreeSum_mono {a b : ℕ} (hab : a ≤ b) : degreeSum a ≤ degreeSum b := by
  unfold degreeSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    have h := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.trans hab⟩
  · intro m _ _
    exact Nat.zero_le _

/-- The window can be computed by two integer square roots and a division.
    The exact tomography criterion holds at every sufficiently large D. -/
theorem side_is_admissible : ∃ onset : ℕ, 4 ≤ onset ∧ ∀ D : ℕ,
    onset ^ 4 ≤ D →
      2 ≤ side D ∧ side D ≤ degreeSum ((D - 1) / (side D - 1)) := by
  obtain ⟨a, ha⟩ := degreeSum_eventually_cubic_lower
  refine ⟨max 4 a, le_max_left _ _, ?_⟩
  intro D hD
  let q := fourthRoot D
  let L := side D
  have hq : max 4 a ≤ q := fourthRoot_large hD
  have hq4 : 4 ≤ q := le_trans (le_max_left _ _) hq
  have hqcube : 64 ≤ q ^ 3 := by
    have h := Nat.pow_le_pow_left hq4 3
    norm_num at h ⊢
    exact h
  have hL : 2 ≤ L := by
    change 2 ≤ q ^ 3 / 24
    omega
  have hc := ha q (le_trans (le_max_right _ _) hq)
  have hci : q ^ 3 ≤ 24 * degreeSum q := by
    have hr : (q : ℝ) ^ 3 ≤ 24 * (degreeSum q : ℝ) := by linarith
    exact_mod_cast hr
  have hLS : L ≤ degreeSum q := by
    change q ^ 3 / 24 ≤ degreeSum q
    have h := Nat.div_le_div_right (c := 24) hci
    simpa using h
  have hLd : q * L ≤ D := by
    calc
      _ ≤ q * q ^ 3 := Nat.mul_le_mul_left q (Nat.div_le_self _ _)
      _ = q ^ 4 := by ring
      _ ≤ _ := (fourthRoot_bounds D).1
  have hquot : q ≤ (D - 1) / (L - 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < L - 1)).mpr
    have hmul : q * L = q * (L - 1) + q := by
      have h := Nat.sub_add_cancel (by omega : 1 ≤ L)
      nlinarith
    have hq0 : 1 ≤ q := by omega
    omega
  exact ⟨hL, hLS.trans (degreeSum_mono hquot)⟩

theorem side_growth_bounds (D : ℕ) (hD : 4 ^ 4 ≤ D) :
    fourthRoot D ^ 3 ≤ 48 * side D ∧ 24 * side D ≤ fourthRoot D ^ 3 ∧
      D < 16 * fourthRoot D ^ 4 := by
  have hq := fourthRoot_large hD
  have hroot := (fourthRoot_bounds D).2
  have hscale : fourthRoot D + 1 ≤ 2 * fourthRoot D := by omega
  have hp := Nat.pow_le_pow_left hscale 4
  simp only [mul_pow] at hp
  have hc : 64 ≤ fourthRoot D ^ 3 := by
    have h := Nat.pow_le_pow_left hq 3
    norm_num at h
    exact h
  have hdiv := Nat.mod_add_div (fourthRoot D ^ 3) 24
  have hmod := Nat.mod_lt (fourthRoot D ^ 3) (by decide : 0 < 24)
  refine ⟨?_, ?_, ?_⟩
  · unfold side
    omega
  · unfold side
    omega
  · norm_num at hp
    exact hroot.trans_le hp

theorem side_three_quarters (D : ℕ) (hD : 4 ^ 4 ≤ D) :
    side D ^ 4 ≤ D ^ 3 ∧ D ^ 3 ≤ (16 ^ 3 * 48 ^ 4) * side D ^ 4 := by
  obtain ⟨hlo, hhi, hDq⟩ := side_growth_bounds D hD
  have hqD := (fourthRoot_bounds D).1
  constructor
  · calc
      _ ≤ (fourthRoot D ^ 3) ^ 4 := Nat.pow_le_pow_left (by nlinarith) 4
      _ = (fourthRoot D ^ 4) ^ 3 := by ring
      _ ≤ D ^ 3 := Nat.pow_le_pow_left hqD 3
  · calc
      D ^ 3 ≤ (16 * fourthRoot D ^ 4) ^ 3 := Nat.pow_le_pow_left (le_of_lt hDq) 3
      _ = 16 ^ 3 * (fourthRoot D ^ 3) ^ 4 := by ring
      _ ≤ 16 ^ 3 * (48 * side D) ^ 4 := by gcongr
      _ = _ := by ring

theorem degreeSum_le_cube (q : ℕ) : degreeSum q ≤ q ^ 3 := by
  unfold degreeSum
  calc
    _ ≤ ∑ _ ∈ Finset.Icc 1 q, q * q := by
      apply Finset.sum_le_sum
      intro m hm
      have hm' := (Finset.mem_Icc.mp hm).2
      exact Nat.mul_le_mul hm' ((Nat.totient_le m).trans hm')
    _ = q * (q * q) := by simp [Nat.card_Icc]
    _ = _ := by ring

theorem every_admissible_side_upper (D L : ℕ) (hL : 2 ≤ L)
    (hsize : L ≤ degreeSum ((D - 1) / (L - 1))) : L ^ 4 ≤ 8 * D ^ 3 := by
  let q := (D - 1) / (L - 1)
  have hLq : L ≤ q ^ 3 := hsize.trans (degreeSum_le_cube q)
  have hp : q * (L - 1) ≤ D - 1 := Nat.div_mul_le_self _ _
  have hql : q * L ≤ 2 * D := by
    have hL' : L ≤ 2 * (L - 1) := by omega
    have hm := Nat.mul_le_mul_left q hL'
    calc
      _ ≤ 2 * (q * (L - 1)) := by simpa [Nat.mul_left_comm] using hm
      _ ≤ 2 * (D - 1) := Nat.mul_le_mul_left 2 hp
      _ ≤ 2 * D := Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
  calc
    L ^ 4 = L * L ^ 3 := by ring
    _ ≤ q ^ 3 * L ^ 3 := Nat.mul_le_mul_right _ hLq
    _ = (q * L) ^ 3 := (mul_pow _ _ _).symm
    _ ≤ (2 * D) ^ 3 := Nat.pow_le_pow_left hql 3
    _ = _ := by ring

theorem inverse_exists_at_computed_window (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p) :
    ∃ onset : ℕ, ∀ lo₁ lo₂ : ℤ, onset ^ 4 ≤ window primes →
      ∃ B : Matrix (Fin (side (window primes)) × Fin (side (window primes)))
          (PairResidueRow (fun p : primes => p.val)) ℚ,
        leftInverseCheck (pairMatrix primes lo₁ lo₂ (side (window primes))) B = true := by
  obtain ⟨onset, _, h⟩ := side_is_admissible
  refine ⟨onset, ?_⟩
  intro lo₁ lo₂ hD
  obtain ⟨hL, hwindow⟩ := h (window primes) hD
  exact pair_inverse_exists primes hne hprime lo₁ lo₂ _ hL hwindow

end NearCubicGates.QuantitativePairWindow
