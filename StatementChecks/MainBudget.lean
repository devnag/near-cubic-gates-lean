import Statement

/-! # The integer budget is exactly the paper's floor budget

A check of `MainBudget` in the trusted statement against the boxed budget of the main theorem
(`paper/paper.tex:212-225`, `thm:main`):

  `W(C) ≤ ⌊n^3 / (K_d · λ_n^(21/4) · μ_n^7)⌋`,  with `λ_n = ⌈log₂ n⌉`, `μ_n = ⌈log₂ λ_n⌉` for `n ≥ 4`
  (`paper/paper.tex:202-205`).

`Statement.lean` states the budget without real division or fractional powers, as
`(K·W·μ^7)^4 · λ^21 ≤ n^12` (`SourceMapping/main-theorem.md`, item 5). A skeptic should ask whether this
integer form allows more or fewer circuits than the paper's, and whether it allows any nonconstant circuit
at all. This module proves:

* `mainBudget_iff_floor`: for `n ≥ 4` and `K > 0` the two forms are equivalent, with the paper's real
  power `λ^(21/4)` and the natural floor `⌊·⌋₊`.
* `lambda_ge_two`, `mu_ge_one`: for `n ≥ 4` every denominator is positive.
* `mainBudget_eventually`: for every fixed `K` and every fixed top weight `W`, the budget allows `W` at
  every sufficiently large `n`, so the conclusion constrains circuits of every fixed size.
* `mu_eq_zero_of_le_two`, `mainBudget_of_le_two`: the only edge case. At `n ≤ 2` the integer form allows
  every circuit; the main theorem's onset is at least 4, so this case never enters it.
-/

namespace NearCubicGates.StatementChecks.MainBudget

open NearCubicGates.Target
open Filter Topology

set_option autoImplicit false

/-- For `n ≥ 4`, `λ_n = ⌈log₂ n⌉ ≥ 2`. -/
theorem lambda_ge_two {n : ℕ} (hn : 4 ≤ n) : 2 ≤ lambda n := by
  have h4 : Nat.clog 2 4 = 2 := by norm_num
  calc 2 = Nat.clog 2 4 := h4.symm
    _ ≤ Nat.clog 2 n := Nat.clog_mono_right 2 hn

/-- For `n ≥ 4`, `μ_n = ⌈log₂ λ_n⌉ ≥ 1`. -/
theorem mu_ge_one {n : ℕ} (hn : 4 ≤ n) : 1 ≤ mu n := by
  have h2 : Nat.clog 2 2 = 1 := by norm_num
  calc 1 = Nat.clog 2 2 := h2.symm
    _ ≤ Nat.clog 2 (lambda n) := Nat.clog_mono_right 2 (lambda_ge_two hn)

/-- For `n ≥ 4` and `K > 0`, `MainBudget K n w` holds exactly when
`w ≤ ⌊n^3 / (K · λ_n^(21/4) · μ_n^7)⌋₊`, the paper's boxed budget. -/
theorem mainBudget_iff_floor {K n w : ℕ} (hK : 0 < K) (hn : 4 ≤ n) :
    MainBudget K n w ↔
      w ≤ ⌊(n : ℝ) ^ 3 / ((K : ℝ) * (lambda n : ℝ) ^ ((21 : ℝ) / 4) * (mu n : ℝ) ^ 7)⌋₊ := by
  have hL : (0 : ℝ) < lambda n := by
    have := lambda_ge_two hn
    exact_mod_cast (show 0 < lambda n by omega)
  have hM : (0 : ℝ) < mu n := by
    have := mu_ge_one hn
    exact_mod_cast (show 0 < mu n by omega)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set Lr : ℝ := (lambda n : ℝ) ^ ((21 : ℝ) / 4) with hLr
  have hLr0 : 0 < Lr := Real.rpow_pos_of_pos hL _
  have hLr4 : Lr ^ (4 : ℕ) = (lambda n : ℝ) ^ (21 : ℕ) := by
    rw [hLr, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  have hden : 0 < (K : ℝ) * Lr * (mu n : ℝ) ^ 7 := by positivity
  rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hden]
  have key : ((w : ℝ) * ((K : ℝ) * Lr * (mu n : ℝ) ^ 7)) ^ (4 : ℕ)
      = (((K * w * mu n ^ 7) ^ 4 * lambda n ^ 21 : ℕ) : ℝ) := by
    push_cast
    rw [← hLr4]
    ring
  have hn3 : ((n : ℝ) ^ 3) ^ (4 : ℕ) = ((n ^ 12 : ℕ) : ℝ) := by
    push_cast
    ring
  unfold MainBudget
  rw [← Nat.cast_le (α := ℝ), ← key, ← hn3]
  exact pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)

/-- The budget is downward closed in the top weight. -/
theorem mainBudget_mono {K n w w' : ℕ} (hw : w ≤ w') (h : MainBudget K n w') :
    MainBudget K n w := by
  unfold MainBudget at h ⊢
  calc (K * w * mu n ^ 7) ^ 4 * lambda n ^ 21 ≤ (K * w' * mu n ^ 7) ^ 4 * lambda n ^ 21 := by
        gcongr
    _ ≤ n ^ 12 := h

/-- For every fixed `K` and top weight `w`, the budget allows `w` at every sufficiently large `n`. -/
theorem mainBudget_eventually (K w : ℕ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → MainBudget K n w := by
  set c : ℕ := (K * w) ^ 4 with hc
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 49 (show (1 : ℝ) < 2 ^ 12 by norm_num)
  have hev := hlim.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / ((c : ℝ) * 2 ^ 12 + 1) by positivity))
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 4 (2 ^ (L + 1)), fun n hn => ?_⟩
  have hn4 : 4 ≤ n := le_trans (le_max_left _ _) hn
  have hnL : 2 ^ (L + 1) ≤ n := le_trans (le_max_right _ _) hn
  set k := lambda n with hk
  have hLk : L + 1 ≤ k := by
    have := Nat.clog_mono_right 2 hnL
    rwa [Nat.clog_pow 2 (L + 1) one_lt_two] at this
  have hmu : mu n ≤ k := by
    show Nat.clog 2 k ≤ k
    exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hpow : 2 ^ (k - 1) < n := by
    have := Nat.pow_pred_clog_lt_self one_lt_two (show 1 < n by omega)
    rw [hk]
    exact this
  have hk49 := hL k (by omega)
  have hpoly : c * k ^ 49 * 2 ^ 12 < 2 ^ 12 * (2 ^ (k - 1)) ^ 12 := by
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ 12) ^ k := by positivity
    have hcpos : (0 : ℝ) < (c : ℝ) * 2 ^ 12 + 1 := by positivity
    rw [div_lt_div_iff₀ hpos hcpos, one_mul] at hk49
    have hsplit : (2 : ℕ) ^ 12 * (2 ^ (k - 1)) ^ 12 = (2 ^ 12) ^ k := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      omega
    rw [hsplit]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) ^ 49 := by positivity
    have hexp : (k : ℝ) ^ 49 * ((c : ℝ) * 2 ^ 12 + 1) = (c : ℝ) * (k : ℝ) ^ 49 * 2 ^ 12 + (k : ℝ) ^ 49 := by
      ring
    have hlt : (c : ℝ) * (k : ℝ) ^ 49 * 2 ^ 12 < ((2 : ℝ) ^ 12) ^ k := by linarith
    exact_mod_cast hlt
  unfold MainBudget
  calc (K * w * mu n ^ 7) ^ 4 * lambda n ^ 21 = c * mu n ^ 28 * k ^ 21 := by
        rw [hc, hk]
        ring
    _ ≤ c * k ^ 28 * k ^ 21 := by gcongr
    _ = c * k ^ 49 := by ring
    _ ≤ (2 ^ (k - 1)) ^ 12 := by
        have h' : 2 ^ 12 * (c * k ^ 49) < 2 ^ 12 * (2 ^ (k - 1)) ^ 12 := by
          rw [mul_comm (2 ^ 12) (c * k ^ 49)]
          exact hpoly
        exact (Nat.lt_of_mul_lt_mul_left h').le
    _ ≤ n ^ 12 := Nat.pow_le_pow_left hpow.le 12

/-- At `n ≤ 2`, `μ_n = 0`. -/
theorem mu_eq_zero_of_le_two {n : ℕ} (hn : n ≤ 2) : mu n = 0 := by
  have hl : lambda n ≤ 1 := by
    show Nat.clog 2 n ≤ 1
    exact Nat.clog_le_of_le_pow (by omega)
  exact Nat.clog_of_right_le_one hl 2

/-- At `n ≤ 2` the integer form allows every top weight; the onset of `MainAt` is at least 4, so this case never enters the theorem. -/
theorem mainBudget_of_le_two (K w : ℕ) {n : ℕ} (hn : n ≤ 2) : MainBudget K n w := by
  unfold MainBudget
  rw [mu_eq_zero_of_le_two hn]
  simp

end NearCubicGates.StatementChecks.MainBudget
