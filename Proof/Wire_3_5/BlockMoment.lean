import Mathlib

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open Finset

variable {N : ℕ}

abbrev Cell (N : ℕ) := Fin N × Fin N

/-- The centred one-sample contribution to cell `c`. -/
def yc (N : ℕ) (s c : Cell N) : ℝ := 1 - (N : ℝ) ^ 2 * (if s = c then 1 else 0)

theorem prod_yc_eq (s : Cell N) (cs : List (Cell N)) :
    (cs.map (yc N s)).prod = (1 - (N : ℝ) ^ 2) ^ cs.count s := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, List.prod_cons, ih, List.count_cons]
    by_cases h : s = c
    · subst h; simp [yc, pow_succ, mul_comm]
    · simp [yc, h, Ne.symm h]

/-- Exact one-sample block sum. -/
theorem block_sum_eq (cs : List (Cell N)) :
    ∑ s : Cell N, (cs.map (yc N s)).prod =
      ((N : ℝ) ^ 2 - cs.toFinset.card) + ∑ d ∈ cs.toFinset, (1 - (N : ℝ) ^ 2) ^ cs.count d := by
  simp only [prod_yc_eq]
  rw [← Finset.sum_add_sum_compl cs.toFinset]
  have hcompl : ∑ s ∈ cs.toFinsetᶜ, (1 - (N : ℝ) ^ 2) ^ cs.count s = (N : ℝ) ^ 2 - cs.toFinset.card := by
    have : ∀ s ∈ cs.toFinsetᶜ, (1 - (N : ℝ) ^ 2) ^ cs.count s = 1 := by
      intro s hs
      rw [Finset.mem_compl, List.mem_toFinset] at hs
      rw [List.count_eq_zero_of_not_mem hs, pow_zero]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_compl, nsmul_eq_mul, mul_one]
    have hle : cs.toFinset.card ≤ N * N := by
      have := Finset.card_le_univ cs.toFinset; simpa [Fintype.card_prod, Fintype.card_fin] using this
    simp only [Fintype.card_prod, Fintype.card_fin]
    rw [Nat.cast_sub hle, Nat.cast_mul, sq]
  rw [hcompl]; ring

/-- Centring: a sample index read by a single edge contributes zero. -/
theorem block_sum_singleton (c : Cell N) : ∑ s : Cell N, ([c].map (yc N s)).prod = 0 := by
  rw [block_sum_eq]; simp

/-- The block bound used in the walk sum. -/
theorem block_sum_abs_le (cs : List (Cell N)) :
    |∑ s : Cell N, (cs.map (yc N s)).prod| ≤
      (N : ℝ) ^ 2 + ∑ d ∈ cs.toFinset, ((N : ℝ) ^ 2 - 1) ^ cs.count d := by
  rw [block_sum_eq]
  have hN : (cs.toFinset.card : ℝ) ≤ (N : ℝ) ^ 2 := by
    have := Finset.card_le_univ cs.toFinset
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    exact_mod_cast (show cs.toFinset.card ≤ N ^ 2 by rw [sq]; exact this)
  calc _ ≤ |(N : ℝ) ^ 2 - cs.toFinset.card| + |∑ d ∈ cs.toFinset, (1 - (N : ℝ) ^ 2) ^ cs.count d| :=
        abs_add_le _ _
    _ ≤ (N : ℝ) ^ 2 + ∑ d ∈ cs.toFinset, ((N : ℝ) ^ 2 - 1) ^ cs.count d := by
        apply add_le_add
        · rw [abs_of_nonneg (by linarith)]; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ cs.toFinset.card)]
        · calc _ ≤ ∑ d ∈ cs.toFinset, |(1 - (N : ℝ) ^ 2) ^ cs.count d| := Finset.abs_sum_le_sum_abs _ _
            _ = _ := by
              apply Finset.sum_congr rfl; intro d _
              rw [abs_pow, abs_sub_comm, abs_of_nonneg]
              rcases Nat.eq_zero_or_pos N with h | h
              · subst h; exact d.1.elim0
              · have : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by
                  have : (1 : ℝ) ≤ N := by exact_mod_cast h
                  nlinarith
                linarith

/-- Independence: a product of functions of distinct sample coordinates averages to the product of the
one-sample averages (the factorization over the sample-index partition `α`). -/
theorem sum_prod_fiber {Q : ℕ} {K : ℕ} (α : Fin K → Fin Q) (f : Fin K → Cell N → ℝ) :
    ∑ S : Fin Q → Cell N, ∏ k, f k (S (α k)) = ∏ j, ∑ s : Cell N, ∏ k ∈ univ.filter (fun k => α k = j), f k s := by
  classical
  have hfib : ∀ S : Fin Q → Cell N, ∏ k, f k (S (α k)) = ∏ j, ∏ k ∈ univ.filter (fun k => α k = j), f k (S j) := by
    intro S
    rw [← Finset.prod_fiberwise univ α (fun k => f k (S (α k)))]
    apply Finset.prod_congr rfl; intro j _
    apply Finset.prod_congr rfl; intro k hk
    rw [(Finset.mem_filter.mp hk).2]
  simp only [hfib]
  exact (Finset.prod_univ_sum (fun _ => univ) (fun j s => ∏ k ∈ univ.filter (fun k => α k = j), f k s)).symm.trans
    (by simp)

end NearCubicWires.WireExponent3_5.Shared
