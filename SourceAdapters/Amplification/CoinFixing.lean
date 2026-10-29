import Mathlib

/-!
# A02 step (c): fixing the coins by majority (STV Remark 21)

STV text l.776–781 (Remark 21): "for computing functions, a majority vote of several runs can be used. … the success
probability can be increased to `1 − γ` with an `O(log(1/γ))` slowdown in efficiency. As a consequence, in a
nonuniform model of computation (e.g. circuits) we can set `γ = 1/|X|` and then fix the coin tosses of `A` to
obtain a deterministic procedure solving the same problem with only a `O(log|X|)` slowdown in efficiency (as in
[Adl78])." (`app:sources`, "Full-range amplification interface"): "The polynomial reconstruction overhead includes fixing the decoder's randomness."

`exists_majority_coins`: if on every input `x` (at most `2^n` of them) at least `3/4` of the coin strings are good
(STV Definition 20's success probability), then `N = 2(3n + 3)` coin strings exist on which, for **every** `x`,
fewer than `N/2` are bad (a strict majority is good). Proof: for each `x`, `Σ_{r⃗} 3^{#bad} = (Σ_r 3^{[bad r]})^N
≤ (3T/2)^N` (product over the `N` independent coordinates), so at most `T^N (3/4)^{N/2}` tuples have `#bad ≥ N/2`
(Markov); summed over the `≤ 2^n` inputs this is `< T^N` because `2^n (3/4)^{3n+3} < 1`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open Finset

theorem prod_three_pow {N : ℕ} (P : Fin N → Prop) [DecidablePred P] :
    ∏ i, (if P i then (3 : ℝ) else 1) = 3 ^ (univ.filter P).card := by
  rw [prod_ite, prod_const_one, mul_one, prod_const]

/-- **Coin fixing by majority.** -/
theorem exists_majority_coins {X C : Type} [Fintype X] [Fintype C] [Nonempty C] [DecidableEq C]
    (good : X → C → Prop) [∀ x, DecidablePred (good x)] (n : ℕ) (hX : Fintype.card X ≤ 2 ^ n)
    (hgood : ∀ x, 3 * Fintype.card C ≤ 4 * (univ.filter (good x)).card) :
    ∃ rs : Fin (2 * (3 * n + 3)) → C, ∀ x, (univ.filter fun i => ¬ good x (rs i)).card < 3 * n + 3 := by
  classical
  have hTpos : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast (Fintype.card_pos (α := C))
  have hbound : ∀ x, ((univ.filter fun rs : Fin (2 * (3 * n + 3)) → C =>
      3 * n + 3 ≤ (univ.filter fun i => ¬ good x (rs i)).card).card : ℝ) * 3 ^ (3 * n + 3) ≤
      (3 * (Fintype.card C : ℝ) / 2) ^ (2 * (3 * n + 3)) := by
    intro x
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset C)) (good x)
    have h2 := hgood x
    rw [card_univ] at h1
    have hb : (univ.filter fun r => ¬ good x r).card * 4 ≤ Fintype.card C := by omega
    have hbR : ((univ.filter fun r => ¬ good x r).card : ℝ) * 4 ≤ Fintype.card C := by exact_mod_cast hb
    have hsum : ∑ rs : Fin (2 * (3 * n + 3)) → C, ∏ i, (if ¬ good x (rs i) then (3 : ℝ) else 1) =
        ((Fintype.card C : ℝ) + 2 * (univ.filter fun r => ¬ good x r).card) ^ (2 * (3 * n + 3)) := by
      have h := sum_prod_piFinset (univ : Finset C)
        (fun (_ : Fin (2 * (3 * n + 3))) (r : C) => if ¬ good x r then (3 : ℝ) else 1)
      rw [Fintype.piFinset_univ] at h
      rw [h, prod_const, card_univ, Fintype.card_fin]
      congr 1
      rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
      have h3 := card_filter_add_card_filter_not (s := (univ : Finset C)) (fun r => ¬ good x r)
      rw [card_univ] at h3
      have h3' : ((univ.filter fun r => ¬ ¬ good x r).card : ℝ) =
          (Fintype.card C : ℝ) - (univ.filter fun r => ¬ good x r).card := by
        rw [eq_sub_iff_add_eq, add_comm]; exact_mod_cast h3
      rw [h3']; ring
    have hmono : ((univ.filter fun rs : Fin (2 * (3 * n + 3)) → C =>
        3 * n + 3 ≤ (univ.filter fun i => ¬ good x (rs i)).card).card : ℝ) * 3 ^ (3 * n + 3) ≤
        ∑ rs : Fin (2 * (3 * n + 3)) → C, ∏ i, (if ¬ good x (rs i) then (3 : ℝ) else 1) := by
      calc _ = ∑ _rs ∈ (univ.filter fun rs : Fin (2 * (3 * n + 3)) → C =>
            3 * n + 3 ≤ (univ.filter fun i => ¬ good x (rs i)).card), (3 : ℝ) ^ (3 * n + 3) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ rs ∈ (univ.filter fun rs : Fin (2 * (3 * n + 3)) → C =>
            3 * n + 3 ≤ (univ.filter fun i => ¬ good x (rs i)).card),
              ∏ i, (if ¬ good x (rs i) then (3 : ℝ) else 1) := by
            apply sum_le_sum
            intro rs hrs
            rw [prod_three_pow]
            exact pow_le_pow_right₀ (by norm_num) (mem_filter.mp hrs).2
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
    rw [hsum] at hmono
    exact hmono.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
  set fail : X → Finset (Fin (2 * (3 * n + 3)) → C) := fun x =>
    univ.filter fun rs => 3 * n + 3 ≤ (univ.filter fun i => ¬ good x (rs i)).card with hfail
  have h3 : (3 * (Fintype.card C : ℝ) / 2) ^ (2 * (3 * n + 3)) / 3 ^ (3 * n + 3) =
      (Fintype.card C : ℝ) ^ (2 * (3 * n + 3)) * (3 / 4) ^ (3 * n + 3) := by
    rw [div_eq_iff (by positivity), pow_mul, pow_mul, ← mul_pow, ← mul_pow]
    congr 1; ring
  have h4 : (Fintype.card X : ℝ) * (3 / 4) ^ (3 * n + 3) < 1 := by
    have hX' : (Fintype.card X : ℝ) ≤ 2 ^ n := by exact_mod_cast hX
    have h5 : ((3 : ℝ) / 4) ^ (3 * n + 3) = (27 / 64) ^ (n + 1) := by
      rw [show 3 * n + 3 = 3 * (n + 1) by ring, pow_mul]; norm_num
    have h6 : ((27 : ℝ) / 64) ^ (n + 1) ≤ (1 / 2) ^ (n + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h7 : (2 : ℝ) ^ n * (1 / 2) ^ (n + 1) = 1 / 2 := by
      rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
    calc (Fintype.card X : ℝ) * (3 / 4) ^ (3 * n + 3) ≤ 2 ^ n * (1 / 2) ^ (n + 1) := by
          rw [h5]; exact mul_le_mul hX' h6 (by positivity) (by positivity)
      _ < 1 := by rw [h7]; norm_num
  have hall : ((univ.biUnion fail).card : ℝ) < (Fintype.card C : ℝ) ^ (2 * (3 * n + 3)) := by
    have h1 : ((univ.biUnion fail).card : ℝ) ≤ ∑ x, ((fail x).card : ℝ) := by exact_mod_cast card_biUnion_le
    have h2 : ∑ x, ((fail x).card : ℝ) ≤
        Fintype.card X * ((3 * (Fintype.card C : ℝ) / 2) ^ (2 * (3 * n + 3)) / 3 ^ (3 * n + 3)) := by
      calc ∑ x, ((fail x).card : ℝ) ≤ ∑ _x : X,
            (3 * (Fintype.card C : ℝ) / 2) ^ (2 * (3 * n + 3)) / 3 ^ (3 * n + 3) := by
            apply sum_le_sum; intro x _
            rw [le_div_iff₀ (by positivity)]; exact hbound x
        _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
    rw [h3] at h2
    have hTN : (0 : ℝ) < (Fintype.card C : ℝ) ^ (2 * (3 * n + 3)) := by positivity
    nlinarith
  have hlt : (univ.biUnion fail).card < (univ : Finset (Fin (2 * (3 * n + 3)) → C)).card := by
    rw [card_univ, Fintype.card_fun, Fintype.card_fin]; exact_mod_cast hall
  obtain ⟨rs, -, hrs⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨rs, fun x => ?_⟩
  by_contra h
  push Not at h
  exact hrs (mem_biUnion.mpr ⟨x, mem_univ x, mem_filter.mpr ⟨mem_univ rs, h⟩⟩)

end NearCubicGates.Adapters.Amplification
