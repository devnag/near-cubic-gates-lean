import Mathlib

/-!
# A01 step 4 (inner code): the Hadamard code and its list-size bound (STV Lemma 27), proved

STV text l.861–868: "For a string z ∈ {0,1}^k, the Hadamard encoding of z is a 2^k-bit string Had(z) whose
positions are indexed by strings w ∈ {0,1}^k. The w-th coordinate of the encoding Had(z) is ⟨w,z⟩ = Σ_j w_j z_j
(mod 2) … Lemma 27 For every k, Had : {0,1}^k → {0,1}^{2^k} is a (ε, 1/(4ε²)) list-decodable code for all ε > 0."

By Definition 18 (text l.717–719) with `q = 2`: at most `1/(4ε²)` codewords agree with any received word on a
`1/2 + ε` fraction. `hadamard_list_bound` proves it (no leaf needed): the correlations `Σ_u (−1)^{r(u)+⟨a,u⟩}` of
the `2^t` codewords have squares summing to `4^t` (orthogonality of characters), and each listed codeword has
correlation at least `2ε·2^t`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open Finset

variable {t : ℕ}

/-- The Hadamard bit `⟨a, u⟩ mod 2`. -/
def had (a u : Fin t → Bool) : Bool := decide ((univ.filter fun s => a s && u s).card % 2 = 1)

/-- `±1` of a bit. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

theorem sgn_mul_sgn (x y : Bool) : sgn x * sgn y = if x = y then 1 else -1 := by
  cases x <;> cases y <;> simp [sgn]

theorem sgn_sq (x : Bool) : sgn x * sgn x = 1 := by cases x <;> simp [sgn]

/-- The character `(−1)^{⟨a,u⟩}` as a product over coordinates. -/
theorem sgn_had (a u : Fin t → Bool) :
    sgn (had a u) = ∏ s, (if (a s && u s) = true then (-1 : ℝ) else 1) := by
  rw [prod_ite, prod_const_one, mul_one, prod_const]
  unfold had sgn
  set n := (univ.filter fun s => a s && u s).card
  rcases Nat.even_or_odd n with h | h
  · have h2 : n % 2 = 0 := Nat.even_iff.mp h
    simp [h2, h.neg_one_pow]
  · have h2 : n % 2 = 1 := Nat.odd_iff.mp h
    simp [h2, h.neg_one_pow]

/-- **Orthogonality**: `Σ_a (−1)^{⟨a,u⟩+⟨a,v⟩} = 2^t·[u = v]`. -/
theorem sum_sgn_had_mul (u v : Fin t → Bool) :
    ∑ a : Fin t → Bool, sgn (had a u) * sgn (had a v) = if u = v then (2 : ℝ) ^ t else 0 := by
  have h1 : ∀ a : Fin t → Bool, sgn (had a u) * sgn (had a v) =
      ∏ s, ((if (a s && u s) = true then (-1 : ℝ) else 1) * (if (a s && v s) = true then (-1 : ℝ) else 1)) := by
    intro a; rw [sgn_had, sgn_had, ← prod_mul_distrib]
  simp_rw [h1]
  have h2 := sum_prod_piFinset (univ : Finset Bool)
    (fun s (b : Bool) => (if (b && u s) = true then (-1 : ℝ) else 1) * (if (b && v s) = true then (-1 : ℝ) else 1))
  rw [Fintype.piFinset_univ] at h2
  rw [h2]
  have h3 : ∀ s, ∑ b : Bool, (if (b && u s) = true then (-1 : ℝ) else 1) * (if (b && v s) = true then (-1 : ℝ) else 1)
      = if u s = v s then 2 else 0 := by
    intro s
    rw [Fintype.sum_bool]
    cases u s <;> cases v s <;> norm_num
  simp_rw [h3]
  by_cases huv : u = v
  · subst huv; simp
  · rw [if_neg huv]
    obtain ⟨s, hs⟩ : ∃ s, u s ≠ v s := Function.ne_iff.mp huv
    exact prod_eq_zero (mem_univ s) (if_neg hs)

/-- The correlation of `r` with the codeword of `a`. -/
noncomputable def corr (r : (Fin t → Bool) → Bool) (a : Fin t → Bool) : ℝ :=
  ∑ u, sgn (r u) * sgn (had a u)

/-- **Parseval**: the squared correlations sum to `4^t`. -/
theorem sum_corr_sq (r : (Fin t → Bool) → Bool) : ∑ a, corr r a ^ 2 = (4 : ℝ) ^ t := by
  have h : ∀ a, corr r a ^ 2 = ∑ u, ∑ v, (sgn (r u) * sgn (r v)) * (sgn (had a u) * sgn (had a v)) := by
    intro a
    rw [corr, sq, sum_mul_sum]
    refine sum_congr rfl (fun u _ => sum_congr rfl (fun v _ => by ring))
  simp_rw [h]
  rw [sum_comm]
  have h2 : ∀ u : Fin t → Bool, ∑ a : Fin t → Bool, ∑ v : Fin t → Bool,
      (sgn (r u) * sgn (r v)) * (sgn (had a u) * sgn (had a v)) = (2 : ℝ) ^ t := by
    intro u
    rw [sum_comm]
    simp_rw [← mul_sum, sum_sgn_had_mul]
    simp [sgn_sq]
  simp_rw [h2]
  rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [← mul_pow]; norm_num

/-- The number of positions where `r` agrees with the codeword of `a`. -/
def agreeCount (r : (Fin t → Bool) → Bool) (a : Fin t → Bool) : ℕ :=
  (univ.filter fun u => r u = had a u).card

/-- The correlation is `2·(agreements) − 2^t`. -/
theorem corr_eq (r : (Fin t → Bool) → Bool) (a : Fin t → Bool) :
    corr r a = 2 * (agreeCount r a : ℝ) - 2 ^ t := by
  unfold corr agreeCount
  simp_rw [sgn_mul_sgn]
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_neg, mul_one]
  have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin t → Bool)))
    (fun u => r u = had a u)
  rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hc
  have hc' : ((univ.filter fun u => ¬ r u = had a u).card : ℝ) =
      2 ^ t - ((univ.filter fun u => r u = had a u).card : ℝ) := by
    rw [eq_sub_iff_add_eq, add_comm]; exact_mod_cast hc
  rw [hc']; ring

/-- **STV Lemma 27** (proved): at most `1/(4η²)` Hadamard codewords agree with any received word on at least a
`1/2 + η` fraction of the `2^t` positions. -/
theorem hadamard_list_bound (r : (Fin t → Bool) → Bool) (η : ℝ) (hη : 0 < η) :
    (((univ : Finset (Fin t → Bool)).filter fun a => (1 / 2 + η) * 2 ^ t ≤ (agreeCount r a : ℝ)).card : ℝ) ≤
      1 / (4 * η ^ 2) := by
  set L := (univ : Finset (Fin t → Bool)).filter fun a => (1 / 2 + η) * 2 ^ t ≤ (agreeCount r a : ℝ)
  have h4 : (0 : ℝ) < 4 ^ t := by positivity
  have hmem : ∀ a ∈ L, 4 * η ^ 2 * 4 ^ t ≤ corr r a ^ 2 := by
    intro a ha
    have ha' := (mem_filter.mp ha).2
    have hc : 2 * η * 2 ^ t ≤ corr r a := by rw [corr_eq]; linarith
    have hp : 0 ≤ 2 * η * 2 ^ t := by positivity
    have h44 : (4 : ℝ) ^ t = 2 ^ t * 2 ^ t := by rw [← mul_pow]; norm_num
    rw [h44]
    nlinarith
  have hsum : (L.card : ℝ) * (4 * η ^ 2 * 4 ^ t) ≤ 4 ^ t := by
    calc (L.card : ℝ) * (4 * η ^ 2 * 4 ^ t) = ∑ _a ∈ L, 4 * η ^ 2 * 4 ^ t := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ L, corr r a ^ 2 := sum_le_sum hmem
      _ ≤ ∑ a, corr r a ^ 2 := sum_le_sum_of_subset_of_nonneg (subset_univ L) (fun _ _ _ => sq_nonneg _)
      _ = 4 ^ t := sum_corr_sq r
  have hpos : 0 < 4 * η ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  nlinarith

end NearCubicGates.Adapters.Amplification
