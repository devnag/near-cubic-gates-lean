import Mathlib
import Proof.Wire_3_5.TraceBias

/-!
# X4 (part ii): Walsh–Fourier analysis on `{0,1}^r` and the hitting property of small-bias sets

`lem:small-bias`, part (ii): "If `S` is `ε`-biased and `𝓑 ⊆ {0,1}^r` has density `μ > 0`, then the
set of `R ∈ {0,1}^r` with `R ⊕ σ ∉ 𝓑` for every `σ ∈ S` has density at most `ε²/μ`." Proof as printed
: `g(R) = E_{σ∈S} 1_𝓑(R ⊕ σ)`, `ĝ(α) = 1̂_𝓑(α)·E_σ (−1)^{α·σ}`, Parseval.

A multiset `S` is an index type `ι` with `σ : ι → {0,1}^r` (repeated vectors keep their multiplicity).
Self-contained (no Mathlib `AddChar`): the characters are `χ_α(x) = ∏_j (−1)^{α_j x_j}`.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ShortPCP.SmallBias

open Finset

variable {r : ℕ}

/-- `(−1)^{α·x}` over `𝔽₂` (proof of `lem:small-bias`: "`α·σ` for the inner product over `𝔽₂`"). -/
def chi (α x : Fin r → Bool) : ℝ := ∏ j, if α j && x j then -1 else 1

/-- **Orthogonality**: `Σ_α χ_α(x) = 2^r` if `x = 0`, else `0`. -/
theorem sum_chi (x : Fin r → Bool) :
    ∑ α : Fin r → Bool, chi α x = if x = fun _ => false then (2 : ℝ) ^ r else 0 := by
  unfold chi
  have h : ∑ α : Fin r → Bool, ∏ j, (if α j && x j then (-1 : ℝ) else 1) =
      ∏ j : Fin r, ∑ a : Bool, (if a && x j then (-1 : ℝ) else 1) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [h]
  split_ifs with hx
  · subst hx; simp
  · obtain ⟨j, hj⟩ : ∃ j, x j = true := by
      by_contra hc; push Not at hc; apply hx; funext j; simpa using hc j
    apply Finset.prod_eq_zero (mem_univ j)
    simp [hj]

/-- Coordinatewise xor `R ⊕ σ`. -/
def vxor (x y : Fin r → Bool) : Fin r → Bool := fun j => xor (x j) (y j)

theorem chi_vxor (α x y : Fin r → Bool) : chi α (vxor x y) = chi α x * chi α y := by
  unfold chi vxor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  cases α j <;> cases x j <;> cases y j <;> norm_num

theorem chi_comm (α x : Fin r → Bool) : chi α x = chi x α := by
  unfold chi
  apply Finset.prod_congr rfl
  intro j _
  rw [Bool.and_comm]

theorem vxor_vxor (x s : Fin r → Bool) : vxor (vxor x s) s = x := by
  funext j; simp [vxor]

/-- Translation by `s` as a permutation of `{0,1}^r`. -/
def shiftEquiv (s : Fin r → Bool) : (Fin r → Bool) ≃ (Fin r → Bool) where
  toFun x := vxor x s
  invFun x := vxor x s
  left_inv x := vxor_vxor x s
  right_inv x := vxor_vxor x s

theorem sum_chi_mul (x y : Fin r → Bool) :
    ∑ α : Fin r → Bool, chi α x * chi α y = if x = y then (2 : ℝ) ^ r else 0 := by
  simp only [← chi_vxor, sum_chi]
  have : (vxor x y = fun _ => false) ↔ x = y := by
    constructor
    · intro h; funext j; have := congrFun h j; simp only [vxor] at this; cases hx : x j <;> cases hy : y j <;> simp_all
    · rintro rfl; funext j; simp [vxor]
  simp only [this]

/-- **Parseval**: `Σ_α (Σ_x h(x)χ_α(x))² = 2^r Σ_x h(x)²`. -/
theorem sum_sq_sum (h : (Fin r → Bool) → ℝ) :
    ∑ α : Fin r → Bool, (∑ x, h x * chi α x) ^ 2 = 2 ^ r * ∑ x, h x ^ 2 := by
  calc ∑ α : Fin r → Bool, (∑ x, h x * chi α x) ^ 2
      = ∑ α : Fin r → Bool, ∑ x, ∑ y, h x * h y * (chi α x * chi α y) := by
        apply sum_congr rfl; intro α _
        rw [sq, Finset.sum_mul_sum]
        apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; ring
    _ = ∑ x, ∑ y, h x * h y * ∑ α : Fin r → Bool, chi α x * chi α y := by
        rw [Finset.sum_comm]; apply sum_congr rfl; intro x _
        rw [Finset.sum_comm]; apply sum_congr rfl; intro y _
        rw [Finset.mul_sum]
    _ = ∑ x, h x * h x * 2 ^ r := by
        apply sum_congr rfl; intro x _
        simp only [sum_chi_mul]
        rw [Finset.sum_eq_single x]
        · simp
        · intro y _ hy; simp [Ne.symm hy]
        · simp
    _ = 2 ^ r * ∑ x, h x ^ 2 := by rw [Finset.mul_sum]; apply sum_congr rfl; intro x _; ring

/-- **Hitting property** (`lem:small-bias`(ii),, proof ). -/
theorem hitting {ι : Type} [Fintype ι] [Nonempty ι] (σ : ι → (Fin r → Bool)) (ε : ℝ)
    (hbias : ∀ α : Fin r → Bool, α ≠ (fun _ => false) →
      |(∑ i, chi α (σ i)) / (Fintype.card ι : ℝ)| ≤ ε)
    (B : Finset (Fin r → Bool)) (hB : B.Nonempty) :
    ((univ.filter fun R => ∀ i, vxor R (σ i) ∉ B).card : ℝ) / 2 ^ r ≤ ε ^ 2 / ((B.card : ℝ) / 2 ^ r) := by
  classical
  set N : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  set ind : (Fin r → Bool) → ℝ := fun x => if x ∈ B then 1 else 0 with hind
  set μ : ℝ := (B.card : ℝ) / 2 ^ r with hμ
  set g : (Fin r → Bool) → ℝ := fun R => (∑ i, ind (vxor R (σ i))) / N with hg
  set h : (Fin r → Bool) → ℝ := fun R => g R - μ with hh
  -- (b) the transform of g
  have hshift : ∀ (α s : Fin r → Bool),
      ∑ x, ind (vxor x s) * chi α x = chi α s * ∑ y, ind y * chi α y := by
    intro α s
    rw [← Equiv.sum_comp (shiftEquiv s)]
    simp only [shiftEquiv, Equiv.coe_fn_mk, vxor_vxor, chi_vxor, Finset.mul_sum]
    apply sum_congr rfl; intro y _; ring
  have hgchi : ∀ α, ∑ x, g x * chi α x = (∑ i, chi α (σ i)) / N * ∑ y, ind y * chi α y := by
    intro α
    simp only [hg, div_mul_eq_mul_div, Finset.sum_mul, ← Finset.sum_div]
    rw [Finset.sum_comm]
    simp only [hshift, ← Finset.sum_mul]
  have hsumind : ∑ y, ind y = B.card := by simp [hind]
  have hhchi : ∀ α, (∑ x, h x * chi α x) ^ 2 ≤ ε ^ 2 * (∑ y, ind y * chi α y) ^ 2 := by
    intro α
    by_cases hα : α = fun _ => false
    · subst hα
      have : ∑ x, h x * chi (fun _ => false) x = 0 := by
        simp only [hh, sub_mul, Finset.sum_sub_distrib, hgchi]
        simp [chi, hsumind, hμ]
        have hc : (Fintype.card ι : ℝ) ≠ 0 := by rw [← hN]; exact hNpos.ne'
        rw [hN]; field_simp; ring
      rw [this]
      have : 0 ≤ ε ^ 2 * (∑ y, ind y * chi (fun _ => false) y) ^ 2 := by positivity
      simpa using this
    · have hsplit : ∑ x, h x * chi α x = ∑ x, g x * chi α x := by
        simp only [hh, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
        have : ∑ x, chi α x = 0 := by
          rw [show (∑ x, chi α x) = ∑ x, chi x α from sum_congr rfl fun x _ => chi_comm α x, sum_chi, if_neg hα]
        rw [this, mul_zero, sub_zero]
      rw [hsplit, hgchi, mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbias α hα) 2
  have hparsB : ∑ α : Fin r → Bool, (∑ y, ind y * chi α y) ^ 2 = 2 ^ r * B.card := by
    rw [sum_sq_sum]
    congr 1
    rw [← hsumind]
    apply sum_congr rfl; intro y _; simp only [hind]; split_ifs <;> norm_num
  have hbound : 2 ^ r * ∑ x, h x ^ 2 ≤ ε ^ 2 * (2 ^ r * B.card) := by
    rw [← sum_sq_sum, ← hparsB, Finset.mul_sum]
    exact sum_le_sum fun α _ => hhchi α
  have hsq : ∑ x, h x ^ 2 ≤ ε ^ 2 * B.card := by nlinarith
  -- (e) on the set in question, g = 0 and h² = μ²
  set Z := univ.filter fun R => ∀ i, vxor R (σ i) ∉ B
  have hZ : (Z.card : ℝ) * μ ^ 2 ≤ ∑ x, h x ^ 2 := by
    calc (Z.card : ℝ) * μ ^ 2 = ∑ x ∈ Z, μ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ x ∈ Z, h x ^ 2 := by
          apply sum_congr rfl; intro x hx
          simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have : g x = 0 := by
            simp only [hg, hind]
            rw [Finset.sum_eq_zero (fun i _ => by simp [hx i]), zero_div]
          simp [hh, this]
      _ ≤ ∑ x, h x ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => sq_nonneg _
  have hμpos : 0 < μ := by rw [hμ]; positivity
  rw [le_div_iff₀ hμpos, div_mul_eq_mul_div, div_le_iff₀ h2r]
  have : (Z.card : ℝ) * μ ^ 2 ≤ ε ^ 2 * B.card := hZ.trans hsq
  rw [hμ] at this ⊢
  field_simp at this ⊢
  nlinarith

/-! ## X4 (part i): the powering construction (proof of `lem:small-bias`) -/

section Powering

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- `(−1)^b`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

theorem sgn_xor (x y : Bool) : sgn (xor x y) = sgn x * sgn y := by
  cases x <;> cases y <;> norm_num [sgn]

/-- The vectors `σ_{a,b}` of the powering construction: "`σ_{a,b} ∈ {0,1}^r` have coordinates `a^j·b`,
`0 ≤ j < r`" (proof of `lem:small-bias`), for a bilinear `𝔽₂`-pairing `β` on `K` ("identify `𝔽_{2^m}` with `𝔽₂^m`"). -/
def powVec (β : K → K → Bool) (r : ℕ) (ab : K × K) : Fin r → Bool := fun j => β (ab.1 ^ j.val) ab.2

omit [Fintype K] [DecidableEq K] in
theorem chi_powVec (β : K → K → Bool) (hadd : ∀ u v w, β (u + v) w = xor (β u w) (β v w)) (r : ℕ)
    (α : Fin r → Bool) (a b : K) :
    chi α (powVec β r (a, b)) =
      sgn (β ((NearCubicWires.WireExponent3_5.Shared.selectorPoly
        ((univ.filter fun j : Fin r => α j = true).map Fin.valEmbedding)).eval a) b) := by
  have h0 : ∀ w, β 0 w = false := by
    intro w; have := hadd 0 0 w; rw [add_zero] at this; cases h : β 0 w <;> simp_all
  have hsum : ∀ (s : Finset (Fin r)), sgn (β (∑ j ∈ s, a ^ j.val) b) = ∏ j ∈ s, sgn (β (a ^ j.val) b) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [h0, sgn]
    | insert j s hj ih => rw [Finset.sum_insert hj, hadd, sgn_xor, ih, Finset.prod_insert hj]
  simp only [NearCubicWires.WireExponent3_5.Shared.selectorPoly, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, Polynomial.eval_X, Finset.sum_map, Fin.valEmbedding_apply]
  rw [hsum, chi, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _
  cases α j <;> simp [powVec, sgn]

/-- **Bias of the powering construction** (proof of `lem:small-bias`): for nonzero `α`, `|E_{a,b}(−1)^{α·σ_{a,b}}|` is the
fraction of `a` with `p_α(a) = 0`, at most `r/|K|`. -/
theorem powering_bias (β : K → K → Bool) (hadd : ∀ u v w, β (u + v) w = xor (β u w) (β v w))
    (hbal : ∀ u, u ≠ 0 → ∑ w, sgn (β u w) = 0) (r : ℕ) (α : Fin r → Bool) (hα : α ≠ fun _ => false) :
    |(∑ ab : K × K, chi α (powVec β r ab)) / (Fintype.card (K × K) : ℝ)| ≤ r / Fintype.card K := by
  have h0 : ∀ w, β 0 w = false := by
    intro w; have := hadd 0 0 w; rw [add_zero] at this; cases h : β 0 w <;> simp_all
  set J := (univ.filter fun j : Fin r => α j = true).map Fin.valEmbedding with hJ
  set P := NearCubicWires.WireExponent3_5.Shared.selectorPoly (K := K) J
  have hJne : J.Nonempty := by
    obtain ⟨j, hj⟩ : ∃ j, α j = true := by
      by_contra hc; push Not at hc; apply hα; funext j; simpa using hc j
    exact ⟨j.val, by simp only [hJ, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨j, hj, rfl⟩⟩
  have hJM : ∀ i ∈ J, i ≤ r := by
    intro i hi; simp only [hJ, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at hi
    obtain ⟨j, _, rfl⟩ := hi; exact j.isLt.le
  have hZ := NearCubicWires.WireExponent3_5.Shared.card_zeros_le (K := K) J hJne r hJM
  have hrow : ∀ a : K, ∑ b, sgn (β (P.eval a) b) = if P.eval a = 0 then (Fintype.card K : ℝ) else 0 := by
    intro a
    split_ifs with h
    · simp [h, h0, sgn]
    · exact hbal _ h
  have htot : ∑ ab : K × K, chi α (powVec β r ab) =
      (Fintype.card K : ℝ) * ((univ.filter fun v : K => P.eval v = 0).card : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp only [chi_powVec β hadd]
    show ∑ a, ∑ b, sgn (β (P.eval a) b) = _
    simp only [hrow]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hK : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  rw [htot, Fintype.card_prod, Nat.cast_mul, abs_div, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
    mul_div_mul_left _ _ hK.ne']
  exact div_le_div_of_nonneg_right (by exact_mod_cast hZ) hK.le

end Powering

end NearCubicGates.Adapters.ShortPCP.SmallBias
