import NineInputs

/-!
# The single-run proximity verifiers as an abstract interface

The proof of `thm:short-pcp-ours`, Step 2, uses perfect completeness and strong
soundness from BCGT13 Definition 4.15 and Theorem 11.1. `StrongPCPP F S code s`
packages them: every codeword has a proof accepted on every random string, and
a table at distance at least δ from the code is rejected with probability at
least s·δ.

`rsOfLeaf` and `vrsOfLeaf` instantiate this interface with the transcribed
`V_RS` and `V_VRS`, under the stated valid-tuple and positive-exponent hypotheses.
Their acceptance functions are the transcribed ones, also used by the machines.

`prefix_count` proves that a test reading the first k bits of a uniform r-bit
string, k ≤ r, has the same acceptance fraction as on its own uniform k-bit
coins. This supplies the shared-random-string convention of Step 2.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open Finset NearCubicGates.Published.BCGT13

/-- Acceptance fraction of a coin test over `{0,1}^rand`. -/
noncomputable def acceptFrac {rand : ℕ} (t : (Fin rand → Bool) → Bool) : ℝ :=
  ((univ.filter fun r => t r = true).card : ℝ) / (2 : ℝ) ^ rand

/-- A strong PCPP verifier for `code` on the evaluation set `S` with soundness factor `s` (proof of `thm:short-pcp-ours`). -/
structure StrongPCPP (F : Type) [DecidableEq F] (S : Finset F) (code : Set (F → F)) (s : ℝ) where
  rand : ℕ
  length : ℕ
  accepts : (F → F) → (Fin length → F) → (Fin rand → Bool) → Bool
  complete : ∀ p ∈ code, ∃ π : Fin length → F, ∀ r, accepts p π r = true
  sound : ∀ (p : F → F) (π : Fin length → F) (δ : ℝ), (∀ q ∈ code, δ ≤ fracDist S p q) →
    acceptFrac (accepts p π) ≤ 1 - s * δ

section Leaf

variable (h : BCGT13_Theorem11_1) (T : Tuple) (hT : T.Valid) (hE : T.PositiveExponents)
  {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (ℓ : ℕ) (hF : Fintype.card F = 2 ^ ℓ)
  (B : List F) (O : F) (hB : IsBasis B O)

/-- The transcribed `V_RS` (BCGT13 Algorithm 13 / Lemma 12.19) as a `StrongPCPP`, soundness factor
`1/(1 + K_κ)` (Theorem 11.1). -/
noncomputable def rsOfLeaf (d : ℕ) (hd1 : 1 ≤ d) (hd : d < 2 ^ B.length) :
    StrongPCPP F (span B O) (RS (span B O) d) (1 / (1 + soundTerm T.η T.κ0 T.γ T.μ B.length)) where
  rand := (vRS T B O d).rand
  length := (vRS T B O d).length
  accepts := (vRS T B O d).accepts B O
  complete := ((h T hT hE F ℓ hF B O hB).1 d hd1 hd).1
  sound := by
    intro p π δ hfar
    have hs := ((h T hT hE F ℓ hF B O hB).1 d hd1 hd).2 p π δ hfar
    unfold FlatVerifier.acceptProb at hs
    unfold acceptFrac
    rw [one_div_mul_eq_div]
    exact hs

/-- The transcribed `V_VRS` (BCGT13 Algorithm 12 / Lemma 12.20) as a `StrongPCPP`, soundness factor
`1/(2 + K_κ)` (Theorem 11.1). -/
noncomputable def vrsOfLeaf (BH : List F) (OH : F) (hBH : IsBasis BH OH) (hsub : span BH OH ⊆ span B O)
    (d : ℕ) (hHd : 2 ^ BH.length ≤ d) (hd : d < 2 ^ B.length) :
    StrongPCPP F (span B O) (VRS (span B O) (span BH OH) d)
      (1 / (2 + soundTerm T.η T.κ0 T.γ T.μ B.length)) where
  rand := (vVRS T B O BH OH d).rand
  length := (vVRS T B O BH OH d).length
  accepts := (vVRS T B O BH OH d).accepts B O
  complete := ((h T hT hE F ℓ hF B O hB).2 BH OH hBH hsub d hHd hd).1
  sound := by
    intro p π δ hfar
    have hs := ((h T hT hE F ℓ hF B O hB).2 BH OH hBH hsub d hHd hd).2 p π δ hfar
    unfold FlatVerifier.acceptProb at hs
    unfold acceptFrac
    rw [one_div_mul_eq_div]
    exact hs

end Leaf

/-! ## Prefixes of one random string -/

/-- The first `k` bits of an `r`-bit string. -/
def pre {r : ℕ} (k : ℕ) (hk : k ≤ r) (R : Fin r → Bool) : Fin k → Bool :=
  fun i => R ⟨i.val, lt_of_lt_of_le i.isLt hk⟩

/-- Counting through the prefix map: every `k`-bit string has exactly `2^(r−k)` extensions. -/
theorem card_filter_pre {r k : ℕ} (hk : k ≤ r) (t : (Fin k → Bool) → Bool) :
    (univ.filter fun R : Fin r → Bool => t (pre k hk R) = true).card =
      2 ^ (r - k) * (univ.filter fun x : Fin k → Bool => t x = true).card := by
  classical
  -- split `Fin r → Bool` as `(Fin k → Bool) × (Fin (r - k) → Bool)`
  have hr : k + (r - k) = r := Nat.add_sub_cancel' hk
  let e : (Fin k → Bool) × (Fin (r - k) → Bool) ≃ (Fin r → Bool) :=
    (Equiv.sumArrowEquivProdArrow (Fin k) (Fin (r - k)) Bool).symm.trans
      ((Equiv.arrowCongr finSumFinEquiv (Equiv.refl Bool)).trans
        (Equiv.arrowCongr (finCongr hr) (Equiv.refl Bool)))
  have hpre : ∀ x y, pre k hk (e (x, y)) = x := by
    intro x y
    funext i
    simp [e, pre, Equiv.arrowCongr, finCongr, Equiv.sumArrowEquivProdArrow]
    exact congrArg (Sum.elim x y) (finSumFinEquiv_symm_apply_castAdd i)
  rw [← Finset.card_map ⟨e.symm, e.symm.injective⟩]
  have : (univ.filter fun R : Fin r → Bool => t (pre k hk R) = true).map ⟨e.symm, e.symm.injective⟩ =
      (univ.filter fun x : Fin k → Bool => t x = true) ×ˢ (univ : Finset (Fin (r - k) → Bool)) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨R, hR, hRe⟩
      have : R = e (x, y) := by rw [← hRe]; simp
      subst this
      simpa [hpre] using hR
    · intro hx
      exact ⟨e (x, y), by simpa [hpre] using hx, by simp⟩
  rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    mul_comm]

/-- **Prefix uniformity** (proof of `thm:short-pcp-ours`): a test on the first `k ≤ r` coins has the same acceptance fraction. -/
theorem acceptFrac_pre {r k : ℕ} (hk : k ≤ r) (t : (Fin k → Bool) → Bool) :
    acceptFrac (fun R : Fin r → Bool => t (pre k hk R)) = acceptFrac t := by
  unfold acceptFrac
  rw [card_filter_pre hk t]
  have h2 : (2 : ℝ) ^ r = 2 ^ (r - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [h2, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

end NearCubicGates.Adapters.ShortPCP
