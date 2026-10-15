import Proof.Wire_3_5.GFTrace

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.GF
open Polynomial NearCubicWires.WireExponent3_5.GF2

/-- The LFSR orbit of `1` returns to `1` at step `j` exactly when `x^j = 1`. -/
theorem lfsrPow_eq_one_iff (p ℓ j : ℕ) (hp : ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) :
    lfsrPow p ℓ j = 1 ↔ xRoot p ^ j = 1 := by
  obtain ⟨h1, h2⟩ := lfsrPow_spec p ℓ hp hℓ j
  constructor
  · intro h; rw [← h2, h, rep_one]
  · intro h
    apply rep_injOn p ℓ _ _ hp h1 (Nat.one_lt_two_pow (by omega))
    rw [h2, h, rep_one]

theorem period_eq (p ℓ : ℕ) (hp : ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (hord : orderOf (xRoot p) = 2 ^ ℓ - 1) :
    period p ℓ = 2 ^ ℓ - 1 := by
  have h2 : 2 ≤ 2 ^ ℓ := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  have hfind : (List.range (2 ^ ℓ)).find? (fun j => j ≠ 0 && lfsrPow p ℓ j == 1) = some (2 ^ ℓ - 1) := by
    rw [List.find?_range_eq_some]
    refine ⟨?_, List.mem_range.mpr (by omega), ?_⟩
    · have : lfsrPow p ℓ (2 ^ ℓ - 1) = 1 := by
        rw [lfsrPow_eq_one_iff p ℓ _ hp hℓ, ← hord]; exact pow_orderOf_eq_one _
      simp [this]; omega
    · intro j hj
      by_cases hj0 : j = 0
      · simp [hj0]
      · have : lfsrPow p ℓ j ≠ 1 := by
          rw [ne_eq, lfsrPow_eq_one_iff p ℓ _ hp hℓ]
          exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
        simp [hj0, this]
  unfold period
  rw [hfind]
  rfl

/-- The bit vector of a monic polynomial of degree `ℓ` is a modulus of degree `ℓ` with that polynomial. -/
theorem ofPoly_modulus (m : (ZMod 2)[X]) (ℓ : ℕ) (hm : m.Monic) (hdeg : m.natDegree = ℓ) :
    ModulusOk (ofPoly m (ℓ + 1)) ℓ ∧ toPoly (ofPoly m (ℓ + 1)) = m := by
  have hlt : m.degree < ↑(ℓ + 1) := by
    rw [degree_eq_natDegree hm.ne_zero, hdeg]; exact_mod_cast Nat.lt_succ_self ℓ
  have htp := toPoly_ofPoly m (ℓ + 1) hlt
  refine ⟨⟨?_, ofPoly_lt m (ℓ + 1)⟩, htp⟩
  have hc : (toPoly (ofPoly m (ℓ + 1))).coeff ℓ = 1 := by
    rw [htp, ← hdeg]; exact hm
  rw [coeff_toPoly] at hc
  cases h : (ofPoly m (ℓ + 1)).testBit ℓ
  · rw [h] at hc; exact absurd hc (by decide)
  · rfl

theorem exists_primitiveCert (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : ∃ p, PrimitiveCert p ℓ := by
  classical
  let K := GaloisField 2 ℓ
  haveI : Fintype K := Fintype.ofFinite K
  have hℓ0 : ℓ ≠ 0 := by omega
  have hcard : Fintype.card K = 2 ^ ℓ := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card 2 ℓ hℓ0
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hordg : orderOf g = 2 ^ ℓ - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units, hcard]
  set α : K := (g : K) with hα
  have hint : IsIntegral (ZMod 2) α := IsIntegral.of_finite (ZMod 2) α
  -- `α` generates the field, so its minimal polynomial has degree `ℓ`
  have htop : IntermediateField.adjoin (ZMod 2) {α} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_cases hx : x = 0
    · rw [hx]; exact zero_mem _
    · obtain ⟨k, hk⟩ := hg (Units.mk0 x hx)
      have hx' : x = (g : K) ^ k := by
        have := congrArg (fun u : Kˣ => (u : K)) hk
        simp only [Units.val_mk0, Units.val_zpow_eq_zpow_val] at this
        exact this.symm
      rw [hx']
      exact zpow_mem (IntermediateField.mem_adjoin_simple_self (ZMod 2) α) k
  have hdeg : (minpoly (ZMod 2) α).natDegree = ℓ := by
    rw [(Field.primitive_element_iff_minpoly_natDegree_eq (ZMod 2) α).mp htop, GaloisField.finrank 2 hℓ0]
  have hmon := minpoly.monic hint
  obtain ⟨hmod, htp⟩ := ofPoly_modulus (minpoly (ZMod 2) α) ℓ hmon hdeg
  set p := ofPoly (minpoly (ZMod 2) α) (ℓ + 1) with hp
  refine ⟨p, hℓ, hmod, period_eq p ℓ hmod hℓ ?_⟩

  haveI : Fact (Irreducible (toPoly p)) := ⟨htp ▸ minpoly.irreducible hint⟩
  have hev : (toPoly p).eval₂ (algebraMap (ZMod 2) K) α = 0 := by
    rw [htp, ← aeval_def]; exact minpoly.aeval _ _
  let φ : AdjoinRoot (toPoly p) →+* K := AdjoinRoot.lift (algebraMap (ZMod 2) K) α hev
  have hφ : Function.Injective φ := φ.injective
  have hroot : φ (xRoot p) = α := AdjoinRoot.lift_root hev
  have := orderOf_injective φ.toMonoidHom hφ (xRoot p)
  have h2 : φ.toMonoidHom (xRoot p) = α := hroot
  rw [h2] at this
  rw [← this, hα, orderOf_units, hordg]

/-- **The search always returns a certified modulus.** -/
theorem firstPrimitive_cert (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : PrimitiveCert (firstPrimitive ℓ) ℓ := by
  obtain ⟨p, hc⟩ := exists_primitiveCert ℓ hℓ
  have hlo : 2 ^ ℓ ≤ p := Nat.ge_two_pow_of_testBit hc.2.1.1
  have hhi : p < 2 ^ (ℓ + 1) := hc.2.1.2
  unfold firstPrimitive
  cases hfind : (List.range (2 ^ ℓ)).find? (fun j => decide (PrimitiveCert (2 ^ ℓ + j) ℓ)) with
  | none =>
    rw [List.find?_range_eq_none] at hfind
    have := hfind (p - 2 ^ ℓ) (by rw [pow_succ] at hhi; omega)
    rw [show 2 ^ ℓ + (p - 2 ^ ℓ) = p by omega] at this
    simp [hc] at this
  | some i =>
    have := List.find?_some hfind
    simpa using this

end NearCubicWires.WireExponent3_5.GF
