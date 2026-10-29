import SourceAdapters.Joins.BinaryFieldArithmetic

/-!
# Join X3 proved by citation

`binaryFieldArithmetic : BinaryFieldArithmetic`. Every conjunct is a released theorem (proof of `lem:small-bias`; proof of `thm:short-pcp-ours`); this module only adjusts the step counts to the join's closed forms.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Field

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Adapters.Joins

/-- The search cost in closed form: `modCost ℓ ≤ 300·4^ℓ·(ℓ+1)`. -/
theorem modCost_le (ℓ : ℕ) : PrimAsm.Modulus.modCost ℓ ≤ 300 * 4 ^ ℓ * (ℓ + 1) := by
  have h1 := GF2.searchCost_le ℓ (ℓ + 1) (by omega) (by omega)
  have h4 : (2 : ℕ) ^ (2 * ℓ) = 4 ^ ℓ := by rw [pow_mul]; norm_num
  rw [h4, pow_one] at h1
  have h5 : 1 ≤ 4 ^ ℓ := Nat.one_le_pow _ _ (by norm_num)
  have h6 : ℓ + 1 ≤ 4 ^ ℓ * (ℓ + 1) := Nat.le_mul_of_pos_left _ (by omega)
  unfold PrimAsm.Modulus.modCost
  nlinarith

/-- The multiplier's step count in closed form. -/
theorem fmulCost_le (ℓ : ℕ) : ℓ * (mulStepCost ℓ + 2) + 14 * ℓ + 3 ≤ 200 * (ℓ + 1) ^ 2 := by
  unfold mulStepCost; nlinarith

/-- **Join X3 holds** (by citation of the released field machinery). -/
theorem binaryFieldArithmetic : BinaryFieldArithmetic := by
  refine ⟨?_, ?_, modCost_le, GF.rep_xor, ?_, ?_⟩
  · intro p ℓ hc
    refine ⟨GF.irreducible_ref p ℓ hc, GF.natCard_ref p ℓ hc.2.1, ?_⟩
    exact (GF.encEquiv p ℓ hc.2.1).bijective
  · intro ℓ hℓ
    obtain ⟨tout, hs, _, h12⟩ := PrimAsm.Modulus.modulus_step ℓ hℓ
    exact ⟨GF.firstPrimitive_cert ℓ hℓ, tout, hs, h12⟩
  · intro ns nr cap A B F R hAB hFR ℓ a b restA restB σ hcap1 hcap hA hhA hB hhB hF hR
    have h := mapPass_spec cap xorOut keepS A B F R hAB hFR hcap1 (binary ℓ a) (binary ℓ b) restA restB false σ
      (by simp) hA hhA hB hhB (by simpa using hF) hR (by simpa using hcap)
    rw [mapS_xor _ _ _ (by simp), ← GF2.binary_xor] at h
    simpa [binary_length, Nat.mul_comm] using h
  · intro ns nr cap Y ACC ST Pm F G R RY hL ℓ p x y hℓ hp hx hy hcap σ hI
    obtain ⟨τ, h, hI', hF⟩ := fmulW_spec cap Y ACC ST Pm F G R RY hL ℓ p x y hℓ hcap σ hI
    obtain ⟨hz, hrep⟩ := GF.fmulShift_spec p ℓ x y hp hx hy
    exact ⟨τ, _, _, WExec.mono h (fmulCost_le ℓ), hI', hz, hrep, hF⟩

end NearCubicGates.Adapters.Field
