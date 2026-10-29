import SourceAdapters.Amplification.Regimes
import SourceAdapters.Amplification.TM2Dock

/-!
# A04 + A06: the amplifier `g` over all ranges, and input 8 from its stated hypotheses

 `app:sources`, "Full-range amplification interface". The output `ampG`:
* `S(n) = 0`: a constant function (arity `0`) — "no circuit has zero nodes";
* `n < n0`, `S(n) > 0`: parity on `S(n) + 1` bits — "Since `S(n)^{1/c} ≤ S(n)`, the same missing-input argument";
* `1 ≤ S(n) ≤ n^c`: parity on `n + 1` bits;
* `S(n) ≥ U(n) = 2^(n+3)`: a constant function — "no input function satisfies the hardness premise" (Shannon);
* otherwise the rounded STV code `stvEncode` at `k = dyadicExp c S(n)`, over the field `firstPrimitive t` of X3.
`ampG_amplifies`: the target's `amplifies` clause (hardness at **every** length, arity `≤ 6(44 + size C)·n` from the
onset `n0`), given the A02 bound. `input8_of_obligations`: the field `CLW20_Lemma3_9_Multitape` from the leaf
`STV.Theorem29`, the A02 condition (`ReconstructionObligation`), the X1 join (`OrdinaryToTM2InTime`) and the A05
condition (`ConstructionObligation`: an ordinary machine computing `ampG` in `2^{O(n)}`). The
outer `c = 2a + 2` is chosen from the leaf's constants before `S` ("Choose an integer `c > 2a + 2`,
once and before `S`"; `c ≥ 2a + 2` suffices for `size_inequality`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open Finset Polynomial NearCubicWires NearCubicWires.ExecutableInterfaces NearCubicWires.RepairSource
open NearCubicWires.Bindings.CLW20Lemma39 NearCubicWires.Bindings.CLW20Lemma39TM2
open NearCubicGates.Published.STV NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.Joins

theorem one_le_tParam (C n k : ℕ) : 1 ≤ tParam C n k := by unfold tParam; omega

/-- The middle-regime output: the rounded STV code of `f` at `k = dyadicExp c S`. -/
noncomputable def midOutput (C c : ℕ) (hc : 1 ≤ c) (S n : ℕ) (f : BoolFunction n) : AmplifierOutput :=
  letI : Fact (Irreducible (GF.toPoly (GF.firstPrimitive (tParam C n (dyadicExp c S hc))))) :=
    ⟨(stvField _ (one_le_tParam C n _)).2.1⟩
  ⟨(mParam n (dyadicExp c S hc) + 1) * tParam C n (dyadicExp c S hc),
    stvEncode C n (dyadicExp c S hc) (stvField _ (one_le_tParam C n _)).1 (stvField _ (one_le_tParam C n _)).2.2 f⟩

/-- The onset `n0 = 2A·8^a + 4`. -/
def ampOnset (A a : ℕ) : ℕ := 2 * A * 8 ^ a + 4

/-- **The amplifier output over all ranges** (`app:sources`, "Full-range amplification interface"). -/
noncomputable def ampG (C A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (n : ℕ) (f : BoolFunction n) : AmplifierOutput :=
  if S n = 0 then ⟨0, fun _ => false⟩
  else if n < ampOnset A a then ⟨S n + 1, par (S n + 1)⟩
  else if S n ≤ n ^ c then ⟨n + 1, par (n + 1)⟩
  else if 2 ^ (n + 3) ≤ S n then ⟨0, fun _ => false⟩
  else midOutput C c hc (S n) n f

theorem rpow_inv_le_self (S c : ℕ) (hS : 1 ≤ S) (hc : 1 ≤ c) : (S : ℝ) ^ ((1 : ℝ) / c) ≤ S := by
  have h1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
  calc (S : ℝ) ^ ((1 : ℝ) / c) ≤ (S : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le h1
        rw [div_le_one (by exact_mod_cast (show 0 < c by omega))]; exact_mod_cast hc
    _ = S := Real.rpow_one _

theorem rpow_inv_le_of_le_pow (S n c : ℕ) (hc : 1 ≤ c) (h : S ≤ n ^ c) : (S : ℝ) ^ ((1 : ℝ) / c) ≤ n := by
  have h1 : (S : ℝ) ≤ (n : ℝ) ^ c := by exact_mod_cast h
  calc (S : ℝ) ^ ((1 : ℝ) / c) ≤ ((n : ℝ) ^ c) ^ ((1 : ℝ) / c) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = n := by rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)]

/-- The middle-regime arity is `O(n)`: `k ≤ n + 3` there. -/
theorem dyadicExp_le (c S n : ℕ) (hc : 1 ≤ c) (hS2 : 2 ≤ S) (hU : S < 2 ^ (n + 3)) : dyadicExp c S hc ≤ n + 3 := by
  have h := two_pow_pred_lt c S hc hS2
  have h2 : 2 ^ (c * (dyadicExp c S hc - 1)) < 2 ^ (n + 3) := lt_trans h hU
  have h3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have h4 : dyadicExp c S hc - 1 ≤ c * (dyadicExp c S hc - 1) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **The amplifies clause** of `Lemma3_9AtTM2`, for `c ≥ 2a + 2`, given A02. -/
theorem ampG_amplifies (C A a c : ℕ) (hc : 2 * a + 2 ≤ c) (hR : ReconstructionBound C A a) (S : ℕ → ℕ)
    (n : ℕ) (f : BoolFunction n) (hf : ¬ HasCircuitOfSize f (S n)) :
    (ampOnset A a ≤ n → (ampG C A a c (by omega) S n f).arity ≤ (6 * (44 + Nat.size C)) * n) ∧
    CannotBeApproximated (ampG C A a c (by omega) S n f).function
      ((S n : ℝ) ^ (-(1 : ℝ) / (c : ℝ))) ((S n : ℝ) ^ ((1 : ℝ) / (c : ℝ))) := by
  have hc1 : 1 ≤ c := by omega
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc1
  unfold ampG
  by_cases h0 : S n = 0
  · rw [if_pos h0]
    refine ⟨fun _ => by simp, ?_⟩
    have := cannotBeApproximated_at_size_zero (fun _ : BitInput 0 => false) (c : ℝ) hcR
    rw [h0]; exact this
  rw [if_neg h0]
  have hεpos : 0 < (S n : ℝ) ^ (-(1 : ℝ) / (c : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (Nat.pos_of_ne_zero h0)) _
  by_cases hsmall : n < ampOnset A a
  · rw [if_pos hsmall]
    refine ⟨fun h => absurd h (by omega), ?_⟩
    apply parity_cannotBeApproximated _ _ _ hεpos
    have := rpow_inv_le_self (S n) c (by omega) hc1
    push_cast; linarith
  rw [if_neg hsmall]
  have hn1 : 1 ≤ n := by unfold ampOnset at hsmall; omega
  by_cases hpoly : S n ≤ n ^ c
  · rw [if_pos hpoly]
    refine ⟨fun _ => by nlinarith, ?_⟩
    apply parity_cannotBeApproximated _ _ _ hεpos
    have := rpow_inv_le_of_le_pow (S n) n c hc1 hpoly
    push_cast; linarith
  rw [if_neg hpoly]
  by_cases hU : 2 ^ (n + 3) ≤ S n
  · exact absurd (hasCircuitOfSize_of_U_le f (S n) hU) hf
  rw [if_neg hU]
  push Not at hpoly hU
  have hS : (n : ℝ) ^ c < S n := by exact_mod_cast hpoly
  have hS2 : 2 ≤ S n := by
    have : 2 ≤ n ^ c := by
      calc 2 ≤ n := by unfold ampOnset at hsmall; omega
        _ = n ^ 1 := (pow_one n).symm
        _ ≤ n ^ c := Nat.pow_le_pow_right (by omega) hc1
    omega
  refine ⟨fun _ => ?_, ?_⟩
  · unfold midOutput
    have h1 := arity_le C n (dyadicExp c (S n) hc1)
    have h2 := dyadicExp_le c (S n) n hc1 hS2 hU
    calc (mParam n (dyadicExp c (S n) hc1) + 1) * tParam C n (dyadicExp c (S n) hc1)
        ≤ (44 + Nat.size C) * (n + dyadicExp c (S n) hc1 + 1) := h1
      _ ≤ (44 + Nat.size C) * (6 * n) := Nat.mul_le_mul_left _ (by omega)
      _ = 6 * (44 + Nat.size C) * n := by ring
  · unfold midOutput
    haveI : Fact (Irreducible (GF.toPoly (GF.firstPrimitive (tParam C n (dyadicExp c (S n) hc1))))) :=
      ⟨(stvField _ (one_le_tParam C n _)).2.1⟩
    exact middle_regime_hard C A a c hc hR n (by unfold ampOnset at hsmall; omega) (S n) hS _
      (stvField _ (one_le_tParam C n _)).1 (stvField _ (one_le_tParam C n _)).2.2 f hf

/-- The A05 hypothesis (`app:sources`, "Full-range amplification interface"): an ordinary machine computes `ampG` in `2^{O(n)}` time, on every
truth table, for every time-constructible `S` (the machine may depend on `S`). -/
def ConstructionObligation : Prop :=
  ∀ (C A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ), NearCubicWires.Bindings.CLW20Theorem113.TimeConstructible S →
    Nonempty (TruthTableConstruction (ampG C A a c hc S))

/-- **Input 8 from the leaf and its stated hypotheses** (A02, X1, A05). -/
theorem input8_of_obligations (h29 : Theorem29) (hA02 : ReconstructionObligation) (hX1 : OrdinaryToTM2InTime)
    (hA05 : ConstructionObligation) : NearCubicGates.Close.CLW20_Lemma3_9_Multitape := by
  obtain ⟨C, A, a, hR⟩ := hA02 h29
  refine ⟨((2 * a + 2 : ℕ) : ℝ), by exact_mod_cast (show 1 ≤ 2 * a + 2 by omega), fun S hS => ?_⟩
  obtain ⟨T⟩ := hA05 C A a (2 * a + 2) (by omega) S hS
  obtain ⟨M⟩ := tm2Construction_of_ordinary hX1 T
  exact ⟨{ g := ampG C A a (2 * a + 2) (by omega) S
           arityFactor := 6 * (44 + Nat.size C)
           arityOnset := ampOnset A a
           amplifies := fun n f hf => ampG_amplifies C A a (2 * a + 2) le_rfl hR S n f hf
           construction := M }⟩

end NearCubicGates.Adapters.Amplification
