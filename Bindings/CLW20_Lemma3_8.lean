import Bindings.CLW20_Lemma3_8_CaseOne
import Bindings.CLW20_Lemma3_8_CaseTwo

/-! # CLW20 Lemma 3.8: the imported XOR source, proved

CLW20 (ECCC TR20-150), Lemma 3.8, PDF p.17, printed p.16:

> "Lemma 3.8. Let f : {0,1}^n → {0,1} be a boolean function. Let δ < 1/2, For any k ≥ 1, let
> ε_k = (1 − δ)^{k−1}(1/2 − δ). If f cannot be (1 − δ)-approximated in ℓ1 distance by
> [0,1]Sum ◦ C circuits of complexity O(n·s/(δ·ε_k)^2), then f^{⊕k} cannot be (1/2 + ε_k)-approximated
> by C circuits of size s."

Its proof, Appendix A, PDF p.50, printed p.49:

> "We prove the contrapositive, i.e., given a C circuit C of size s approximating f^{⊕k} on at least
> a (1/2 + ε_k)-fraction of inputs, we show how to construct a [0,1]Sum ◦ C circuit Q approximating
> f with a much better guarantee. [...] Our proof is by induction on k. The case k = 1 is clearly
> trivial. Assuming the hypothesis holds for k − 1, we now consider the following two cases."

`clw20_xor_source` proves the imported `RepairRepresentation.XorSource` outright, so the XOR lemma
is no longer a hypothesis of the headline theorem. `XorSource` is the contrapositive form above,
with the construction of the printed proof recorded in its type (`SampleForm`): either one term with
coefficient 1 (reached at level 1), or, at some level `2 ≤ j ≤ k`, exactly
`sampleCount δ n j = ⌈4(n+1)/(δ²ε_j²)⌉` restricted or negated-restricted candidates with coefficient
`α_j/ℓ` plus the constant function 1 with coefficient `(1 − α_j)/2`, `α_j = 1/r`. The proof follows
Appendix A step by step: `base_case` (k = 1), `case_one_step` (Case 1, PDF p.50), `case_two_step`
(Case 2, PDF pp.50–52), and `xor_all_levels` (the induction on k).

Readings, recorded: "C circuits of size s" is the member predicate `family (k·n) · size` of a
size-indexed family closed under literal projection and output negation (the typical-class
operations, PDF p.15); `δ` is rational with `0 < δ < 1/2`; "at least 1/2 + ε_k" is taken strictly;
the printed `O(n/(δε_k)^2)` sample count is the explicit `⌈4(n+1)/(δ²ε_k²)⌉`, and the printed
"Chernoff bound" is Hoeffding's inequality (`Bindings.CLW20_Lemma3_8_Sampling`). The resource bounds of
the resulting sum (term count, coefficient mass and bit length) are proved separately in the
repository from `SampleForm` (`RepairXorResources.rationalXorResources`). -/
namespace NearCubicWires.Bindings.CLW20Lemma38
open NearCubicWires SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- One induction step: Case 1 or Case 2 at level `k + 1`, from the hypothesis at level `k`. -/
theorem xor_step (delta : ℚ) (h0 : 0 < delta) (h1 : delta < 1 / 2)
    {family : SizedFunctionFamily} (hproj : LiteralProjectionClosed family)
    (hneg : NegationClosedFamily family) {n k : ℕ} (hk : 1 ≤ k) (f : BoolFunction n) (size : ℕ)
    (ih : ∀ D : BoolFunction (k * n), family (k * n) D size →
      1 / 2 + xorEpsilon (delta : ℝ) k < agreement D (xorPower f k) →
        Nonempty (SampledXorSum family delta n k size f))
    (C : BoolFunction ((k + 1) * n)) (hC : family ((k + 1) * n) C size)
    (hagree : 1 / 2 + xorEpsilon (delta : ℝ) (k + 1) < agreement C (xorPower f (k + 1))) :
    Nonempty (SampledXorSum family delta n (k + 1) size f) := by
  by_cases hcase : ∃ y, xorEpsilon (delta : ℝ) k < |fiberAgreement C (xorPower f (k + 1)) y - 1 / 2|
  · obtain ⟨y, hy⟩ := hcase
    exact case_one_step delta (family := family) hproj hneg f size ih C hC y hy
  · simp only [not_exists, not_lt] at hcase
    exact case_two_step delta h0 h1 (family := family) hproj hneg hk f size C hC hagree hcase

/-- "Our proof is by induction on k." -/
theorem xor_all_levels (delta : ℚ) (h0 : 0 < delta) (h1 : delta < 1 / 2)
    {family : SizedFunctionFamily} (hproj : LiteralProjectionClosed family)
    (hneg : NegationClosedFamily family) {n : ℕ} (f : BoolFunction n) (size : ℕ) :
    ∀ k, 1 ≤ k → ∀ C : BoolFunction (k * n), family (k * n) C size →
      1 / 2 + xorEpsilon (delta : ℝ) k < agreement C (xorPower f k) →
        Nonempty (SampledXorSum family delta n k size f) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun C hC hagree => base_case delta (family := family) hproj f size C hC hagree
  | succ k hk ih =>
    intro C hC hagree
    exact xor_step delta h0 h1 (family := family) hproj hneg hk f size ih C hC hagree

/-- CLW20 Lemma 3.8 in the imported sampled form, proved from Appendix A. -/
theorem clw20_xor_source : NearCubicWires.RepairRepresentation.XorSource := by
  intro delta h0 h1 family hproj hneg n f _hn k size hk candidate hcand hagree
  exact xor_all_levels delta h0 h1 (family := family) hproj hneg f size k hk candidate hcand hagree

end NearCubicWires.Bindings.CLW20Lemma38
