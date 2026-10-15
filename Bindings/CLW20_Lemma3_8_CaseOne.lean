import Bindings.CLW20_Lemma3_8_Base

/-! # CLW20 Lemma 3.8, Appendix A: Case 1

CLW20 (ECCC TR20-150), Appendix A, PDF p.50, printed p.49 (with `k + 1` here in place of the
paper's `k`):

> "Case 1. Suppose for some y ∈ {0,1}^n, we have |Pr_z[f^{⊕k}(y,z) = C(y,z)] − 1/2| >
> ε_k/(1 − δ) = (1 − δ)^{k−2}·(1/2 − δ) = ε_{k−1}. Then, we can fix one such y, and note that either
> circuit C′(z) := C(y,z) or ¬C′(z) approximates f^{⊕(k−1)} well enough so that we can reduce it to
> the case of k − 1."

`case_one_step` takes the threshold in its reduced form `ε_{k−1}` (here `xorEpsilon δ k`); the
identity `ε_k/(1 − δ) = ε_{k−1}` is `xorEpsilon_succ` in the Case 2 module. By
`fiber_eq_agreement`, the fiber agreement at `y` is the agreement of `D(z) := f(y) ⊕ C(y,z)` with
`f^{⊕(k−1)}`, and `D` is `C′` or `¬C′` according to `f(y)`. If the fiber advantage is positive,
`D` has agreement above `1/2 + ε_{k−1}`; if negative, `¬D` does (`agreement_not`). The induction
hypothesis at `k − 1` then gives the sampled sum, whose level is lifted (`sampledXorSum_lift`). -/
namespace NearCubicWires.Bindings.CLW20Lemma38
open NearCubicWires SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem case_one_step (delta : ℚ) {family : SizedFunctionFamily}
    (hproj : LiteralProjectionClosed family) (hneg : NegationClosedFamily family)
    {n k : ℕ} (f : BoolFunction n) (size : ℕ)
    (ih : ∀ D : BoolFunction (k * n), family (k * n) D size →
      1 / 2 + xorEpsilon (delta : ℝ) k < agreement D (xorPower f k) →
        Nonempty (SampledXorSum family delta n k size f))
    (C : BoolFunction ((k + 1) * n)) (hC : family ((k + 1) * n) C size) (y : BitInput n)
    (hy : xorEpsilon (delta : ℝ) k < |fiberAgreement C (xorPower f (k + 1)) y - 1 / 2|) :
    Nonempty (SampledXorSum family delta n (k + 1) size f) := by
  have hD : family (k * n) (fun z => xor (f y) (C (joinInput y z))) size :=
    family_xor (family := family) (size := size) hneg (family_fixFirst (family := family) hproj hC y) (f y)
  rw [fiber_eq_agreement] at hy
  have hadv : ∃ D : BoolFunction (k * n), family (k * n) D size ∧
      1 / 2 + xorEpsilon (delta : ℝ) k < agreement D (xorPower f k) := by
    rcases lt_abs.mp hy with h | h
    · exact ⟨_, hD, by linarith⟩
    · have hnot := agreement_not (fun z => xor (f y) (C (joinInput y z))) (xorPower f k)
      exact ⟨_, hneg _ hD, by rw [hnot]; linarith⟩
  obtain ⟨D, hDf, hDa⟩ := hadv
  obtain ⟨w⟩ := ih D hDf hDa
  exact ⟨sampledXorSum_lift w⟩

end NearCubicWires.Bindings.CLW20Lemma38
