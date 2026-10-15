import Proof.CaseAnalysis.FinalTailFeedPrep

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdWidths

open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open CompetitorThresholdDecision
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The width every one of the six threshold integers fits in: the largest `Nat.size`
among the numerators and denominators of `meanThreshold`, `momentThreshold` and
`acceptanceThreshold`. A closed form of the constants; no free parameter. -/
def thresholdWidth {source : PointwisePCPPAlgorithm} (constants : Constants source) : ℕ :=
  max (max (Nat.size (numerator (meanThreshold constants)))
           (Nat.size (meanThreshold constants).den))
    (max (max (Nat.size (numerator (momentThreshold constants)))
              (Nat.size (momentThreshold constants).den))
         (max (Nat.size (numerator (acceptanceThreshold constants)))
              (Nat.size (acceptanceThreshold constants).den)))

/-- `W ≤ w W`: the comparator parameter is at least the record width. -/
theorem le_w (W : ℕ) : W ≤ w W := by
  show W ≤ 2*W+2
  omega

/-- An integer of binary size at most `W` is below `2^(w W)`. -/
theorem lt_two_pow_w {n W : ℕ} (h : Nat.size n ≤ W) : n < 2^(w W) :=
  lt_of_lt_of_le (Nat.lt_size_self n)
    (Nat.pow_le_pow_right (by norm_num) (h.trans (le_w W)))

/-- **The six width facts `tail_step` consumes**, from `thresholdWidth constants ≤ W`. -/
theorem threshold_widths {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (W : ℕ) (hW : thresholdWidth constants ≤ W) :
    numerator (meanThreshold constants) < 2^(w W) ∧
      (meanThreshold constants).den < 2^(w W) ∧
      numerator (momentThreshold constants) < 2^(w W) ∧
      (momentThreshold constants).den < 2^(w W) ∧
      numerator (acceptanceThreshold constants) < 2^(w W) ∧
      (acceptanceThreshold constants).den < 2^(w W) := by
  unfold thresholdWidth at hW
  simp only [max_le_iff] at hW
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩ := hW
  exact ⟨lt_two_pow_w h1, lt_two_pow_w h2, lt_two_pow_w h3, lt_two_pow_w h4,
    lt_two_pow_w h5, lt_two_pow_w h6⟩

/-- `Estimate.Valid` is monotone in the width. -/
theorem valid_mono {est : CompetitorValidity.Estimate} {W W' : ℕ}
    (h : est.Valid W) (hW : W ≤ W') : est.Valid W' :=
  ⟨lt_of_lt_of_le h.positive (Nat.pow_le_pow_right (by norm_num) hW),
   lt_of_lt_of_le h.negative (Nat.pow_le_pow_right (by norm_num) hW),
   lt_of_lt_of_le h.denominator (Nat.pow_le_pow_right (by norm_num) hW),
   h.denominatorPositive⟩

end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdWidths
