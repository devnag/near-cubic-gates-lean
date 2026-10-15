import Std

/-!
# Integer score boxes from the certified final-stage error

This file proves the range arithmetic in equation `box` of the manuscript.
All statements concern integer arithmetic and arbitrary proposed values.
Neither sampling honesty nor tomography is assumed.
-/

namespace NearCubicGates.ScoreBox

/-- Ceiling division, including negative numerators, for a positive divisor. -/
def ceilDiv (numerator denominator : Int) : Int :=
  (numerator + denominator - 1) / denominator

theorem ceilDiv_le_iff (numerator denominator value : Int)
    (hden : 0 < denominator) :
    ceilDiv numerator denominator ≤ value ↔ numerator ≤ denominator * value := by
  unfold ceilDiv
  rw [Int.ediv_le_iff_le_mul hden, Int.mul_comm value denominator]
  omega

theorem le_floorDiv_iff (numerator denominator value : Int)
    (hden : 0 < denominator) :
    value ≤ numerator / denominator ↔ denominator * value ≤ numerator := by
  rw [Int.le_ediv_iff_mul_le hden, Int.mul_comm value denominator]

/-- `center` is `M₁ * (K(κ) - K(z_y))`; `scale` is the integer `A`. -/
def Certified (center scale reference radius score : Int) : Prop :=
  -radius < center - scale * (score - reference) ∧
  center - scale * (score - reference) < radius

def lower (center scale reference radius : Int) : Int :=
  reference + ceilDiv (center - radius + 1) scale

def upper (center scale reference radius : Int) : Int :=
  reference + (center + radius - 1) / scale

/-- Exact endpoints, with the `+1` and `-1` forced by strict integer tests. -/
theorem certified_iff_in_box
    (center scale reference radius score : Int) (hscale : 0 < scale) :
    Certified center scale reference radius score ↔
      lower center scale reference radius ≤ score ∧
      score ≤ upper center scale reference radius := by
  have hL := ceilDiv_le_iff (center - radius + 1) scale
    (score - reference) hscale
  have hU := le_floorDiv_iff (center + radius - 1) scale
    (score - reference) hscale
  unfold Certified lower upper
  omega

/-- The magnitude test supplied by the even moment certificate implies the
strict two-sided error test. -/
theorem certified_of_magnitude
    (center scale reference radius score : Int)
    (hmag : ((center - scale * (score - reference)).natAbs : Int) < radius) :
    Certified center scale reference radius score := by
  have hp : center - scale * (score - reference) ≤
      ((center - scale * (score - reference)).natAbs : Int) := Int.le_natAbs
  have hn : -(center - scale * (score - reference)) ≤
      ((center - scale * (score - reference)).natAbs : Int) := by
    simpa only [Int.natAbs_neg] using
      (Int.le_natAbs (a := -(center - scale * (score - reference))))
  unfold Certified
  omega

/-- Every score satisfying the final-stage certificate lies in the computed
integer box. No property of the proposal other than its certificate is used. -/
theorem score_in_box
    (center scale reference radius score : Int) (hscale : 0 < scale)
    (hmag : ((center - scale * (score - reference)).natAbs : Int) < radius) :
    lower center scale reference radius ≤ score ∧
      score ≤ upper center scale reference radius :=
  (certified_iff_in_box center scale reference radius score hscale).mp
    (certified_of_magnitude center scale reference radius score hmag)

/-- Any two certified scores differ by at most `length - 1` whenever the
public window-width inequality holds. -/
theorem score_difference_le
    (center scale reference radius length first second : Int)
    (hscale : 0 < scale)
    (hwidth : 2 * radius - 2 ≤ (length - 1) * scale)
    (hfirst : Certified center scale reference radius first)
    (hsecond : Certified center scale reference radius second) :
    first - second ≤ length - 1 := by
  have hid : scale * (first - second) =
      scale * (first - reference) - scale * (second - reference) := by
    simp only [Int.mul_sub]
    omega
  have hsmall : scale * (first - second) ≤ 2 * radius - 2 := by
    unfold Certified at hfirst hsecond
    omega
  have hprod : scale * (first - second) ≤ scale * (length - 1) := by
    rw [Int.mul_comm scale (length - 1)]
    omega
  exact Int.le_of_mul_le_mul_left hprod hscale

/-- Cardinality of the consecutive integer interval, with empty intervals
represented by zero. -/
def boxCount (center scale reference radius : Int) : Nat :=
  (upper center scale reference radius - lower center scale reference radius + 1).toNat

theorem boxCount_le
    (center scale reference radius length : Int)
    (hscale : 0 < scale) (hlength : 0 ≤ length)
    (hwidth : 2 * radius - 2 ≤ (length - 1) * scale) :
    boxCount center scale reference radius ≤ length.toNat := by
  by_cases hnonempty : lower center scale reference radius ≤
      upper center scale reference radius
  · have hfirst : Certified center scale reference radius
        (upper center scale reference radius) :=
      (certified_iff_in_box center scale reference radius
        (upper center scale reference radius) hscale).mpr ⟨hnonempty, Int.le_refl _⟩
    have hsecond : Certified center scale reference radius
        (lower center scale reference radius) :=
      (certified_iff_in_box center scale reference radius
        (lower center scale reference radius) hscale).mpr ⟨Int.le_refl _, hnonempty⟩
    have hdiff := score_difference_le center scale reference radius length
      (upper center scale reference radius) (lower center scale reference radius)
      hscale hwidth hfirst hsecond
    unfold boxCount
    omega
  · unfold boxCount
    omega

/-- The exact public rule `Λ = floor((L - 1)A/2) + 1` supplies the required
width inequality automatically. -/
theorem public_radius_width (scale length : Int) :
    2 * (((length - 1) * scale) / 2 + 1) - 2 ≤ (length - 1) * scale := by
  have h := Int.ediv_mul_le ((length - 1) * scale) (by decide : (2 : Int) ≠ 0)
  omega

theorem public_radius_boxCount_le
    (center scale reference length : Int)
    (hscale : 0 < scale) (hlength : 0 ≤ length) :
    boxCount center scale reference (((length - 1) * scale) / 2 + 1) ≤ length.toNat :=
  boxCount_le center scale reference (((length - 1) * scale) / 2 + 1) length
    hscale hlength (public_radius_width scale length)

end NearCubicGates.ScoreBox
