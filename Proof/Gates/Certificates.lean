import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Exact arithmetic of certified intervals

These are finite algebraic components of `sec:printing`, `sec:algorithm`, `sec:imports` and `sec:gadget-transfer` of the
paper. On their own they do not assert that the counting algorithm exists, that its reconstruction is correct,
or that it satisfies the running time; other modules prove those.
In particular `cell_interval_sound` assumes exactness of the certified cells;
the paper's reconstruction argument (proof of `prop:sound`) must supply that premise.
-/

namespace NearCubicGates.Certificates

open scoped BigOperators

/-- A closed interval represented by midpoint and nonnegative radius. -/
structure Interval where
  center : ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius

def Interval.Contains (I : Interval) (p : ℝ) : Prop :=
  |I.center - p| ≤ I.radius

theorem contains_iff (I : Interval) (p : ℝ) :
    I.Contains p ↔ I.center - I.radius ≤ p ∧ p ≤ I.center + I.radius := by
  unfold Interval.Contains
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

noncomputable def defaultInterval : Interval := ⟨1 / 2, 1 / 2, by norm_num⟩

theorem default_sound (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    defaultInterval.Contains p := by
  rw [contains_iff]
  dsimp [defaultInterval]
  constructor <;> linarith

/-- The sign is handled in the center and the absolute value in the radius. -/
def Interval.scale (a : ℝ) (I : Interval) : Interval :=
  ⟨a * I.center, |a| * I.radius, mul_nonneg (abs_nonneg _) I.radius_nonneg⟩

theorem scale_sound (a p : ℝ) (I : Interval) (h : I.Contains p) :
    (I.scale a).Contains (a * p) := by
  change |a * I.center - a * p| ≤ |a| * I.radius
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg a)

def Interval.add (I J : Interval) : Interval :=
  ⟨I.center + J.center, I.radius + J.radius,
    add_nonneg I.radius_nonneg J.radius_nonneg⟩

theorem add_sound (I J : Interval) (p q : ℝ)
    (hp : I.Contains p) (hq : J.Contains q) :
    (I.add J).Contains (p + q) := by
  change |I.center + J.center - (p + q)| ≤ I.radius + J.radius
  calc
    _ = |(I.center - p) + (J.center - q)| := by congr 1; ring
    _ ≤ |I.center - p| + |J.center - q| := abs_add_le _ _
    _ ≤ I.radius + J.radius := add_le_add hp hq

theorem upper_endpoint_sound (I : Interval) (p : ℝ) (h : I.Contains p) :
    p ≤ I.center + I.radius := (contains_iff I p).mp h |>.2

theorem upper_endpoint_loss (I : Interval) (p θ : ℝ)
    (h : I.Contains p) (hθ : I.radius ≤ θ) :
    I.center + I.radius ≤ p + 2 * θ := by
  have := (contains_iff I p).mp h |>.1
  linarith

theorem lower_endpoint_sound (I : Interval) (p : ℝ) (h : I.Contains p) :
    I.center - I.radius ≤ p := (contains_iff I p).mp h |>.1

theorem lower_endpoint_loss (I : Interval) (p θ : ℝ)
    (h : I.Contains p) (hθ : I.radius ≤ θ) :
    p - 2 * θ ≤ I.center - I.radius := by
  have := (contains_iff I p).mp h |>.2
  linarith

variable {ι : Type*}

/-- Finite signed interval combination; no independence assumption appears. -/
theorem signed_sum_sound (s : Finset ι) (a p c r : ι → ℝ)
    (h : ∀ i ∈ s, |c i - p i| ≤ r i) :
    |(∑ i ∈ s, a i * c i) - (∑ i ∈ s, a i * p i)| ≤
      ∑ i ∈ s, |a i| * r i := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ = |∑ i ∈ s, a i * (c i - p i)| := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ s, |a i * (c i - p i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |a i| * |c i - p i| := by
      apply Finset.sum_congr rfl
      intro i hi
      exact abs_mul _ _
    _ ≤ ∑ i ∈ s, |a i| * r i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (h i hi) (abs_nonneg _)

theorem coefficient_mass_budget (s : Finset ι) (a r : ι → ℝ)
    (β M : ℝ) (hβ : 0 ≤ β) (hr : ∀ i ∈ s, r i ≤ β)
    (hm : ∑ i ∈ s, |a i| ≤ M) :
    ∑ i ∈ s, |a i| * r i ≤ β * M := by
  calc
    _ ≤ ∑ i ∈ s, |a i| * β := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hr i hi) (abs_nonneg _)
    _ = (∑ i ∈ s, |a i|) * β := (Finset.sum_mul ..).symm
    _ ≤ M * β := mul_le_mul_of_nonneg_right hm hβ
    _ = β * M := mul_comm _ _

/-- Uncertain cells contribute half their cardinality as radius.  This is
the numerator version of `eq:output`, before division by 2^n. -/
theorem cell_interval_sound (s : Finset ι) (exact : ι → Bool)
    (truth recovered : ι → ℝ) (cellSize : ℝ)
    (hlo : ∀ i ∈ s, 0 ≤ truth i)
    (hhi : ∀ i ∈ s, truth i ≤ cellSize)
    (he : ∀ i ∈ s, exact i = true → recovered i = truth i) :
    |(∑ i ∈ s, if exact i then recovered i else cellSize / 2) -
        (∑ i ∈ s, truth i)| ≤
      ∑ i ∈ s, if exact i then 0 else cellSize / 2 := by
  rw [← Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply Finset.sum_le_sum
  intro i hi
  cases h : exact i with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [abs_le]
      have h₀ := hlo i hi
      have h₁ := hhi i hi
      constructor <;> linarith
  | true =>
      simp [he i hi h]

/-- Algebraic soundness of combining scalar intervals with a verified
pointwise representation error. This does not prove Fourier existence. -/
theorem representation_interval_sound (p approximate center η radius : ℝ)
    (hrep : |p - approximate| ≤ η)
    (hnative : |approximate - center| ≤ radius) :
    |p - center| ≤ η + radius := by
  calc
    |p - center| = |(p - approximate) + (approximate - center)| := by
      congr 1; ring
    _ ≤ |p - approximate| + |approximate - center| := abs_add_le _ _
    _ ≤ η + radius := add_le_add hrep hnative

/-- Numerical reserve from the periodic supplier, once native calls and
the coefficient-mass bound have been established. -/
theorem periodic_radius_reserve (m r η β : ℝ)
    (hη : η ≤ r / 2) (hβ : β ≤ r / (32 * m ^ 2))
    (hmpos : 0 < m) : η + 8 * m ^ 2 * β ≤ 3 * r / 4 := by
  have hd : 0 < 32 * m ^ 2 := by positivity
  have hb := (le_div_iff₀ hd).mp hβ
  nlinarith

/-- The strict gadget acceptance margin used in the unrestricted transfer. -/
theorem gadget_acceptance_margin (γ ε δ U : ℝ)
    (hγ : γ < 1) (hε : 0 < ε) (hδ : δ ≤ γ / 5 - ε)
    (hU : U ≤ (5 + ε) * δ + 10 * (ε / 128)) :
    U < γ - ε := by
  have hmul : (5 + ε) * δ ≤ (5 + ε) * (γ / 5 - ε) :=
    mul_le_mul_of_nonneg_left hδ (by linarith)
  nlinarith [sq_nonneg ε]

end NearCubicGates.Certificates
