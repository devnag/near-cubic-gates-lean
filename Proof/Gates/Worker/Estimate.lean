import Proof.Gates.Gadget
import Proof.Gates.FiniteAverages
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicGates NearCubicGates.Gadget NearCubicGates.FiniteAverages

/-- The ten basic terms at one point: helper, three literals, three literal pairs, three literal–helper pairs. -/
def tenTerms (x₁ x₂ x₃ y : Bool) : Fin 10 → Bool :=
  ![y, x₁, x₂, x₃, xor x₁ x₂, xor x₁ x₃, xor x₂ x₃, xor x₁ y, xor x₂ y, xor x₃ y]

/-- Their signs in eq:gadget-pair-identity. -/
def tenSigns : Fin 10 → ℤ := ![1, -1, -1, -1, -1, -1, -1, 1, 1, 1]

/-- eq:gadget-pair-identity: `Q = 1 + ½ Σ_t σ_t [term_t]`. -/
theorem penalty_ten (x₁ x₂ x₃ y : Bool) :
    (penalty x₁ x₂ x₃ y : ℝ) = 1 + (1 / 2) * ∑ t : Fin 10, (tenSigns t : ℝ) * (bit (tenTerms x₁ x₂ x₃ y t) : ℝ) := by
  have h := pair_xor_identity x₁ x₂ x₃ y
  have h' : ((2 * penalty x₁ x₂ x₃ y : ℤ) : ℝ) = ((2 + bit y - (bit x₁ + bit x₂ + bit x₃) -
        (bit (Bool.xor x₁ x₂) + bit (Bool.xor x₁ x₃) + bit (Bool.xor x₂ x₃)) +
        (bit (Bool.xor x₁ y) + bit (Bool.xor x₂ y) + bit (Bool.xor x₃ y)) : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  simp [Fin.sum_univ_succ, tenSigns, tenTerms]
  linarith

variable {Gd Pt : Type*} [Fintype Gd] [Nonempty Gd] [Fintype Pt] [Nonempty Pt]

/-- A family of gadgets: literal values and helper values at every point. -/
structure GadgetFamily (Gd Pt : Type*) where
  x : Gd → Fin 3 → Pt → Bool
  y : Gd → Pt → Bool

namespace GadgetFamily
variable (F : GadgetFamily Gd Pt)

/-- Term `t` of gadget `a` as a function of the point. -/
def term (a : Gd) (t : Fin 10) (r : Pt) : Bool := tenTerms (F.x a 0 r) (F.x a 1 r) (F.x a 2 r) (F.y a r) t

/-- The mean of a term over points. -/
noncomputable def termMean (a : Gd) (t : Fin 10) : ℝ := mean (fun r => (bit (F.term a t r) : ℝ))

/-- `𝔼Q`: the penalty averaged over gadgets and points. -/
noncomputable def meanPenalty : ℝ :=
  mean (fun a : Gd => mean (fun r => (penalty (F.x a 0 r) (F.x a 1 r) (F.x a 2 r) (F.y a r) : ℝ)))

omit [Nonempty Gd] in
theorem meanPenalty_eq : F.meanPenalty =
    mean (fun a : Gd => 1 + (1 / 2) * ∑ t : Fin 10, (tenSigns t : ℝ) * F.termMean a t) := by
  unfold meanPenalty termMean
  congr 1
  funext a
  have key : ∀ r, (penalty (F.x a 0 r) (F.x a 1 r) (F.x a 2 r) (F.y a r) : ℝ) =
      1 + (1 / 2) * ∑ t : Fin 10, (tenSigns t : ℝ) * (bit (F.term a t r) : ℝ) := fun r => penalty_ten _ _ _ _
  simp only [key]
  unfold mean
  have hc : (Fintype.card Pt : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_comm]
  simp only [mul_div_assoc', ← Finset.mul_sum]
  rw [← Finset.sum_div]
  field_simp

end GadgetFamily

theorem tenSigns_cases (t : Fin 10) : tenSigns t = 1 ∨ tenSigns t = -1 := by
  fin_cases t <;> decide

/-- Intervals `(p̂, κ̂)` for every gadget and term. -/
abbrev Intervals (Gd : Type*) := Gd → Fin 10 → ℚ × ℚ

/-- The certified upper estimate `U`. -/
noncomputable def upper (I : Intervals Gd) : ℝ :=
  mean (fun a : Gd => 1 + (1 / 2) * ∑ t : Fin 10, ((tenSigns t : ℝ) * ((I a t).1 : ℝ) + ((I a t).2 : ℝ)))

/-- Every interval contains its term's mean. -/
def Sound (F : GadgetFamily Gd Pt) (I : Intervals Gd) : Prop :=
  ∀ a t, |((I a t).1 : ℝ) - F.termMean a t| ≤ ((I a t).2 : ℝ)

omit [Nonempty Gd] in
/-- eq:gadget-upper: `U ≥ 𝔼Q` for sound intervals. -/
theorem upper_ge (F : GadgetFamily Gd Pt) (I : Intervals Gd) (h : Sound F I) : F.meanPenalty ≤ upper I := by
  rw [F.meanPenalty_eq]
  unfold upper
  apply mean_le_mean
  intro a
  have : ∀ t : Fin 10, (tenSigns t : ℝ) * F.termMean a t ≤ (tenSigns t : ℝ) * ((I a t).1 : ℝ) + ((I a t).2 : ℝ) := by
    intro t
    have ht := abs_le.mp (h a t)
    rcases tenSigns_cases t with hs | hs <;> rw [hs] <;> push_cast <;> linarith [ht.1, ht.2]
  have := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => this t)
  linarith

/-- eq:gadget-upper-complete: `U ≤ 𝔼Q + 10ω` when also every radius is at most `ω`. -/
theorem upper_le (F : GadgetFamily Gd Pt) (I : Intervals Gd) (h : Sound F I) (ω : ℝ)
    (hω : ∀ a t, ((I a t).2 : ℝ) ≤ ω) : upper I ≤ F.meanPenalty + 10 * ω := by
  rw [F.meanPenalty_eq]
  unfold upper
  have hconst : mean (fun _a : Gd => 10 * ω) = 10 * ω := by
    unfold mean; simp
  rw [← hconst, ← mean_add]
  apply mean_le_mean
  intro a
  have : ∀ t : Fin 10, (tenSigns t : ℝ) * ((I a t).1 : ℝ) + ((I a t).2 : ℝ) ≤
      (tenSigns t : ℝ) * F.termMean a t + 2 * ω := by
    intro t
    have ht := abs_le.mp (h a t)
    have hw := hω a t
    rcases tenSigns_cases t with hs | hs <;> rw [hs] <;> push_cast <;> linarith [ht.1, ht.2]
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => this t)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  push_cast at hs
  rw [Finset.sum_add_distrib]
  linarith

end NearCubicGates.Close.Worker
