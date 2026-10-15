import Proof.Gates.Gadget
import Proof.Gates.Certificates
import Proof.Gates.FiniteAverages
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! Exact ten-term observations and their signed interval endpoints. XOR is
    used as an observable, without asserting circuit closure under XOR. -/

set_option autoImplicit false

namespace NearCubicGates.GadgetPairMeans

open scoped BigOperators
open FiniteAverages Certificates

def observations (x₁ x₂ x₃ y : Bool) : Fin 10 → Bool :=
  ![y, x₁, x₂, x₃, Bool.xor x₁ x₂, Bool.xor x₁ x₃, Bool.xor x₂ x₃,
    Bool.xor x₁ y, Bool.xor x₂ y, Bool.xor x₃ y]

def sign : Fin 10 → ℝ := ![1, -1, -1, -1, -1, -1, -1, 1, 1, 1]

theorem sign_abs (i : Fin 10) : |sign i| = 1 := by
  fin_cases i <;> norm_num [sign]

theorem pointwise_identity (x₁ x₂ x₃ y : Bool) :
    (Gadget.penalty x₁ x₂ x₃ y : ℝ) =
      1 + (∑ i, sign i * (Gadget.bit (observations x₁ x₂ x₃ y i) : ℝ)) / 2 := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> cases y <;>
    norm_num [Gadget.penalty, Gadget.bit, observations, sign, Fin.sum_univ_succ]

variable {Input G : Type*} [Fintype Input] [Nonempty Input]
  [Fintype G] [Nonempty G]

noncomputable def probabilities (bits : G → Input → Fin 4 → Bool)
    (a : G) (i : Fin 10) : ℝ :=
  mean (fun x => (Gadget.bit (observations (bits a x 0) (bits a x 1)
    (bits a x 2) (bits a x 3) i) : ℝ))

noncomputable def exactPenalty (bits : G → Input → Fin 4 → Bool) : ℝ :=
  mean (fun a => mean (fun x =>
    (Gadget.penalty (bits a x 0) (bits a x 1) (bits a x 2) (bits a x 3) : ℝ)))

omit [Nonempty G] in
theorem averaged_identity (bits : G → Input → Fin 4 → Bool) :
    exactPenalty bits = mean (fun a => 1 + (∑ i, sign i * probabilities bits a i) / 2) := by
  unfold exactPenalty
  congr 1
  funext a
  simp_rw [pointwise_identity, div_eq_mul_inv, mul_comm _ (2 : ℝ)⁻¹]
  rw [mean_add, mean_const, mean_smul, mean_finset_sum]
  simp_rw [mean_smul]
  rfl

noncomputable def upper (I : G → Fin 10 → Interval) : ℝ :=
  mean (fun a => 1 + (∑ i, (sign i * (I a i).center + (I a i).radius)) / 2)

theorem signed_endpoint_sound (I : Interval) (p : ℝ) (s : ℝ)
    (hs : |s| = 1) (h : I.Contains p) : s * p ≤ s * I.center + I.radius := by
  have hscaled := upper_endpoint_sound (I.scale s) (s * p) (scale_sound s p I h)
  simpa [Interval.scale, hs] using hscaled

theorem signed_endpoint_loss (I : Interval) (p s θ : ℝ)
    (hs : |s| = 1) (h : I.Contains p) (hθ : I.radius ≤ θ) :
    s * I.center + I.radius ≤ s * p + 2 * θ := by
  have hscaled := upper_endpoint_loss (I.scale s) (s * p) θ
    (scale_sound s p I h) (by simpa [Interval.scale, hs] using hθ)
  simpa [Interval.scale, hs] using hscaled

omit [Nonempty G] in
/-- Every supplied interval is sound, regardless of its radius. -/
theorem upper_sound (bits : G → Input → Fin 4 → Bool)
    (I : G → Fin 10 → Interval)
    (hI : ∀ a i, (I a i).Contains (probabilities bits a i)) :
    exactPenalty bits ≤ upper I := by
  rw [averaged_identity]
  apply mean_le_mean
  intro a
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    signed_endpoint_sound (I a i) (probabilities bits a i) (sign i) (sign_abs i) (hI a i)
  linarith

/-- The ten actual coefficients have magnitude one half, giving loss 10θ. -/
theorem upper_useful (bits : G → Input → Fin 4 → Bool)
    (I : G → Fin 10 → Interval) (θ : ℝ)
    (hI : ∀ a i, (I a i).Contains (probabilities bits a i))
    (hθ : ∀ a i, (I a i).radius ≤ θ) :
    upper I ≤ exactPenalty bits + 10 * θ := by
  rw [averaged_identity]
  have hpoint : ∀ a,
      1 + (∑ i, (sign i * (I a i).center + (I a i).radius)) / 2 ≤
      (1 + (∑ i, sign i * probabilities bits a i) / 2) + 10 * θ := by
    intro a
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      signed_endpoint_loss (I a i) (probabilities bits a i) (sign i) θ
        (sign_abs i) (hI a i) (hθ a i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    norm_num only [Nat.cast_ofNat] at hsum
    rw [Finset.sum_add_distrib]
    linarith
  have hm := mean_le_mean _ _ hpoint
  simpa [upper, mean_add] using hm

end NearCubicGates.GadgetPairMeans
