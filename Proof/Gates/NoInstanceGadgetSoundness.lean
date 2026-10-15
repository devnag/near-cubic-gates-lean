import Proof.Gates.GadgetPairMeans

/-! Every sound tuple of the ten intervals rejects a hierarchy NO instance
    once the pointwise three-query gap and the outer acceptance bound hold.
    These finite hypotheses are where the published PCP constructions connect. -/

set_option autoImplicit false

namespace NearCubicGates.NoInstanceGadgetSoundness

open scoped BigOperators
open FiniteAverages GadgetPairMeans Certificates

variable {Input G : Type*} [Fintype Input] [Nonempty Input] [Fintype G] [Nonempty G]

noncomputable def falseClauseMean (bits : G → Input → Fin 4 → Bool) (x : Input) : ℝ :=
  mean (fun a => if Gadget.originalClause (bits a x 0) (bits a x 1) (bits a x 2)
    then 0 else 1)

omit [Fintype Input] [Nonempty Input] [Nonempty G] in
theorem falseMean_le_penalty (bits : G → Input → Fin 4 → Bool) (x : Input) :
    falseClauseMean bits x ≤ mean (fun a =>
      (Gadget.penalty (bits a x 0) (bits a x 1) (bits a x 2) (bits a x 3) : ℝ)) := by
  apply mean_le_mean
  intro a
  have h := Gadget.false_indicator_le_penalty (bits a x 0) (bits a x 1) (bits a x 2) (bits a x 3)
  have hc : ((if Gadget.originalClause (bits a x 0) (bits a x 1) (bits a x 2)
    then (0 : ℤ) else 1) : ℝ) ≤
      (Gadget.penalty (bits a x 0) (bits a x 1) (bits a x 2) (bits a x 3) : ℝ) := by exact_mod_cast h
  simpa only [Int.cast_ite, Int.cast_zero, Int.cast_one] using hc

omit [Fintype Input] [Nonempty Input] in
theorem penalty_mean_nonneg (bits : G → Input → Fin 4 → Bool) (x : Input) :
    0 ≤ mean (fun a =>
      (Gadget.penalty (bits a x 0) (bits a x 1) (bits a x 2) (bits a x 3) : ℝ)) := by
  have h := mean_le_mean (fun _ : G => (0 : ℝ))
    (fun a => (Gadget.penalty (bits a x 0) (bits a x 1) (bits a x 2) (bits a x 3) : ℝ))
    (fun a => by
      exact_mod_cast (Gadget.penalty_nonnegative
        (bits a x 0) (bits a x 1) (bits a x 2) (bits a x 3)))
  simpa using h

theorem gap_lower_bound (bits : G → Input → Fin 4 → Bool) (D : Input → Bool)
    (γ η : ℝ) (hγ : 0 ≤ γ)
    (hpointwise : ∀ x, D x = false → γ ≤ falseClauseMean bits x)
    (houter : mean (fun x => (Gadget.bit (D x) : ℝ)) ≤ η) :
    γ * (1 - η) ≤ exactPenalty bits := by
  have hpoint : ∀ x, γ * (if D x then (0 : ℝ) else 1) ≤
      mean (fun a => (Gadget.penalty (bits a x 0) (bits a x 1) (bits a x 2) (bits a x 3) : ℝ)) := by
    intro x
    cases hx : D x
    · simpa only [Bool.false_eq_true, ↓reduceIte, mul_one] using
        (hpointwise x hx).trans (falseMean_le_penalty bits x)
    · simpa only [↓reduceIte, mul_zero] using penalty_mean_nonneg bits x
  have hm := mean_le_mean _ _ hpoint
  rw [mean_smul] at hm
  have hb : mean (fun x => if D x then (0 : ℝ) else 1) =
      1 - mean (fun x => (Gadget.bit (D x) : ℝ)) := by
    have hid : (fun x => (if D x then (0 : ℝ) else 1) + (Gadget.bit (D x) : ℝ)) =
        (fun _ : Input => (1 : ℝ)) := by
      funext x
      cases D x <;> norm_num [Gadget.bit]
    have hh := congrArg mean hid
    rw [mean_add, mean_const] at hh
    linarith
  rw [hb] at hm
  have hlow : γ * (1 - η) ≤ γ * (1 - mean (fun x => (Gadget.bit (D x) : ℝ))) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hγ
  have he : exactPenalty bits = mean (fun x => mean (fun a =>
      (Gadget.penalty (bits a x 0) (bits a x 1) (bits a x 2) (bits a x 3) : ℝ))) :=
    mean_mean_comm _
  rw [he]
  exact hlow.trans hm

theorem every_sound_witness_rejects (bits : G → Input → Fin 4 → Bool)
    (D : Input → Bool) (I : G → Fin 10 → Interval) (γ η ε : ℝ)
    (hγ : 0 ≤ γ) (hpointwise : ∀ x, D x = false → γ ≤ falseClauseMean bits x)
    (houter : mean (fun x => (Gadget.bit (D x) : ℝ)) ≤ η)
    (hI : ∀ a i, (I a i).Contains (probabilities bits a i)) (hreserve : γ * η < ε) :
    γ - ε < upper I := by
  have hl := gap_lower_bound bits D γ η hγ hpointwise houter
  have hu := upper_sound bits I hI
  nlinarith

end NearCubicGates.NoInstanceGadgetSoundness
