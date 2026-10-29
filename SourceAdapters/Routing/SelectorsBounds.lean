import SourceAdapters.Routing.SelectorsDegree

/-! Formal weighted degree of normalized selectors and emitted terms. -/
set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.Selectors

open scoped BigOperators
open Polynomial
variable {F : Type} [Field F]

theorem lift_linearized {m : ℕ} (c : Fin m → F) :
    liftX (linearized m c) =
      ∑ r : Fin m, MvPolynomial.C (c r) * MvPolynomial.X none ^ (2 ^ r.val) := by
  simp [liftX, linearized, Polynomial.eval₂_finsetSum]

theorem degree_coordinate {m : ℕ} (c : Fin m → F) :
    (liftX (linearized m c)).weightedTotalDegree (weight m) ≤ 2 ^ (m - 1) := by
  rw [lift_linearized]
  apply degree_sum
  intro r _
  have hx : (MvPolynomial.X none : MP F).weightedTotalDegree (weight m) ≤ 1 := by
    simp [degree_X, weight]
  have ht := degree_mul (weight m) (degree_C (weight m) (c r)) (degree_pow _ hx (2 ^ r.val))
  simp only [Nat.mul_one, Nat.zero_add] at ht
  exact ht.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem degree_selector {m : ℕ} {e : Fin m → F} (coords : Coordinates m e)
    (p : Pattern m) :
    (selector coords p).weightedTotalDegree (weight m) ≤ m * 2 ^ (m - 1) := by
  unfold selector
  have hb (a : Fin m) :
      (match p a with
        | none => (1 : MP F)
        | some true => liftX (linearized m (coords.coeff a))
        | some false => 1 + liftX (linearized m (coords.coeff a))).weightedTotalDegree
          (weight m) ≤ 2 ^ (m - 1) := by
    cases p a with
    | none => exact (degree_one _).trans (Nat.zero_le _)
    | some b =>
      cases b
      · exact degree_add _ ((degree_one _).trans (Nat.zero_le _)) (degree_coordinate _)
      · exact degree_coordinate _
  have hd := degree_prod (weight m) Finset.univ _ (2 ^ (m - 1)) (fun a _ => hb a)
  rw [Finset.card_univ, Fintype.card_fin] at hd
  exact hd

theorem degree_emit {m : ℕ} {e : Fin m → F} (coords : Coordinates m e)
    (ts : List (Term m F)) (d : ℕ)
    (ht : ∀ t ∈ ts, t.equation.weightedTotalDegree (weight m) ≤ d) :
    (emit coords ts).weightedTotalDegree (weight m) ≤ m * 2 ^ (m - 1) + d := by
  induction ts with
  | nil => exact (degree_zero _).trans (Nat.zero_le _)
  | cons t ts ih =>
    change (selector coords t.guard * t.equation + emit coords ts).weightedTotalDegree _ ≤ _
    apply degree_add
    · exact degree_mul _ (degree_selector coords t.guard) (ht t (by simp))
    · exact ih (fun u hu => ht u (by simp [hu]))

end NearCubicGates.Adapters.Routing.Selectors
