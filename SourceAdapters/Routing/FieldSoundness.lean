import SourceAdapters.Routing.BenesSoundness
import Mathlib.Algebra.CharP.Two

/-! Local characteristic-two equations transport all columns by one permutation. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.FieldSoundness

variable {F : Type} [Field F] [CharP F 2]

/-- The routing equation is precisely the selected stay-or-cross equality. -/
theorem routing_equation_iff (b : Bool) (u v w : F) :
    u + v + (if b then 1 else 0) * (v + w) = 0 ↔
      (if b then w else v) = u := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, one_mul, add_zero]
  · rw [CharTwo.add_eq_zero, eq_comm]
  · rw [add_assoc, CharTwo.add_cancel_left, CharTwo.add_eq_zero, eq_comm]

/-- No label-injectivity hypothesis is needed for soundness: the same
switch value is used for all columns, and all equations are on the given table. -/
theorem fieldRoutingSoundness (l : Layout) (e : Fin l.m → F) :
    FieldRoutingSoundness l e := by
  classical
  intro a h
  obtain ⟨_, hbit, hcolumn, hpair, hroute⟩ := h
  let c0 : Fin l.C := ⟨0, by unfold Layout.C; positivity⟩
  let s : Settings l.k := fun j x => decide (switchValue l e a j x c0 = 1)
  have hs : Coherent l.k s := by
    intro j hj x
    dsimp only [s]
    rw [hpair j hj x c0]
  have value (j : ℕ) (hj : j < switchCount l.k) (x : Lane l.k) (c : Fin l.C) :
      switchValue l e a j x c = if s j x then 1 else 0 := by
    rw [← hcolumn j hj x c0 c]
    rcases hbit j hj x c0 with hz | ho
    · simp [s, hz]
    · simp [s, ho]
  have transport : ∀ j < switchCount l.k, ∀ x,
      (fun c => dataValue l e a (j + 1) (stageMap l.k s j x) c) =
        (fun c => dataValue l e a j x c) := by
    intro j hj x
    funext c
    have hr := hroute j hj x c
    rw [value j hj x c] at hr
    have ht := (routing_equation_iff (s j x) _ _ _).mp hr
    cases hbool : s j x <;> simpa only [stageMap, hbool, Bool.false_eq_true,
      ↓reduceIte] using ht
  refine ⟨Equiv.ofBijective (path l.k s) (Soundness.path_bijective l.k s hs), ?_⟩
  intro x c
  exact congrFun (Soundness.path_transport l.k s (Fin l.C → F)
    (fun j x c => dataValue l e a j x c) transport x) c

end NearCubicGates.Adapters.Routing.FieldSoundness
