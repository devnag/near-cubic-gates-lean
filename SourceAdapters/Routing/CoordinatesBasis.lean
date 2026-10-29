import SourceAdapters.Routing.CoordinatesKernel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-! # Boolean cube independence supplies the solver's nonzero pivots -/

set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.Coordinates

open scoped BigOperators
variable {F : Type*} [Field F]

def cube (e : ℕ → F) (n : ℕ) (v : Fin n → Bool) : F :=
  ∑ i : Fin n, if v i then e i.val else 0

theorem cube_snoc (e : ℕ → F) (n : ℕ) (v : Fin n → Bool) (b : Bool) :
    cube e (n + 1) (Fin.snoc v b) = cube e n v + if b then e n else 0 := by
  simp [cube, Fin.sum_univ_castSucc]

theorem prefixSpan_has_cube [CharP F 2] (e : ℕ → F) (n : ℕ) (x : F)
    (hx : x ∈ prefixSpan e n) : ∃ v : Fin n → Bool, cube e n v = x := by
  induction n generalizing x with
  | zero =>
    have : x = 0 := hx
    subst x
    exact ⟨fun _ => false, by simp [cube]⟩
  | succ n ih =>
    rcases hx with hx | hx
    · obtain ⟨v, hv⟩ := ih x hx
      exact ⟨Fin.snoc v false, by simpa [cube_snoc] using hv⟩
    · obtain ⟨v, hv⟩ := ih (x + e n) hx
      refine ⟨Fin.snoc v true, ?_⟩
      rw [cube_snoc, hv]
      simp [add_assoc, CharTwo.add_self_eq_zero]

theorem cube_injective_init (e : ℕ → F) (n : ℕ)
    (hi : Function.Injective (cube e (n + 1))) : Function.Injective (cube e n) := by
  intro v w hvw
  have he : cube e (n + 1) (Fin.snoc v false) = cube e (n + 1) (Fin.snoc w false) := by
    simpa [cube_snoc] using hvw
  have h := hi he
  funext i
  simpa using congrFun h i.castSucc

theorem cube_injective_prefix (e : ℕ → F) {n m : ℕ} (hnm : n ≤ m)
    (hi : Function.Injective (cube e m)) : Function.Injective (cube e n) := by
  revert hi
  induction m, hnm using Nat.le_induction with
  | base => exact fun h => h
  | succ m _ ih => exact fun h => ih (cube_injective_init e m h)

theorem pivot_ne_zero_of_cube_injective [CharP F 2] (e : ℕ → F) (m : ℕ)
    (hi : Function.Injective (cube e m)) (n : ℕ) (hn : n < m) :
    (annihilator e n).eval (e n) ≠ 0 := by
  rw [pivot_ne_zero_iff]
  intro he
  obtain ⟨v, hv⟩ := prefixSpan_has_cube e n (e n) he
  have h := cube_injective_prefix e hn hi
  have same : cube e (n + 1) (Fin.snoc v false) =
      cube e (n + 1) (Fin.snoc (fun _ => false) true) := by
    rw [cube_snoc, cube_snoc, hv]
    simp [cube]
  have bad := congrFun (h same) (Fin.last n)
  simp at bad

end NearCubicGates.Adapters.Routing.Coordinates
