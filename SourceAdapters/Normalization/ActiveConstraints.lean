import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Active constraints of a finite pointed system

The integer normalization in `lem:integer` uses a basic feasible solution of a
finite system of linear inequalities. The following algebraic proof works over
any linearly ordered field: maximize the number of active constraints, then move
in a direction annihilating them until a new constraint becomes tight.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Normalization

open Finset

variable {R E ι : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E] [Fintype ι]

def activeConstraints (A : ι → E →ₗ[R] R) (b : ι → R) (x : E) : Finset ι := by
  classical
  exact univ.filter fun i => A i x = b i

omit [IsStrictOrderedRing R] in
@[simp] theorem mem_activeConstraints (A : ι → E →ₗ[R] R) (b : ι → R) (x : E) (i : ι) :
    i ∈ activeConstraints A b x ↔ A i x = b i := by
  classical
  simp [activeConstraints]

/-- A feasible direction which annihilates all tight constraints either continues
forever or reaches a new tight constraint. A negative slope forces the latter. -/
theorem exists_more_active (A : ι → E →ₗ[R] R) (b : ι → R) (x v : E)
    (hx : ∀ i, b i ≤ A i x) (hv : ∀ i, A i x = b i → A i v = 0)
    (hneg : ∃ i, A i v < 0) :
    ∃ y, (∀ i, b i ≤ A i y) ∧ activeConstraints A b x ⊂ activeConstraints A b y := by
  classical
  let J : Finset ι := univ.filter fun i => A i v < 0
  have hJ : J.Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, by simpa [J] using hi⟩
  let q : ι → R := fun i => (A i x - b i) / (-A i v)
  obtain ⟨j, hj, hmin⟩ := J.exists_min_image q hJ
  have hjv : A j v < 0 := by simpa [J] using hj
  have hjx : b j < A j x := by
    have h := hx j
    by_contra hn
    have he : A j x = b j := le_antisymm (le_of_not_gt hn) h
    have := hv j he
    linarith
  have hq : 0 < q j := div_pos (sub_pos.mpr hjx) (neg_pos.mpr hjv)
  let y := x + q j • v
  have hy (i : ι) : b i ≤ A i y := by
    change b i ≤ A i (x + q j • v)
    rw [map_add, map_smul, smul_eq_mul]
    by_cases hi : A i v < 0
    · have hm : q j ≤ q i := hmin i (by simpa [J] using hi)
      have hd : 0 < -A i v := neg_pos.mpr hi
      have hmul := (le_div_iff₀ hd).mp hm
      change q j * (-A i v) ≤ A i x - b i at hmul
      nlinarith
    · have hnonneg : 0 ≤ A i v := le_of_not_gt hi
      have hmul : 0 ≤ q j * A i v := mul_nonneg hq.le hnonneg
      linarith [hx i]
  have hsub : activeConstraints A b x ⊆ activeConstraints A b y := by
    intro i hi
    have hi' := (mem_activeConstraints A b x i).mp hi
    apply (mem_activeConstraints A b y i).mpr
    simp only [y, map_add, map_smul, smul_eq_mul, hv i hi', mul_zero, add_zero, hi']
  have hjy : j ∈ activeConstraints A b y := by
    apply (mem_activeConstraints A b y j).mpr
    dsimp only [y]
    rw [map_add, map_smul, smul_eq_mul]
    have hd : -A j v ≠ 0 := ne_of_gt (neg_pos.mpr hjv)
    have he : q j * (-A j v) = A j x - b j := div_mul_cancel₀ _ hd
    nlinarith
  have hjnot : j ∉ activeConstraints A b x := by
    simp only [mem_activeConstraints]
    exact ne_of_gt hjx
  exact ⟨y, hy, Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hjnot (by rw [he]; exact hjy)⟩⟩

/-- A nonempty finite system whose normals separate directions has a feasible
point at which the active normals still separate directions. -/
theorem exists_active_separating (A : ι → E →ₗ[R] R) (b : ι → R)
    (hsep : ∀ v : E, (∀ i, A i v = 0) → v = 0)
    (hne : ∃ x : E, ∀ i, b i ≤ A i x) :
    ∃ x : E, (∀ i, b i ≤ A i x) ∧
      ∀ v : E, (∀ i, A i x = b i → A i v = 0) → v = 0 := by
  classical
  let S : Set (Finset ι) := {s | ∃ x : E, (∀ i, b i ≤ A i x) ∧ activeConstraints A b x = s}
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨activeConstraints A b x, x, hx, rfl⟩
  obtain ⟨s, hs, hmax⟩ := Set.exists_max_image S Finset.card (Set.toFinite S) hS
  obtain ⟨x, hx, hxs⟩ := hs
  refine ⟨x, hx, ?_⟩
  intro v hv
  by_contra hv0
  have hn : ∃ i, A i v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (hsep v h)
  obtain ⟨i, hi⟩ := hn
  have hmore : ∃ y, (∀ i, b i ≤ A i y) ∧
      activeConstraints A b x ⊂ activeConstraints A b y := by
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · exact exists_more_active A b x v hx hv ⟨i, hneg⟩
    · exact exists_more_active A b x (-v) hx
        (fun j hj => by rw [map_neg, hv j hj, neg_zero])
        ⟨i, by simpa only [map_neg] using neg_neg_of_pos hpos⟩
  obtain ⟨y, hy, hxy⟩ := hmore
  have hm := hmax (activeConstraints A b y) ⟨y, hy, rfl⟩
  have hc := Finset.card_lt_card hxy
  rw [← hxs] at hm
  omega

end NearCubicGates.Adapters.Normalization
