import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Basic

/-! Zero actual fiber sums and pairwise monomial congruences force a factor
    of the generating sum. Representatives are selected from the finite image;
    no kernel/primality hypothesis is inserted here. -/

set_option autoImplicit false

namespace NearCubicGates.FiberDivisibility

open scoped BigOperators

theorem factor_of_zero_fibers {Points Score R : Type*} [Fintype Points]
    [Nonempty Points] [DecidableEq Score] [CommRing R]
    (score : Points → Score) (coefficient monomial : Points → R) (B : R)
    (hzero : ∀ s, (∑ x, if score x = s then coefficient x else 0) = 0)
    (hfactor : ∀ x y, score x = score y → B ∣ monomial x - monomial y) :
    B ∣ ∑ x, coefficient x * monomial x := by
  classical
  let rep : Score → Points := fun s => if h : ∃ x, score x = s then
    Classical.choose h else Classical.choice (inferInstance : Nonempty Points)
  have hrep : ∀ x, score (rep (score x)) = score x := by
    intro x
    have hx : ∃ y, score y = score x := ⟨x, rfl⟩
    simp only [rep, dif_pos hx]
    exact Classical.choose_spec hx
  let S : Finset Score := Finset.univ.image score
  have hm : ∀ x ∈ Finset.univ, score x ∈ S :=
    fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hvanish : (∑ x, coefficient x * monomial (rep (score x))) = 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to hm]
    apply Finset.sum_eq_zero
    intro s _
    calc
      _ = ∑ x ∈ Finset.univ.filter (fun x => score x = s), coefficient x * monomial (rep s) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ = (∑ x ∈ Finset.univ.filter (fun x => score x = s), coefficient x) * monomial (rep s) :=
        (Finset.sum_mul ..).symm
      _ = 0 := by rw [Finset.sum_filter, hzero s, zero_mul]
  have hd : B ∣ ∑ x, coefficient x * (monomial x - monomial (rep (score x))) := by
    apply Finset.dvd_sum
    intro x _
    exact dvd_mul_of_dvd_right (hfactor x (rep (score x)) (hrep x).symm) _
  simpa only [mul_sub, Finset.sum_sub_distrib, hvanish, sub_zero] using hd

end NearCubicGates.FiberDivisibility
