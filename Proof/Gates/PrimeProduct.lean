import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Product divisibility for a finite list of pairwise distinct prime factors. -/

set_option autoImplicit false

namespace NearCubicGates.PrimeProduct

open scoped BigOperators

theorem product_dvd {ι R : Type*} [CommMonoidWithZero R]
    (s : Finset ι) (B : ι → R)
    (hprime : ∀ i ∈ s, Prime (B i))
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ B i ∣ B j)
    (f : R) (hfactor : ∀ i ∈ s, B i ∣ f) : (∏ i ∈ s, B i) ∣ f := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨g, hg⟩ := hfactor i (Finset.mem_insert_self i s)
    have hrest : ∀ j ∈ s, B j ∣ g := by
      intro j hj
      have hJ := hfactor j (Finset.mem_insert_of_mem hj)
      rw [hg] at hJ
      rcases (hprime j (Finset.mem_insert_of_mem hj)).dvd_mul.mp hJ with hji | hjg
      · exact False.elim (hdistinct j (Finset.mem_insert_of_mem hj) i
          (Finset.mem_insert_self i s) (by intro he; subst j; exact hi hj) hji)
      · exact hjg
    have hprod := ih (fun j hj => hprime j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk hne => hdistinct j (Finset.mem_insert_of_mem hj) k
        (Finset.mem_insert_of_mem hk) hne) g hrest
    rw [Finset.prod_insert hi, hg]
    exact mul_dvd_mul_left (B i) hprod

end NearCubicGates.PrimeProduct
