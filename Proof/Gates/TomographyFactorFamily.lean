import Proof.Gates.BinomialSeparation
import Proof.Gates.PrimitiveDirectionSeparation
import Proof.Gates.PrimeProduct
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma

/-! The actual family of short primitive binomials used by tomography. -/

set_option autoImplicit false

namespace NearCubicGates.ProjectionBinomials

noncomputable section

open scoped BigOperators
open TomographyDirections PrimitiveDirectionSeparation Polynomial

abbrev ShellIndex (q : ℕ) := Σ m : {m // m ∈ Finset.Icc 2 q}, {a // a ∈ shell m.val}
abbrev Direction (q : ℕ) := Option (ShellIndex q × Bool)

def factor (q : ℕ) : Direction q → Bivariate
  | none => verticalBinomial
  | some (d, false) => positiveBinomial d.2.val (d.1.val - d.2.val)
  | some (d, true) => negativeBinomial d.2.val (d.1.val - d.2.val)

theorem index_bounds {q : ℕ} (d : ShellIndex q) :
    0 < d.2.val ∧ 0 < d.1.val - d.2.val ∧ d.1.val ≤ q := by
  have hm := Finset.mem_Icc.mp d.1.property
  have ha := shell_bounds d.1.val hm.1 d.2.property
  omega

theorem factor_prime (q : ℕ) (d : Direction q) : Prime (factor q d) := by
  rcases d with _ | ⟨i, flag⟩
  · exact verticalBinomial_prime
  · have hb := index_bounds i
    cases flag
    · exact positiveBinomial_prime _ _ hb.1 hb.2.1 (shell_coprime _ i.2.property)
    · exact negativeBinomial_prime _ _ hb.1 hb.2.1 (shell_coprime _ i.2.property)

theorem index_ext {q : ℕ} (d e : ShellIndex q)
    (h : (d.1.val, d.2.val) = (e.1.val, e.2.val)) : d = e := by
  rcases d with ⟨⟨m, hm⟩, ⟨a, ha⟩⟩
  rcases e with ⟨⟨n, hn⟩, ⟨b, hb⟩⟩
  have hmn : m = n := congrArg Prod.fst h
  have hab : a = b := congrArg Prod.snd h
  subst n
  subst b
  rfl

theorem index_determinant {q : ℕ} (d e : ShellIndex q) (hne : d ≠ e) :
    (e.1.val - e.2.val) * d.2.val ≠ e.2.val * (d.1.val - d.2.val) := by
  apply distinct_shell_determinant _ _ _ _ (Finset.mem_Icc.mp d.1.property).1
    (Finset.mem_Icc.mp e.1.property).1 d.2.property e.2.property
  exact fun h => hne (index_ext d e h)

theorem factor_not_dvd {q : ℕ} (d e : Direction q) (hne : d ≠ e) :
    ¬ factor q d ∣ factor q e := by
  rcases d with _ | ⟨i, flag⟩ <;> rcases e with _ | ⟨j, other⟩
  · exact False.elim (hne rfl)
  · have hb := index_bounds j
    cases other
    · exact (vertical_not_dvd_binomials _ _ hb.1).1
    · exact (vertical_not_dvd_binomials _ _ hb.1).2
  · have hb := index_bounds i
    cases flag
    · exact (binomials_not_dvd_vertical _ _ hb.1).1
    · exact (binomials_not_dvd_vertical _ _ hb.1).2
  · have hi := index_bounds i
    have hj := index_bounds j
    cases flag <;> cases other
    · apply positive_not_dvd_positive
      exact_mod_cast index_determinant i j (fun h => hne (by rw [h]))
    · exact positive_not_dvd_negative _ _ _ _ hi.1 hi.2.1 hj.1 hj.2.1
    · exact negative_not_dvd_positive _ _ _ _ hi.1 hi.2.1 hj.1 hj.2.1
    · apply negative_not_dvd_negative
      exact_mod_cast index_determinant i j (fun h => hne (by rw [h]))

def factorProduct (q : ℕ) : Bivariate := ∏ d : Direction q, factor q d

theorem factorProduct_dvd (q : ℕ) (f : Bivariate)
    (h : ∀ d : Direction q, factor q d ∣ f) : factorProduct q ∣ f := by
  exact PrimeProduct.product_dvd Finset.univ (factor q)
    (fun d _ => factor_prime q d) (fun d _ e _ hne => factor_not_dvd d e hne)
    f (fun d _ => h d)

theorem factorProduct_natDegree (q : ℕ) (hq : 1 ≤ q) :
    (factorProduct q).natDegree = degreeSum q := by
  rw [factorProduct, Polynomial.natDegree_prod Finset.univ (factor q)
    (fun d _ => (factor_prime q d).ne_zero)]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  have hsum : (∑ d : ShellIndex q, ∑ flag : Bool, (factor q (some (d, flag))).natDegree) =
      ∑ m ∈ Finset.Icc 2 q, 2 * ∑ a ∈ shell m, (m - a) := by
    simp only [Fintype.sum_bool, factor, positiveBinomial_natDegree, negativeBinomial_natDegree,
      ← two_mul, Fintype.sum_sigma, Finset.mul_sum]
    calc
      _ = ∑ m : {m // m ∈ Finset.Icc 2 q}, ∑ a ∈ shell m.val, 2 * (m.val - a) := by
        apply Finset.sum_congr rfl
        intro m _
        exact Finset.sum_coe_sort (shell m.val) (fun a => 2 * (m.val - a))
      _ = _ := Finset.sum_coe_sort (Finset.Icc 2 q)
        (fun m => ∑ a ∈ shell m, 2 * (m - a))
  rw [hsum, factor, verticalBinomial_natDegree]
  simpa [directionalDegree, show q ≠ 0 by omega] using directionalDegree_eq q

end
end NearCubicGates.ProjectionBinomials
